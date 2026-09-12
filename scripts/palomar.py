#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Developed with AI assistance; see ACKNOWLEDGEMENTS.md.
"""Validate and compare the Palomar package locally; never submit it.

The default proof check requires Linux and real Landrun. The explicit
--native option uses Comparator's upstream development launcher on macOS.
It still compares declarations and runs both kernels, but supplies no Landrun
isolation and is recorded as a native diagnostic, not Palomar verification.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time

from palomar_tools import ROOT, CACHE, PINS, tool_path, verify_checkout
from check import lean_code

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
SUCCESS = ('nanoda kernel accepts the solution',
           'Lean default kernel accepts the solution', 'Your solution is okay!')


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def proof_hashes() -> dict[str, str]:
    files = [ROOT / name for name in (
        'Challenge.lean', 'Solution.lean', 'Audit.lean', 'AllAxioms.lean',
        'RecurrentSections.lean', 'BorelToolkit.lean', 'MetricGeometry.lean',
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
        'comparator.json', 'formalization.yaml', 'LICENSE',
        'scripts/palomar.Dockerfile')]
    for library in ('RecurrentSections', 'BorelToolkit', 'MetricGeometry', 'scripts'):
        files.extend(p for p in (ROOT / library).rglob('*')
                     if p.is_file() and p.suffix in ('.lean', '.py', '.json', '.txt', '.c'))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(files))}


def validate() -> dict:
    import yaml
    import jsonschema
    for name in ('policy', 'metadata'):
        verify_checkout(name)
    sys.path.insert(0, str(tool_path('policy')))
    from scripts.submission_contract import load_formalization_metadata
    from scripts.verify_submission import load_comparator_config, repository_license_file
    metadata = load_formalization_metadata(ROOT / 'formalization.yaml')
    schema = json.loads((tool_path('metadata') / 'schema/v0.4.schema.json').read_text())
    jsonschema.validate(yaml.safe_load((ROOT / 'formalization.yaml').read_text()), schema)
    config = load_comparator_config(ROOT / 'comparator.json')
    require(config.get('enable_nanoda') is True, 'This project requires NanoDa to be enabled.')
    require(set(config['permitted_axioms']) == ALLOWED, 'Unexpected project axiom policy.')
    require(not config.get('definition_names'), 'This submission has no unspecified definitions.')
    require(len(config['theorem_names']) == len(set(config['theorem_names'])) == 5,
            'This submission advertises exactly five distinct theorems.')
    license_path = repository_license_file(ROOT)
    require(metadata['project']['license'] == 'Apache-2.0', 'Root licence metadata differs.')
    # Byte-identical standard Apache text, also used by PalomarTemplate.
    expected_license = 'c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4'
    require(hashlib.sha256(license_path.read_bytes()).hexdigest() == expected_license,
            'The standard Apache licence text changed; review licence identification.')
    challenge = ROOT / 'Challenge.lean'
    code = lean_code(challenge.read_text())
    require(challenge.stat().st_size <= 100 * 1024 and len(code.splitlines()) <= 1000,
            'Challenge exceeds Palomar hard limits.')
    imports = re.findall(r'(?m)^import\s+(\S+)', code)
    require(imports and all(n.startswith('Mathlib.') for n in imports),
            'Challenge must import only canonical Mathlib modules.')
    holes = re.findall(r'\bsorry\b', code)
    require(len(holes) == 5 and len(re.findall(r':=\s*by sorry\b', code)) == 5,
            'Only the five explicit Challenge theorem holes are allowed.')
    require(not re.search(r'\b(axiom|admit|unsafe|native_decide|implemented_by|ofReduceBool)\b', code),
            'Forbidden command in Challenge.')
    solution = lean_code((ROOT / 'Solution.lean').read_text())
    require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b', solution),
            'Unproved or unsafe Solution declaration.')
    require(not re.search(r'(?m)^import\s+Challenge\b', solution), 'Solution must not import Challenge.')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        require(package['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', package['rev']),
                f"Unpinned dependency: {package['name']}")
        require(re.fullmatch(r'https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', package['url']),
                f"Unsupported dependency URL: {package['name']}")
    # Verify that the canonical Mathlib dependency closure is unchanged.
    mathlib_path = ROOT / manifest['packagesDir'] / 'mathlib'
    mathlib_manifest = json.loads((mathlib_path / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    for package in mathlib_manifest['packages']:
        require(packages[package['name']]['rev'] == package['rev'],
                f"Changed Mathlib dependency: {package['name']}")
    listed = subprocess.check_output(
        ['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=ROOT)
    files = {ROOT / name.decode() for name in listed.split(b'\0') if name}
    forbidden = {'.olean', '.ilean', '.a', '.bc', '.dll', '.dylib', '.o', '.obj', '.so', '.trace'}
    for path in files:
        require(not path.is_symlink(), f'Submitted symlink: {path.relative_to(ROOT)}')
        require(path.suffix not in forbidden, f'Submitted compiled output: {path.relative_to(ROOT)}')
        if path.is_file():
            with path.open('rb') as handle:
                require(not handle.read(100).startswith(b'version https://git-lfs.github.com/spec/v1'),
                        f'Git LFS pointer: {path.relative_to(ROOT)}')
    stages = subprocess.check_output(['git', 'ls-files', '--stage'], cwd=ROOT, text=True)
    require(not re.search(r'(?m)^160000 ', stages), 'Submodules are not allowed.')
    size = sum(p.stat().st_size for p in files if p.is_file())
    require(size <= 500 * 1024**2, 'Submitted source exceeds 500 MiB.')
    print('Upstream v0.4 schema and Palomar metadata/configuration validators: passed.', flush=True)
    print('Local statement, dependency, licence, and source-layout checks: passed.', flush=True)
    return {'status': 'passed', 'compared_theorems': config['theorem_names'],
            'challenge_lines': len(challenge.read_text().splitlines()),
            'challenge_bytes': challenge.stat().st_size, 'source_bytes': size,
            'scope': 'Local checks; not the registry preparation or protected-import pipeline.'}


def command_and_environment(native: bool) -> tuple[list[str], dict[str, str]]:
    for name in ('comparator', 'lean4export', 'nanoda'):
        verify_checkout(name)
    env = os.environ.copy()
    env.setdefault('LEAN_NUM_THREADS', '2')
    if native:
        require(platform.system() == 'Darwin', '--native is the explicit macOS diagnostic mode.')
        launcher = tool_path('comparator') / 'scripts/fake-landrun.sh'
        print('Native diagnostic: no Landrun isolation; both kernels remain mandatory.', flush=True)
    else:
        require(platform.system() == 'Linux', 'Use Linux for the isolated check, or --native on macOS.')
        require(os.geteuid() != 0, 'Run the isolated comparison as an unprivileged user.')
        verify_checkout('landrun')
        launcher = CACHE / 'bin/landrun'
    binaries = {
        'COMPARATOR_LANDRUN': launcher,
        'COMPARATOR_LEAN4EXPORT': tool_path('lean4export') / '.lake/build/bin/lean4export',
        'COMPARATOR_NANODA': tool_path('nanoda') / 'target/release/nanoda_bin',
    }
    for key, value in binaries.items():
        require(value.is_file(), f'Missing tool {value}; run scripts/palomar_tools.py.')
        env[key] = str(value)
    command = ['lake', 'env', str(tool_path('comparator') / '.lake/build/bin/comparator'),
               'comparator.json']
    if not native:
        blocker = CACHE / 'bin/palomar-no-unix'
        require(blocker.is_file(), 'Missing AF_UNIX filter; rebuild the Linux tools.')
        command.insert(0, str(blocker))
    return command, env


def compare(project: Path, native: bool, log: Path) -> tuple[int, str, float]:
    command, env = command_and_environment(native)
    started = time.monotonic()
    log.parent.mkdir(parents=True, exist_ok=True)
    print(f'Comparator: {project.name}; output: {log.relative_to(ROOT)}', flush=True)
    with log.open('w') as output:
        proc = subprocess.run(command, cwd=project, env=env, stdout=output, stderr=subprocess.STDOUT)
    return proc.returncode, log.read_text(), time.monotonic() - started


def controls(native: bool, logs: Path) -> list[dict]:
    cases = [
        ('valid', 'theorem Probe.result : (2 : Nat) = 2 := by sorry\n',
         'theorem Probe.result : (2 : Nat) = 2 := by rfl\n', None),
        ('changed-statement', 'theorem Probe.result : (2 : Nat) = 2 := by sorry\n',
         'theorem Probe.result : (3 : Nat) = 3 := by rfl\n', 'theorem statement do not match'),
        ('changed-definition', 'def Probe.value : Nat := 2\ntheorem Probe.result : Probe.value = Probe.value := by sorry\n',
         'def Probe.value : Nat := 3\ntheorem Probe.result : Probe.value = Probe.value := by rfl\n',
         'Const does not match'),
        ('custom-axiom', 'theorem Probe.result : (2 : Nat) = 2 := by sorry\n',
         'axiom Probe.injected : (2 : Nat) = 2\ntheorem Probe.result : (2 : Nat) = 2 := Probe.injected\n',
         "Illegal axiom detected: 'Probe.injected'"),
        ('unproved-solution', 'theorem Probe.result : (2 : Nat) = 2 := by sorry\n',
         'theorem Probe.result : (2 : Nat) = 2 := by sorry\n', "Illegal axiom detected: 'sorryAx'"),
    ]
    results = []
    CACHE.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='controls-', dir=CACHE) as tmp:
        for name, challenge, solution, error in cases:
            project = Path(tmp) / name
            project.mkdir()
            (project / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
            (project / 'lakefile.toml').write_text('name = "palomar_probe"\n[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Solution"\n')
            (project / 'Challenge.lean').write_text(challenge)
            (project / 'Solution.lean').write_text(solution)
            config = json.loads((ROOT / 'comparator.json').read_text())
            config['theorem_names'] = ['Probe.result']
            (project / 'comparator.json').write_text(json.dumps(config))
            code, text, elapsed = compare(project, native, logs / f'{name}.txt')
            if error is None:
                require(code == 0 and all(s in text for s in SUCCESS), f'Positive control failed: {name}')
            else:
                require(code != 0 and error in text, f'Negative control failed for an unexpected reason: {name}')
            print(f'Control {name}: passed.', flush=True)
            results.append({'name': name, 'exit_code': code, 'expected_failure': error,
                            'elapsed_seconds': round(elapsed, 3),
                            'challenge': challenge, 'solution': solution})
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['validate', 'check', 'controls', 'all'])
    parser.add_argument('--native', action='store_true')
    parser.add_argument('--record', action='store_true')
    args = parser.parse_args()
    flavor = 'native' if args.native else ('linux' if platform.system() == 'Linux' else 'local')
    logs = ROOT / '.lake/palomar-results' / flavor
    logs.mkdir(parents=True, exist_ok=True)
    before = proof_hashes()
    result = {'timestamp_utc': datetime.now(timezone.utc).isoformat(),
              'mode': args.mode, 'platform': platform.platform(), 'landrun_isolation': not args.native and args.mode != 'validate',
              'registry_submission': False, 'tools': PINS, 'source_sha256': before}
    if args.mode in ('validate', 'all'):
        result['validation'] = validate()
    if args.mode in ('check', 'all'):
        code, text, elapsed = compare(ROOT, args.native, logs / 'comparator.txt')
        require(code == 0 and all(s in text for s in SUCCESS),
                f'Full comparison failed; inspect {logs / "comparator.txt"}')
        result['comparison'] = {'status': 'passed', 'exit_code': code,
                                'elapsed_seconds': round(elapsed, 3), 'kernels': ['nanoda', 'Lean']}
        print('All five statements match; NanoDa and Lean both accept the full solution.', flush=True)
    if args.mode in ('controls', 'all'):
        result['controls'] = controls(args.native, logs)
    require(before == proof_hashes(), 'Proof or verification inputs changed during the run; rerun.')
    if args.record:
        dest = ROOT / 'verification' / f'palomar-{flavor}'
        dest.mkdir(exist_ok=True)
        selected = (['comparator.txt'] if 'comparison' in result else [])
        if 'controls' in result:
            selected += [r['name'] + '.txt' for r in result['controls']]
        result['log_sha256'] = {}
        for name in selected:
            data = (logs / name).read_bytes()
            (dest / name).write_bytes(data)
            result['log_sha256'][name] = hashlib.sha256(data).hexdigest()
        (dest / f'{args.mode}.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Requested local checks passed. No registry submission was made.', flush=True)


if __name__ == '__main__':
    main()

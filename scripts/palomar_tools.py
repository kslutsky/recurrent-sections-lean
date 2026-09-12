#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Developed with AI assistance; see ACKNOWLEDGEMENTS.md.
"""Fetch and build pinned verification tools; never contact the registry intake.

Pins follow PalomarSubmission's submission.yml at the recorded revision.
The exporter is the exact v4.33.0-rc2 tag. Comparator uses its own toolchain
and manifest, independently of the library's Lean version.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / '.lake' / 'palomar'
PINS = json.loads((ROOT / 'scripts/palomar-pins.json').read_text())


def tool_path(name: str) -> Path:
    return CACHE / f"{name}-{PINS[name]['revision']}"


def run(args: list[str], cwd: Path = ROOT, env: dict[str, str] | None = None) -> None:
    print('+', ' '.join(args), flush=True)
    subprocess.run(args, cwd=cwd, env=env, check=True)


def verify_checkout(name: str) -> None:
    path = tool_path(name)
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
    if actual != PINS[name]['revision']:
        raise SystemExit(f'Wrong verification-tool revision: {name}')
    dirty = subprocess.check_output(
        ['git', 'status', '--porcelain', '--untracked-files=no'], cwd=path, text=True)
    if dirty:
        raise SystemExit(f'Modified tracked verification-tool sources: {name}')


def checkout(name: str) -> None:
    path = tool_path(name)
    if not path.exists():
        run(['git', 'clone', '--filter=blob:none', '--no-checkout',
             f"https://github.com/{PINS[name]['repository']}.git", str(path)])
        run(['git', 'checkout', '--detach', PINS[name]['revision']], cwd=path)
    verify_checkout(name)


def main() -> None:
    CACHE.mkdir(parents=True, exist_ok=True)
    for name in ('policy', 'metadata', 'comparator', 'lean4export', 'nanoda'):
        checkout(name)
    env = os.environ.copy()
    env.setdefault('LEAN_NUM_THREADS', '2')
    for name, target in [('comparator', 'comparator'), ('lean4export', 'lean4export')]:
        run(['lake', 'build', target], cwd=tool_path(name), env=env)
    if (tool_path('lean4export') / 'lean-toolchain').read_text().strip() != (
            ROOT / 'lean-toolchain').read_text().strip():
        raise SystemExit('The exporter and project toolchains differ; update the exporter pin.')
    env['CARGO_HOME'] = str(CACHE / 'cargo-home')
    env.setdefault('CARGO_BUILD_JOBS', '2')
    run(['cargo', 'build', '--release', '--locked'], cwd=tool_path('nanoda'), env=env)
    if platform.system() == 'Linux':
        if not shutil.which('go'):
            raise SystemExit('Linux verification requires Go to build the pinned Landrun.')
        checkout('landrun')
        (CACHE / 'bin').mkdir(exist_ok=True)
        env['GOBIN'] = str(CACHE / 'bin')
        env['GOCACHE'] = str(CACHE / 'go-build')
        env['GOMODCACHE'] = str(CACHE / 'go-modules')
        env['CGO_ENABLED'] = '0'
        run(['go', 'install', './cmd/landrun'], cwd=tool_path('landrun'), env=env)
        run(['cc', '-O2', '-Wall', '-Wextra', '-Werror',
             str(ROOT / 'scripts/palomar-no-unix.c'), '-lseccomp',
             '-o', str(CACHE / 'bin/palomar-no-unix')])
        run([str(CACHE / 'bin/palomar-no-unix'), 'python3',
             str(ROOT / 'scripts/check_socket_filter.py')])
    for name in ('policy', 'metadata', 'comparator', 'lean4export', 'nanoda'):
        verify_checkout(name)
    print('Pinned tools ready. No submission or registry request was made.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Konstantin Slutsky and contributors.
"""Build every project source and check the compiled axiom dependencies."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ["RecurrentSections", "BorelToolkit", "MetricGeometry"]


def fail(message: str) -> None:
    raise SystemExit(message)


def lean_code(text: str) -> str:
    """Remove nested comments and strings before checking forbidden tokens."""
    result = []
    i = depth = 0
    while i < len(text):
        if text[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def run(command: list[str], *, expected_failure: str | None = None) -> str:
    print("+ " + " ".join(command), flush=True)
    proc = subprocess.run(command, cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(proc.stdout, end="", flush=True)
    if expected_failure is None:
        if proc.returncode:
            fail(f"Command failed with exit code {proc.returncode}.")
    elif proc.returncode == 0 or expected_failure not in proc.stdout:
        fail("The negative-control audit did not reject the injected axiom.")
    return proc.stdout


def check_sources() -> list[Path]:
    modules = sorted(path for library in LIBRARIES
                     for path in (ROOT / library).rglob("*.lean"))
    drivers = [ROOT / (library + ".lean") for library in LIBRARIES]
    drivers += [ROOT / name for name in ["Audit.lean", "AllAxioms.lean"]]
    sources = modules + drivers
    forbidden = re.compile(
        r"\b(sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|ofReduceBool)\b")
    for path in sources:
        if path.is_symlink():
            fail(f"Project source must be self-contained: {path.name}")
        code = lean_code(path.read_text())
        match = forbidden.search(code)
        if match:
            fail(f"Forbidden proof token {match[0]} in {path.relative_to(ROOT)}")
    # Every library module must be reachable from the root import.
    reached = set()
    pending = ["RecurrentSections"]
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            fail(f"Missing local module: {module}")
        for imported in re.findall(r"(?m)^import\s+((?:" + "|".join(LIBRARIES) +
                                   r")(?:\.\w+)*)\s*$",
                                   lean_code(path.read_text())):
            pending.append(imported)
    expected = {str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
                for path in modules} | set(LIBRARIES)
    if not expected <= reached:
        fail(f"Unbuilt source modules: {sorted(expected - reached)}")
    # The reusable libraries must never import the recurrence application.
    for library in ["BorelToolkit", "MetricGeometry"]:
        for path in [ROOT / (library + ".lean"), *(ROOT / library).rglob("*.lean")]:
            if re.search(r"(?m)^import\s+RecurrentSections(?:\.|\s|$)",
                         lean_code(path.read_text())):
                fail(f"Reusable module imports the application: {path.relative_to(ROOT)}")
    print(f"Source guard passed; all {len(modules)} modules in {len(LIBRARIES)} libraries are imported.",
          flush=True)
    return sources


def dependency_revisions() -> dict[str, str]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    revisions = {}
    for package in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / package["name"]
        proc = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                              text=True, capture_output=True, check=True)
        actual = proc.stdout.strip()
        if actual != package["rev"]:
            fail(f"Dependency revision mismatch: {package['name']}")
        status = subprocess.run(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
            text=True, capture_output=True, check=True)
        if status.stdout:
            fail(f"Tracked dependency modifications: {package['name']}")
        revisions[package["name"]] = actual
    return revisions


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true",
                        help="refresh the checked-in verification evidence")
    args = parser.parse_args()
    sources = check_sources()
    build = run(["lake", "build", "--wfail"])
    dependencies = dependency_revisions()
    audit = run(["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"])
    if "sorryAx" in audit or "depends on axioms:" not in audit:
        fail("Principal-theorem audit is missing or contains a placeholder.")
    all_axioms = run(["lake", "env", "lean", "-DwarningAsError=true",
                     "AllAxioms.lean"])
    if not re.search(r"Audited [1-9][0-9]* project declarations", all_axioms):
        fail("Whole-project audit did not report success.")
    # A negative control checks that the diagnostic really rejects custom axioms.
    scratch = ROOT / ".lake" / "verification"
    scratch.mkdir(parents=True, exist_ok=True)
    negative = (ROOT / "AllAxioms.lean").read_text().replace(
        "open Lean Elab Command",
        "axiom BorelToolkit.auditSentinel : False\n\nopen Lean Elab Command",
        1)
    (scratch / "NegativeAudit.lean").write_text(negative)
    negative_log = run(
        ["lake", "env", "lean", "-DwarningAsError=true",
         ".lake/verification/NegativeAudit.lean"],
        expected_failure="Unexpected axiom dependency: BorelToolkit.auditSentinel")
    if args.record:
        evidence = ROOT / "verification"
        evidence.mkdir(exist_ok=True)
        for name, content in [
            ("build-output.txt", build), ("audit-output.txt", audit),
            ("all-axioms-output.txt", all_axioms),
            ("negative-control-output.txt", negative_log),
        ]:
            (evidence / name).write_text(content)
        inputs = sources + [
            ROOT / name for name in
            ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "scripts/check.py"]
        ]
        checksums = {str(path.relative_to(ROOT)):
                     hashlib.sha256(path.read_bytes()).hexdigest()
                     for path in sorted(inputs)}
        record = {
            "checked_at_utc": datetime.now(timezone.utc).isoformat(),
            "platform": {"system": platform.system(), "machine": platform.machine()},
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "dependency_revisions": dependencies,
            "source_sha256": checksums,
            "checks": ["source guard", "all library imports", "lake build --wfail",
                       "pinned and unmodified dependency sources",
                       "principal signatures and axioms", "all project axioms",
                       "negative-control rejection"],
        }
        (evidence / "verification.json").write_text(
            json.dumps(record, indent=2, sort_keys=True) + "\n")
    print("All verification checks passed.", flush=True)


if __name__ == "__main__":
    main()

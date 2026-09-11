/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit the compiled kernel dependencies of every declaration in the
project namespace, including private declarations from project modules.
This diagnostic adds no mathematical theorem or axiom. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names name _ => do
    if (`RecurrentSections).isPrefixOf name ||
        name.toString.startsWith "_private.RecurrentSections." then
      return names.push name
    else
      return names
  if names.isEmpty then
    throwError "No project declarations found; the audit cannot pass vacuously."
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in state.axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom dependency: {axiomName}"
  logInfo m!"Audited {names.size} project declarations. All axiom dependencies are in: propext, Classical.choice, Quot.sound."

/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit the compiled kernel dependencies of every declaration in the
three project libraries and the Palomar Solution, including private declarations.
This diagnostic adds no mathematical theorem or axiom. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let libraries := #[`RecurrentSections, `BorelToolkit, `MetricGeometry, `PalomarRecurrence]
  let names ← env.constants.foldM (init := #[]) fun names name _ => do
    if libraries.any (fun library => library.isPrefixOf name ||
        name.toString.startsWith ("_private." ++ library.toString ++ ".")) then
      return names.push name
    else
      return names
  if names.isEmpty then
    throwError "No project declarations found; the audit cannot pass vacuously."
  for library in libraries do
    unless names.any (fun name => library.isPrefixOf name) do
      throwError "No declarations from project library {library}; check the imports."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom dependency: {axiomName}"
  logInfo m!"Audited {names.size} project declarations. All axiom dependencies are in: propext, Classical.choice, Quot.sound."

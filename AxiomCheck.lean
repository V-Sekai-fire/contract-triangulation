/-
Every theorem in this package is proved rather than assumed.

`sorry` elaborates, compiles, and leaves a declaration that looks exactly like a theorem: the
build stays green and the proof is not there. That is the failure mode the conventions call a
check that reports -- worse than no check, because it reads as coverage. So the axiom set is
gated rather than trusted, and `lake build AxiomCheck` is what CI runs.

`propext`, `Classical.choice` and `Quot.sound` are Mathlib's own three and are expected.
`sorryAx` is not.
-/
import Triangulation
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut offenders : Array Name := #[]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    if (`Contract.Triangulation).isPrefixOf n && !n.isInternal then
      checked := checked + 1
      let axs ← liftCoreM <| collectAxioms n
      if axs.contains ``sorryAx then
        offenders := offenders.push n
  if offenders.isEmpty then
    logInfo m!"{checked} declarations checked; none depends on sorryAx"
  else
    throwError m!"these depend on sorryAx and are not proved: {offenders}"

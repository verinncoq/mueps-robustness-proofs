import Mueps
import Lean.Util.CollectAxioms

/-! Reject any nonstandard axiom (including `sorryAx`) in the paper-facing results. -/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let results := #[
    ``Mueps.Paper.CoveringCharacterization.from_paper,
    ``Mueps.Paper.FloatAbsoluteSpace.from_paper,
    ``Mueps.Paper.FloatSquaredSpace.from_paper,
    ``Mueps.Paper.SumProductSpace.from_paper,
    ``Mueps.Paper.MaximumProductSpace.from_paper,
    ``Mueps.Paper.ListSpaces.from_paper,
    ``Mueps.Paper.GeneralExistence.from_paper,
    ``Mueps.Paper.BoundaryCoveringCharacterization.from_paper,
    ``Mueps.Paper.BoundaryExistence.from_paper,
    ``Mueps.Paper.SuccessorCovering.from_paper,
    ``Mueps.Paper.PrecisionObstruction.from_paper,
    ``Mueps.Paper.Noncompositionality.from_paper,
    ``Mueps.Paper.DecompositionObstruction.from_paper,
    ``Mueps.Paper.PartialOrderPrecisionBound.from_paper]
  for result in results do
    let axioms ← collectAxioms result
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{result} depends on unexpected axiom {axiomName}"
  logInfo m!"Verified {results.size} paper results: only propext, Classical.choice, Quot.sound."

import Mueps
import Lean.Util.CollectAxioms

/-! Reject any nonstandard axiom (including `sorryAx`) in the paper-facing results and supporting example/correspondence lemmas. -/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let results := #[
    ``Mueps.Paper.CoveringCharacterization.theorem1,
    ``Mueps.Paper.GeneralExistence.theorem2,
    ``Mueps.Paper.BoundaryCoveringCharacterization.theorem3,
    ``Mueps.Paper.BoundaryExistence.corollary1,
    ``Mueps.Paper.SuccessorCovering.theorem4,
    ``Mueps.Paper.PrecisionObstruction.corollary2,
    ``Mueps.Paper.Noncompositionality.lemma1,
    ``Mueps.Paper.DecompositionObstruction.theorem5,
    ``Mueps.Paper.PartialOrderPrecisionBound.corollary3,
    ``Mueps.Paper.FloatAbsoluteSpace.proposition1_absolute,
    ``Mueps.Paper.FloatSquaredSpace.proposition1_squared,
    ``Mueps.Paper.SumProductSpace.proposition1_sumProduct,
    ``Mueps.Paper.MaximumProductSpace.proposition1_maximumProduct,
    ``Mueps.Paper.ListSpaces.proposition1_sumList,
    ``Mueps.Paper.ListSpaces.proposition1_maximumList,
    ``MuepsProofs.FlocqStrict.squareDistance_strict_antitriangle,
    ``MuepsProofs.FlocqBridge.format_finite_exponent,
    ``MuepsProofs.FlocqBridge.format_zero_exponent,
    ``MuepsProofs.FlocqBridge.format_mantissa_bound,
    ``MuepsProofs.FlocqBridge.finiteQ_cast,
    ``MuepsProofs.FlocqBridge.phiQ_cast,
    ``MuepsProofs.FlocqBridge.distQ_cast,
    ``MuepsProofs.FlocqBridge.squareDistQ_cast,
    ``MuepsProofs.FlocqBridge.ieeeLe_iff_phiQ_le,
    ``MuepsProofs.FlocqBridge.phiQ_injective,
    ``MuepsProofs.FlocqBridge.finiteQ_eq,
    ``MuepsProofs.FlocqBridge.format_finite_value,
    ``MuepsProofs.FlocqBridge.distQ_nonneg,
    ``MuepsProofs.FlocqBridge.distQ_eq_zero_iff,
    ``MuepsProofs.FlocqBridge.distQ_symm,
    ``MuepsProofs.FlocqBridge.distQ_add,
    ``MuepsProofs.FlocqBridge.squareDistQ_nonneg,
    ``MuepsProofs.FlocqBridge.squareDistQ_eq_zero_iff,
    ``MuepsProofs.FlocqBridge.squareDistQ_symm,
    ``MuepsProofs.FlocqBridge.squareDistQ_strict_antitriangle,
    ``MuepsProofs.FlocqExamples.binary64NaNInfinityDistanceQ,
    ``MuepsProofs.FlocqExamples.binary64SignedZeroDistanceQ,
    ``MuepsProofs.FlocqExamples.binary64SignedZeroSquaredDistanceQ,
    ``MuepsProofs.FlocqExamples.squaredStrictAntitriangleOneTwoThree,
    ``MuepsProofs.FlocqExamples.binary64PointwiseMaximumFailure,
    ``MuepsProofs.FlocqExamples.binary64NaNListLengthPenalty,
    ``MuepsProofs.FlocqExamples.binary64SumProductOrdered,
    ``MuepsProofs.FlocqExamples.binary64MaximumProductOrdered,
    ``MuepsProofs.FlocqExamples.binary64SumListOrdered,
    ``MuepsProofs.FlocqExamples.binary64MaximumListOrdered,
    ``MuepsProofs.PaperExamples.realAbsDistance_coe,
    ``MuepsProofs.PaperExamples.realSquaredDistance_coe,
    ``MuepsProofs.PaperExamples.realAbsDistance_isOrdered,
    ``MuepsProofs.PaperExamples.realSquaredDistance_isOrdered,
    ``MuepsProofs.PaperExamples.realSquaredDistance_not_triangle]
  for result in results do
    let axioms ← collectAxioms result
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{result} depends on unexpected axiom {axiomName}"
  logInfo m!"Verified {results.size} paper results and supporting lemmas: only propext, Classical.choice, Quot.sound."

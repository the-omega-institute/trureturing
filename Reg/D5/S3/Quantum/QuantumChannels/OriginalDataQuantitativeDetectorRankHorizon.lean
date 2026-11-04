import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon

/-!
The source family retains every dimension, matrix, CP map, scalar and hypothesis
of the original quantitative detector-rank theorem. Its selected observation is
the real order comparison in the conclusion. No cutoff, rank, corner or Kraus
certificate is added to the endpoint premises.
-/

namespace Reg.D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon

open _root_.D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀
    (D r n : ℕ) (hD : 2 ≤ D) (hr : 2 ≤ r) (hrD : r ≤ D) (hn : 1 ≤ n)
    (T : CompletelyPositiveMap (CStarMatrix (Fin D) (Fin D) ℂ)
      (CStarMatrix (Fin D) (Fin D) ℂ)) (hT : T 1 ≤ 1)
    (B σ : CStarMatrix (Fin D) (Fin D) ℂ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hσ : 0 ≤ σ) (hσtr : Matrix.trace (CStarMatrix.ofMatrix.symm σ) = 1)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 < p) (hp1 : p ≤ 1)
    (hearly : ∀ k : ℕ, k ≤ D - r →
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * T^[k] B))).re ≤ ε)
    (hlate : p ≤ (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * T^[n] B))).re),
    R.readout () ()
      ((Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hB0)).isHermitian.eigenvalues₀
        ⟨r - 1, by simpa using (show r - 1 < D by omega)⟩)
      ((8 * (D : ℝ) / p ^ 2) *
        (8 * (n : ℝ) * (D : ℝ) ^ (5 / 2 : ℝ) / p) ^ (2 * (D - r)) * ε)

private abbrev M := CStarMatrix (Fin 2) (Fin 2) ℂ

private def identityCP : CompletelyPositiveMap M M :=
  CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.id ℂ M)

private def density : M := (1 / 2 : ℝ) • 1

private theorem density_nonneg : 0 ≤ density := by
  exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) zero_le_one

private theorem density_trace : Matrix.trace (CStarMatrix.ofMatrix.symm density) = 1 := by
  change Matrix.trace ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
  norm_num [Matrix.trace_smul]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have early : ∀ k : ℕ, k ≤ 2 - 2 →
      (Matrix.trace (CStarMatrix.ofMatrix.symm (density * identityCP^[k] 1))).re ≤ (1 : ℝ) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa only [Function.iterate_zero_apply, mul_one, density_trace, Complex.one_re]
      using (le_rfl : (1 : ℝ) ≤ 1)
  have late : (1 : ℝ) ≤
      (Matrix.trace (CStarMatrix.ofMatrix.symm (density * identityCP^[1] 1))).re := by
    change (1 : ℝ) ≤ (Matrix.trace (CStarMatrix.ofMatrix.symm (density * 1))).re
    simp only [mul_one, density_trace, Complex.one_re, le_refl]
  exact h 2 2 1 (by omega) (by omega) le_rfl le_rfl identityCP (by exact le_rfl)
    1 density zero_le_one le_rfl density_nonneg density_trace
    1 1 zero_le_one zero_lt_one le_rfl early late

def familyRegistration : Registration arena (type_of% @detector_rank_horizon) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@detector_rank_horizon, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have bad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at bad

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@detector_rank_horizon) (type_of% actual) (Type) Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon.detector_rank_horizon.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon

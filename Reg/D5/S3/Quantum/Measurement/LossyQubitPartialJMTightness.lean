import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness

open _root_.D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness
open _root_.D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open _root_.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ η => η) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Only the efficiency occurrence in the final inequality is observed. The
original vectors, efficiency domain, and joint-measurability hypothesis remain. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r₁ r₂ : EuclideanSpace ℝ (Fin 3)) (η : ℝ),
    ‖r₁‖ = 1 → ‖r₂‖ = 1 → 0 ≤ η → η ≤ 1 →
    GJointMeasurable η ![r₁, r₂] →
    R.readout () () η *
      (2 + ‖WithLp.toLp 2 (WithLp.ofLp r₁ ⨯₃ WithLp.ofLp r₂)‖) ≤ 2

private def erasureEffect (_β : Fin 2) (b : Fin 3) (_y : Fin 2) : QubitMatrix :=
  if b = 2 then (1 / 2 : ℂ) • (1 : QubitMatrix) else 0

private def erasureWeight (_β : Fin 2) : QubitMatrix :=
  (1 / 2 : ℂ) • (1 : QubitMatrix)

private theorem zero_efficiency (r : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    GJointMeasurable 0 r := by
  refine ⟨erasureEffect, erasureWeight, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    constructor
    · intro k
      dsimp only [erasureEffect]
      split_ifs
      · exact Matrix.PosSemidef.one.smul (by
          apply Complex.nonneg_iff.mpr
          norm_num [Complex.div_re, Complex.div_im] : (0 : ℂ) ≤ 1 / 2)
      · exact Matrix.PosSemidef.zero
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [erasureEffect, Fintype.sum_prod_type, Fin.sum_univ_two,
          Fin.sum_univ_three, Matrix.smul_apply]
  · intro β y
    simp [erasureEffect, erasureWeight, Fin.sum_univ_three]
  · intro b y
    fin_cases b <;> simp [effects, erasureEffect, Fin.sum_univ_two]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.smul_apply, Matrix.ofNat_apply]
  · intro β y
    have hz : starPart erasureEffect erasureWeight β y = 0 := by
      fin_cases y <;>
        simp [starPart, erasureEffect, erasureWeight, G, Fin.sum_univ_three,
          Finset.sum_filter]
    rw [hz]
    exact Matrix.PosSemidef.zero
  · intro β y b hb
    fin_cases y <;> fin_cases b <;>
      simp_all [G, erasureEffect, starPart, erasureWeight, Fin.sum_univ_three,
        Finset.sum_filter]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let r : EuclideanSpace ℝ (Fin 3) := PiLp.single 2 2 1
  have hr : ‖r‖ = 1 := by simp [r]
  have h := law r r 0 hr hr (by norm_num) (by norm_num)
    (zero_efficiency ![r, r])
  change (2 : ℝ) * (2 + ‖WithLp.toLp 2 (WithLp.ofLp r ⨯₃ WithLp.ofLp r)‖) ≤ 2 at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (WithLp.ofLp r ⨯₃ WithLp.ofLp r))]

def evidence : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, zero_ne_one⟩

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness.result)
    (type_of% (realize signature (fun _ _ η => η) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness.result
    "Reg.D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness/\
    Reg.D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ η => η) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness,
    definition := some {
      owner := `D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness,
      name := `D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness

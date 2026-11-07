import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality
import Reg.Support.SingleDependentReadout

/-! The full tensor duality telescope, observed through its actual native
SOS conclusion. The unknown continuation makes no inexhaustibility claim. -/

namespace Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality

open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality
open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix MvPolynomial
open scoped BigOperators ComplexOrder RealInnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure Parameters where
  r : ℕ
  n : ℕ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => HermitianMat (Fin p.r → Fin p.n) ℂ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ A => IsSumSq (realSymbol A.mat)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {r n : ℕ} (A : HermitianMat (Fin r → Fin n) ℂ),
    A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ))
      (bosePPT : Set (HermitianMat (Fin r → Fin n) ℂ)) →
    R.readout () ⟨r,n⟩ A

private lemma zero_dual : (0 : HermitianMat (Fin 1 → Fin 1) ℂ) ∈
    ProperCone.dual (innerₗ (HermitianMat (Fin 1 → Fin 1) ℂ))
      (bosePPT : Set (HermitianMat (Fin 1 → Fin 1) ℂ)) := by
  intro E hE
  change 0 ≤ inner ℝ E 0
  simp

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 zero_dual

private lemma eval_nonneg {p : MvPolynomial (Fin 1) ℝ} (hp : IsSumSq p)
    (u : Fin 1 → ℝ) : 0 ≤ eval u p := by
  induction hp with
  | zero => simp
  | sq_add q _ ih =>
    rw [MvPolynomial.eval_add, MvPolynomial.eval_mul]
    exact add_nonneg (mul_self_nonneg (eval u q)) ih

private def negative : HermitianMat (Fin 1 → Fin 1) ℂ :=
  ⟨-1,Matrix.isHermitian_one.neg⟩

private lemma negative_not_sos : ¬ IsSumSq (realSymbol negative.mat) := by
  intro h
  change IsSumSq (realSymbol (-1 : Matrix (Fin 1 → Fin 1) (Fin 1 → Fin 1) ℂ)) at h
  have hv := eval_nonneg h (fun _ => 1)
  rw [eval_realSymbol] at hv
  norm_num [tensorPhase,Matrix.mulVec,dotProduct] at hv

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩,0,negative,?_⟩
  intro he
  have hz : actual.readout () ⟨1,1⟩ 0 := by
    change IsSumSq (realSymbol (0 : Matrix (Fin 1 → Fin 1) (Fin 1 → Fin 1) ℂ))
    simpa only [realSymbol,Matrix.zero_apply,Complex.zero_re,map_zero,
      Finset.sum_const_zero] using (IsSumSq.zero : IsSumSq (0 : MvPolynomial (Fin 1) ℝ))
  exact negative_not_sos (Eq.mp he hz)

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality.dual_bosePPT_real_sos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality.dual_bosePPT_real_sos,
    rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality.dual_bosePPT_real_sos)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => IsSumSq (realSymbol A.mat))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality

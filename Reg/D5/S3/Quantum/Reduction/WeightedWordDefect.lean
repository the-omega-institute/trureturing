import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Reduction.WeightedWordDefect
import Reg.Support.DependentFamily

/-! The actual square-root observation supports the complete source word estimate. -/

open _root_.D5.S3.Quantum.Reduction.WeightedWordDefect
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Reg.D5.S3.Quantum.Reduction.WeightedWordDefect
universe u v

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
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : Type u} {k : Type v} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (Φ : CompletelyPositiveMap (CStarMatrix d d ℂ) (CStarMatrix k k ℂ))
    (_hΦ : Φ 1 = 1) (w : List (Matrix d d ℂ)) (_hw : ∀ A ∈ w, Aᴴ = A),
    ‖CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix w.prod)) -
      (w.map (fun A => CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix A)))).prod‖ ≤
    pairSum (fun i : Fin w.length => ‖w.get i‖) (fun i => R.readout () ()
      ‖CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix ((w.get i)ᴴ * w.get i))) -
        (CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix (w.get i)))).conjTranspose *
          CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix (w.get i)))‖)

private lemma sum_ulift_two.{z} (f : ULift.{z} (Fin 2) → ℂ) :
    ∑ i, f i = f ⟨0⟩ + f ⟨1⟩ := by
  have h := Fintype.sum_equiv (Equiv.ulift : ULift.{z} (Fin 2) ≃ Fin 2)
    f (fun i => f ⟨i⟩) (by intro x; cases x; rfl)
  simpa only [Fin.sum_univ_two] using h

private lemma rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 2)
  let k := ULift.{v} (Fin 2)
  let K : Fin 2 → Matrix k d ℂ := fun r i j => if i.down = r ∧ j.down = r then 1 else 0
  have hK : (∑ r, (K r)ᴴ * K r) = 1 := by
    ext ⟨i⟩ ⟨j⟩
    simp only [Matrix.sum_apply, Fin.sum_univ_two]
    change (∑ t : k, star (K 0 t ⟨i⟩) * K 0 t ⟨j⟩) +
      (∑ t : k, star (K 1 t ⟨i⟩) * K 1 t ⟨j⟩) = _
    rw [sum_ulift_two, sum_ulift_two]
    fin_cases i <;> fin_cases j <;> norm_num [K, Matrix.one_apply]
  obtain ⟨T, hT⟩ := finite_kraus_quantum_channel K hK
  let Φ := T.toCompletelyPositiveMap
  have ha (X : Matrix d d ℂ) : CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix X)) =
      Matrix.diagonal (fun i : k => X ⟨i.down⟩ ⟨i.down⟩) := by
    rw [hT]
    ext ⟨i⟩ ⟨j⟩
    simp only [Matrix.sum_apply, Fin.sum_univ_two]
    change (∑ t : d, (∑ q : d, K 0 ⟨i⟩ q * X q t) * star (K 0 ⟨j⟩ t)) +
      (∑ t : d, (∑ q : d, K 1 ⟨i⟩ q * X q t) * star (K 1 ⟨j⟩ t)) = _
    simp only [sum_ulift_two]
    fin_cases i <;> fin_cases j <;> norm_num [K, Matrix.diagonal_apply]
  have hΦ : Φ 1 = 1 := by
    apply CStarMatrix.ofMatrix.symm.injective
    change CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix (1 : Matrix d d ℂ))) = 1
    rw [ha]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  let A : Matrix d d ℂ := fun i j => if i.down = j.down then 0 else 1
  have hA : Aᴴ = A := by
    ext ⟨i⟩ ⟨j⟩
    change star (A ⟨j⟩ ⟨i⟩) = A ⟨i⟩ ⟨j⟩
    simp [A, eq_comm]
  have hAA : A * A = 1 := by
    ext ⟨i⟩ ⟨j⟩
    change (∑ t : d, A ⟨i⟩ t * A t ⟨j⟩) = _
    rw [sum_ulift_two]
    fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.one_apply]
  have hAZ : CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix A)) = 0 := by
    rw [ha]
    ext i j
    simp [A, Matrix.diagonal_apply]
  have hh := h Φ hΦ [A,A] (by intro X hX; simp only [List.mem_cons, List.not_mem_nil,
    or_false, or_self] at hX; subst X; exact hA)
  simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, List.map_cons, List.map_nil,
    hAA, hAZ, Matrix.zero_mul, sub_zero] at hh
  have hm1 : CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix (1 : Matrix d d ℂ))) = 1 := by
    change CStarMatrix.ofMatrix.symm (Φ 1) = 1
    rw [hΦ]
    rfl
  rw [hm1] at hh
  simpa [rejected, realize, pairSum] using hh

def source_registration : Registration arena.{u,v} (type_of% @ucp_word_pair_bound.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ucp_word_pair_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@ucp_word_pair_bound.{u,v}) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Reduction.WeightedWordDefect.unit
  realizationName := `Reg.D5.S3.Quantum.Reduction.WeightedWordDefect.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Reduction.WeightedWordDefect
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.Quantum.Reduction.WeightedWordDefect

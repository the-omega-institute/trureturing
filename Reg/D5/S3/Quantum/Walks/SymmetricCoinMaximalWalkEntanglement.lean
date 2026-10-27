import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
import Reg.Support.DependentFamily

/-! Source-bound audit of symmetric-coin maximal walk entanglement. -/

namespace Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement

open _root_.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the amplitude vector at the original circle size, time and coin. -/
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ pn := Fin 2 × ZMod pn.1 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ pn c => walkState pn.1 pn.2 c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain every original parameter, normalization hypothesis and entanglement bound. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : ℕ) (hp : 1 ≤ p) (n : ℕ) (c : Fin 2 → ℂ),
    _root_.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c →
    letI : NeZero p := ⟨by omega⟩
    geometricEntanglement (r.readout () ⟨p, n⟩ c) ≤
      geometricEntanglement (walkState p n cStar)

open Classical in
private lemma overlap_expansion {ι : Type*} [Fintype ι] (lam : ι → ℂ)
    (z : ι → Fin 2 → ℂ) : overlap lam z =
      ∑ k, lam k * conj (z k 1 * ∏ l ∈ Finset.univ.erase k, z l 0) := by
  classical
  unfold overlap wState
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_comm]
  congr 2
  unfold productState
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  apply congrArg₂ (· * ·)
  · simp only [Function.update_self, ite_true]
  · apply Finset.prod_congr rfl
    intro l hl
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rfl

private lemma overlap_bounded {ι : Type*} [Fintype ι] (lam : ι → ℂ) :
    BddAbove {t | ∃ z : ι → Fin 2 → ℂ,
      unitFactors z ∧ t = Complex.normSq (overlap lam z)} := by
  classical
  refine ⟨∑ s : ι → Bool, ‖wState lam s‖ ^ 2, ?_⟩
  rintro t ⟨z, hz, rfl⟩
  have hprod : (∑ s : ι → Bool, ‖productState z s‖ ^ 2) = 1 := by
    unfold productState
    simp only [norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun k (b : Bool) => ‖z k (if b then 1 else 0)‖ ^ 2)]
    calc
      _ = ∏ k : ι, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro k hk
        have h := hz k
        unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor at h
        rw [Fin.sum_univ_two] at h
        simpa only [Fintype.sum_bool, Bool.cond_false, Bool.cond_true,
          Bool.false_eq_true, ite_false, ite_true,
          Complex.normSq_eq_norm_sq, add_comm] using h
      _ = 1 := Finset.prod_const_one
  have h := D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq
    (productState z) (wState lam)
  change ‖overlap lam z‖ ^ 2 ≤ _ at h
  rw [hprod, one_mul] at h
  exact (Complex.normSq_eq_norm_sq _).symm ▸ h

private lemma cStar_unit :
    _root_.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor cStar := by
  have hs : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  norm_num [D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor,
    Fin.sum_univ_two, cStar, hs]

private lemma zero_gMax {ι : Type*} [Fintype ι] : gMax (0 : ι → ℂ) = 0 := by
  have hz (z : ι → Fin 2 → ℂ) : overlap (0 : ι → ℂ) z = 0 := by
    simp [overlap, wState]
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ?_⟩
      refine ⟨fun _ => ![1, 0], ?_, ?_⟩
      · intro k
        norm_num [D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor,
          Fin.sum_univ_two]
      · simp [hz]
    · rintro t ⟨z, _, rfl⟩
      simp [hz]
  · apply le_csSup (overlap_bounded _)
    refine ⟨fun _ => ![1, 0], ?_, ?_⟩
    · intro k
      norm_num [D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor,
        Fin.sum_univ_two]
    · simp [hz]

private lemma star_gMax_pos : 0 < gMax (walkState 1 0 cStar) := by
  classical
  letI : DecidableEq (Fin 2 × ZMod 1) := fun a b => Classical.propDecidable (a = b)
  let z : Fin 2 × ZMod 1 → Fin 2 → ℂ :=
    fun k b => if k.1 = b then 0 else 1
  have hz : unitFactors z := by
    intro k
    rcases k with ⟨b, x⟩
    fin_cases b <;>
      norm_num [z, D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor,
        Fin.sum_univ_two]
  have he : overlap (walkState 1 0 cStar) z = cStar 0 := by
    rw [overlap_expansion]
    simp [z, Fintype.sum_prod_type, Fin.sum_univ_two, walkState]
    split_ifs with h
    · calc
        _ = cStar 0 * 1 := by
          congr 1
          apply Finset.prod_eq_one
          intro k hk
          have hn : k.1 ≠ 0 := by
            intro he
            exact (Finset.mem_erase.mp hk).1 (Prod.ext he (Subsingleton.elim _ _))
          simp [hn]
        _ = _ := mul_one _
    · exact (h (Subsingleton.elim _ _)).elim
  have hs : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  apply lt_of_lt_of_le (b := Complex.normSq (overlap (walkState 1 0 cStar) z))
  · rw [he]
    norm_num [cStar, Complex.normSq_div, hs]
  · exact le_csSup (overlap_bounded _) ⟨z, hz, rfl⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) 0 cStar cStar_unit
  change geometricEntanglement (0 : Fin 2 × ZMod 1 → ℂ) ≤
    geometricEntanglement (walkState 1 0 cStar) at hbad
  unfold geometricEntanglement at hbad
  rw [zero_gMax] at hbad
  linarith [star_gMax_pos]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, cStar, ?_⟩
  intro he
  have h := congrFun he (0, 0)
  have hn : cStar 0 ≠ 0 := by simp [cStar]
  apply hn
  change (0 : ℂ) = cStar 0 at h
  exact h.symm

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ pn c => walkState pn.1 pn.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
    definition := some {
      owner := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
      name := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement

/- GID: D5/S3/VertexAlgebra/HeisenbergFockPolynomial
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/HeisenbergFockPolynomial
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Shifted polynomial modes construct a Heisenberg vertex operator. -/

/-
proof_shape: heisenberg_fock_polynomial: content
escape_witness: form (2), the constructed operator satisfies the all-integer central
  commutator with a nonzero vacuum value; neither follows by binding an existing theorem.
admission_basis: escape-witness
Direct frozen dependencies: none; the polynomial and vertex-operator APIs are pinned Mathlib.
-/

import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.VertexAlgebra.HeisenbergFockPolynomial

open MvPolynomial
open scoped VertexOperator

abbrev Fock := MvPolynomial ℕ ℚ

/-- The shifted creation and annihilation modes on rational polynomials. -/
noncomputable def mode : ℤ → Module.End ℚ Fock
  | .ofNat 0 => 0
  | .ofNat (k + 1) => (k + 1 : ℚ) • (pderiv k).toLinearMap
  | .negSucc k => LinearMap.mulLeft ℚ (X k)

private theorem partials_commute (p : Fock) (i j : ℕ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  have h : ⁅pderiv (R := ℚ) i, pderiv (R := ℚ) j⁆ =
      (0 : Derivation ℚ Fock Fock) := by
    apply MvPolynomial.derivation_ext
    intro k
    simp [Derivation.commutator_apply, pderiv_X, Pi.single_apply, apply_ite]
  have he := DFunLike.congr_fun h p
  simpa [Derivation.commutator_apply, sub_eq_zero] using he

private theorem positive_vanish (p : Fock) (m : ℤ)
    (hm : ((p.vars.sup id : ℕ) + 1 : ℤ) < m) : mode m p = 0 := by
  cases m with
  | negSucc k => omega
  | ofNat k =>
    cases k with
    | zero => simp [mode]
    | succ k =>
      have hnot : k ∉ p.vars := by
        intro hk
        have hle : k ≤ p.vars.sup id := Finset.le_sup (f := id) hk
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hm
        omega
      simp [mode, pderiv_eq_zero_of_notMem_vars hnot]

private theorem coefficient_support (p : Fock) :
    BddBelow (Function.support fun e : ℤ => mode (-e - 1) p) := by
  refine ⟨-((p.vars.sup id : ℕ) + 2 : ℤ), ?_⟩
  intro e he
  by_contra h
  have hm : ((p.vars.sup id : ℕ) + 1 : ℤ) < -e - 1 := by omega
  have hz := positive_vanish p (-e - 1) hm
  exact he hz

/-- A field with coefficient `a_m` at normalized index `m`. -/
noncomputable def field : VertexOperator ℚ Fock :=
  VertexOperator.of_coeff (fun e => mode (-e - 1)) coefficient_support

/-- A finite word of negative modes applied to the vacuum. -/
noncomputable def creationState (word : List ℕ) : Fock :=
  word.foldr (fun k p => mode (Int.negSucc k) p) 1

private theorem creation_spans :
    Submodule.span ℚ (Set.range creationState) = ⊤ := by
  let S := Submodule.span ℚ (Set.range creationState)
  have hstable (k : ℕ) : ∀ p ∈ S, X k * p ∈ S := by
    intro p hp
    refine Submodule.span_induction (p := fun p _ => X k * p ∈ S) ?_ ?_ ?_ ?_ hp
    · intro p hpword
      obtain ⟨word, hw⟩ := hpword
      subst p
      apply Submodule.subset_span
      exact ⟨k :: word, by simp [creationState, mode]⟩
    · simp
    · intro p q _ _ hp hq
      simpa [mul_add] using S.add_mem hp hq
    · intro a p _ hp
      simpa [smul_eq_C_mul, mul_assoc, mul_comm, mul_left_comm] using S.smul_mem a hp
  apply le_antisymm le_top
  intro p hp
  clear hp
  change p ∈ S
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hunit : (1 : Fock) ∈ S := by
      apply Submodule.subset_span
      exact ⟨[], by simp [creationState]⟩
    simpa [smul_eq_C_mul] using S.smul_mem a hunit
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p k hp =>
    simpa [mul_comm] using hstable k p hp

private theorem field_mode (m : ℤ) : field[[m]] = mode m := by
  rw [field, VertexOperator.ncoeff_of_coeff]
  congr 1
  omega

private theorem mode_ccr (m n : ℤ) :
    (mode m).comp (mode n) - (mode n).comp (mode m) =
      if m + n = 0 then (m : ℚ) • LinearMap.id else 0 := by
  cases m with
  | ofNat m =>
    cases m with
    | zero => simp [mode]
    | succ i =>
      cases n with
      | ofNat n =>
        cases n with
        | zero =>
          simp only [mode, LinearMap.comp_zero, LinearMap.zero_comp,
            sub_self]
          split_ifs with h
          · exfalso
            have hh : ((i : ℤ) + 1) ≠ 0 := by omega
            exact hh h
          · rfl
        | succ j =>
          have hsum : (↑(i + 1) : ℤ) + ↑(j + 1) ≠ 0 := by omega
          simp only [Nat.cast_add, Nat.cast_one] at hsum
          apply LinearMap.ext
          intro p
          simp [mode, hsum, LinearMap.comp_apply, partials_commute p i j,
            smul_smul, mul_comm]
      | negSucc j =>
        by_cases hij : i = j
        · subst j
          have hsum : (↑(i + 1) : ℤ) + Int.negSucc i = 0 := by omega
          simp only [Nat.cast_add, Nat.cast_one] at hsum
          apply LinearMap.ext
          intro p
          simp [mode, hsum, LinearMap.comp_apply]
        · have hsum : (↑(i + 1) : ℤ) + Int.negSucc j ≠ 0 := by omega
          simp only [Nat.cast_add, Nat.cast_one] at hsum
          apply LinearMap.ext
          intro p
          simp [mode, hsum, LinearMap.comp_apply, hij]
  | negSucc i =>
    cases n with
    | ofNat n =>
      cases n with
      | zero => simp [mode]
      | succ j =>
        by_cases hij : i = j
        · subst j
          have hsum : Int.negSucc i + (↑(i + 1) : ℤ) = 0 := by omega
          simp only [Nat.cast_add, Nat.cast_one] at hsum
          apply LinearMap.ext
          intro p
          simp [mode, hsum, LinearMap.comp_apply]
          rw [show (-1 + -↑i : ℚ) = -(↑i + 1) by ring, neg_smul]
        · have hsum : Int.negSucc i + (↑(j + 1) : ℤ) ≠ 0 := by omega
          simp only [Nat.cast_add, Nat.cast_one] at hsum
          apply LinearMap.ext
          intro p
          simp [mode, hsum, LinearMap.comp_apply, hij]
    | negSucc j =>
      have hsum : Int.negSucc i + Int.negSucc j ≠ 0 := by omega
      apply LinearMap.ext
      intro p
      simp [mode, hsum, LinearMap.comp_apply, mul_left_comm]

/-- The rational polynomial Fock field realizes the nonzero-central Heisenberg CCR. -/
theorem heisenberg_fock_polynomial :
    (∀ m : ℤ, field[[m]] = mode m) ∧
    (∀ p : Fock, ∃ B : ℤ, ∀ m : ℤ, B < m → (field[[m]]) p = 0) ∧
    (∀ m n : ℤ, (field[[m]]).comp (field[[n]]) -
      (field[[n]]).comp (field[[m]]) =
        if m + n = 0 then (m : ℚ) • LinearMap.id else 0) ∧
    (((field[[1]]).comp (field[[-1]]) -
      (field[[-1]]).comp (field[[1]])) (1 : Fock) = 1) ∧
    (∀ k : ℕ, (field[[Int.negSucc k]]) (1 : Fock) = X k) ∧
    Submodule.span ℚ (Set.range creationState) = ⊤ := by
  refine ⟨field_mode, ?_, ?_, ?_, ?_, creation_spans⟩
  · intro p
    refine ⟨(p.vars.sup id : ℕ) + 1, ?_⟩
    intro m hm
    rw [field_mode]
    exact positive_vanish p m hm
  · intro m n
    rw [field_mode, field_mode]
    exact mode_ccr m n
  · rw [field_mode, field_mode]
    simpa using congrArg (fun T : Module.End ℚ Fock => T (1 : Fock))
      (mode_ccr 1 (-1))
  · intro k
    rw [field_mode]
    simp [mode]

end D5.S3.VertexAlgebra.HeisenbergFockPolynomial

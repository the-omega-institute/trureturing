/- GID: D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference
   generality: G
   mirror-B: D5/B/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Takemura's fixed-point alternating power difference formulas. -/

/-
proof_shape:
  resultDegree: bind-only
  resultValue: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #8837; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Order.Lattice.Nat

open scoped BigOperators

namespace D5.S3.ArithSums.TakemuraFixedPointAlternatingPowerDifference

/-- Definition 1 of arXiv:2512.18169v1: `APD_m(f) = Σ_{σ ∈ S_n} sgn(σ) f(σ)^m`. -/
def apd (n : ℕ) (f : Equiv.Perm (Fin n) → ℤ) (m : ℕ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) * f σ ^ m

/-- §5.2.1: the fixed-point function `fix(σ) = |{i : σ i = i}|`, the
function `f_{I_n}` of the identity matrix. -/
def fix {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℤ :=
  (Finset.univ.filter (fun i => σ i = i)).card

/-- Definition 2: the least `m ≥ 1` with `APD_m(f) ≠ 0` (`Nat.sInf` of the
defining set; the theorems below prove the set nonempty, so the empty-set value never enters). -/
noncomputable def firstAppearanceDegree (n : ℕ) (f : Equiv.Perm (Fin n) → ℤ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ apd n f m ≠ 0}

/- The tuple expansion and injection count are kept local to the two results. -/

/- Conjecture 2 is proved first so Conjecture 1 can use its nonzero value. -/
/-- Conjecture 2 of arXiv:2512.18169v1: `APD_{n−1}(I_n) = n!` for `n ≥ 2`. -/
theorem resultValue (n : ℕ) (hn : 2 ≤ n) : apd n fix (n - 1) = (n.factorial : ℤ) := by
  classical
  have sign_sum_fixed (S : Finset (Fin n)) :
      (∑ σ : Equiv.Perm (Fin n),
        if ∀ i ∈ S, σ i = i then (Equiv.Perm.sign σ : ℤ) else 0) =
          if n - S.card ≤ 1 then 1 else 0 := by
    let fixedEq :
        (fun σ : Equiv.Perm (Fin n) => ∀ i, ¬i ∉ S → σ i = i) =
          (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ S, σ i = i) := by
      funext σ
      apply propext
      simp
    let e := (Equiv.Perm.subtypeEquivSubtypePerm (fun i : Fin n => i ∉ S)).trans
      (Equiv.subtypeEquivProp fixedEq)
    have hsub :
        (∑ σ : Equiv.Perm (Fin n),
          if ∀ i ∈ S, σ i = i then (Equiv.Perm.sign σ : ℤ) else 0) =
            ∑ σ : {σ : Equiv.Perm (Fin n) // ∀ i ∈ S, σ i = i},
              (Equiv.Perm.sign σ.1 : ℤ) := by
      rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp
    have hreindex :
        (∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, (Equiv.Perm.sign τ : ℤ)) =
          ∑ σ : {σ : Equiv.Perm (Fin n) // ∀ i ∈ S, σ i = i},
            (Equiv.Perm.sign σ.1 : ℤ) := by
      apply Fintype.sum_equiv e
      intro τ
      change (Equiv.Perm.sign τ : ℤ) =
        (Equiv.Perm.sign (Equiv.Perm.ofSubtype τ) : ℤ)
      rw [Equiv.Perm.sign_ofSubtype]
    have hcard : Fintype.card {i : Fin n // i ∉ S} = n - S.card := by
      simpa using Fintype.card_subtype_compl (fun i : Fin n => i ∈ S)
    have sum_sign_perm :
        (∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, (Equiv.Perm.sign τ : ℤ)) =
          if Fintype.card {i : Fin n // i ∉ S} ≤ 1 then 1 else 0 := by
      split_ifs with hcard'
      · let _ : Subsingleton {i : Fin n // i ∉ S} :=
          Fintype.card_le_one_iff_subsingleton.mp hcard'
        simp
      · have hlt : 1 < Fintype.card {i : Fin n // i ∉ S} := by omega
        let _ : Nontrivial {i : Fin n // i ∉ S} :=
          Fintype.one_lt_card_iff_nontrivial.mp hlt
        obtain ⟨a, b, hab⟩ := exists_pair_ne {i : Fin n // i ∉ S}
        have hsum := Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b))
          (fun τ : Equiv.Perm {i : Fin n // i ∉ S} =>
            (Equiv.Perm.sign ((Equiv.swap a b) * τ) : ℤ))
          (fun τ : Equiv.Perm {i : Fin n // i ∉ S} =>
            (Equiv.Perm.sign τ : ℤ))
          (fun τ => by simp)
        have hneg :
            (∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, -(Equiv.Perm.sign τ : ℤ)) =
              ∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, (Equiv.Perm.sign τ : ℤ) := by
          simpa [Equiv.Perm.sign_mul, hab] using hsum
        rw [Finset.sum_neg_distrib] at hneg
        omega
    rw [hsub, ← hreindex, sum_sign_perm, hcard]
  have apd_eq_sum_images (m : ℕ) :
      apd n fix m =
        ∑ t : Fin m → Fin n,
          (if n - (Finset.univ.image t).card ≤ 1 then (1 : ℤ) else 0) := by
    have fix_eq_sum_indicators (σ : Equiv.Perm (Fin n)) :
        fix σ = ∑ i : Fin n, if σ i = i then (1 : ℤ) else 0 := by
      simp [fix]
    have fix_pow_expansion (m : ℕ) (σ : Equiv.Perm (Fin n)) :
        fix σ ^ m =
          ∑ t : Fin m → Fin n, if ∀ k, σ (t k) = t k then (1 : ℤ) else 0 := by
      rw [fix_eq_sum_indicators, Fintype.sum_pow]
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : ∀ k, σ (t k) = t k
      · simp [h]
      · simp only [h, if_false]
        push Not at h
        obtain ⟨k, hk⟩ := h
        exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
    unfold apd
    simp_rw [fix_pow_expansion, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    have hiff (σ : Equiv.Perm (Fin n)) :
        (∀ k, σ (t k) = t k) ↔
          ∀ i ∈ Finset.univ.image t, σ i = i := by
      constructor
      · intro h i hi
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
        exact h k
      · intro h k
        exact h (t k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    calc
      (∑ σ : Equiv.Perm (Fin n),
          (Equiv.Perm.sign σ : ℤ) *
            (if ∀ k, σ (t k) = t k then (1 : ℤ) else 0)) =
        ∑ σ : Equiv.Perm (Fin n),
          if ∀ i ∈ Finset.univ.image t, σ i = i then
            (Equiv.Perm.sign σ : ℤ) else 0 := by
              apply Finset.sum_congr rfl
              intro σ _
              simp only [hiff σ]
              split_ifs <;> simp_all
      _ = if n - (Finset.univ.image t).card ≤ 1 then 1 else 0 :=
        sign_sum_fixed (Finset.univ.image t)
  rw [apd_eq_sum_images]
  have hiff (t : Fin (n - 1) → Fin n) :
      n - (Finset.univ.image t).card ≤ 1 ↔ Function.Injective t := by
    constructor
    · intro h
      have hupper : (Finset.univ.image t).card ≤ n - 1 := by
        calc
          (Finset.univ.image t).card ≤ Finset.univ.card := Finset.card_image_le
          _ = n - 1 := Fintype.card_fin (n - 1)
      have hlower : n - 1 ≤ (Finset.univ.image t).card := by omega
      have hcard : (Finset.univ.image t).card =
          (Finset.univ : Finset (Fin (n - 1))).card := by
        simpa using Nat.le_antisymm hupper hlower
      have hinjOn : Set.InjOn t (Finset.univ : Finset (Fin (n - 1))) :=
        Finset.card_image_iff.mp hcard
      intro a b hab
      exact hinjOn (Finset.mem_univ a) (Finset.mem_univ b) hab
    · intro ht
      rw [Finset.card_image_of_injective Finset.univ ht, Finset.card_univ,
        Fintype.card_fin]
      omega
  simp_rw [hiff]
  calc
    (∑ t : Fin (n - 1) → Fin n,
        if Function.Injective t then (1 : ℤ) else 0) =
        (Fintype.card {t : Fin (n - 1) → Fin n // Function.Injective t} : ℤ) := by
          rw [Finset.sum_boole]
          norm_cast
          exact (Fintype.card_subtype Function.Injective).symm
    _ = (Fintype.card (Fin (n - 1) ↪ Fin n) : ℤ) := by
      rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _)]
    _ = (n.descFactorial (n - 1) : ℤ) := by
      norm_cast
      simpa using
        (Fintype.card_embedding_eq (α := Fin (n - 1)) (β := Fin n))
    _ = (n.factorial : ℤ) := by
      norm_cast
      have hfac := Nat.factorial_mul_descFactorial (n := n) (k := n - 1) (by omega)
      have hsub : n - (n - 1) = 1 := by omega
      rw [hsub] at hfac
      simpa using hfac

/- Conjecture 1 uses the same tuple expansion locally and the value theorem above. -/
/-- Conjecture 1 of arXiv:2512.18169v1: `m₁(I_n) = n − 1` for `n ≥ 2`. -/
theorem resultDegree (n : ℕ) (hn : 2 ≤ n) : firstAppearanceDegree n fix = n - 1 := by
  classical
  have sign_sum_fixed (S : Finset (Fin n)) :
      (∑ σ : Equiv.Perm (Fin n),
        if ∀ i ∈ S, σ i = i then (Equiv.Perm.sign σ : ℤ) else 0) =
          if n - S.card ≤ 1 then 1 else 0 := by
    let fixedEq :
        (fun σ : Equiv.Perm (Fin n) => ∀ i, ¬i ∉ S → σ i = i) =
          (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ S, σ i = i) := by
      funext σ
      apply propext
      simp
    let e := (Equiv.Perm.subtypeEquivSubtypePerm (fun i : Fin n => i ∉ S)).trans
      (Equiv.subtypeEquivProp fixedEq)
    have hsub :
        (∑ σ : Equiv.Perm (Fin n),
          if ∀ i ∈ S, σ i = i then (Equiv.Perm.sign σ : ℤ) else 0) =
            ∑ σ : {σ : Equiv.Perm (Fin n) // ∀ i ∈ S, σ i = i},
              (Equiv.Perm.sign σ.1 : ℤ) := by
      rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp
    have hreindex :
        (∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, (Equiv.Perm.sign τ : ℤ)) =
          ∑ σ : {σ : Equiv.Perm (Fin n) // ∀ i ∈ S, σ i = i},
            (Equiv.Perm.sign σ.1 : ℤ) := by
      apply Fintype.sum_equiv e
      intro τ
      change (Equiv.Perm.sign τ : ℤ) =
        (Equiv.Perm.sign (Equiv.Perm.ofSubtype τ) : ℤ)
      rw [Equiv.Perm.sign_ofSubtype]
    have hcard : Fintype.card {i : Fin n // i ∉ S} = n - S.card := by
      simpa using Fintype.card_subtype_compl (fun i : Fin n => i ∈ S)
    have sum_sign_perm :
        (∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, (Equiv.Perm.sign τ : ℤ)) =
          if Fintype.card {i : Fin n // i ∉ S} ≤ 1 then 1 else 0 := by
      split_ifs with hcard'
      · let _ : Subsingleton {i : Fin n // i ∉ S} :=
          Fintype.card_le_one_iff_subsingleton.mp hcard'
        simp
      · have hlt : 1 < Fintype.card {i : Fin n // i ∉ S} := by omega
        let _ : Nontrivial {i : Fin n // i ∉ S} :=
          Fintype.one_lt_card_iff_nontrivial.mp hlt
        obtain ⟨a, b, hab⟩ := exists_pair_ne {i : Fin n // i ∉ S}
        have hsum := Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b))
          (fun τ : Equiv.Perm {i : Fin n // i ∉ S} =>
            (Equiv.Perm.sign ((Equiv.swap a b) * τ) : ℤ))
          (fun τ : Equiv.Perm {i : Fin n // i ∉ S} =>
            (Equiv.Perm.sign τ : ℤ))
          (fun τ => by simp)
        have hneg :
            (∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, -(Equiv.Perm.sign τ : ℤ)) =
              ∑ τ : Equiv.Perm {i : Fin n // i ∉ S}, (Equiv.Perm.sign τ : ℤ) := by
          simpa [Equiv.Perm.sign_mul, hab] using hsum
        rw [Finset.sum_neg_distrib] at hneg
        omega
    rw [hsub, ← hreindex, sum_sign_perm, hcard]
  have apd_eq_sum_images (m : ℕ) :
      apd n fix m =
        ∑ t : Fin m → Fin n,
          (if n - (Finset.univ.image t).card ≤ 1 then (1 : ℤ) else 0) := by
    have fix_eq_sum_indicators (σ : Equiv.Perm (Fin n)) :
        fix σ = ∑ i : Fin n, if σ i = i then (1 : ℤ) else 0 := by
      simp [fix]
    have fix_pow_expansion (m : ℕ) (σ : Equiv.Perm (Fin n)) :
        fix σ ^ m =
          ∑ t : Fin m → Fin n, if ∀ k, σ (t k) = t k then (1 : ℤ) else 0 := by
      rw [fix_eq_sum_indicators, Fintype.sum_pow]
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : ∀ k, σ (t k) = t k
      · simp [h]
      · simp only [h, if_false]
        push Not at h
        obtain ⟨k, hk⟩ := h
        exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
    unfold apd
    simp_rw [fix_pow_expansion, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    have hiff (σ : Equiv.Perm (Fin n)) :
        (∀ k, σ (t k) = t k) ↔
          ∀ i ∈ Finset.univ.image t, σ i = i := by
      constructor
      · intro h i hi
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
        exact h k
      · intro h k
        exact h (t k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    calc
      (∑ σ : Equiv.Perm (Fin n),
          (Equiv.Perm.sign σ : ℤ) *
            (if ∀ k, σ (t k) = t k then (1 : ℤ) else 0)) =
        ∑ σ : Equiv.Perm (Fin n),
          if ∀ i ∈ Finset.univ.image t, σ i = i then
            (Equiv.Perm.sign σ : ℤ) else 0 := by
              apply Finset.sum_congr rfl
              intro σ _
              simp only [hiff σ]
              split_ifs <;> simp_all
      _ = if n - (Finset.univ.image t).card ≤ 1 then 1 else 0 :=
        sign_sum_fixed (Finset.univ.image t)
  unfold firstAppearanceDegree
  have hmem : n - 1 ∈ {m : ℕ | 1 ≤ m ∧ apd n fix m ≠ 0} := by
    constructor
    · omega
    · rw [resultValue n hn]
      exact_mod_cast Nat.factorial_ne_zero n
  apply Nat.le_antisymm
  · exact Nat.sInf_le hmem
  · refine le_csInf ⟨n - 1, hmem⟩ ?_
    intro m hm
    by_contra hlt
    have hmle : m ≤ n - 2 := by omega
    have hz : apd n fix m = 0 := by
      rw [apd_eq_sum_images]
      apply Finset.sum_eq_zero
      intro t _
      have hcard : (Finset.univ.image t).card ≤ m := by
        calc
          (Finset.univ.image t).card ≤ Finset.univ.card := Finset.card_image_le
          _ = m := Fintype.card_fin m
      have hnot : ¬n - (Finset.univ.image t).card ≤ 1 := by omega
      simp [hnot]
    exact hm.2 hz

example : apd 3 fix 1 = 0 := by decide
example : apd 3 fix 2 = 6 := by decide
example : apd 4 fix 3 = 24 := by decide

#print axioms resultDegree
#print axioms resultValue

end D5.S3.ArithSums.TakemuraFixedPointAlternatingPowerDifference

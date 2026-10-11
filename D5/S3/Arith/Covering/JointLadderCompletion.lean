/- GID: D5/S3/Arith/Covering/JointLadderCompletion
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/JointLadderCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint root repairs on fresh coprime ladders construct smaller whole covers. -/

import D5.S3.Arith.Covering.SingleChainFreshCompletion
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos7.OddDistinctCoveringSystem

/-- A fixed cover of the complete prime-free residual by selected roots from
several fresh ladders yields a smaller actual whole covering system. -/
theorem joint_ladder_completion
    {n p ell : ℕ} (F : OddDistinctCoveringSystem n)
    (hp : Nat.Prime p) (hell : Nat.Prime ell) (hne : p ≠ ell)
    (slot : Fin p → Fin n)
    (hmod : ∀ j, F.modulus (slot j) = p * ell ^ j.val)
    (hroot : Function.Injective (fun j => F.residue (slot j) % p))
    (hcomplete : ∀ i, p ∣ F.modulus i → ∃ j, slot j = i)
    {ι : Type*} [Fintype ι] (s : ι → ℕ)
    (hsInj : Function.Injective s)
    (hsOdd : ∀ i, Odd (s i)) (hsOne : ∀ i, 1 < s i)
    (hcop : ∀ i, Nat.Coprime (s i) ell)
    (R : (i : ι) → Finset (Fin (s i)))
    (hcapacity : ∀ i, (R i).card ≤ (freshLadderHeights F p ell (s i)).card)
    (hbudget : (∑ i, (R i).card) < p)
    (hrootCover : ∀ x : ℕ,
      (∀ k, ¬p ∣ F.modulus k → ¬x ≡ F.residue k [MOD F.modulus k]) →
      ∃ i, ∃ r : Fin (s i), r ∈ R i ∧ x % s i = r.val) :
    ∃ N < n, Nonempty (OddDistinctCoveringSystem N) := by
  classical
  let U (i : ι) := freshLadderHeights F p ell (s i)
  have hsize (i : ι) : Fintype.card (R i) ≤ Fintype.card (U i) := by
    simpa only [Fintype.card_coe] using hcapacity i
  let height (i : ι) : R i ↪ U i :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hsize i))
  have hslotInj : Function.Injective slot := by
    intro j k heq
    exact hroot (congrArg (fun i => F.residue i % p) heq)
  let top : Fin p := ⟨p - 1, by have := hp.pos; omega⟩
  let c := F.residue (slot top)
  let Added := (i : ι) × R i
  let Rem := {i : Fin n // ¬p ∣ F.modulus i}
  let newMod : Added ⊕ Rem → ℕ := Sum.elim
    (fun r => s r.1 * ell ^ (height r.1 r.2).val.val)
    (fun i => F.modulus i.val)
  let newRes : Added ⊕ Rem → ℕ := Sum.elim
    (fun r => (Nat.chineseRemainder
      ((hcop r.1).pow_right (height r.1 r.2).val.val) r.2.val.val c).val)
    (fun i => F.residue i.val)
  have hellOdd : Odd ell := by
    let one : Fin p := ⟨1, hp.one_lt⟩
    apply (F.modulus_odd (slot one)).of_dvd_nat
    rw [hmod one]
    simpa only [one, pow_one] using (dvd_mul_left ell p)
  have fresh (r : Added) (i : Fin n) :
      F.modulus i ≠ s r.1 * ell ^ (height r.1 r.2).val.val := by
    exact (Finset.mem_filter.mp (height r.1 r.2).property).2 i
  have hnewInj : Function.Injective newMod := by
    rintro (r | i) (t | k) heq
    · apply congrArg Sum.inl
      rcases r with ⟨a, r⟩
      rcases t with ⟨b, t⟩
      change s a * ell ^ (height a r).val.val =
        s b * ell ^ (height b t).val.val at heq
      have hab : s a ∣ s b := by
        apply ((hcop a).pow_right (height b t).val.val).dvd_of_dvd_mul_right
        rw [← heq]
        exact dvd_mul_right _ _
      have hba : s b ∣ s a := by
        apply ((hcop b).pow_right (height a r).val.val).dvd_of_dvd_mul_right
        rw [heq]
        exact dvd_mul_right _ _
      have hi : a = b := hsInj (Nat.dvd_antisymm hab hba)
      subst b
      have hpow : ell ^ (height a r).val.val = ell ^ (height a t).val.val :=
        Nat.eq_of_mul_eq_mul_left (by have := hsOne a; omega) heq
      have hheight : height a r = height a t := by
        apply Subtype.ext
        apply Fin.ext
        exact Nat.pow_right_injective hell.two_le hpow
      exact congrArg (Sigma.mk a) ((height a).injective hheight)
    · exact False.elim (fresh r k.val heq.symm)
    · exact False.elim (fresh t i.val heq)
    · exact congrArg Sum.inr (Subtype.ext (F.modulus_injective heq))
  have hnewCover (x : ℕ) : ∃ i, x ≡ newRes i [MOD newMod i] := by
    by_cases hhole : ∀ i, ¬p ∣ F.modulus i → ¬x ≡ F.residue i [MOD F.modulus i]
    · obtain ⟨i, r, hr, hxr⟩ := hrootCover x hhole
      let rr : R i := ⟨r, hr⟩
      have hxc : x ≡ c [MOD ell ^ (p - 1)] :=
        single_chain_pfree_residual_subset F hp hell hne slot hmod hroot hcomplete x hhole top
      have hheight : (height i rr).val.val ≤ p - 1 := by
        have := (height i rr).val.isLt
        omega
      refine ⟨Sum.inl ⟨i, rr⟩, ?_⟩
      exact Nat.chineseRemainder_modEq_unique ((hcop i).pow_right _)
        (by change x % s i = r.val % s i; simpa only [Nat.mod_eq_of_lt r.isLt] using hxr)
        (hxc.of_dvd (pow_dvd_pow ell hheight))
    · push Not at hhole
      obtain ⟨i, hpi, hxi⟩ := hhole
      exact ⟨Sum.inr ⟨i, hpi⟩, hxi⟩
  let K := Added ⊕ Rem
  let N := Fintype.card K
  let enum : Fin N ≃ K := (Fintype.equivFin K).symm
  let G : OddDistinctCoveringSystem N := {
    modulus := fun i => newMod (enum i)
    residue := fun i => newRes (enum i)
    covers := by
      intro x
      obtain ⟨i, hi⟩ := hnewCover x
      exact ⟨enum.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩
    modulus_one_lt := by
      intro i
      cases enum i with
      | inl r =>
        exact (hsOne r.1).trans_le
          (Nat.le_mul_of_pos_right (s r.1) (pow_pos hell.pos _))
      | inr i => exact F.modulus_one_lt i.val
    modulus_odd := by
      intro i
      cases enum i with
      | inl r => exact (hsOdd r.1).mul hellOdd.pow
      | inr i => exact F.modulus_odd i.val
    modulus_injective := hnewInj.comp enum.injective }
  have hpCount : (Finset.univ.filter fun i : Fin n => p ∣ F.modulus i).card = p := by
    have heq : (Finset.univ.filter fun i : Fin n => p ∣ F.modulus i) =
        Finset.univ.image slot := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi
        obtain ⟨j, hj⟩ := hcomplete i hi
        exact ⟨j, hj⟩
      · rintro ⟨j, rfl⟩
        rw [hmod j]
        exact dvd_mul_right _ _
    rw [heq, Finset.card_image_of_injective _ hslotInj]
    simp
  have hpartition : p + Fintype.card Rem = n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin n => p ∣ F.modulus i)
    simpa only [hpCount, Fintype.card_subtype, Finset.card_univ, Fintype.card_fin, Rem] using h
  have hAdded : Fintype.card Added = ∑ i, (R i).card := by
    simp only [Added, Fintype.card_sigma, Fintype.card_coe]
  have hNlt : N < n := by
    change Fintype.card (Added ⊕ Rem) < n
    rw [Fintype.card_sum, hAdded]
    omega
  exact ⟨N, hNlt, ⟨G⟩⟩

end Erdos7.OddDistinctCoveringSystem

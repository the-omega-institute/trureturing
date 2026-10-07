/- GID: D5/S3/Arith/Covering/SingleChainFreshCompletion
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/SingleChainFreshCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete residual projections bound fresh repairs of a saturated prime chain. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

/-- With the complete prime-bearing inventory and distinct first-prime roots,
every point avoiding all prime-free originals satisfies every chain cofactor. -/
theorem single_chain_pfree_residual_subset
    {n p ell : ℕ} (F : OddDistinctCoveringSystem n)
    (hp : Nat.Prime p) (hell : Nat.Prime ell) (hne : p ≠ ell)
    (slot : Fin p → Fin n)
    (hmod : ∀ j, F.modulus (slot j) = p * ell ^ j.val)
    (hroot : Function.Injective (fun j => F.residue (slot j) % p))
    (hcomplete : ∀ i, p ∣ F.modulus i → ∃ j, slot j = i)
    (x : ℕ)
    (hx : ∀ i, ¬p ∣ F.modulus i → ¬x ≡ F.residue i [MOD F.modulus i]) :
    ∀ j : Fin p, x ≡ F.residue (slot j) [MOD ell^j.val] := by
  obtain ⟨G, R, hpRnot, hQ⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd F.commonModulus_ne_zero p hp.ne_one
  have hpR : Nat.Coprime p R := hp.coprime_iff_not_dvd.mpr hpRnot
  have hperiod : ∀ i, F.modulus i ∣ p^G*R := by
    intro i
    rw [← hQ]
    exact F.modulus_dvd_commonModulus i
  have hfree : ∀ i, ¬p ∣ F.modulus i → F.modulus i ∣ R := by
    intro i hi
    exact ((hp.coprime_iff_not_dvd.mpr hi).symm.pow_right G).dvd_of_dvd_mul_left
      (hperiod i)
  intro j
  have hellR : ell^j.val ∣ R := by
    apply (((Nat.coprime_primes hell hp).mpr (Ne.symm hne)).pow j.val G).dvd_of_dvd_mul_left
    have hd : ell^j.val ∣ F.modulus (slot j) := by
      rw [hmod j]
      exact dvd_mul_left _ _
    exact hd.trans (hperiod (slot j))
  obtain ⟨y, hyp, hyR⟩ := Nat.chineseRemainder hpR (F.residue (slot j)) x
  obtain ⟨i, hyi⟩ := F.covers y
  have hpi : p ∣ F.modulus i := by
    by_contra hfreei
    exact hx i hfreei (((hyR.of_dvd (hfree i hfreei)).symm).trans hyi)
  obtain ⟨k, rfl⟩ := hcomplete i hpi
  have hkp : p ∣ F.modulus (slot k) := by rw [hmod k]; exact dvd_mul_right _ _
  have hkj : k = j := hroot ((hyi.of_dvd hkp).symm.trans hyp)
  subst k
  have hcof : ell^j.val ∣ F.modulus (slot j) := by
    rw [hmod j]
    exact dvd_mul_left _ _
  exact (hyR.of_dvd hellR).symm.trans (hyi.of_dvd hcof)

/-- Unoccupied labels on a finite cofactor ladder. -/
noncomputable def freshLadderHeights {n : ℕ} (F : OddDistinctCoveringSystem n)
    (p ell s : ℕ) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter fun j => ∀ i, F.modulus i ≠ s*ell^j.val

/-- Actual roots attained by the complete complement of the prime-free originals. -/
noncomputable def primeFreeRootProjection {n : ℕ} (F : OddDistinctCoveringSystem n)
    (p s : ℕ) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter fun r => ∃ x : ℕ,
    (∀ i, ¬p ∣ F.modulus i → ¬x ≡ F.residue i [MOD F.modulus i]) ∧ x%s=r.val

/-- Roots covered throughout the terminal cylinder by retained prime-free aligned ladder classes. -/
noncomputable def alignedLadderRoots {n : ℕ} (F : OddDistinctCoveringSystem n)
    (p ell s c : ℕ) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter fun r => ∃ (j : Fin p) (i : Fin n),
    ¬p ∣ F.modulus i ∧ F.modulus i = s*ell^j.val ∧
    F.residue i ≡ c [MOD ell^j.val] ∧ F.residue i%s=r.val

/-- A complete saturated chain forces more actual residual roots than unused
heights on every odd coprime ladder with fewer than p residual roots.
Otherwise fresh CRT classes repair
the simultaneous deletion of the whole chain with strictly fewer originals. -/
theorem fresh_ladder_projection_bounds
    {n p ell s : ℕ} (F : OddDistinctCoveringSystem n)
    (countMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → n ≤ N)
    (hp : Nat.Prime p) (hell : Nat.Prime ell) (hne : p ≠ ell)
    (hsOdd : Odd s) (hsOne : 1 < s) (hcop : Nat.Coprime s ell)
    (hcapacity : (primeFreeRootProjection F p s).card < p)
    (slot : Fin p → Fin n)
    (hmod : ∀ j, F.modulus (slot j) = p * ell ^ j.val)
    (hroot : Function.Injective (fun j => F.residue (slot j) % p))
    (hcomplete : ∀ i, p ∣ F.modulus i → ∃ j, slot j = i) :
    (freshLadderHeights F p ell s).card < (primeFreeRootProjection F p s).card ∧
    (primeFreeRootProjection F p s).card +
      (alignedLadderRoots F p ell s
        (F.residue (slot ⟨p-1, by have := hp.pos; omega⟩))).card ≤ s := by
  classical
  constructor
  · let U := freshLadderHeights F p ell s
    let S := primeFreeRootProjection F p s
    change U.card < S.card
    by_contra hnot
    have hsize : Fintype.card S ≤ Fintype.card U := by
      simpa only [Fintype.card_coe] using (show S.card ≤ U.card by omega)
    obtain ⟨height⟩ := Function.Embedding.nonempty_of_card_le hsize
    have hslotInj : Function.Injective slot := by
      intro j k heq
      exact hroot (congrArg (fun i => F.residue i % p) heq)
    let top : Fin p := ⟨p-1, by have := hp.pos; omega⟩
    let c := F.residue (slot top)
    let Rem := {i : Fin n // ¬p ∣ F.modulus i}
    let newMod : S ⊕ Rem → ℕ := Sum.elim
      (fun r => s*ell^(height r).val.val) (fun i => F.modulus i.val)
    let newRes : S ⊕ Rem → ℕ := Sum.elim
      (fun r => (Nat.chineseRemainder (hcop.pow_right (height r).val.val) r.val.val c).val)
      (fun i => F.residue i.val)
    have hellOdd : Odd ell := by
      let one : Fin p := ⟨1, hp.one_lt⟩
      apply (F.modulus_odd (slot one)).of_dvd_nat
      rw [hmod one]
      simpa only [one, pow_one] using (dvd_mul_left ell p)
    have fresh (r : S) (i : Fin n) : F.modulus i ≠ s*ell^(height r).val.val := by
      exact (Finset.mem_filter.mp (height r).property).2 i
    have hnewInj : Function.Injective newMod := by
      rintro (r | i) (t | k) heq
      · apply congrArg Sum.inl
        apply height.injective
        apply Subtype.ext
        apply hslotInj
        apply F.modulus_injective
        have hpows : ell^(height r).val.val = ell^(height t).val.val :=
          Nat.eq_of_mul_eq_mul_left (by omega : 0 < s) heq
        rw [hmod, hmod, hpows]
      · exact False.elim (fresh r k.val heq.symm)
      · exact False.elim (fresh t i.val heq)
      · exact congrArg Sum.inr (Subtype.ext (F.modulus_injective heq))
    have hnewCover (x : ℕ) : ∃ i, x ≡ newRes i [MOD newMod i] := by
      by_cases hhole : ∀ i, ¬p ∣ F.modulus i → ¬x ≡ F.residue i [MOD F.modulus i]
      · let r : Fin s := ⟨x%s, Nat.mod_lt _ (by omega)⟩
        have hr : r ∈ S := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hhole, rfl⟩
        let rr : S := ⟨r, hr⟩
        have hxc : x ≡ c [MOD ell^(p-1)] :=
          single_chain_pfree_residual_subset F hp hell hne slot hmod hroot hcomplete x hhole top
        have hheight : (height rr).val.val ≤ p-1 := by
          have := (height rr).val.isLt
          omega
        refine ⟨Sum.inl rr, ?_⟩
        exact Nat.chineseRemainder_modEq_unique (hcop.pow_right _)
          (by change x%s=(x%s)%s; exact (Nat.mod_mod x s).symm)
          (hxc.of_dvd (pow_dvd_pow ell hheight))
      · push Not at hhole
        obtain ⟨i, hpi, hxi⟩ := hhole
        exact ⟨Sum.inr ⟨i,hpi⟩,hxi⟩
    let K := S ⊕ Rem
    let N := Fintype.card K
    let enum : Fin N ≃ K := (Fintype.equivFin K).symm
    let G : OddDistinctCoveringSystem N := {
      modulus := fun i => newMod (enum i)
      residue := fun i => newRes (enum i)
      covers := by
        intro x
        obtain ⟨i,hi⟩ := hnewCover x
        exact ⟨enum.symm i,by simpa only [Equiv.apply_symm_apply] using hi⟩
      modulus_one_lt := by
        intro i
        cases enum i with
        | inl r =>
          exact hsOne.trans_le (Nat.le_mul_of_pos_right s (pow_pos hell.pos _))
        | inr i => exact F.modulus_one_lt i.val
      modulus_odd := by
        intro i
        cases enum i with
        | inl r => exact hsOdd.mul hellOdd.pow
        | inr i => exact F.modulus_odd i.val
      modulus_injective := hnewInj.comp enum.injective }
    have hpCount : (Finset.univ.filter fun i : Fin n => p ∣ F.modulus i).card = p := by
      have heq : (Finset.univ.filter fun i : Fin n => p ∣ F.modulus i) =
          Finset.univ.image slot := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hi
          obtain ⟨j,hj⟩ := hcomplete i hi
          exact ⟨j,hj⟩
        · rintro ⟨j,rfl⟩
          rw [hmod j]
          exact dvd_mul_right _ _
      rw [heq, Finset.card_image_of_injective _ hslotInj]
      simp
    have hpartition : p + Fintype.card Rem = n := by
      have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin n => p ∣ F.modulus i)
      simpa only [hpCount, Fintype.card_subtype, Finset.card_univ, Fintype.card_fin, Rem] using h
    have hSlt : Fintype.card S < p := by
      simpa only [Fintype.card_coe] using hcapacity
    have hNlt : N < n := by
      change Fintype.card (S ⊕ Rem) < n
      rw [Fintype.card_sum]
      omega
    exact (Nat.not_lt_of_ge (countMin G)) hNlt
  · let c := F.residue (slot ⟨p-1, by have := hp.pos; omega⟩)
    let S := primeFreeRootProjection F p s
    let A := alignedLadderRoots F p ell s c
    have hdisjoint : Disjoint S A := by
      apply Finset.disjoint_left.mpr
      intro r hrS hrA
      obtain ⟨x, hx, hxr⟩ := (Finset.mem_filter.mp hrS).2
      obtain ⟨j, i, hfree, hlabel, hphase, hir⟩ := (Finset.mem_filter.mp hrA).2
      have hxc : x ≡ c [MOD ell^(p-1)] :=
        single_chain_pfree_residual_subset F hp hell hne slot hmod hroot hcomplete x hx
          ⟨p-1, by have := hp.pos; omega⟩
      have hj : j.val ≤ p-1 := by have := j.isLt; omega
      apply hx i hfree
      rw [hlabel]
      apply (Nat.modEq_and_modEq_iff_modEq_mul (hcop.pow_right j.val)).mp
      exact ⟨hxr.trans hir.symm, (hxc.of_dvd (pow_dvd_pow ell hj)).trans hphase.symm⟩
    have hbound := Finset.card_le_univ (S ∪ A)
    rw [Finset.card_union_of_disjoint hdisjoint] at hbound
    simpa only [Fintype.card_fin] using hbound

end Erdos7.OddDistinctCoveringSystem

/- GID: D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostRelativeEnergy
   mirror-E: none(waiver:algebraic-relative-ghost-energy)
   anchors: []
   utility: none
   digest: The actual bc ghost Virasoro zero mode is diagonal on the original finite-occupation carrier.
 -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Fermionic.BcGhostVirasoro
import D5.S3.Quantum.Fermionic.BcGhostCharge
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostVirasoro
open D5.S3.Quantum.Fermionic.BcGhostCharge

open private modeSite_siteMode siteMode_modeSite normal_term_site siteTerm_ket term_support_subset
  from D5.S3.Quantum.Fermionic.BcGhostCharge
open private annihilate_coefficient from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy

def siteEnergy (j : ℕ) : ℤ := -siteMode j * siteSign j

def energy (S : Finset ℕ) : ℤ := ∑ j ∈ S, siteEnergy j

def relativeEnergy (S : Finset ℕ) : ℤ := energy S + 1

private theorem normal_zero (q : ℤ) : normal (-q) q = -normalTerm q := by
  by_cases hq : q ≤ 1
  · have hp : ¬ -q ≤ -2 := by omega
    simp [normal, normalTerm, hq, hp]
  · have hp : -q ≤ -2 := by omega
    simp [normal, normalTerm, hq, hp]

private theorem summand_zero (q : ℤ) : summand 0 q = ((-q : ℤ) : ℂ) • normalTerm q := by
  simp [summand, normal_zero, smul_neg]

private theorem summand_zero_support (v : Fock) :
    Function.support (fun q : ℤ => summand 0 q v) ⊆ (activeModes v : Set ℤ) := by
  classical
  intro q hq
  apply term_support_subset v
  intro hzero
  exact hq (by simp [summand_zero, hzero])

private theorem weighted_normal_ket (S : Finset ℕ) :
    (∑ᶠ q : ℤ, ((-q : ℤ) : ℂ) • normalTerm q (ket S)) =
      (energy S : ℂ) • ket S := by
  classical
  have hsupport : Function.support
      (fun q : ℤ => ((-q : ℤ) : ℂ) • normalTerm q (ket S)) ⊆
      (activeModes (ket S) : Set ℤ) := by
    simpa only [summand_zero] using summand_zero_support (ket S)
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  have hactive : activeModes (ket S) = S.image siteMode := by
    ext q
    simp [activeModes, ket]
  rw [hactive]
  rw [Finset.sum_image (fun i _ j _ h => by
    simpa only [modeSite_siteMode] using congrArg modeSite h)]
  calc
    _ = ∑ j ∈ S, (siteEnergy j : ℂ) • ket S := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [normal_term_site, siteTerm_ket, modeSite_siteMode, hj, smul_smul,
        siteEnergy]
    _ = (energy S : ℂ) • ket S := by
      rw [← Finset.sum_smul, ← Int.cast_sum]
      rfl

theorem L_zero_ket (S : Finset ℕ) :
    L 0 (ket S) = (energy S : ℂ) • ket S := by
  change (∑ᶠ q : ℤ, summand 0 q (ket S)) = _
  simp_rw [summand_zero]
  exact weighted_normal_ket S

theorem L_zero_coefficient (v : Fock) (S : Finset ℕ) :
    (L 0 v) S = (energy S : ℂ) * v S := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, Finsupp.add_apply, hf, hg, mul_add]
  | single T a =>
      have hsingle : Finsupp.single T a = a • ket T := by simp [ket]
      rw [hsingle, map_smul, L_zero_ket]
      by_cases hST : T = S
      · subst S; simp [ket, mul_comm]
      · simp [ket, hST, Ne.symm hST]

theorem siteEnergy_even (k : ℕ) : siteEnergy (2*k) = (k : ℤ) + 2 := by
  simp [siteEnergy, siteMode, siteSign]

theorem siteEnergy_odd (k : ℕ) : siteEnergy (2*k+1) = (k : ℤ) - 1 := by
  simp [siteEnergy, siteMode, siteSign]

theorem siteEnergy_one : siteEnergy 1 = -1 := by norm_num [siteEnergy, siteMode, siteSign]

theorem siteEnergy_three : siteEnergy 3 = 0 := by norm_num [siteEnergy, siteMode, siteSign]

theorem siteEnergy_pos_of_ne_one_three {j : ℕ} (h1 : j ≠ 1) (h3 : j ≠ 3) :
    0 < siteEnergy j := by
  by_cases heven : j % 2 = 0
  · have hje : j = 2 * (j / 2) := by omega
    rw [hje, siteEnergy_even]
    omega
  · have hjo : j = 2 * (j / 2) + 1 := by omega
    rw [hjo, siteEnergy_odd]
    have hk0 : j / 2 ≠ 0 := by
      intro hk
      apply h1
      omega
    have hk1 : j / 2 ≠ 1 := by
      intro hk
      apply h3
      omega
    omega

theorem b_zero : b 0 = annihilate 3 := by simp [b]

private theorem annihilate_coefficient_not_mem (v : Fock) (T : Finset ℕ)
    (hT : 3 ∉ T) : (annihilate 3 v) T = phase 3 (insert 3 T) * v (insert 3 T) := by
  simpa [Finset.erase_insert hT] using
    (annihilate_coefficient 3 v (insert 3 T) (Finset.mem_insert_self 3 T))

private theorem annihilate_output_mem_zero (v : Fock) (T : Finset ℕ)
    (hT : 3 ∈ T) : (annihilate 3 v) T = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single S a =>
      have hsingle : Finsupp.single S a = a • ket S := by simp [ket]
      rw [hsingle, map_smul, annihilate_ket]
      by_cases hS : 3 ∈ S
      · simp only [if_pos hS]
        have hnot : 3 ∉ S.erase 3 := Finset.notMem_erase 3 S
        have hne : S.erase 3 ≠ T := by
          intro heq
          exact hnot (heq.symm ▸ hT)
        simp [ket, hne, Ne.symm hne]
      · simp [hS]

theorem b_zero_kernel_iff (v : Fock) :
    b 0 v = 0 ↔ ∀ S : Finset ℕ, 3 ∈ S → v S = 0 := by
  rw [b_zero]
  constructor
  · intro hv S hS
    have hc := congrArg (fun w : Fock => w (S.erase 3)) hv
    rw [annihilate_coefficient 3 v S hS] at hc
    have hphase : phase 3 S ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp hc).resolve_left hphase
  · intro hv
    ext T
    by_cases hT : 3 ∈ T
    · exact annihilate_output_mem_zero v T hT
    · rw [annihilate_coefficient_not_mem v T hT]
      rw [hv (insert 3 T) (Finset.mem_insert_self 3 T), mul_zero]

theorem L_zero_down : L 0 (c 1 vacuum) = -(c 1 vacuum) := by
  rw [ghost_vacuum.2.2.1, L_zero_ket]
  norm_num [energy, siteEnergy, siteMode, siteSign]

theorem b_zero_down : b 0 (ket {1}) = 0 := by
  apply (b_zero_kernel_iff _).mpr
  intro S hS
  have hne : ({1} : Finset ℕ) ≠ S := by
    intro heq
    subst S
    simpa using hS
  simp [ket, hne, Ne.symm hne]

private theorem siteEnergy_nonneg_of_ne_one {j : ℕ} (h1 : j ≠ 1) :
    0 ≤ siteEnergy j := by
  by_cases he : j % 2 = 0
  · have hj : j = 2 * (j / 2) := by omega
    rw [hj, siteEnergy_even]
    omega
  · have hj : j = 2 * (j / 2) + 1 := by omega
    rw [hj, siteEnergy_odd]
    by_cases hk : j / 2 = 0
    · have : j = 1 := by omega
      exact (h1 this).elim
    · omega

private theorem energy_nonneg_of_not_mem_one {S : Finset ℕ} (h1 : 1 ∉ S) :
    0 ≤ energy S := by
  classical
  unfold energy
  apply Finset.sum_nonneg
  intro j hj
  exact siteEnergy_nonneg_of_ne_one (by intro h; subst j; exact h1 hj)

theorem relativeEnergy_split (S : Finset ℕ) :
    relativeEnergy S = (if 1 ∉ S then 1 else 0) +
      ∑ j ∈ (S.erase 1).erase 3, siteEnergy j := by
  classical
  by_cases h1 : 1 ∈ S
  · simp only [h1, not_true_eq_false, if_false]
    have h3' : 3 ∈ S.erase 1 ↔ 3 ∈ S := by
      simp [h1]
    by_cases h3 : 3 ∈ S
    · have hm3 : 3 ∈ S.erase 1 := h3'.mpr h3
      unfold relativeEnergy energy
      rw [← Finset.sum_erase_add S siteEnergy h1,
        ← Finset.sum_erase_add (S.erase 1) siteEnergy hm3,
        siteEnergy_one, siteEnergy_three]
      ring
    · have hm3 : 3 ∉ S.erase 1 := by simpa using h3
      unfold relativeEnergy energy
      rw [← Finset.sum_erase_add S siteEnergy h1,
        Finset.erase_eq_of_not_mem hm3, siteEnergy_one]
      ring
  · simp only [h1, not_false_eq_true, if_true]
    have hm1 : S.erase 1 = S := Finset.erase_eq_of_not_mem h1
    have h3' : 3 ∈ S.erase 1 ↔ 3 ∈ S := by simp [hm1]
    by_cases h3 : 3 ∈ S
    · have hm3 : 3 ∈ S.erase 1 := h3'.mpr h3
      unfold relativeEnergy energy
      rw [hm1, ← Finset.sum_erase_add S siteEnergy h3, siteEnergy_three]
      ring
    · have hm3 : 3 ∉ S.erase 1 := by simpa using h3
      unfold relativeEnergy energy
      rw [hm1, Finset.erase_eq_of_not_mem h3]
      ring

theorem relativeEnergy_nonneg (S : Finset ℕ) : 0 ≤ relativeEnergy S := by
  classical
  rw [relativeEnergy_split]
  apply add_nonneg
  · split_ifs <;> norm_num
  · apply Finset.sum_nonneg
    intro j hj
    have hj3 : j ≠ 3 := (Finset.mem_erase.mp hj).1
    have hj1 : j ≠ 1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    exact (siteEnergy_pos_of_ne_one_three hj1 hj3).le

def level (S : Finset ℕ) : ℕ := (relativeEnergy S).toNat

theorem level_cast (S : Finset ℕ) :
    (level S : ℤ) = relativeEnergy S := by
  exact Int.toNat_of_nonneg (relativeEnergy_nonneg S)

def relativeOperator : Module.End ℂ Fock := L 0 + (1 : Module.End ℂ Fock)

abbrev N : Module.End ℂ Fock := relativeOperator

theorem relativeOperator_coefficient (v : Fock) (S : Finset ℕ) :
    (relativeOperator v) S = (relativeEnergy S : ℂ) * v S := by
  change (L 0 v) S + v S = _
  rw [L_zero_coefficient]
  simp only [relativeEnergy, Int.cast_add, Int.cast_one]
  ring

def RelativeKernel (v : Fock) : Prop := b 0 v = 0

def RelativeLevel (ell : ℕ) (v : Fock) : Prop :=
  RelativeKernel v ∧ relativeOperator v = (ell : ℂ) • v

theorem relativeOperator_invariant (v : Fock) (hb : RelativeKernel v) :
    RelativeKernel (relativeOperator v) := by
  have hzero : L 0 * b 0 - b 0 * L 0 = 0 := by simpa using ward_b 0 0
  have hcomm : L 0 * b 0 = b 0 * L 0 := sub_eq_zero.mp hzero
  unfold RelativeKernel relativeOperator at *
  calc
    b 0 (L 0 v + v) = b 0 (L 0 v) + b 0 v := map_add _ _ _
    _ = L 0 (b 0 v) + b 0 v := by
      rw [← LinearMap.congr_fun hcomm v]
    _ = 0 := by rw [hb, map_zero, add_zero]

theorem relative_level_coeff_iff (ell : ℕ) (v : Fock) :
    RelativeLevel ell v ↔
      (∀ S : Finset ℕ, 3 ∈ S → v S = 0) ∧
      (∀ S : Finset ℕ, v S ≠ 0 → relativeEnergy S = (ell : ℤ)) := by
  constructor
  · rintro ⟨hb, he⟩
    refine ⟨(b_zero_kernel_iff v).mp hb, ?_⟩
    intro S hS
    have hc := congrArg (fun w : Fock => w S) he
    simp only [relativeOperator_coefficient, Finsupp.smul_apply, smul_eq_mul] at hc
    have hc' : (relativeEnergy S : ℂ) * v S = (ell : ℂ) * v S := hc
    have hcast : (relativeEnergy S : ℂ) = (ell : ℂ) := mul_right_cancel₀ hS hc'
    exact_mod_cast hcast
  · rintro ⟨hb, he⟩
    refine ⟨(b_zero_kernel_iff v).mpr hb, ?_⟩
    ext S
    simp only [relativeOperator_coefficient, Finsupp.smul_apply, smul_eq_mul]
    by_cases hS : v S = 0
    · simp [hS]
    · rw [he S hS]
      simp

private theorem relative_ground : relativeOperator (ket {1}) = 0 := by
  have hl : L 0 (ket {1}) = -ket {1} := by
    simpa only [ghost_vacuum.2.2.1] using L_zero_down
  change L 0 (ket {1}) + ket {1} = 0
  rw [hl, neg_add_cancel]

theorem relative_ground_line (v : Fock) :
    (RelativeKernel v ∧ relativeOperator v = 0) ↔ ∃ α : ℂ, v = α • ket {1} := by
  constructor
  · rintro ⟨hb, he⟩
    have hlevel : RelativeLevel 0 v := by
      refine ⟨hb, ?_⟩
      simpa using he
    obtain ⟨h3, hE⟩ := (relative_level_coeff_iff 0 v).mp hlevel
    refine ⟨v {1}, ?_⟩
    ext S
    by_cases hS : S = {1}
    · subst S
      simp [ket]
    · by_cases hcoef : v S = 0
      · simp [hcoef, ket, hS, Ne.symm hS]
      · have h3S : 3 ∉ S := by
          intro h3mem
          exact hcoef (h3 S h3mem)
        have hE0 : relativeEnergy S = 0 := hE S hcoef
        have h1S : 1 ∈ S := by
          by_contra hn
          have hnon := energy_nonneg_of_not_mem_one hn
          have : 0 < relativeEnergy S := by
            unfold relativeEnergy
            omega
          omega
        have hnonempty : (S.erase 1).Nonempty := by
          by_contra hempty
          have hEempty : S.erase 1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
          have hcases : S = ∅ ∨ S = {1} := (Finset.erase_eq_empty_iff S 1).mp hEempty
          cases hcases with
          | inl h => exact (Finset.not_mem_empty 1) (h ▸ h1S)
          | inr h => exact hS h
        obtain ⟨j, hj⟩ := hnonempty
        have hj1 : j ≠ 1 := Finset.mem_erase.mp hj |>.1
        have hj3 : j ≠ 3 := by
          intro h; subst j; exact h3S (Finset.mem_of_mem_erase hj)
        have hpos : 0 < siteEnergy j := by
          exact siteEnergy_pos_of_ne_one_three hj1 hj3
        have hsum : siteEnergy j ≤ ∑ k ∈ S.erase 1, siteEnergy k :=
          Finset.single_le_sum (fun k hk => siteEnergy_nonneg_of_ne_one
            (Finset.mem_erase.mp hk |>.1))
            (Finset.mem_erase.mpr ⟨hj1, Finset.mem_of_mem_erase hj⟩)
        have hsplit : relativeEnergy S = ∑ k ∈ S.erase 1, siteEnergy k := by
          unfold relativeEnergy energy
          rw [← Finset.sum_erase_add S siteEnergy h1S, siteEnergy_one]
          ring
        rw [hsplit] at hE0
        have hsum' : siteEnergy j ≤ relativeEnergy S := by simpa [hsplit] using hsum
        have : 0 < relativeEnergy S := lt_of_lt_of_le hpos hsum'
        omega
  · rintro ⟨α, rfl⟩
    constructor
    · change b 0 (α • ket {1}) = 0
      rw [map_smul, b_zero_down, smul_zero]
    · rw [map_smul, relative_ground, smul_zero]

private theorem relativeEnergy_eq_sum_erase_one (S : Finset ℕ) (h1 : 1 ∈ S) :
    relativeEnergy S = ∑ j ∈ S.erase 1, siteEnergy j := by
  unfold relativeEnergy energy
  rw [← Finset.sum_erase_add S siteEnergy h1, siteEnergy_one]
  ring

private theorem siteEnergy_le_relativeEnergy (S : Finset ℕ) (j : ℕ) (hj : j ∈ S) :
    siteEnergy j ≤ relativeEnergy S := by
  classical
  by_cases h1 : 1 ∈ S
  · rw [relativeEnergy_eq_sum_erase_one S h1]
    by_cases hj1 : j = 1
    · subst j
      rw [siteEnergy_one]
      apply le_trans (by omega : (-1 : ℤ) ≤ 0)
      exact Finset.sum_nonneg (fun k hk => siteEnergy_nonneg_of_ne_one
        (Finset.mem_erase.mp hk |>.1))
    · apply Finset.single_le_sum (fun k hk => siteEnergy_nonneg_of_ne_one
        (Finset.mem_erase.mp hk |>.1))
        (Finset.mem_erase.mpr ⟨hj1, hj⟩)
  · have hsum : siteEnergy j ≤ energy S := by
      unfold energy
      apply Finset.single_le_sum (fun k hk => siteEnergy_nonneg_of_ne_one
        (by intro h; subst k; exact h1 hk)) hj
    unfold relativeEnergy
    omega

theorem relative_level_support (ell : ℕ) (v : Fock) (hv : RelativeLevel ell v) :
    ∀ S : Finset ℕ, v S ≠ 0 → S ⊆ Finset.range (2*ell+4) := by
  classical
  obtain ⟨h3, hE⟩ := (relative_level_coeff_iff ell v).mp hv
  intro S hS j hj
  have h3S : 3 ∉ S := by
    intro h
    exact hS (h3 S h)
  have hle : siteEnergy j ≤ (ell : ℤ) := by
    rw [← hE S hS]
    exact siteEnergy_le_relativeEnergy S j hj
  have hbound : j ≤ 2*ell+3 := by
    by_cases heven : j % 2 = 0
    · have hje : j = 2 * (j / 2) := by omega
      rw [hje, siteEnergy_even] at hle
      omega
    · have hjo : j = 2 * (j / 2) + 1 := by omega
      rw [hjo, siteEnergy_odd] at hle
      by_cases hk0 : j / 2 = 0
      · omega
      · by_cases hk1 : j / 2 = 1
        · exfalso
          apply h3S
          have hj3 : j = 3 := by omega
          simpa only [hj3] using hj
        · omega
  exact Finset.mem_range.mpr (by omega)

def levelOccupationSets (ell : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (2*ell+4)).powerset.filter
    (fun S => 3 ∉ S ∧ relativeEnergy S = (ell : ℤ))

theorem mem_levelOccupationSets_iff (ell : ℕ) (S : Finset ℕ) :
    S ∈ levelOccupationSets ell ↔
      S ⊆ Finset.range (2*ell+4) ∧ 3 ∉ S ∧ relativeEnergy S = (ell : ℤ) := by
  simp [levelOccupationSets]

theorem relative_level_expansion (ell : ℕ) (v : Fock) (hv : RelativeLevel ell v) :
    v = ∑ S ∈ levelOccupationSets ell, v S • ket S := by
  classical
  ext T
  by_cases hT : T ∈ levelOccupationSets ell
  · simp [hT, ket]
  · have hzero : v T = 0 := by
      by_contra hn
      have hsub := relative_level_support ell v hv T hn
      have h3 : 3 ∉ T := by
        intro h3T
        exact hn ((relative_level_coeff_iff ell v).mp hv |>.1 T h3T)
      have hE := (relative_level_coeff_iff ell v).mp hv |>.2 T hn
      apply hT
      rw [mem_levelOccupationSets_iff]
      exact ⟨hsub, h3, hE⟩
    simp [hzero, ket, hT]

def levelKets (ell : ℕ) : Set Fock :=
  ket '' (levelOccupationSets ell : Set (Finset ℕ))

theorem level_ket_linearIndependent (ell : ℕ) :
    LinearIndependent ℂ (fun S : {S : Finset ℕ // S ∈ levelOccupationSets ell} => ket S) := by
  simpa [ket] using
    (Finsupp.linearIndependent_single_one (Finset ℕ) ℂ).comp
      (fun S : {S : Finset ℕ // S ∈ levelOccupationSets ell} => S.1)
      Subtype.val_injective

theorem relative_level_mem_span (ell : ℕ) (v : Fock) (hv : RelativeLevel ell v) :
    v ∈ Submodule.span ℂ (levelKets ell) := by
  rw [relative_level_expansion ell v hv]
  apply Submodule.sum_mem
  intro S hS
  apply Submodule.smul_mem
  · exact Submodule.subset_span ⟨S, hS, rfl⟩

def relativeLevelSpace (ell : ℕ) : Submodule ℂ Fock where
  carrier := {v | RelativeLevel ell v}
  zero_mem' := by
    constructor
    · simp [RelativeKernel]
    · simp [relativeOperator]
  add_mem' := by
    intro v w hv hw
    constructor
    · change b 0 (v + w) = 0
      rw [map_add, hv.1, hw.1, add_zero]
    · rw [map_add, hv.2, hw.2, smul_add]
  smul_mem' := by
    intro a v hv
    constructor
    · change b 0 (a • v) = 0
      rw [map_smul, hv.1, smul_zero]
    · simp only [map_smul, hv.2, smul_smul, mul_comm]

theorem mem_relativeLevelSpace_iff (ell : ℕ) (v : Fock) :
    v ∈ relativeLevelSpace ell ↔ RelativeLevel ell v := Iff.rfl

private theorem level_ket_mem_space (ell : ℕ) {S : Finset ℕ}
    (hS : S ∈ levelOccupationSets ell) : ket S ∈ relativeLevelSpace ell := by
  rw [mem_relativeLevelSpace_iff]
  rw [relative_level_coeff_iff]
  refine ⟨?_, ?_⟩
  · intro T hT
    have hne : S ≠ T := by
      intro heq
      subst T
      exact ((mem_levelOccupationSets_iff ell S).mp hS |>.2.1) hT
    simp [ket, hne, Ne.symm hne]
  · intro T hT
    by_cases hTS : T = S
    · subst T
      exact (mem_levelOccupationSets_iff ell S).mp hS |>.2.2
    · simp [ket, hTS, Ne.symm hTS] at hT

theorem relative_level_space_eq_span (ell : ℕ) :
    relativeLevelSpace ell = Submodule.span ℂ (levelKets ell) := by
  apply le_antisymm
  · intro v hv
    exact relative_level_mem_span ell v hv
  · apply Submodule.span_le.2
    rintro x ⟨S, hS, rfl⟩
    exact level_ket_mem_space ell hS

def relativeLevelBasis (ell : ℕ) :
    Basis {S : Finset ℕ // S ∈ levelOccupationSets ell} ℂ (relativeLevelSpace ell) :=
  (Basis.span (level_ket_linearIndependent ell)).map (LinearEquiv.ofEq _ _ (by
    rw [relative_level_space_eq_span]
    congr 1
    ext v
    simp [levelKets, Set.mem_range, Set.mem_image]))

theorem relative_level_finite_dimensional (ell : ℕ) :
    FiniteDimensional ℂ (relativeLevelSpace ell) := by
  exact Module.Finite.of_basis (relativeLevelBasis ell)

end D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy

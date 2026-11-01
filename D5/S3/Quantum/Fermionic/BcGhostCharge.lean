/- GID: D5/S3/Quantum/Fermionic/BcGhostCharge
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostCharge
   mirror-E: none(waiver:algebraic-ghost-charge)
   anchors: []
   utility: none
   digest: Signed occupation charge is the locally finite normal ghost bilinear. -/

import D5.S3.Quantum.Fermionic.BcGhostFock
import Mathlib.Algebra.BigOperators.Finprod

/-! Ghost number on the original algebraic finite-excitation representation. -/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostCharge

/-- Integer subtraction is essential: an occupied even site has charge minus one. -/
def charge (S : Finset ℕ) : ℤ :=
  ((S.filter (fun j => j % 2 = 1)).card : ℤ) -
    ((S.filter (fun j => j % 2 = 0)).card : ℤ)

def siteSign (j : ℕ) : ℤ := if j % 2 = 0 then -1 else 1

def ghostNumber : Module.End ℂ Fock :=
  Finsupp.lsum ℂ fun S => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
    ((charge S : ℂ) • ket S)

@[simp] private theorem number_ket (S : Finset ℕ) :
    ghostNumber (ket S) = (charge S : ℂ) • ket S := by
  simp only [ghostNumber, ket, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul]

private theorem charge_insert (j : ℕ) (S : Finset ℕ) (hj : j ∉ S) :
    charge (insert j S) = charge S + siteSign j := by
  classical
  have hodd : j % 2 = 1 ↔ j % 2 ≠ 0 := by omega
  by_cases he : j % 2 = 0 <;>
    simp [charge, siteSign, Finset.filter_insert, he, hodd, hj] <;> omega

private theorem charge_erase (j : ℕ) (S : Finset ℕ) (hj : j ∈ S) :
    charge (S.erase j) = charge S - siteSign j := by
  have h := charge_insert j (S.erase j) (Finset.notMem_erase j S)
  rw [Finset.insert_erase hj] at h
  omega

private theorem charge_sum (S : Finset ℕ) : charge S = ∑ j ∈ S, siteSign j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [charge]
  | @insert j S hj ih => rw [charge_insert j S hj, Finset.sum_insert hj, ih]; omega

private theorem number_create (j : ℕ) :
    ghostNumber * create j - create j * ghostNumber = (siteSign j : ℂ) • create j := by
  apply end_ext
  intro S
  classical
  by_cases hj : j ∈ S
  · simp [Module.End.mul_apply, create_ket, hj]
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, create_ket,
      if_neg hj, map_smul, number_ket, LinearMap.smul_apply]
    rw [charge_insert j S hj, Int.cast_add]
    module

private theorem number_annihilate (j : ℕ) :
    ghostNumber * annihilate j - annihilate j * ghostNumber =
      -(siteSign j : ℂ) • annihilate j := by
  apply end_ext
  intro S
  classical
  by_cases hj : j ∈ S
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, annihilate_ket,
      if_pos hj, map_smul, number_ket, LinearMap.smul_apply]
    rw [charge_erase j S hj, Int.cast_sub]
    module
  · simp [Module.End.mul_apply, annihilate_ket, hj]

/-- The SL2 vacuum has ghost number zero. -/
private theorem ghost_number_vacuum : ghostNumber vacuum = 0 := by
  simp [vacuum, charge]

/-- Every integer b mode lowers ghost number by one, on both branches. -/
private theorem ghost_number_b (m : ℤ) :
    ghostNumber * b m - b m * ghostNumber = -b m := by
  by_cases hm : m ≤ -2
  · simpa [b, hm, siteSign] using number_create (2 * (-m-2).toNat)
  · simpa [b, hm, siteSign] using number_annihilate (2 * (m+1).toNat + 1)

/-- Every integer c mode raises ghost number by one, on both branches. -/
private theorem ghost_number_c (m : ℤ) :
    ghostNumber * c m - c m * ghostNumber = c m := by
  by_cases hm : m ≤ 1
  · simpa [c, hm, siteSign] using number_create (2 * (1-m).toNat + 1)
  · simpa [c, hm, siteSign] using number_annihilate (2 * (m-2).toNat)

/-- The vacuum and every integer mode have their exact ghost-number degrees. -/
theorem ghost_number_relations :
    ghostNumber vacuum = 0 ∧
    (∀ m : ℤ, ghostNumber * b m - b m * ghostNumber = -b m) ∧
    (∀ m : ℤ, ghostNumber * c m - c m * ghostNumber = c m) :=
  ⟨ghost_number_vacuum, ghost_number_b, ghost_number_c⟩

/-- A signed occupation projection, expressed by actual creation and annihilation. -/
def siteTerm (j : ℕ) : Module.End ℂ Fock :=
  (siteSign j : ℂ) • (create j * annihilate j)

private theorem occupation_projection (j : ℕ) (S : Finset ℕ) :
    (create j * annihilate j) (ket S) = if j ∈ S then ket S else 0 := by
  classical
  by_cases hj : j ∈ S
  · have hl : lowerCount j (S.erase j) = lowerCount j S := by
      unfold lowerCount
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hi⟩, hlt⟩
        exact ⟨hi, hlt⟩
      · rintro ⟨hi, hlt⟩
        exact ⟨⟨by omega, hi⟩, hlt⟩
    simp only [Module.End.mul_apply, annihilate_ket, if_pos hj, map_smul,
      create_ket, Finset.notMem_erase, ite_false, Finset.insert_erase hj,
      smul_smul, phase, hl, ← pow_add]
    have he : lowerCount j S + lowerCount j S = 2 * lowerCount j S := by omega
    rw [he, pow_mul]
    norm_num
  · simp [Module.End.mul_apply, annihilate_ket, hj]

private theorem siteTerm_ket (j : ℕ) (S : Finset ℕ) :
    siteTerm j (ket S) = if j ∈ S then (siteSign j : ℂ) • ket S else 0 := by
  classical
  simp only [siteTerm, LinearMap.smul_apply, occupation_projection]
  split_ifs <;> simp

/-- Normal order is taken relative to the exact ghost vacuum cuts. -/
def normalTerm (n : ℤ) : Module.End ℂ Fock :=
  if n ≤ 1 then c n * b (-n) else -(b (-n) * c n)

def modeSite (n : ℤ) : ℕ :=
  if n ≤ 1 then 2 * (1-n).toNat + 1 else 2 * (n-2).toNat

def siteMode (j : ℕ) : ℤ :=
  if j % 2 = 0 then (j / 2 : ℕ) + 2 else 1 - (j / 2 : ℕ)

private theorem modeSite_siteMode (j : ℕ) : modeSite (siteMode j) = j := by
  unfold modeSite siteMode
  by_cases he : j % 2 = 0
  · have h : ¬ ((j / 2 : ℕ) : ℤ) + 2 ≤ 1 := by omega
    simp only [if_pos he, if_neg h]
    omega
  · have h : 1 - ((j / 2 : ℕ) : ℤ) ≤ 1 := by omega
    simp only [if_neg he, if_pos h]
    omega

private theorem siteMode_modeSite (n : ℤ) : siteMode (modeSite n) = n := by
  unfold modeSite siteMode
  by_cases hn : n ≤ 1
  · simp only [if_pos hn]
    have he : (2 * (1-n).toNat + 1) % 2 ≠ 0 := by omega
    simp only [if_neg he]
    omega
  · simp only [if_neg hn]
    have he : (2 * (n-2).toNat) % 2 = 0 := by omega
    simp only [if_pos he]
    omega

/-- The two normal-ordering branches are precisely the signed site projections. -/
private theorem normal_term_site (n : ℤ) : normalTerm n = siteTerm (modeSite n) := by
  by_cases hn : n ≤ 1
  · have hb : ¬ -n ≤ -2 := by omega
    have hi : -n+1 = 1-n := by omega
    simp [normalTerm, modeSite, hn, b, c, hb, hi, siteTerm, siteSign]
  · have hb : -n ≤ -2 := by omega
    have hi : - -n-2 = n-2 := by omega
    simp [normalTerm, modeSite, hn, b, c, hb, hi, siteTerm, siteSign]

/-- A finite set of integer labels captures all occupied sites of one input. -/
def activeModes (v : Fock) : Finset ℤ :=
  (v.support.biUnion id).image siteMode

private theorem sum_on_ket (S : Finset ℕ) (K : Finset ℤ)
    (hK : ∀ j ∈ S, siteMode j ∈ K) :
    (∑ n ∈ K, normalTerm n) (ket S) = ghostNumber (ket S) := by
  classical
  rw [LinearMap.sum_apply]
  simp_rw [normal_term_site, siteTerm_ket]
  have hsub : S.image siteMode ⊆ K := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    exact hK j hj
  have hinj : Function.Injective siteMode := by
    intro i j h
    simpa only [modeSite_siteMode] using congrArg modeSite h
  have hzero : ∀ n ∈ K, n ∉ S.image siteMode →
      (if modeSite n ∈ S then (siteSign (modeSite n) : ℂ) • ket S else 0) = 0 := by
    intro n hn hnot
    have hs : modeSite n ∉ S := by
      intro hs
      exact hnot (Finset.mem_image.mpr ⟨modeSite n, hs, siteMode_modeSite n⟩)
    simp [hs]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image (fun i _ j _ h => hinj h)]
  calc
    _ = ∑ j ∈ S, (siteSign j : ℂ) • ket S := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [modeSite_siteMode, if_pos hj]
    _ = ghostNumber (ket S) := by
      rw [← Finset.sum_smul, ← Int.cast_sum, ← charge_sum, number_ket]

/-- Every larger finite capture computes the actual diagonal operator on this input. -/
theorem finite_normal_capture (v : Fock) (K : Finset ℤ) (hK : activeModes v ⊆ K) :
    (∑ n ∈ K, normalTerm n) v = ghostNumber v := by
  classical
  conv_lhs => rw [← v.sum_single]
  conv_rhs => rw [← v.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hs : Finsupp.single S (v S) = v S • ket S := by simp [ket]
  simp only [hs, map_smul]
  rw [sum_on_ket S K]
  intro j hj
  exact hK (Finset.mem_image.mpr ⟨j, Finset.mem_biUnion.mpr ⟨S, hS, hj⟩, rfl⟩)

private theorem term_support_subset (v : Fock) :
    Function.support (fun n : ℤ => normalTerm n v) ⊆ (activeModes v : Set ℤ) := by
  classical
  intro n hn
  by_contra hnot
  apply hn
  rw [← v.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  have hj : modeSite n ∉ S := by
    intro hj
    apply hnot
    exact Finset.mem_image.mpr ⟨modeSite n,
      Finset.mem_biUnion.mpr ⟨S, hS, hj⟩, siteMode_modeSite n⟩
  have hs : Finsupp.single S (v S) = v S • ket S := by simp [ket]
  rw [hs, map_smul, normal_term_site, siteTerm_ket, if_neg hj, smul_zero]

/-- Local finiteness is a statement about each input, not the endomorphism family. -/
theorem normal_term_finite_support (v : Fock) :
    (fun n : ℤ => normalTerm n v).HasFiniteSupport :=
  Set.Finite.subset (activeModes v).finite_toSet (term_support_subset v)

/-- Ghost number is the pointwise, locally finite normal-ordered bilinear sum. -/
theorem ghost_number_normal_sum (v : Fock) :
    ghostNumber v = ∑ᶠ n : ℤ, normalTerm n v := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (term_support_subset v)]
  simpa only [LinearMap.sum_apply] using
    (finite_normal_capture v (activeModes v) (fun _ h => h)).symm

end D5.S3.Quantum.Fermionic.BcGhostCharge

/- GID: D5/S3/VertexAlgebra/BcGhostBrstSupport
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostBrstSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Occupied-site deletion and statewise support of the actual ghost charge. -/

import D5.S3.VertexAlgebra.BcGhostFockSupport
import D5.S3.VertexAlgebra.BcGhostStressTails

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostBrstSupport

open BcGhostFockSupport
open scoped BigOperators

noncomputable section

variable {K : Type*} [CommRing K]

private theorem annihilate_support_origin (i : ℕ) (g : Fock K) (S : Finset ℕ)
    (hS : S ∈ (annihilate i g).support) :
    ∃ T ∈ g.support, i ∈ T ∧ S = T.erase i := by
  classical
  change S ∈ (g.sum (fun T a => a • annihilateBasis i T)).support at hS
  obtain ⟨T, hT, hterm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hS)
  have hb := Finsupp.support_smul hterm
  by_cases hi : i ∈ T
  · refine ⟨T, hT, hi, ?_⟩
    simp only [annihilateBasis, if_pos hi] at hb
    exact Finset.mem_singleton.mp (Finsupp.support_single_subset hb)
  · simp [annihilateBasis, hi] at hb

theorem occupied_annihilate_subset (i : ℕ) (g : Fock K) :
    occupied (annihilate i g) ⊆ (occupied g).erase i := by
  classical
  intro site hsite
  obtain ⟨S, hS, hsite⟩ := Finset.mem_biUnion.mp hsite
  obtain ⟨T, hT, _, rfl⟩ := annihilate_support_origin i g S hS
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hsite).1,
    Finset.mem_biUnion.mpr ⟨T, hT, (Finset.mem_erase.mp hsite).2⟩⟩

def bound (g : Fock K) : ℤ := ((occupied g).sup id : ℕ)

theorem c_vanish_below (g : Fock K) (n : ℤ) (hn : n < -bound g - 2) :
    c (-n) g = 0 := by
  have hbranch : ¬ -n ≤ 1 := by
    have : 0 ≤ bound g := Int.natCast_nonneg _
    omega
  rw [c, if_neg hbranch]
  apply annihilate_eq_zero_of_sup_lt g
  have hnonneg : 0 ≤ -n - 2 := by
    have : 0 ≤ bound g := Int.natCast_nonneg _
    omega
  have hcast := Int.toNat_of_nonneg hnonneg
  dsimp [bound] at hn
  omega

private theorem occupied_c_negative_subset (g : Fock K) (n : ℤ) (hn : n ≤ -2) :
    occupied (c (-n) g) ⊆ occupied g := by
  have hbranch : ¬ -n ≤ 1 := by omega
  rw [c, if_neg hbranch]
  exact (occupied_annihilate_subset _ g).trans (Finset.erase_subset _ _)

def expanded (g : Fock K) (index : ℤ × ℤ) : Fock K :=
  if -1 ≤ index.1 then
    c (-index.1) (normalPair (index.1 + index.2) (-index.2) g)
  else normalPair (index.1 + index.2) (-index.2) (c (-index.1) g)

private theorem weighted_row_finite (n : ℤ) (g : Fock K) :
    Function.HasFiniteSupport (fun k : ℤ => (n - k : K) • normalPair (n + k) (-k) g) := by
  apply (Set.finite_Icc (-cutoff n g) (cutoff n g)).subset
  intro k hk
  apply normal_pair_support_interval n g
  intro hzero
  exact hk (by simp only [hzero, smul_zero])

private theorem normalGhost_finsum (n : ℤ) (g : Fock K) :
    BcGhostStressTails.outerNormalPair n g =
      ∑ᶠ k : ℤ, (n - k : K) • expanded g (n, k) := by
  by_cases hn : -1 ≤ n
  · simp only [BcGhostStressTails.outerNormalPair, if_pos hn, LinearMap.comp_apply]
    change c (-n) (∑ᶠ k : ℤ, (n - k : K) • normalPair (n + k) (-k) g) = _
    have hmap := (c (K := K) (-n)).toAddMonoidHom.map_finsum (weighted_row_finite n g)
    simp only [LinearMap.toAddMonoidHom_coe] at hmap
    rw [hmap]
    simp only [map_smul, expanded, hn, ↓reduceIte]
  · simp only [BcGhostStressTails.outerNormalPair, hn, ↓reduceIte, LinearMap.comp_apply, L,
      LinearMap.coe_mk, AddHom.coe_mk, expanded]

private theorem expanded_low (g : Fock K) (n k : ℤ) (hn : n < -bound g - 2) :
    expanded g (n, k) = 0 := by
  have hnonneg : 0 ≤ bound g := Int.natCast_nonneg _
  have hbranch : ¬ -1 ≤ n := by omega
  simp [expanded, hbranch, c_vanish_below g n hn]

private theorem expanded_k_bound (g : Fock K) (n k : ℤ)
    (hnlo : -bound g - 2 ≤ n) (hnhi : n ≤ 2 * bound g + 4)
    (hne : expanded g (n, k) ≠ 0) :
    -(3 * bound g + 8) ≤ k ∧ k ≤ 3 * bound g + 8 := by
  have hnonneg : 0 ≤ bound g := Int.natCast_nonneg _
  have habs : (n.natAbs : ℤ) ≤ 2 * bound g + 4 := by
    rw [Int.natCast_natAbs, abs_le]
    omega
  by_cases hn : -1 ≤ n
  · have hp : normalPair (n + k) (-k) g ≠ 0 := by
      intro hzero
      exact hne (by simp [expanded, hn, hzero])
    obtain ⟨hklo, hkhi⟩ : -cutoff n g ≤ k ∧ k ≤ cutoff n g :=
      normal_pair_support_interval n g hp
    dsimp [cutoff] at hklo hkhi
    dsimp [bound] at *
    omega
  · have hng : n ≤ -2 := by omega
    have hsup : (occupied (c (-n) g)).sup id ≤ (occupied g).sup id :=
      Finset.sup_mono (occupied_c_negative_subset g n hng)
    have hp : normalPair (n + k) (-k) (c (-n) g) ≠ 0 := by
      simpa only [expanded, hn, ↓reduceIte] using hne
    obtain ⟨hklo, hkhi⟩ : -cutoff n (c (-n) g) ≤ k ∧
        k ≤ cutoff n (c (-n) g) := normal_pair_support_interval n (c (-n) g) hp
    dsimp [cutoff] at hklo hkhi
    dsimp [bound] at *
    omega

private theorem expanded_high (g : Fock K) (n k : ℤ)
    (hn : 2 * bound g + 4 < n) : expanded g (n, k) = 0 := by
  have hnonneg : 0 ≤ bound g := Int.natCast_nonneg _
  have hbranch : -1 ≤ n := by omega
  have hp := BcGhostStressTails.normal_pair_high n k g hn
  simp [expanded, hbranch, hp]

def modeInterval (g : Fock K) : Finset ℤ :=
  Finset.Icc (-bound g - 2) (2 * bound g + 4)

def rowInterval (g : Fock K) : Finset ℤ :=
  Finset.Icc (-(3 * bound g + 8)) (3 * bound g + 8)

def rectangle (g : Fock K) : Finset (ℤ × ℤ) :=
  (modeInterval g).product (rowInterval g)

theorem expanded_support_rectangle (g : Fock K) :
    Function.support (expanded g) ⊆ (rectangle g : Set (ℤ × ℤ)) := by
  rintro ⟨n, k⟩ hne
  have hnlo : -bound g - 2 ≤ n := by
    by_contra hlow
    exact hne (expanded_low g n k (lt_of_not_ge hlow))
  have hnhi : n ≤ 2 * bound g + 4 := by
    by_contra hhigh
    exact hne (expanded_high g n k (lt_of_not_ge hhigh))
  have hk := expanded_k_bound g n k hnlo hnhi hne
  change (n, k) ∈ (modeInterval g).product (rowInterval g)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hnlo, hnhi⟩, Finset.mem_Icc.mpr hk⟩

theorem normalGhost_support_interval (g : Fock K) :
    Function.support (fun n : ℤ => BcGhostStressTails.outerNormalPair n g) ⊆
      Set.Icc (-bound g - 2) (2 * bound g + 4) := by
  intro n hn
  have hrow : ∃ k : ℤ, expanded g (n, k) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hn (by simp [normalGhost_finsum, hnone])
  obtain ⟨k, hk⟩ := hrow
  have hb := expanded_support_rectangle g hk
  change (n, k) ∈ (modeInterval g).product (rowInterval g) at hb
  exact Finset.mem_Icc.mp (Finset.mem_product.mp hb).1

private theorem normalGhost_rectangle_row (n : ℤ) (g : Fock K) :
    BcGhostStressTails.outerNormalPair n g =
      ∑ k ∈ rowInterval g, (n - k : K) • expanded g (n, k) := by
  rw [normalGhost_finsum]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  have hne : expanded g (n, k) ≠ 0 := by
    intro hzero
    exact hk (by simp [hzero])
  have hb := expanded_support_rectangle g hne
  change (n, k) ∈ (modeInterval g).product (rowInterval g) at hb
  exact (Finset.mem_product.mp hb).2

private theorem normalGhost_double_sum (g : Fock K) :
    (∑ᶠ n : ℤ, BcGhostStressTails.outerNormalPair n g) =
      ∑ n ∈ modeInterval g, ∑ k ∈ rowInterval g, (n - k : K) • expanded g (n, k) := by
  rw [finsum_eq_sum_of_support_subset _ (s := modeInterval g) (by
    simpa only [modeInterval, Finset.coe_Icc] using normalGhost_support_interval g)]
  exact Finset.sum_congr rfl (fun n _ => normalGhost_rectangle_row n g)

theorem expanded_joint_sum (g : Fock K) :
    (∑ᶠ index : ℤ × ℤ, (index.1 - index.2 : K) • expanded g index) =
      ∑ n ∈ modeInterval g, ∑ k ∈ rowInterval g, (n - k : K) • expanded g (n, k) := by
  rw [finsum_eq_sum_of_support_subset _ (s := rectangle g) (by
    intro index hne
    apply expanded_support_rectangle g
    intro hzero
    exact hne (by simp [hzero]))]
  exact Finset.sum_product _ _ _

theorem normalGhost_joint_finsum (g : Fock K) :
    (∑ᶠ n : ℤ, BcGhostStressTails.outerNormalPair n g) =
      ∑ᶠ index : ℤ × ℤ, (index.1 - index.2 : K) • expanded g index := by
  rw [normalGhost_double_sum, expanded_joint_sum]

#print axioms occupied_annihilate_subset
#print axioms c_vanish_below
#print axioms expanded_support_rectangle
#print axioms normalGhost_support_interval
#print axioms normalGhost_rectangle_row
#print axioms normalGhost_double_sum
#print axioms expanded_joint_sum
#print axioms normalGhost_joint_finsum

end

end D5.S3.VertexAlgebra.BcGhostBrstSupport

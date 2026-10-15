/- GID: D5/S3/VertexAlgebra/BcGhostStressTails
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostStressTails
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ghost stress modes have positive tails and finite outer normal ordering. -/

import D5.S3.VertexAlgebra.BcGhostFockSupport

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostStressTails
noncomputable section

open D5.S3.VertexAlgebra.BcGhostFockSupport

variable {K : Type*} [CommRing K]

private theorem normal_pair_single_high (S : Finset ℕ) (a : K) (m k : ℤ)
    (hm : 2 * ((S.sup id : ℕ) : ℤ) + 4 < m) :
    normalPair (m + k) (-k) (Finsupp.single S a) = 0 := by
  have hbound (site : ℕ) (hsite : S.sup id < site) : site ∉ S := by
    intro hmem
    have hle : site ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  have hnonneg : (0 : ℤ) ≤ ((S.sup id : ℕ) : ℤ) := Int.natCast_nonneg _
  by_cases hp : m + k ≤ -2
  · have hq : ¬ -k ≤ 1 := by omega
    have hnat : 0 ≤ -k - 2 := by omega
    have hcast := Int.toNat_of_nonneg hnat
    have hsite : S.sup id < 2 * (-k - 2).toNat := by omega
    simp [normalPair, hp, c, hq, annihilate, Finsupp.linearCombination_single,
      annihilateBasis, hbound _ hsite]
  · have hbnat : 0 ≤ m + k + 1 := by omega
    have hbcast := Int.toNat_of_nonneg hbnat
    by_cases hb : S.sup id < 2 * (m + k + 1).toNat + 1
    · simp [normalPair, hp, b, annihilate, Finsupp.linearCombination_single,
        annihilateBasis, hbound _ hb]
    · have hq : ¬ -k ≤ 1 := by omega
      have hcnat : 0 ≤ -k - 2 := by omega
      have hccast := Int.toNat_of_nonneg hcnat
      have hc : S.sup id < 2 * (-k - 2).toNat := by omega
      have hnot : 2 * (-k - 2).toNat ∉ S.erase (2 * (m + k + 1).toNat + 1) := by
        intro hmem
        exact hbound _ hc (Finset.mem_of_mem_erase hmem)
      by_cases hmem : 2 * (m + k + 1).toNat + 1 ∈ S
      · simp [normalPair, hp, b, c, hq, annihilate, Finsupp.linearCombination_single,
          annihilateBasis, hmem, hnot]
      · simp [normalPair, hp, b, annihilate, Finsupp.linearCombination_single,
          annihilateBasis, hmem]

theorem normal_pair_high (m k : ℤ) (v : Fock K)
    (hm : 2 * (((occupied v).sup id : ℕ) : ℤ) + 4 < m) :
    normalPair (m + k) (-k) v = 0 := by
  conv_lhs => rw [← Finsupp.sum_single v]
  rw [Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  have hsup : S.sup id ≤ (occupied v).sup id := by
    apply Finset.sup_le
    intro site hsite
    exact Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨S, hS, hsite⟩)
  apply normal_pair_single_high
  have hcast : ((S.sup id : ℕ) : ℤ) ≤ (((occupied v).sup id : ℕ) : ℤ) := by
    exact_mod_cast hsup
  omega

theorem L_high_mode (m : ℤ) (v : Fock K)
    (hm : 2 * (((occupied v).sup id : ℕ) : ℤ) + 4 < m) : L m v = 0 := by
  change (∑ᶠ k : ℤ, (m - k : K) • normalPair (m + k) (-k) v) = 0
  simp only [normal_pair_high m _ v hm, smul_zero, finsum_zero]

def outerNormalPair (n : ℤ) : Module.End K (Fock K) :=
  if -1 ≤ n then (c (K := K) (-n)).comp (L n)
  else (L (K := K) n).comp (c (-n))

theorem outer_has_finite_support (v : Fock K) :
    Function.HasFiniteSupport (fun n : ℤ => outerNormalPair n v) := by
  apply (Set.finite_Icc (-(((occupied v).sup id : ℕ) : ℤ) - 2)
    (2 * (((occupied v).sup id : ℕ) : ℤ) + 4)).subset
  intro n hn
  have hnonneg : (0 : ℤ) ≤ (((occupied v).sup id : ℕ) : ℤ) := Int.natCast_nonneg _
  constructor
  · by_contra hleft
    have hlt : n < -(((occupied v).sup id : ℕ) : ℤ) - 2 := lt_of_not_ge hleft
    have hbranch : ¬ -1 ≤ n := by omega
    have hq : ¬ -n ≤ 1 := by omega
    have hnat : 0 ≤ -n - 2 := by omega
    have hcast := Int.toNat_of_nonneg hnat
    have hsite : (occupied v).sup id < 2 * (-n - 2).toNat := by omega
    have hzero : c (-n) v = 0 := by
      rw [c, if_neg hq, annihilate, Finsupp.linearCombination_apply, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro S hS
      have hnot : 2 * (-n - 2).toNat ∉ S := by
        intro hmem
        have hocc : 2 * (-n - 2).toNat ∈ occupied v :=
          Finset.mem_biUnion.mpr ⟨S, hS, hmem⟩
        have hle : 2 * (-n - 2).toNat ≤ (occupied v).sup id :=
          Finset.le_sup (f := id) hocc
        omega
      simp [annihilateBasis, hnot]
    exact hn (by simp [outerNormalPair, hbranch, hzero])
  · by_contra hright
    have hgt : 2 * (((occupied v).sup id : ℕ) : ℤ) + 4 < n := lt_of_not_ge hright
    have hbranch : -1 ≤ n := by omega
    exact hn (by simp [outerNormalPair, hbranch, L_high_mode n v hgt])

#check @L_high_mode
#check @normal_pair_high
#check @outer_has_finite_support
#print axioms normal_pair_single_high
#print axioms normal_pair_high
#print axioms L_high_mode
#print axioms outer_has_finite_support

end
end D5.S3.VertexAlgebra.BcGhostStressTails

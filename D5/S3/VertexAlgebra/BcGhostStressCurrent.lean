/- GID: D5/S3/VertexAlgebra/BcGhostStressCurrent
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostStressCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual infinite bc ghost stress tensor has current weights two and minus one. -/

import D5.S3.VertexAlgebra.BcGhostExteriorOperators

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostStressCurrent
noncomputable section

open D5.S3.VertexAlgebra.BcGhostFockSupport
open D5.S3.VertexAlgebra.BcGhostExteriorOperators

variable {K : Type*} [CommRing K]

private theorem create_create (i j : ℕ) :
    create (K := K) i * create j + create j * create i = 0 := by
  apply LinearMap.ext
  intro v
  apply exteriorCoordinates.injective
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    map_add, exterior_create, map_zero]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

private theorem annihilate_annihilate (i j : ℕ) :
    annihilate (K := K) i * annihilate j + annihilate j * annihilate i = 0 := by
  apply LinearMap.ext
  intro v
  apply exteriorCoordinates.injective
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    map_add, exterior_annihilate, map_zero]
  apply add_eq_zero_iff_eq_neg.mpr
  exact CliffordAlgebra.contractLeft_comm _ _ _

private theorem annihilate_create (i j : ℕ) :
    annihilate (K := K) i * create j + create j * annihilate i =
      if i = j then 1 else 0 := by
  apply LinearMap.ext
  intro v
  apply exteriorCoordinates.injective
  simp only [LinearMap.add_apply, Module.End.mul_apply,
    map_add, exterior_create, exterior_annihilate]
  unfold exteriorContraction
  rw [CliffordAlgebra.contractLeft_ι_mul]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

theorem b_b (p n : ℤ) : b (K := K) p * b n + b n * b p = 0 := by
  by_cases hp : p ≤ -2 <;> by_cases hn : n ≤ -2
  · simpa [b, hp, hn] using (create_create (K := K) (2 * (-p - 2).toNat) (2 * (-n - 2).toNat))
  · have he : 2 * (n + 1).toNat + 1 ≠ 2 * (-p - 2).toNat := by omega
    have h := annihilate_create (K := K) (2 * (n + 1).toNat + 1) (2 * (-p - 2).toNat)
    rw [if_neg he] at h
    simpa only [b, if_pos hp, if_neg hn, add_comm] using h
  · have he : 2 * (p + 1).toNat + 1 ≠ 2 * (-n - 2).toNat := by omega
    simpa [b, hp, hn, he] using
      (annihilate_create (K := K) (2 * (p + 1).toNat + 1) (2 * (-n - 2).toNat))
  · simpa [b, hp, hn] using
      (annihilate_annihilate (K := K) (2 * (p + 1).toNat + 1) (2 * (n + 1).toNat + 1))

theorem c_c (q n : ℤ) : c (K := K) q * c n + c n * c q = 0 := by
  by_cases hq : q ≤ 1 <;> by_cases hn : n ≤ 1
  · simpa [c, hq, hn] using
      (create_create (K := K) (2 * (1 - q).toNat + 1) (2 * (1 - n).toNat + 1))
  · have he : 2 * (n - 2).toNat ≠ 2 * (1 - q).toNat + 1 := by omega
    have h := annihilate_create (K := K) (2 * (n - 2).toNat) (2 * (1 - q).toNat + 1)
    rw [if_neg he] at h
    simpa only [c, if_pos hq, if_neg hn, add_comm] using h
  · have he : 2 * (q - 2).toNat ≠ 2 * (1 - n).toNat + 1 := by omega
    simpa [c, hq, hn, he] using
      (annihilate_create (K := K) (2 * (q - 2).toNat) (2 * (1 - n).toNat + 1))
  · simpa [c, hq, hn] using
      (annihilate_annihilate (K := K) (2 * (q - 2).toNat) (2 * (n - 2).toNat))

theorem b_c (p q : ℤ) : b (K := K) p * c q + c q * b p =
    if p + q = 0 then 1 else 0 := by
  by_cases hp : p ≤ -2 <;> by_cases hq : q ≤ 1
  · have he : p + q ≠ 0 := by omega
    simpa [b, c, hp, hq, he] using
      (create_create (K := K) (2 * (-p - 2).toNat) (2 * (1 - q).toNat + 1))
  · have he : 2 * (q - 2).toNat = 2 * (-p - 2).toNat ↔ p + q = 0 := by omega
    have h := annihilate_create (K := K) (2 * (q - 2).toNat) (2 * (-p - 2).toNat)
    simp only [he] at h
    simpa only [b, c, if_pos hp, if_neg hq, add_comm] using h
  · have he : 2 * (p + 1).toNat + 1 = 2 * (1 - q).toNat + 1 ↔ p + q = 0 := by omega
    have h := annihilate_create (K := K) (2 * (p + 1).toNat + 1) (2 * (1 - q).toNat + 1)
    simp only [he] at h
    simpa only [b, c, if_neg hp, if_pos hq] using h
  · have he : p + q ≠ 0 := by omega
    simpa [b, c, hp, hq, he] using
      (annihilate_annihilate (K := K) (2 * (p + 1).toNat + 1) (2 * (q - 2).toNat))

private theorem product_commutator (A B X U V : Module.End K (Fock K))
    (hB : B * X + X * B = U) (hA : A * X + X * A = V) :
    (A * B) * X - X * (A * B) = A * U - V * B := by
  rw [← hB, ← hA]
  noncomm_ring

private theorem normalPair_b (p q n : ℤ) :
    normalPair (K := K) p q * b n - b n * normalPair p q =
      if q + n = 0 then b p else 0 := by
  have hcb : c (K := K) q * b n + b n * c q = if q + n = 0 then 1 else 0 := by
    simpa [add_comm] using b_c (K := K) n q
  by_cases hp : p ≤ -2
  · rw [normalPair, if_pos hp, ← Module.End.mul_eq_comp,
      product_commutator _ _ _ _ _ hcb (b_b p n)]
    split_ifs <;> simp
  · rw [normalPair, if_neg hp, ← Module.End.mul_eq_comp]
    have hn : -(c (K := K) q * b p) * b n - b n * -(c (K := K) q * b p) =
        -((c (K := K) q * b p) * b n - b n * (c q * b p)) := by noncomm_ring
    rw [hn, product_commutator _ _ _ _ _ (b_b p n) hcb]
    split_ifs <;> simp

private theorem normalPair_c (p q n : ℤ) :
    normalPair (K := K) p q * c n - c n * normalPair p q =
      if p + n = 0 then -c (K := K) q else 0 := by
  by_cases hp : p ≤ -2
  · rw [normalPair, if_pos hp, ← Module.End.mul_eq_comp,
      product_commutator _ _ _ _ _ (c_c q n) (b_c p n)]
    split_ifs <;> simp
  · rw [normalPair, if_neg hp, ← Module.End.mul_eq_comp]
    have hn : -(c (K := K) q * b p) * c n - c n * -(c (K := K) q * b p) =
        -((c (K := K) q * b p) * c n - c n * (c q * b p)) := by noncomm_ring
    rw [hn, product_commutator _ _ _ _ _ (b_c p n) (c_c q n)]
    split_ifs <;> simp

private theorem stress_commutator (m t : ℤ) (X Y : Module.End K (Fock K))
    (h : ∀ k : ℤ, normalPair (m + k) (-k) * X - X * normalPair (m + k) (-k) =
      if k = t then Y else 0) :
    L m * X - X * L m = (m - t : K) • Y := by
  apply LinearMap.ext
  intro v
  let a : ℤ := min (-cutoff m v) (min (-cutoff m (X v)) t)
  let z : ℤ := max (cutoff m v) (max (cutoff m (X v)) t)
  have hav : a ≤ -cutoff m v := min_le_left _ _
  have haX : a ≤ -cutoff m (X v) := (min_le_right _ _).trans (min_le_left _ _)
  have htv : a ≤ t := (min_le_right _ _).trans (min_le_right _ _)
  have hzv : cutoff m v ≤ z := le_max_left _ _
  have hzX : cutoff m (X v) ≤ z := (le_max_left _ _).trans (le_max_right _ _)
  have htz : t ≤ z := (le_max_right _ _).trans (le_max_right _ _)
  change L m (X v) - X (L m v) = (m - t : K) • Y v
  rw [L_interval_sum m (X v) a z haX hzX, L_interval_sum m v a z hav hzv,
    map_sum]
  simp only [map_smul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ k ∈ Finset.Icc a z,
        (m - k : K) • ((normalPair (m + k) (-k) * X -
          X * normalPair (m + k) (-k) : Module.End K (Fock K)) v) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [smul_sub]
    _ = ∑ k ∈ Finset.Icc a z, if k = t then (m - t : K) • Y v else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [h k]
          by_cases hkt : k = t <;> simp [hkt]
    _ = (m - t : K) • Y v := by
          simp [Finset.mem_Icc, htv, htz]

/-- On the full infinite algebraic carrier, the b-current has conformal weight two. -/
theorem L_b_commutator (m n : ℤ) :
    L (K := K) m * b n - b n * L m = (m - n : K) • b (m + n) := by
  apply stress_commutator
  intro k
  rw [normalPair_b]
  have he : -k + n = 0 ↔ k = n := by omega
  simp only [he]
  by_cases hkn : k = n <;> simp [hkn]

/-- On the full infinite algebraic carrier, the c-current has conformal weight minus one. -/
theorem L_c_commutator (m n : ℤ) :
    L (K := K) m * c n - c n * L m = (-2 * m - n : K) • c (m + n) := by
  have h := stress_commutator (K := K) m (-(m + n)) (c n) (-c (K := K) (m + n)) (by
    intro k
    rw [normalPair_c]
    have he : m + k + n = 0 ↔ k = -(m + n) := by omega
    simp only [he]
    by_cases hkn : k = -(m + n)
    · subst k
      simp only [neg_neg]
    · rw [if_neg hkn, if_neg hkn])
  rw [h, smul_neg, ← neg_smul]
  congr 1
  push_cast
  ring

#print axioms L_b_commutator
#print axioms L_c_commutator
end
end D5.S3.VertexAlgebra.BcGhostStressCurrent

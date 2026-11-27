/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ordered quadratic coefficient of the two complementary third-cover grids. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement

/-!
The complementary Virasoro action is the sign-ordered normal product of
the one-third and two-thirds currents plus the scalar shift at mode zero.
The normal product is the field product at n = -1 in Bakalov and Kac,
*Twisted Modules over Lattice Vertex Algebras*, arXiv:math/0402315v3, (3.13).
The equality here is on the concrete complement polynomial space.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedQuadratic

open ThirdCoverIntegerFactor ThirdCoverComplement

private def sortedPair (k l : ℤ) : Module.End ℂ ComplementFock :=
  if k ≤ l then fractionalCurrent k * fractionalCurrent l
  else fractionalCurrent l * fractionalCurrent k

private theorem sortedPair_swap (k l : ℤ) : sortedPair k l = sortedPair l k := by
  rcases lt_trichotomy k l with h | rfl | h
  · simp [sortedPair, h.le, h.not_ge]
  · rfl
  · simp [sortedPair, h.le, h.not_ge]

private theorem sortedPair_eq_smul_complementPair (k l : ℤ) :
    sortedPair k l = (3 : ℂ)⁻¹ • complementPair l k := by
  by_cases h : k ≤ l <;>
    simp only [sortedPair, fractionalCurrent, complementPair, h, ite_true, ite_false,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, inverse_scale_sq,
      Module.End.mul_eq_comp]

/-- The two terms of the usual normal order are selected by the sign of the
first frequency. The native indices are three times their frequencies. -/
def orderedPair (k l : ℤ) : Module.End ℂ ComplementFock :=
  if k < 0 then fractionalCurrent k * fractionalCurrent l
  else fractionalCurrent l * fractionalCurrent k

private theorem sortedPair_eq_orderedPair {k l : ℤ} (hk : ¬ (3 : ℤ) ∣ k)
    (hl : ¬ (3 : ℤ) ∣ l) : sortedPair k l = orderedPair k l := by
  have commute (hn : k + l ≠ 0) :
      fractionalCurrent k * fractionalCurrent l = fractionalCurrent l * fractionalCurrent k :=
    sub_eq_zero.mp (by simpa only [hn, ite_false] using fractionalCurrent_commutator k l hk hl)
  have hk0 : k ≠ 0 := fun h => hk (h ▸ dvd_zero _)
  by_cases hkl : k ≤ l <;> by_cases hneg : k < 0 <;>
    simp only [sortedPair, orderedPair, hkl, hneg, ite_true, ite_false]
  · exact commute (by omega)
  · exact (commute (by omega)).symm

/-- Native indices with remainder a modulo three. For 0 ≤ a < 3 the frequency grid is ℤ + a/3. -/
def residue (a : ℤ) : Set ℤ := {k | k % 3 = a}

private theorem residue_nondivisible {a k : ℤ} (ha : a ≠ 0) (hk : k ∈ residue a) :
    ¬ (3 : ℤ) ∣ k :=
  fun hd => ha ((show k % 3 = a from hk).symm.trans (Int.emod_eq_zero_of_dvd hd))

private theorem sortedPair_eq_orderedPair_on_residue (m : ℤ) {a k : ℤ}
    (ha : a ≠ 0) (hk : k ∈ residue a) :
    sortedPair k (3 * m - k) = orderedPair k (3 * m - k) :=
  sortedPair_eq_orderedPair (residue_nondivisible ha hk)
    (noninteger_partner m k (residue_nondivisible ha hk))

private theorem sorted_residue_sums (m : ℤ) (Q : ComplementFock) :
    (∑ᶠ k ∈ residue 1, sortedPair k (3 * m - k) Q) =
      ∑ᶠ k ∈ residue 2, sortedPair k (3 * m - k) Q := by
  refine finsum_mem_eq_of_bijOn (fun k : ℤ => 3 * m - k) ⟨?_, ?_, ?_⟩ ?_
  · intro k hk
    change k % 3 = 1 at hk
    change (3 * m - k) % 3 = 2
    omega
  · intro k _ l _ h
    change 3 * m - k = 3 * m - l at h
    omega
  · intro l hl
    change l % 3 = 2 at hl
    refine ⟨3 * m - l, ?_, by change 3 * m - (3 * m - l) = l; omega⟩
    change (3 * m - l) % 3 = 1
    omega
  · intro k _
    rw [show 3 * m - (3 * m - k) = k by omega, sortedPair_swap]

/-- Reflection interchanges the two normal-ordered residue sums on every polynomial. -/
theorem complementary_residue_sums (m : ℤ) (Q : ComplementFock) :
    (∑ᶠ k ∈ residue 1, orderedPair k (3 * m - k) Q) =
      ∑ᶠ k ∈ residue 2, orderedPair k (3 * m - k) Q := by
  have convert (a : ℤ) (ha : a ≠ 0) :
      (∑ᶠ k ∈ residue a, sortedPair k (3 * m - k) Q) =
        ∑ᶠ k ∈ residue a, orderedPair k (3 * m - k) Q :=
    finsum_mem_congr rfl fun k hk =>
      LinearMap.congr_fun (sortedPair_eq_orderedPair_on_residue m ha hk) Q
  rw [← convert 1 (by decide), ← convert 2 (by decide), sorted_residue_sums]

/-- The coefficient of z^(-m-2) in :U(z)V(z):. The summation index belongs to U
and the complementary index belongs to V. -/
def orderedCoefficient (m : ℤ) (Q : ComplementFock) : ComplementFock :=
  ∑ᶠ k ∈ residue 1, orderedPair k (3 * m - k) Q

/-- Every polynomial has finite support for the ordered sum on a nonzero residue. -/
theorem orderedPair_finite_on_residue (m : ℤ) (Q : ComplementFock) {a : ℤ} (ha : a ≠ 0) :
    (residue a ∩ Function.support (fun k : ℤ => orderedPair k (3 * m - k) Q)).Finite := by
  refine (complementPair_finiteSupport m Q).subset ?_
  intro k ⟨hk, hs⟩
  refine ⟨residue_nondivisible ha hk, ?_⟩
  change complementPair (3 * m - k) k Q ≠ 0
  intro hz
  apply hs
  change orderedPair k (3 * m - k) Q = 0
  rw [← sortedPair_eq_orderedPair_on_residue m ha hk, sortedPair_eq_smul_complementPair]
  simp only [LinearMap.smul_apply, hz, smul_zero]

/-- The fractional Virasoro mode is one ordered dual-grid sum with the vacuum shift. -/
theorem fractionalVirasoro_apply_ordered (m : ℤ) (Q : ComplementFock) :
    fractionalVirasoro m Q =
      orderedCoefficient m Q + (if m = 0 then (1 / 9 : ℂ) else 0) • Q := by
  have hsplit : integerIndicesᶜ = residue 1 ∪ residue 2 := by
    ext k
    change (¬ (3 : ℤ) ∣ k) ↔ k % 3 = 1 ∨ k % 3 = 2
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  have hd : Disjoint (residue 1) (residue 2) := by
    refine Set.disjoint_left.2 fun k h₁ h₂ => ?_
    change k % 3 = 1 at h₁
    change k % 3 = 2 at h₂
    omega
  have hscale :
      (3 : ℂ)⁻¹ • (∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) =
        ∑ᶠ k ∈ integerIndicesᶜ, orderedPair k (3 * m - k) Q := by
    calc
      _ = ∑ᶠ k ∈ integerIndicesᶜ, (3 : ℂ)⁻¹ • complementPair (3 * m - k) k Q := by
        simpa only [DistribSMul.toAddMonoidHom_apply] using
          (DistribSMul.toAddMonoidHom ComplementFock (3 : ℂ)⁻¹).map_finsum_mem'
            (complementPair_finiteSupport m Q)
      _ = _ := by
        refine finsum_mem_congr rfl fun k hk => ?_
        have hp := sortedPair_eq_orderedPair (k := k) hk (noninteger_partner m k hk)
        rw [sortedPair_eq_smul_complementPair] at hp
        simpa only [LinearMap.smul_apply] using LinearMap.congr_fun hp Q
  change (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ •
      (∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q)) +
      (if m = 0 then (1 / 9 : ℂ) else 0) • Q = _
  rw [orderedCoefficient, smul_comm (3 : ℂ)⁻¹ (2 : ℂ)⁻¹, hscale, hsplit,
    finsum_mem_union' hd (orderedPair_finite_on_residue m Q (by decide))
      (orderedPair_finite_on_residue m Q (by decide)), ← complementary_residue_sums]
  congr 1
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedQuadratic

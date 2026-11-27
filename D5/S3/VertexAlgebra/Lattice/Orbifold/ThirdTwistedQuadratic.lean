import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement
import Batteries.Tactic.OpenPrivate

/-! The ordered moving-pair coefficient of the order-three oscillator field. -/

set_option autoImplicit false

noncomputable section

open private complementPair_finiteSupport inverse_scale_sq
  from D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement

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

private theorem sortedPair_finite (m : ℤ) (Q : ComplementFock) :
    ({k : ℤ | ¬ (3 : ℤ) ∣ k} ∩ Function.support
      (fun k : ℤ => sortedPair k (3 * m - k) Q)).Finite := by
  have scale (k l : ℤ) : sortedPair k l = (3 : ℂ)⁻¹ • complementPair l k := by
    by_cases h : k ≤ l <;>
      simp only [sortedPair, fractionalCurrent, complementPair, h, ite_true, ite_false,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, inverse_scale_sq,
        Module.End.mul_eq_comp]
  refine (complementPair_finiteSupport m Q).subset ?_
  intro k ⟨hk, hs⟩
  refine ⟨hk, ?_⟩
  change complementPair (3 * m - k) k Q ≠ 0
  intro hz
  apply hs
  change sortedPair k (3 * m - k) Q = 0
  simp [scale, hz]

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

/-- Native indices of the frequency grid ℤ + a/3. -/
def residue (a : ℤ) : Set ℤ := {k | k % 3 = a}

private theorem sortedPair_eq_orderedPair_on_residue (m : ℤ) {a k : ℤ}
    (ha : a ≠ 0) (hk : k ∈ residue a) :
    sortedPair k (3 * m - k) = orderedPair k (3 * m - k) := by
  have hk' : ¬ (3 : ℤ) ∣ k :=
    fun hd => ha ((show k % 3 = a from hk).symm.trans (Int.emod_eq_zero_of_dvd hd))
  exact sortedPair_eq_orderedPair hk' fun hd =>
    hk' (by simpa using dvd_sub (dvd_mul_right (3 : ℤ) m) hd)

private theorem residue_finite (m : ℤ) (Q : ComplementFock) {a : ℤ}
    (ha : a ≠ 0) :
    (residue a ∩ Function.support (fun k : ℤ => sortedPair k (3 * m - k) Q)).Finite :=
  (sortedPair_finite m Q).subset fun k ⟨hk, hs⟩ =>
    ⟨fun hd => ha ((show k % 3 = a from hk).symm.trans (Int.emod_eq_zero_of_dvd hd)), hs⟩

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

theorem orderedPair_finite_on_residue (m : ℤ) (Q : ComplementFock) {a : ℤ} (ha : a ≠ 0) :
    (residue a ∩ Function.support (fun k : ℤ => orderedPair k (3 * m - k) Q)).Finite := by
  refine (residue_finite m Q ha).subset ?_
  intro k ⟨hk, hs⟩
  refine ⟨hk, ?_⟩
  change sortedPair k (3 * m - k) Q ≠ 0
  rw [sortedPair_eq_orderedPair_on_residue m ha hk]
  exact hs

theorem fractionalVirasoro_apply_ordered (m : ℤ) (Q : ComplementFock) :
    fractionalVirasoro m Q =
      orderedCoefficient m Q + (if m = 0 then (1 / 9 : ℂ) else 0) • Q := by
  have hsplit : {k : ℤ | ¬ (3 : ℤ) ∣ k} = residue 1 ∪ residue 2 := by
    ext k
    change (¬ (3 : ℤ) ∣ k) ↔ k % 3 = 1 ∨ k % 3 = 2
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  have hd : Disjoint (residue 1) (residue 2) := by
    refine Set.disjoint_left.2 fun k h₁ h₂ => ?_
    change k % 3 = 1 at h₁
    change k % 3 = 2 at h₂
    omega
  rw [fractionalVirasoro_apply, orderedCoefficient]
  change (2 : ℂ)⁻¹ • (∑ᶠ k ∈ {k : ℤ | ¬ (3 : ℤ) ∣ k}, sortedPair k (3 * m - k) Q) + _ = _
  rw [hsplit, finsum_mem_union' hd (residue_finite m Q (by decide))
    (residue_finite m Q (by decide)), ← sorted_residue_sums]
  congr 1
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  exact finsum_mem_congr rfl fun k hk =>
    LinearMap.congr_fun (sortedPair_eq_orderedPair_on_residue m (by decide) hk) Q

#print axioms complementary_residue_sums
#print axioms orderedPair_finite_on_residue
#print axioms fractionalVirasoro_apply_ordered

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedQuadratic

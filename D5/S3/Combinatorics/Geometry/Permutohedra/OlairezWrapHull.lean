/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed wrap hull is an image of the absolute-sum ball. -/
import D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62
import Mathlib.Analysis.Convex.Combination

/-! The cross-polytope image and its constant-translate fibers. -/

namespace OlairezWrapHull

open Finset OlairezQ62
open scoped Pointwise

noncomputable section

variable {n : ℕ} [NeZero n]

def absoluteSum (z : Coordinates n) : ℝ := ∑ i, |z i|

private theorem norm_smul (a : ℝ) (z : Coordinates n) : absoluteSum (a • z) = |a| * absoluteSum z := by
  simp only [absoluteSum, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]

private theorem norm_add_le (z w : Coordinates n) :
    absoluteSum (z + w) ≤ absoluteSum z + absoluteSum w := by
  rw [absoluteSum, absoluteSum, absoluteSum, ← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_add_le (z i) (w i)

private def signedBasis (n : ℕ) : Set (Coordinates n) :=
  Set.range (basisVector (n := n)) ∪ Set.range (fun i : ZMod n => -basisVector i)

private theorem unitBall_eq_hull :
    {z : Coordinates n | absoluteSum z ≤ 1} = convexHull ℝ (signedBasis n) := by
  classical
  symm
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩) <;>
        simp [absoluteSum, basisVector, Pi.single_apply, apply_ite (fun x : ℝ => |x|)]
    · intro z hz w hw a b ha hb hab
      change absoluteSum z ≤ 1 at hz
      change absoluteSum w ≤ 1 at hw
      change absoluteSum (a • z + b • w) ≤ 1
      calc
        _ ≤ absoluteSum (a • z) + absoluteSum (b • w) := norm_add_le _ _
        _ = a * absoluteSum z + b * absoluteSum w := by
          rw [norm_smul, norm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hz ha) (mul_le_mul_of_nonneg_left hw hb)
        _ = 1 := by simp [hab]
  · intro z hz
    change absoluteSum z ≤ 1 at hz
    have hzero : (0 : Coordinates n) ∈ convexHull ℝ (signedBasis n) := by
      have hp : basisVector (0 : ZMod n) ∈ convexHull ℝ (signedBasis n) :=
        subset_convexHull ℝ _ (Or.inl ⟨0, rfl⟩)
      have hm : -basisVector (0 : ZMod n) ∈ convexHull ℝ (signedBasis n) :=
        subset_convexHull ℝ _ (Or.inr ⟨0, rfl⟩)
      have h := convex_convexHull ℝ (signedBasis n) hp hm
        (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
        (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
      simpa [← smul_add] using h
    let coeff : Option (ZMod n) → ℝ := fun i => i.elim (1 - absoluteSum z) (fun i => |z i|)
    let point : Option (ZMod n) → Coordinates n :=
      fun j => j.elim 0 (fun i => if 0 ≤ z i then basisVector i else -basisVector i)
    rw [← (convex_convexHull ℝ (signedBasis n)).convexHull_eq]
    apply mem_convexHull_of_exists_fintype coeff point
    · intro i
      cases i with
      | none => exact sub_nonneg.mpr hz
      | some i => exact abs_nonneg _
    · simp [coeff, Fintype.sum_option, absoluteSum]
    · intro i
      cases i with
      | none => exact hzero
      | some i =>
        apply subset_convexHull ℝ _
        change (if 0 ≤ z i then basisVector i else -basisVector i) ∈ signedBasis n
        split
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨i, rfl⟩
    · funext i
      simp only [Fintype.sum_option, coeff, point, Option.elim, smul_zero, Finset.sum_apply,
        Pi.zero_apply, zero_add]
      calc
        (∑ j : ZMod n, (|z j| • (if 0 ≤ z j then basisVector j else -basisVector j)) i)
            = ∑ j : ZMod n, if j = i then z i else 0 := by
          apply sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            by_cases h : 0 ≤ z i <;>
              simp [h, basisVector, abs_of_nonneg, abs_of_neg, lt_of_not_ge]
          · have hij := Ne.symm hji
            by_cases h : 0 ≤ z j <;> simp [h, basisVector, hji, hij]
        _ = z i := by simp

private def wrapMap (n : ℕ) [NeZero n] : Coordinates n →ₗ[ℝ] sumZero n where
  toFun z := ⟨fun i => (∑ j, z j) - (n : ℝ) * z i, by
    change ∑ i : ZMod n, ((∑ j, z j) - (n : ℝ) * z i) = 0
    simp [sum_sub_distrib, ← mul_sum, ZMod.card, nsmul_eq_mul]⟩
  map_add' z w := by
    apply Subtype.ext
    funext i
    change (∑ j, (z j + w j)) - (n : ℝ) * (z i + w i) =
      ((∑ j, z j) - (n : ℝ) * z i) + ((∑ j, w j) - (n : ℝ) * w i)
    rw [sum_add_distrib]
    ring
  map_smul' c z := by
    apply Subtype.ext
    funext i
    change (∑ j, c * z j) - (n : ℝ) * (c * z i) = c * ((∑ j, z j) - (n : ℝ) * z i)
    rw [← mul_sum]
    ring

private theorem wrapMap_basis (i : ZMod n) : wrapMap n (basisVector i) = wrapPoint i := by
  apply Subtype.ext
  funext j
  change (∑ k, basisVector i k) - (n : ℝ) * basisVector i j =
    1 - (n : ℝ) * basisVector i j
  simp [basisVector]

private theorem wrapMap_ball :
    (wrapMap n) '' {z | absoluteSum z ≤ 1} = convexHull ℝ (signedPoints n) := by
  rw [unitBall_eq_hull, LinearMap.image_convexHull]
  congr 1
  rw [signedBasis, signedPoints, Set.image_union, ← Set.range_comp', ← Set.range_comp']
  simp [wrapMap_basis]

/-- Membership in the scaled wrap hull is exactly feasibility of a real constant translate
in the absolute-sum ball. -/
theorem scaled_wrap_hull_iff (k : ℕ) (d : sumZero n) :
    d ∈ (k : ℝ) • convexHull ℝ (signedPoints n) ↔
      ∃ t : ℝ, absoluteSum (fun i => d.val i + t) ≤ (n : ℝ) * k := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← wrapMap_ball]
  have himage : (wrapMap n) '' ((k : ℝ) • {z | absoluteSum z ≤ 1}) =
      (k : ℝ) • ((wrapMap n) '' {z | absoluteSum z ≤ 1}) := by
    simpa only [RingHom.id_apply] using
      image_smul_setₛₗ (wrapMap n) (k : ℝ) {z | absoluteSum z ≤ 1}
  rw [← himage]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    change absoluteSum q ≤ 1 at hq
    let w : Coordinates n := (k : ℝ) • q
    have hw : absoluteSum w ≤ k := by
      rw [show w = (k : ℝ) • q from rfl, norm_smul, abs_of_nonneg (by positivity)]
      simpa using mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    refine ⟨-(∑ i, w i), ?_⟩
    change absoluteSum (fun i => (∑ j, w j) - (n : ℝ) * w i + -(∑ j, w j)) ≤ _
    rw [show (fun i => (∑ j, w j) - (n : ℝ) * w i + -(∑ j, w j)) =
      (-(n : ℝ)) • w by funext i; change _ = -(n : ℝ) * w i; ring,
      norm_smul, abs_neg, abs_of_pos hn]
    exact mul_le_mul_of_nonneg_left hw hn.le
  · rintro ⟨t, ht⟩
    let z : Coordinates n := fun i => d.val i + t
    have hz : ∑ i, z i = (n : ℝ) * t := by
      have hs : ∑ i, d.val i = 0 := d.property
      simp [z, sum_add_distrib, hs, ZMod.card, nsmul_eq_mul]
    by_cases hk : k = 0
    · subst k
      have hzero (i : ZMod n) : z i = 0 := by
        have hl : |z i| ≤ absoluteSum z := single_le_sum (fun j _ => abs_nonneg (z j)) (mem_univ i)
        have hu : absoluteSum z ≤ 0 := by simpa using ht
        exact abs_eq_zero.mp (le_antisymm (hl.trans hu) (abs_nonneg _))
      have hz' : z = 0 := funext hzero
      have ht0 : t = 0 := by
        rw [hz'] at hz
        simp at hz
        exact hz.resolve_left (NeZero.ne n)
      have hd0 : d = 0 := by
        apply Subtype.ext
        exact funext fun i => by simpa [z, ht0] using hzero i
      exact ⟨0, ⟨0, by simp [absoluteSum], by simp⟩, by simp [hd0]⟩
    · have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      let c : ℝ := (n : ℝ) * k
      have hc : 0 < c := mul_pos hn hkpos
      let q : Coordinates n := (-c⁻¹) • z
      have hq : q ∈ {z : Coordinates n | absoluteSum z ≤ 1} := by
        change absoluteSum ((-c⁻¹) • z) ≤ 1
        rw [norm_smul, abs_neg, abs_of_pos (inv_pos.mpr hc), ← div_eq_inv_mul]
        exact (div_le_one hc).mpr ht
      refine ⟨(k : ℝ) • q, ⟨q, hq, rfl⟩, ?_⟩
      have hscale : (k : ℝ) * (-c⁻¹) = -(n : ℝ)⁻¹ := by
        dsimp [c]
        field_simp
      apply Subtype.ext
      funext i
      change (∑ j, (k : ℝ) * (-c⁻¹ * z j)) - (n : ℝ) * ((k : ℝ) * (-c⁻¹ * z i)) = d.val i
      simp_rw [← mul_assoc, hscale]
      rw [← mul_sum, hz]
      dsimp [z]
      field_simp
      ring

end

end OlairezWrapHull

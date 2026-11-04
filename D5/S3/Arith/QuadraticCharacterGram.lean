/- GID: D5/S3/Arith/QuadraticCharacterGram
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticCharacterGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full quadratic-character correlation and its restricted row Gram identity. -/

import D5.S3.Arith.FiniteFieldQuadraticCharacterSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace D5.S3.Arith.QuadraticCharacterGram

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Correlation of two translates, including the diagonal. -/
theorem correlation (hF : ringChar F ≠ 2) (u v : F) :
    ∑ x : F, quadraticChar F (x - u) * quadraticChar F (x - v) =
      (Fintype.card F : ℤ) * (if u = v then 1 else 0) - 1 := by
  classical
  by_cases huv : u = v
  · subst v
    have hterm (x : F) : quadraticChar F (x - u) * quadraticChar F (x - u) =
        1 - (if x = u then 1 else 0) := by
      by_cases hx : x = u
      · simp [hx, quadraticChar_zero]
      · rw [if_neg hx, sub_zero, ← sq]
        exact quadraticChar_sq_one (sub_ne_zero.mpr hx)
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib]
    simp
  · have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hA : ((u - v) / 2) ^ 2 ≠ 0 :=
      pow_ne_zero _ (div_ne_zero (sub_ne_zero.mpr huv) htwo)
    let c : F := (u + v) / 2
    let e : F ≃ F :=
      { toFun := fun x => x - c
        invFun := fun x => x + c
        left_inv := by intro x; simp
        right_inv := by intro x; simp }
    have hpoly (x : F) : (x - u) * (x - v) =
        (e x) ^ 2 - ((u - v) / 2) ^ 2 := by
      dsimp [e, c]
      field_simp [htwo]
      ring
    rw [if_neg huv, mul_zero, zero_sub]
    calc
      (∑ x : F, quadraticChar F (x - u) * quadraticChar F (x - v)) =
          ∑ x : F, quadraticChar F ((e x) ^ 2 - ((u - v) / 2) ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← map_mul, hpoly]
      _ = ∑ x : F, quadraticChar F (x ^ 2 - ((u - v) / 2) ^ 2) :=
        e.sum_comp _
      _ = -1 := FiniteFieldQuadraticCharacterSum.quadraticChar_shift_square_sum hF hA

/-- An even function sums twice over any genuine choice of one element from each nonzero
negation pair. All partition hypotheses are explicit and none is a Gram assumption. -/
theorem sum_even (H : Finset F) (h0 : (0 : F) ∉ H)
    (hd : Disjoint H (H.image fun x => -x))
    (hc : ∀ x : F, x ≠ 0 → x ∈ H ∨ -x ∈ H)
    (f : F → ℤ) (hf : ∀ x, f (-x) = f x) :
    ∑ x : F, f x = f 0 + 2 * ∑ x ∈ H, f x := by
  classical
  have h0i : (0 : F) ∉ H.image (fun x => -x) := by
    rintro h
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.mp h
    have : x = 0 := neg_eq_zero.mp hx0
    exact h0 (this ▸ hx)
  have hU : insert 0 (H ∪ H.image (fun x => -x)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · apply Finset.mem_insert_of_mem
      rcases hc x hx with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-x, h, neg_neg x⟩)
  rw [← hU, Finset.sum_insert (by simpa only [Finset.mem_union, not_or] using And.intro h0 h0i),
    Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
  simp_rw [hf]
  ring

/-- The restricted row Gram identity used for both signs in the Chen-Sun argument.
The left side is an actual finite sum; the only geometric input is a half-set partition. -/
theorem restricted_gram (hF : ringChar F ≠ 2) (H : Finset F)
    (h0 : (0 : F) ∉ H) (hd : Disjoint H (H.image fun x => -x))
    (hc : ∀ x : F, x ≠ 0 → x ∈ H ∨ -x ∈ H)
    {i j : F} (hi : i ∈ H) (hj : j ∈ H) (t : ℤ) (ht : t = 1 ∨ t = -1) :
    (∑ x ∈ H,
      (quadraticChar F (i + x) + t * quadraticChar F (i - x)) *
      (quadraticChar F (j + x) + t * quadraticChar F (j - x))) =
        (Fintype.card F : ℤ) * (if i = j then 1 else 0) -
          (1 + t * quadraticChar F (-1)) -
            (1 + t) * quadraticChar F i * quadraticChar F j := by
  classical
  let ε : ℤ := quadraticChar F (-1)
  let d : ℤ := (Fintype.card F : ℤ) * (if i = j then 1 else 0)
  let f : F → ℤ := fun x =>
    (quadraticChar F (i + x) + t * quadraticChar F (i - x)) *
    (quadraticChar F (j + x) + t * quadraticChar F (j - x))
  have hij : i ≠ -j := by
    intro h
    exact Finset.disjoint_left.mp hd hi (Finset.mem_image.mpr ⟨j, hj, h.symm⟩)
  have hnij : -i ≠ j := by
    intro h
    apply hij
    exact neg_eq_iff_eq_neg.mp h
  have hε : ε ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have hneg (a x : F) : quadraticChar F (a - x) = ε * quadraticChar F (x - a) := by
    change quadraticChar F (a - x) = quadraticChar F (-1) * quadraticChar F (x - a)
    rw [← map_mul]
    congr 1
    ring
  have hplus (a x : F) : quadraticChar F (a + x) = quadraticChar F (x - -a) := by
    congr 1
    ring
  have hAA : (∑ x : F, quadraticChar F (i + x) * quadraticChar F (j + x)) = d - 1 := by
    simpa only [hplus, neg_inj] using correlation hF (-i) (-j)
  have hBB : (∑ x : F, quadraticChar F (i - x) * quadraticChar F (j - x)) = d - 1 := by
    calc
      _ = ∑ x : F, quadraticChar F (x - i) * quadraticChar F (x - j) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hneg, hneg]
        calc
          _ = ε ^ 2 * (quadraticChar F (x - i) * quadraticChar F (x - j)) := by ring
          _ = _ := by rw [hε, one_mul]
      _ = d - 1 := correlation hF i j
  have hAB : (∑ x : F, quadraticChar F (i + x) * quadraticChar F (j - x)) = -ε := by
    calc
      _ = ∑ x : F, ε * (quadraticChar F (x - -i) * quadraticChar F (x - j)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hplus, hneg]
        ring
      _ = ε * ∑ x : F, quadraticChar F (x - -i) * quadraticChar F (x - j) :=
        (Finset.mul_sum _ _ _).symm
      _ = -ε := by rw [correlation hF (-i) j, if_neg hnij]; ring
  have hBA : (∑ x : F, quadraticChar F (i - x) * quadraticChar F (j + x)) = -ε := by
    calc
      _ = ∑ x : F, ε * (quadraticChar F (x - i) * quadraticChar F (x - -j)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hneg, hplus]
        ring
      _ = ε * ∑ x : F, quadraticChar F (x - i) * quadraticChar F (x - -j) :=
        (Finset.mul_sum _ _ _).symm
      _ = -ε := by rw [correlation hF i (-j), if_neg hij]; ring
  have hfull : (∑ x : F, f x) = 2 * (d - 1) - 2 * t * ε := by
    calc
      _ = ∑ x : F,
          (quadraticChar F (i + x) * quadraticChar F (j + x) +
          t * (quadraticChar F (i + x) * quadraticChar F (j - x)) +
          t * (quadraticChar F (i - x) * quadraticChar F (j + x)) +
          quadraticChar F (i - x) * quadraticChar F (j - x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases ht with rfl | rfl <;> dsimp [f] <;> ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hAA, hAB, hBA, hBB]
        ring
  have hzero : f 0 = 2 * (1 + t) * quadraticChar F i * quadraticChar F j := by
    rcases ht with rfl | rfl <;> simp [f] <;> ring
  have heven (x : F) : f (-x) = f x := by
    rcases ht with rfl | rfl <;> dsimp [f] <;>
      simp only [sub_neg_eq_add, add_neg_eq_sub] <;> ring
  have hhalf := sum_even H h0 hd hc f heven
  rw [hfull, hzero] at hhalf
  change (∑ x ∈ H, f x) = d - (1 + t * ε) -
    (1 + t) * quadraticChar F i * quadraticChar F j
  linarith

end D5.S3.Arith.QuadraticCharacterGram

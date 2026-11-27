/- GID: D5/S3/Quantum/Semigroups/WuCubicLowerCells
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicLowerCells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar and weighted four-by-four corner replay for the lower Wu cubic certificate. -/

import D5.S3.Quantum.Semigroups.WuCubicLowerJets
import D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells
import D5.S3.Quantum.Semigroups.WuCubicUpperScalarCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicLowerCells

open _root_.Matrix Set WuCubicCornerInterpolation WuCubicLowerJets WuCubicLowerOccupation
open scoped BigOperators Matrix Topology
open WuCubicUpperPartition (Box InBox)
open WuCubicLowerCoefficients (tests)
open D5.S0.Certificates.BoxCover.RationalIntervalExpression (value)
open private Checked.expr Checked.lo Checked.hi Checked.ok Checked.sound
  from D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
open private Jet Jet.val Jet.second Jet.sound Jet.ok Jet.encloses padBox along checked_bounds
  from D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational
open private padPoint padPoint_update padPoint_mem boxLo boxHi rationalLoss cast_rationalLoss
  jet_scalar_box_floor from D5.S3.Quantum.Semigroups.WuCubicUpperScalarCells
open private allCorners allCorners_sound cornerBox get_ofFn chord_error
  positivePivots positivePivots_sound from D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells

private theorem inBox_iff (b : Box) (x : Fin 4 → ℝ) :
    InBox b x ↔ ∀ i, boxLo b i ≤ x i ∧ x i ≤ boxHi b i := Iff.rfl

private theorem corner_mem (b : Box) (ε : Fin 4 → Bool) :
    ∀ i, boxLo (cornerBox b ε) i ≤ boxCorner (boxLo b) (boxHi b) ε i ∧
      boxCorner (boxLo b) (boxHi b) ε i ≤ boxHi (cornerBox b ε) i := by
  intro i
  cases h : ε i <;> simp [boxLo, boxHi, cornerBox, boxCorner, h]

private def scalarCorner (b : Box) (ε : Fin 4 → Bool) (k : Fin 11) :=
  Jet.val (scalarJet (cornerBox b ε) 0 k)

private def scalarLoss (b : Box) (k : Fin 11) : ℚ :=
  rationalLoss b (fun i => scalarJet b i k)

private def scalarCheck (b : Box) : Bool :=
  ((List.finRange 4).all fun i => (List.finRange 11).all fun k => Jet.ok (scalarJet b i k)) &&
  let losses := Vector.ofFn (scalarLoss b)
  allCorners fun ε => (List.finRange 11).all fun k =>
    let a := scalarCorner b ε k
    Checked.ok a && decide (losses.get k < Checked.lo a)

private theorem scalarCheck_sound (b : Box) (h : scalarCheck b = true)
    {x : Fin 4 → ℝ} (hx : InBox b x) (k : Fin 11) :
    0 < tests (padPoint x 0) (pointOffsets (padPoint x)) k := by
  let J := fun i => scalarJet b i k
  let F := fun z => tests (z 0) (pointOffsets z) k
  let C := fun ε => F (padPoint (boxCorner (boxLo b) (boxHi b) ε)) - (scalarLoss b k : ℝ)
  obtain ⟨hjet, hcorners⟩ := Bool.and_eq_true_iff.mp h
  have hj (i : Fin 4) : Jet.ok (J i) = true :=
    List.all_eq_true.mp (List.all_eq_true.mp hjet i (List.mem_finRange i)) k (List.mem_finRange k)
  have hcorner (ε : Fin 4 → Bool) : 0 < C ε := by
    have he := List.all_eq_true.mp (allCorners_sound hcorners ε) k (List.mem_finRange k)
    simp only [get_ofFn] at he
    obtain ⟨ha, hl⟩ := Bool.and_eq_true_iff.mp he
    have hlo := (checked_bounds (scalarCorner b ε k) (padPoint_mem (corner_mem b ε)) ha).1
    unfold scalarCorner at hlo
    rw [scalarJet_value] at hlo
    exact sub_pos.mpr ((Rat.cast_lt.mpr (of_decide_eq_true hl)).trans_le hlo)
  obtain ⟨ε₀, _, hmin⟩ := Finset.exists_min_image Finset.univ C Finset.univ_nonempty
  apply (hcorner ε₀).trans_le
  refine jet_scalar_box_floor b J F (fun i z => scalarJet_value b i z k) hj (C ε₀) ?_ x
    ((inBox_iff b x).mp hx)
  intro ε
  have hm := hmin ε (Finset.mem_univ ε)
  have hl := cast_rationalLoss b J
  change (scalarLoss b k : ℝ) = _ at hl
  rw [← hl]
  exact le_sub_iff_add_le.mp hm

private def quad (a : Fin 10 → ℝ) (u v w s : ℝ) : ℝ :=
  a 0 * u ^ 2 + a 4 * v ^ 2 + a 7 * w ^ 2 + a 9 * s ^ 2 +
    2 * a 1 * u * v + 2 * a 2 * u * w + 2 * a 3 * u * s +
    2 * a 5 * v * w + 2 * a 6 * v * s + 2 * a 8 * w * s

-- The weights of the four coordinates are 1, 1/64, 1/2 and 1.
private def diagonalErrors {K : Type*} [Field K] (e : Fin 10 → K) (k : Fin 10) : K :=
  if k = 0 then e 0 + e 1 / 64 + e 2 / 2 + e 3
  else if k = 4 then 64 * e 1 + e 4 + 32 * e 5 + 64 * e 6
  else if k = 7 then 2 * e 2 + e 5 / 32 + e 7 + 2 * e 8
  else if k = 9 then e 3 + e 6 / 64 + e 8 / 2 + e 9
  else 0

private noncomputable def rowLoss (e : Fin 10 → ℝ) (u v w s : ℝ) : ℝ :=
  diagonalErrors e 0 * u ^ 2 + diagonalErrors e 4 * v ^ 2 +
    diagonalErrors e 7 * w ^ 2 + diagonalErrors e 9 * s ^ 2

private theorem cross_weighted {d e : ℝ} (h : |d| ≤ e) (u v w : ℝ) (hw : 0 < w) :
    -(e * (w * u ^ 2 + w⁻¹ * v ^ 2)) ≤ 2 * d * u * v := by
  have ha : 0 ≤ w * (u - v / w) ^ 2 := mul_nonneg hw.le (sq_nonneg _)
  have hb : 0 ≤ w * (u + v / w) ^ 2 := mul_nonneg hw.le (sq_nonneg _)
  have he := (abs_nonneg _).trans h
  have hi : w * (u - v / w) ^ 2 = w * u ^ 2 + w⁻¹ * v ^ 2 - 2 * u * v := by
    field_simp [hw.ne'] <;> ring
  have hj : w * (u + v / w) ^ 2 = w * u ^ 2 + w⁻¹ * v ^ 2 + 2 * u * v := by
    field_simp [hw.ne'] <;> ring
  rw [hi] at ha
  rw [hj] at hb
  by_cases huv : 0 ≤ u * v
  · have hl := mul_le_mul_of_nonneg_right (abs_le.mp h).1 huv
    have hk := mul_nonneg he ha
    linarith only [show -e * (u * v) ≤ d * (u * v) from hl,
      show 0 ≤ e * (w * u ^ 2 + w⁻¹ * v ^ 2 - 2 * u * v) from hk]
  · have hu := mul_le_mul_of_nonpos_right (abs_le.mp h).2 (le_of_not_ge huv)
    have hk := mul_nonneg he hb
    linarith only [show e * (u * v) ≤ d * (u * v) from hu,
      show 0 ≤ e * (w * u ^ 2 + w⁻¹ * v ^ 2 + 2 * u * v) from hk]

private theorem perturb (a b e : Fin 10 → ℝ) (h : ∀ k, |a k - b k| ≤ e k) (u v w s : ℝ) :
    quad b u v w s - rowLoss e u v w s ≤ quad a u v w s := by
  have diag (k : Fin 10) (z : ℝ) :
      -e k * z ^ 2 ≤ (a k - b k) * z ^ 2 :=
    mul_le_mul_of_nonneg_right (abs_le.mp (h k)).1 (sq_nonneg _)
  have h01 := cross_weighted (h 1) u v (1 / 64) (by norm_num)
  have h02 := cross_weighted (h 2) u w (1 / 2) (by norm_num)
  have h03 := cross_weighted (h 3) u s 1 (by norm_num)
  have h12 := cross_weighted (h 5) v w 32 (by norm_num)
  have h13 := cross_weighted (h 6) v s 64 (by norm_num)
  have h23 := cross_weighted (h 8) w s 2 (by norm_num)
  norm_num [quad, rowLoss, diagonalErrors] at h01 h02 h03 h12 h13 h23 ⊢
  linarith only [diag 0 u, diag 4 v, diag 7 w, diag 9 s, h01, h02, h03, h12, h13, h23]

private def complement {K : Type*} [Field K] (a : Fin 10 → K) : Fin 6 → K :=
  ![a 4 - a 1 ^ 2 / a 0, a 5 - a 1 * a 2 / a 0, a 6 - a 1 * a 3 / a 0,
    a 7 - a 2 ^ 2 / a 0, a 8 - a 2 * a 3 / a 0, a 9 - a 3 ^ 2 / a 0]

private def pivots (a : Fin 10 → ℚ) : Bool :=
  decide (0 < a 0) && positivePivots (complement a)

private theorem pivots_sound {a : Fin 10 → ℚ} (h : pivots a = true) (u v w s : ℝ) :
    0 ≤ quad (fun k => (a k : ℝ)) u v w s := by
  obtain ⟨h₀, hc⟩ := Bool.and_eq_true_iff.mp h
  let A : Fin 10 → ℝ := fun k => a k
  have ha : 0 < A 0 := Rat.cast_pos.mpr (of_decide_eq_true h₀)
  have hcast : (fun k => ((complement (K := ℚ) a) k : ℝ)) = complement A := by
    funext k
    fin_cases k <;> simp [complement, A]
  have hq : 0 ≤ quad3Entries (complement A) v w s := by
    by_cases hz : (v, w, s) = (0, 0, 0)
    · simp only [Prod.mk.injEq] at hz
      simp [quad3Entries, quad3, hz.1, hz.2.1, hz.2.2]
    · rw [← hcast]
      exact (positivePivots_sound hc v w s hz).le
  have heq : quad A u v w s =
      A 0 * (u + (A 1 * v + A 2 * w + A 3 * s) / A 0) ^ 2 +
      quad3Entries (complement A) v w s := by
    simp [quad, quad3Entries, quad3, complement]
    field_simp [ha.ne'] <;> ring
  change 0 ≤ quad A u v w s
  rw [heq]
  exact add_nonneg (mul_nonneg ha.le (sq_nonneg _)) hq

private theorem correction_spec (a e : Fin 10 → ℚ) (u v w s : ℝ) :
    quad (fun k => ((a k - diagonalErrors e k : ℚ) : ℝ)) u v w s =
      quad (fun k => (a k : ℝ)) u v w s - rowLoss (fun k => (e k : ℝ)) u v w s := by
  norm_num [quad, rowLoss, diagonalErrors, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div]
  ring

private theorem rowLoss_sum (e : Fin 4 → Fin 10 → ℝ) (u v w s : ℝ) :
    (∑ i, rowLoss (e i) u v w s) = rowLoss (fun k => ∑ i, e i k) u v w s := by
  norm_num [rowLoss, diagonalErrors, Fin.sum_univ_four]
  ring

private theorem rowLoss_add (e f : Fin 10 → ℝ) (u v w s : ℝ) :
    rowLoss (fun k => e k + f k) u v w s = rowLoss e u v w s + rowLoss f u v w s := by
  norm_num [rowLoss, diagonalErrors]
  ring

private def curvature (b : Box) (i : Fin 4) (k : Fin 10) : ℚ :=
  let a := Jet.second (matrixJet b i k)
  max 0 (max (-(Checked.lo a)) (Checked.hi a))

private def axisError (b : Box) (i : Fin 4) (k : Fin 10) : ℚ :=
  curvature b i k * ((b i).2 - (b i).1) ^ 2 / 8

private def totalError (b : Box) (k : Fin 10) : ℚ :=
  ∑ i : Fin 4, axisError b i k

private noncomputable def entries (x : Fin 4 → ℝ) (k : Fin 10) : ℝ :=
  matrixEntry (padPoint x) k

private theorem entry_derivatives (b : Box) (i : Fin 4) (k : Fin 10) (y : Fin 4 → ℝ)
    (hy : ∀ j, boxLo b j ≤ y j ∧ y j ≤ boxHi b j) (t : ℝ)
    (ht : boxLo b i ≤ t ∧ t ≤ boxHi b i) (h : Jet.ok (matrixJet b i k) = true) :
    let f := fun s => entries (Function.update y i s) k
    DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ (deriv f) t ∧
      |deriv (deriv f) t| ≤ (curvature b i k : ℝ) := by
  let x := Function.update y i t
  let a := matrixJet b i k
  have hx : ∀ j, boxLo b j ≤ x j ∧ x j ≤ boxHi b j := by
    intro j
    by_cases hij : j = i
    · subst j
      simpa [x] using ht
    · simpa [x, Function.update_of_ne hij] using hy j
  have hz := padPoint_mem hx
  have hval : Checked.ok (Jet.val a) = true := (Bool.and_eq_true_iff.mp h).1
  obtain ⟨hf, hdf⟩ := Jet.sound a (padPoint x) hz hval
  have hb := (Jet.encloses a hz h).2.2
  have halong : along (Jet.val a) i.castSucc (padPoint x) =
      fun s => entries (Function.update y i s) k := by
    funext s
    change value (Function.update (padPoint x) i.castSucc s) (Checked.expr (Jet.val a)) = _
    rw [padPoint_update y i t, Function.update_idem, ← padPoint_update y i s]
    exact matrixJet_value (b := b) (i := i) (padPoint (Function.update y i s)) k
  have hcoord : padPoint x i.castSucc = t := by
    simp only [padPoint, Fin.lastCases_castSucc, x, Function.update_self]
  have hfAt := hf.self_of_nhds
  rw [halong, hcoord] at hfAt hdf hb
  refine ⟨hfAt.differentiableAt, hdf.differentiableAt, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hn : -curvature b i k ≤ Checked.lo (Jet.second a) := by
      have hm : -Checked.lo (Jet.second a) ≤ curvature b i k :=
        (le_max_left _ _).trans (le_max_right _ _)
      simpa only [neg_neg] using neg_le_neg hm
    have hn' := (Rat.cast_le (K := ℝ)).mpr hn
    rw [Rat.cast_neg] at hn'
    exact hn'.trans hb.1
  · exact hb.2.trans (Rat.cast_le.mpr ((le_max_right _ _).trans (le_max_right _ _)))

private theorem axis_sound (b : Box) (y : Fin 4 → ℝ)
    (hy : ∀ j, boxLo b j ≤ y j ∧ y j ≤ boxHi b j) (i : Fin 4)
    (h : ∀ k, Jet.ok (matrixJet b i k) = true) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ k,
      |entries y k - ((1 - t) * entries (Function.update y i (boxLo b i)) k +
        t * entries (Function.update y i (boxHi b i)) k)| ≤ (axisError b i k : ℝ) := by
  let lo := boxLo b i
  let hi := boxHi b i
  have hx : lo ≤ y i ∧ y i ≤ hi := hy i
  rcases lt_or_eq_of_le (hx.1.trans hx.2) with hw | hw
  · let t := (y i - lo) / (hi - lo)
    refine ⟨t, div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hw.le), ?_, ?_⟩
    · exact (div_le_one (sub_pos.mpr hw)).mpr (sub_le_sub_right hx.2 _)
    · intro k
      have hC : 0 ≤ (curvature b i k : ℝ) := by exact_mod_cast le_max_left 0 _
      have he := chord_error hw hx hC
        (fun s hs => entry_derivatives b i k y hy s hs (h k))
      simpa only [Function.update_eq_self, axisError, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_sub, Rat.cast_ofNat, boxLo, boxHi, lo, hi, t] using he
  · have he : lo = y i := le_antisymm hx.1 (hx.2.trans_eq hw.symm)
    have he' : hi = y i := hw.symm.trans he
    refine ⟨0, le_rfl, zero_le_one, fun k => ?_⟩
    have hC : 0 ≤ curvature b i k := le_max_left 0 _
    have herror : (0 : ℝ) ≤ (axisError b i k : ℝ) := by
      exact_mod_cast (show 0 ≤ axisError b i k by unfold axisError; positivity)
    change |entries y k - ((1 - 0) * entries (Function.update y i lo) k +
      0 * entries (Function.update y i hi) k)| ≤ _
    simpa only [he, he', Function.update_eq_self, sub_zero, one_mul, zero_mul, add_zero,
      sub_self, abs_zero] using herror

private def matrixCorner (b : Box) (ε : Fin 4 → Bool) (k : Fin 10) :=
  Jet.val (matrixJet (cornerBox b ε) 0 k)

private def matrixCornerCheck (b : Box) (ε : Fin 4 → Bool) (errors : Vector ℚ 10) : Bool :=
  (List.finRange 10).all (fun k => Checked.ok (matrixCorner b ε k)) &&
    let bounds := Vector.ofFn fun k => (Checked.lo (matrixCorner b ε k), Checked.hi (matrixCorner b ε k))
    let e := fun k => (bounds.get k).2 - (bounds.get k).1 + errors.get k
    pivots (fun k => (bounds.get k).1 - diagonalErrors e k)

private def matrixCheck (b : Box) : Bool :=
  ((List.finRange 4).all fun i => (List.finRange 10).all fun k => Jet.ok (matrixJet b i k)) &&
    let errors := Vector.ofFn (totalError b)
    allCorners (fun ε => matrixCornerCheck b ε errors)

private theorem matrixCornerCheck_sound (b : Box) (ε : Fin 4 → Bool)
    (h : matrixCornerCheck b ε (Vector.ofFn (totalError b)) = true) (u v w s : ℝ) :
    rowLoss (fun k => (totalError b k : ℝ)) u v w s ≤
      quad (entries (boxCorner (boxLo b) (boxHi b) ε)) u v w s := by
  let c := boxCorner (boxLo b) (boxHi b) ε
  let lo (k : Fin 10) := Checked.lo (matrixCorner b ε k)
  let err (k : Fin 10) := Checked.hi (matrixCorner b ε k) - lo k
  obtain ⟨hok, hpiv⟩ := Bool.and_eq_true_iff.mp h
  have hb (k : Fin 10) : |entries c k - (lo k : ℝ)| ≤ (err k : ℝ) := by
    have H := checked_bounds (matrixCorner b ε k) (padPoint_mem (corner_mem b ε))
      (List.all_eq_true.mp hok k (List.mem_finRange k))
    unfold matrixCorner at H
    rw [matrixJet_value] at H
    change (lo k : ℝ) ≤ entries c k ∧ entries c k ≤ _ at H
    rw [abs_of_nonneg (sub_nonneg.mpr H.1)]
    simp only [err, Rat.cast_sub]
    exact sub_le_sub_right H.2 _
  simp only [get_ofFn] at hpiv
  have hp := pivots_sound hpiv u v w s
  change 0 ≤ quad (fun k => ((lo k - diagonalErrors (fun l => err l + totalError b l) k : ℚ) : ℝ))
    u v w s at hp
  rw [correction_spec] at hp
  simp only [Rat.cast_add, rowLoss_add] at hp
  have hperturb := perturb (entries c) (fun k => (lo k : ℝ)) (fun k => (err k : ℝ)) hb u v w s
  change _ ≤ quad (entries c) u v w s
  linarith only [hp, hperturb]

private theorem quad_nonneg (b : Box) (h : matrixCheck b = true) {x : Fin 4 → ℝ}
    (hx : InBox b x) (u v w s : ℝ) : 0 ≤ quad (entries x) u v w s := by
  let f := fun y => quad (entries y) u v w s
  let loss := fun i => rowLoss (fun k => (axisError b i k : ℝ)) u v w s
  obtain ⟨hjet, hcorner⟩ := Bool.and_eq_true_iff.mp h
  refine finite_box_floor f (boxLo b) (boxHi b) loss x 0 ((inBox_iff b x).mp hx) ?_ ?_
  · intro ε
    rw [zero_add]
    simp only [loss, rowLoss_sum, ← Rat.cast_sum]
    exact matrixCornerCheck_sound b ε (allCorners_sound hcorner ε) u v w s
  · intro y hy i
    obtain ⟨t, ht0, ht1, hentry⟩ := axis_sound b y hy i (fun k =>
      List.all_eq_true.mp (List.all_eq_true.mp hjet i (List.mem_finRange i)) k (List.mem_finRange k))
    let qlo := f (Function.update y i (boxLo b i))
    let qhi := f (Function.update y i (boxHi b i))
    let m := fun k => (1-t) * entries (Function.update y i (boxLo b i)) k +
      t * entries (Function.update y i (boxHi b i)) k
    have he : quad m u v w s = (1-t) * qlo + t * qhi := by
      simp only [quad, m, qlo, qhi, f]
      ring
    have hq := perturb (entries y) m (fun k => (axisError b i k : ℝ)) hentry u v w s
    rw [he] at hq
    have hlow := mul_le_mul_of_nonneg_left (min_le_left qlo qhi) (sub_nonneg.mpr ht1)
    have hhigh := mul_le_mul_of_nonneg_left (min_le_right qlo qhi) ht0
    calc
      min qlo qhi - loss i = (1-t) * min qlo qhi + t * min qlo qhi - loss i := by ring
      _ ≤ (1-t) * qlo + t * qhi - loss i := sub_le_sub_right (add_le_add hlow hhigh) _
      _ ≤ f y := hq

private theorem matrixCheck_sound (b : Box) (h : matrixCheck b = true)
    {x : Fin 4 → ℝ} (hx : InBox b x) :
    (lowerMatrix (padPoint x 0) (pointOffsets (padPoint x))).PosSemidef := by
  let M := lowerMatrix (padPoint x 0) (pointOffsets (padPoint x))
  have hs : M.IsSymm := lowerMatrix_isSymm ..
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hs) ?_
  intro v
  have hquad := quad_nonneg b h hx (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 0))
  have hsym (i j : Fin 3 ⊕ Fin 1) : M j i = M i j := hs.apply i j
  change 0 ≤ dotProduct (star v) (Matrix.mulVec M v)
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, Pi.star_apply, star_trivial]
  have hM : lowerMatrix (padPoint x 0) (pointOffsets (padPoint x)) = M := rfl
  norm_num [quad, entries, matrixEntry, entryIndices, blockIndex, hM] at hquad
  rw [hsym (.inl 0) (.inl 1), hsym (.inl 0) (.inl 2), hsym (.inl 0) (.inr 0),
      hsym (.inl 1) (.inl 2), hsym (.inl 1) (.inr 0), hsym (.inl 2) (.inr 0)]
  linarith only [hquad]

def check (b : Box) : Bool := scalarCheck b && matrixCheck b

theorem check_sound {b : Box} (h : check b = true) {x : Fin 4 → ℝ} (hx : InBox b x) :
    (∀ k, 0 < tests (x 0) (pointOffsets (padPoint x)) k) ∧
      (lowerMatrix (x 0) (pointOffsets (padPoint x))).PosSemidef := by
  obtain ⟨hs, hm⟩ := Bool.and_eq_true_iff.mp h
  have hzero : padPoint x 0 = x 0 := rfl
  rw [← hzero]
  exact ⟨scalarCheck_sound b hs hx, matrixCheck_sound b hm hx⟩

end D5.S3.Quantum.Semigroups.WuCubicLowerCells

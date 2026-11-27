import D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation
import D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational
import Batteries.Tactic.OpenPrivate

/-! Corner certificates for both signed matrices on a closed upper focal cell. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells

open _root_.Matrix Set WuCubicCornerInterpolation
open scoped BigOperators Matrix Topology
open WuCubicGibbsCheckedCoverCompact (InBox)
open WuCubicUpperCornerJet (replayFocalY signed_matrix_replay_semantics)
open D5.S0.Certificates.BoxCover.RationalIntervalExpression (value)

open private Checked.expr Checked.lo Checked.hi Checked.ok
  from D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
open private along Between checked_bounds Jet.val Jet.second Jet.sound Jet.ok Jet.encloses
  padBox upperEntryIndices jetSignedMatrixEntry
  from D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational

abbrev Box := Fin 4 → ℚ × ℚ

/-- Parameters of the upper focal test, in order
`(r, y₀, y₁, blend)`. -/
def InCell (b : Box) (x : Fin 4 → ℝ) : Prop :=
  ∀ i, ((b i).1 : ℝ) ≤ x i ∧ x i ≤ ((b i).2 : ℝ)

private def pad (x : Fin 4 → ℝ) : Fin 5 → ℝ := Fin.lastCases 0 x

/-- The signed focal matrix at four real coordinates. -/
noncomputable def focalMatrix (sign : ℚ) (x : Fin 4 → ℝ) : WuCubicHellingerMatrix.Mat3 :=
  WuCubicHellingerMatrix.signedMatrix (sign : ℝ) (x 0) (replayFocalY (pad x))

private noncomputable def entries (sign : ℚ) (x : Fin 4 → ℝ) (k : Fin 6) : ℝ :=
  focalMatrix sign x (upperEntryIndices k).1 (upperEntryIndices k).2

private theorem pad_mem {b : Box} {x : Fin 4 → ℝ} (hx : InCell b x) :
    InBox (padBox b) (pad x) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [pad, padBox, Fin.lastCases_last, Rat.cast_zero, le_refl, and_self]
  · simpa [pad, padBox] using hx i

private theorem pad_update (x : Fin 4 → ℝ) (i : Fin 4) (t : ℝ) :
    Function.update (pad x) i.castSucc t = pad (Function.update x i t) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [pad, Fin.lastCases_last, Function.update_of_ne (Fin.castSucc_ne_last i).symm]
  · by_cases h : k = i
    · subst k
      simp [pad]
    · have h' : k.castSucc ≠ i.castSucc := fun he => h (Fin.castSucc_injective _ he)
      simp [pad, Function.update, h, h']

private theorem along_eq (b : Box) (sign : ℚ) (i : Fin 4) (k : Fin 6) (x : Fin 4 → ℝ) :
    along (Jet.val (jetSignedMatrixEntry b i sign k)) i.castSucc (pad x) =
      fun t => entries sign (Function.update x i t) k := by
  funext t
  rw [along, pad_update, signed_matrix_replay_semantics]
  rfl

private def curvature (b : Box) (sign : ℚ) (i : Fin 4) (k : Fin 6) : ℚ :=
  let a := Jet.second (jetSignedMatrixEntry b i sign k)
  max 0 (max (-(Checked.lo a)) (Checked.hi a))

private def axisError (b : Box) (sign : ℚ) (i : Fin 4) (k : Fin 6) : ℚ :=
  curvature b sign i k * ((b i).2 - (b i).1) ^ 2 / 8

private def totalError (b : Box) (sign : ℚ) (k : Fin 6) : ℚ :=
  ∑ i : Fin 4, axisError b sign i k

private theorem entry_derivatives (b : Box) (sign : ℚ) (i : Fin 4) (k : Fin 6)
    (y : Fin 4 → ℝ) (hy : InCell b y) (t : ℝ)
    (ht : ((b i).1 : ℝ) ≤ t ∧ t ≤ ((b i).2 : ℝ))
    (h : Jet.ok (jetSignedMatrixEntry b i sign k) = true) :
    let f := fun s => entries sign (Function.update y i s) k
    DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ (deriv f) t ∧
      |deriv (deriv f) t| ≤ (curvature b sign i k : ℝ) := by
  let x := Function.update y i t
  let a := jetSignedMatrixEntry b i sign k
  have hx : InCell b x := by
    intro j
    by_cases hij : j = i
    · subst j
      simpa [x] using ht
    · simpa [x, Function.update_of_ne hij] using hy j
  have hval : Checked.ok (Jet.val a) = true := (Bool.and_eq_true_iff.mp h).1
  obtain ⟨hf, hdf⟩ := Jet.sound a (pad x) (pad_mem hx) hval
  have hb := (Jet.encloses a (pad_mem hx) h).2.2
  have hfun : along (Jet.val a) i.castSucc (pad x) =
      fun s => entries sign (Function.update y i s) k := by
    rw [along_eq]
    simp only [x, Function.update_idem]
  have hp : pad x i.castSucc = t := by simp [pad, x]
  rw [hfun, hp] at hf hdf hb
  exact ⟨hf.self_of_nhds.differentiableAt, hdf.differentiableAt, abs_le.mpr
    ⟨by
      refine (neg_le.mpr ?_).trans hb.1
      exact_mod_cast (le_max_left (-(Checked.lo (Jet.second a))) (Checked.hi (Jet.second a))).trans
        (le_max_right 0 _),
     by
      refine hb.2.trans ?_
      exact_mod_cast (le_max_right (-(Checked.lo (Jet.second a))) (Checked.hi (Jet.second a))).trans
        (le_max_right 0 _)⟩⟩

private theorem chord_error {f : ℝ → ℝ} {lo hi x C : ℝ} (hw : lo < hi)
    (hx : lo ≤ x ∧ x ≤ hi) (hC : 0 ≤ C)
    (hd : ∀ t ∈ Icc lo hi, DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ (deriv f) t ∧
      |deriv (deriv f) t| ≤ C) :
    |f x - ((1 - (x - lo) / (hi - lo)) * f lo + ((x - lo) / (hi - lo)) * f hi)| ≤
      C * (hi - lo) ^ 2 / 8 := by
  have hf : ContinuousOn f (Icc lo hi) := fun t ht => (hd t ht).1.continuousAt.continuousWithinAt
  have hf' : DifferentiableOn ℝ f (Ioo lo hi) :=
    fun t ht => (hd t (Ioo_subset_Icc_self ht)).1.differentiableWithinAt
  have hf'' : DifferentiableOn ℝ (deriv f) (Ioo lo hi) :=
    fun t ht => (hd t (Ioo_subset_Icc_self ht)).2.1.differentiableWithinAt
  have hupper (t : ℝ) (ht : t ∈ Ioo lo hi) : deriv^[2] f t ≤ C :=
    (abs_le.mp (hd t (Ioo_subset_Icc_self ht)).2.2).2
  have hneg : deriv (fun s => -f s) = fun s => -deriv f s := deriv.neg'
  have hlower (t : ℝ) (ht : t ∈ Ioo lo hi) : deriv^[2] (fun s => -f s) t ≤ C := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, hneg]
    rw [show deriv (fun s => -deriv f s) t = -deriv (deriv f) t from deriv.neg]
    exact neg_le.mpr (abs_le.mp (hd t (Ioo_subset_Icc_self ht)).2.2).1
  have hleft := corner_interpolation C lo hi x hw hf hf' hf'' hupper hx.1 hx.2
  have hright := corner_interpolation (f := fun s => -f s) C lo hi x hw hf.neg hf'.neg
    (hneg.symm ▸ hf''.neg) hlower hx.1 hx.2
  have hweight : (hi - x) / (hi - lo) = 1 - (x - lo) / (hi - lo) := by
    field_simp [sub_ne_zero.mpr hw.ne']
    ring
  rw [hweight] at hleft hright
  have hprod : (x - lo) * (hi - x) ≤ (hi - lo) ^ 2 / 4 := by
    nlinarith only [sq_nonneg (2 * x - lo - hi)]
  have herr := mul_le_mul_of_nonneg_left hprod (show 0 ≤ C / 2 by positivity)
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith only [hleft, hright, herr]

private theorem axis_sound (b : Box) (sign : ℚ) (y : Fin 4 → ℝ) (hy : InCell b y)
    (i : Fin 4) (h : ∀ k, Jet.ok (jetSignedMatrixEntry b i sign k) = true) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ k,
      |entries sign y k -
        ((1 - t) * entries sign (Function.update y i (b i).1) k +
          t * entries sign (Function.update y i (b i).2) k)| ≤ (axisError b sign i k : ℝ) := by
  let lo : ℝ := (b i).1
  let hi : ℝ := (b i).2
  have hx : lo ≤ y i ∧ y i ≤ hi := hy i
  rcases lt_or_eq_of_le (hx.1.trans hx.2) with hw | hw
  · let t := (y i - lo) / (hi - lo)
    refine ⟨t, div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hw.le), ?_, ?_⟩
    · exact (div_le_one (sub_pos.mpr hw)).mpr (sub_le_sub_right hx.2 _)
    · intro k
      have hC : 0 ≤ (curvature b sign i k : ℝ) := by exact_mod_cast le_max_left 0 _
      have he := chord_error hw hx hC
        (fun s hs => entry_derivatives b sign i k y hy s hs (h k))
      simpa only [Function.update_eq_self, axisError, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_sub, Rat.cast_ofNat, lo, hi, t] using he
  · have hself : Function.update y i lo = y := by
      rw [show lo = y i from le_antisymm hx.1 (hx.2.trans_eq hw.symm), Function.update_eq_self]
    refine ⟨0, le_rfl, zero_le_one, fun k => ?_⟩
    have he : (0 : ℝ) ≤ (axisError b sign i k : ℝ) := by
      have hC : 0 ≤ curvature b sign i k := le_max_left 0 _
      exact_mod_cast (show 0 ≤ axisError b sign i k by unfold axisError; positivity)
    simpa only [sub_zero, one_mul, zero_mul, add_zero, ← show lo = ((b i).1 : ℝ) from rfl,
      hself, sub_self, abs_zero] using he

private theorem quadratic_eq (sign : ℚ) (x : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (focalMatrix sign x *ᵥ v) = quad3Entries (entries sign x) (v 0) (v 1) (v 2) := by
  let M := focalMatrix sign x
  have hs : M.IsSymm := WuCubicHellingerMatrix.signedMatrix_isSymm ..
  have h10 : M 1 0 = M 0 1 := hs.apply 0 1
  have h20 : M 2 0 = M 0 2 := hs.apply 0 2
  have h21 : M 2 1 = M 1 2 := hs.apply 1 2
  change star v ⬝ᵥ (M *ᵥ v) = quad3 (M 0 0) (M 0 1) (M 0 2) (M 1 1) (M 1 2) (M 2 2) _ _ _
  simp only [dotProduct, mulVec, Fin.sum_univ_three, Pi.star_apply, star_trivial,
    h10, h20, h21, quad3]
  ring

/-- The analytic part of the cell proof. The corner margin is the sum of
the row corrections from the four pure second-derivative bounds. -/
private theorem posDef_of_corners (b : Box) (sign : ℚ) {x : Fin 4 → ℝ} (hx : InCell b x)
    (hjet : ∀ i k, Jet.ok (jetSignedMatrixEntry b i sign k) = true)
    (hcorner : ∀ ε (u v w : ℝ), (u, v, w) ≠ (0, 0, 0) →
      0 < quad3Entries (entries sign (boxCorner (fun i => (b i).1) (fun i => (b i).2) ε)) u v w -
        quad3RowError (fun k => (totalError b sign k : ℝ)) u v w) :
    (focalMatrix sign x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (WuCubicHellingerMatrix.signedMatrix_isSymm ..)) ?_
  intro v hv
  rw [quadratic_eq]
  refine quad3_pos_on_fin4_box (entries sign) (fun i => (b i).1) (fun i => (b i).2) x
    (fun i k => axisError b sign i k) hx ?_ (fun y hy i => axis_sound b sign y hy i (hjet i))
    (v 0) (v 1) (v 2) ?_
  · intro ε u v w huv
    simpa only [totalError, Rat.cast_sum] using hcorner ε u v w huv
  · intro hz
    simp only [Prod.mk.injEq] at hz
    apply hv
    funext i
    fin_cases i
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2


/-- The Schur complement after the first pivot of a symmetric 3×3
matrix, with entries in upper-triangular order. -/
private def secondPivot {K : Type*} [Field K] (a : Fin 6 → K) : K :=
  a 3 - a 1 ^ 2 / a 0

private def schurOffDiag {K : Type*} [Field K] (a : Fin 6 → K) : K :=
  a 4 - a 1 * a 2 / a 0

private def thirdPivot {K : Type*} [Field K] (a : Fin 6 → K) : K :=
  a 5 - a 2 ^ 2 / a 0 - schurOffDiag a ^ 2 / secondPivot a

private def positivePivots (a : Fin 6 → ℚ) : Bool :=
  decide (0 < a 0) && (decide (0 < secondPivot a) && decide (0 < thirdPivot a))

private theorem positivePivots_sound {a : Fin 6 → ℚ} (h : positivePivots a = true)
    (u v w : ℝ) (hn : (u, v, w) ≠ (0, 0, 0)) :
    0 < quad3Entries (fun k => (a k : ℝ)) u v w := by
  obtain ⟨h₀, h'⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h'
  let A : Fin 6 → ℝ := fun k => a k
  have ha : 0 < A 0 := by
    dsimp only [A]
    exact_mod_cast (of_decide_eq_true h₀ : 0 < a 0)
  have hd : 0 < secondPivot A := by
    have hq : 0 < secondPivot a := of_decide_eq_true h₁
    unfold secondPivot at hq ⊢
    dsimp only [A]
    exact_mod_cast hq
  have hf : 0 < thirdPivot A := by
    have hq : 0 < thirdPivot a := of_decide_eq_true h₂
    unfold thirdPivot schurOffDiag secondPivot at hq ⊢
    dsimp only [A]
    exact_mod_cast hq
  let U := u + (A 1 * v + A 2 * w) / A 0
  let V := v + schurOffDiag A * w / secondPivot A
  have hsq : quad3Entries A u v w =
      A 0 * U ^ 2 + secondPivot A * V ^ 2 + thirdPivot A * w ^ 2 := by
    have hfirst : quad3Entries A u v w = A 0 * U ^ 2 +
        (secondPivot A * v ^ 2 + 2 * schurOffDiag A * v * w +
          (A 5 - A 2 ^ 2 / A 0) * w ^ 2) := by
      simp only [quad3Entries, quad3, U, secondPivot, schurOffDiag]
      field_simp [ha.ne']
      ring
    rw [hfirst, add_assoc (A 0 * U ^ 2) (secondPivot A * V ^ 2)]
    apply congrArg (fun t => A 0 * U ^ 2 + t)
    simp only [V, thirdPivot]
    field_simp [hd.ne']
    ring
  change 0 < quad3Entries A u v w
  rw [hsq]
  by_cases hw : w = 0
  · by_cases hv : v = 0
    · have hu : u ≠ 0 := fun he => hn (by simp [he, hv, hw])
      simp [U, V, hv, hw, mul_pos ha (sq_pos_of_ne_zero hu)]
    · have hV : V ≠ 0 := by simpa [V, hw] using hv
      have hpos := mul_pos hd (sq_pos_of_ne_zero hV)
      have hnon := mul_nonneg ha.le (sq_nonneg U)
      simpa [hw] using add_pos_of_nonneg_of_pos hnon hpos
  · exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg ha.le (sq_nonneg U)) (mul_nonneg hd.le (sq_nonneg V)))
      (mul_pos hf (sq_pos_of_ne_zero hw))

private def cornerBox (b : Box) (ε : Fin 4 → Bool) : Box := fun i =>
  let q := if ε i then (b i).2 else (b i).1
  (q, q)

private def cornerVal (b : Box) (sign : ℚ) (ε : Fin 4 → Bool) (k : Fin 6) :=
  Jet.val (jetSignedMatrixEntry (cornerBox b ε) 0 sign k)

private def cornerLo (b : Box) (sign : ℚ) (ε : Fin 4 → Bool) (k : Fin 6) : ℚ :=
  Checked.lo (cornerVal b sign ε k)

private def cornerError (b : Box) (sign : ℚ) (ε : Fin 4 → Bool) (k : Fin 6) : ℚ :=
  Checked.hi (cornerVal b sign ε k) - cornerLo b sign ε k

private def subtractRowErrors (a e : Fin 6 → ℚ) (k : Fin 6) : ℚ :=
  a k - if k = 0 then e 0 + e 1 + e 2 else if k = 3 then e 1 + e 3 + e 4
    else if k = 5 then e 2 + e 4 + e 5 else 0

private theorem subtractRowErrors_spec (a e : Fin 6 → ℚ) (u v w : ℝ) :
    quad3Entries (fun k => (subtractRowErrors a e k : ℝ)) u v w =
      quad3Entries (fun k => (a k : ℝ)) u v w -
        quad3RowError (fun k => (e k : ℝ)) u v w := by
  norm_num [quad3Entries, quad3, quad3RowError, subtractRowErrors, Rat.cast_sub, Rat.cast_add]
  ring

private theorem get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  exact Vector.getElem_ofFn i.isLt

private def cornerCheck (b : Box) (sign : ℚ) (ε : Fin 4 → Bool)
    (errors : Vector ℚ 6) : Bool :=
  (List.finRange 6).all (fun k => Checked.ok (cornerVal b sign ε k)) &&
    let bounds := Vector.ofFn fun k => (cornerLo b sign ε k, cornerError b sign ε k)
    positivePivots (subtractRowErrors (fun k => (bounds.get k).1)
      (fun k => (bounds.get k).2 + errors.get k))

open private quad3_entries_sub_row_error_le from D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation

private theorem cornerCheck_sound (b : Box) (sign : ℚ) (ε : Fin 4 → Bool)
    (h : cornerCheck b sign ε (Vector.ofFn (totalError b sign)) = true)
    (u v w : ℝ) (hn : (u, v, w) ≠ (0, 0, 0)) :
    0 < quad3Entries (entries sign (boxCorner (fun i => (b i).1) (fun i => (b i).2) ε)) u v w -
      quad3RowError (fun k => (totalError b sign k : ℝ)) u v w := by
  let x := boxCorner (fun i => (b i).1) (fun i => (b i).2) ε
  obtain ⟨hval, hpivots⟩ := Bool.and_eq_true_iff.mp h
  have hx : InCell (cornerBox b ε) x := by
    intro i
    cases hε : ε i <;> simp [x, cornerBox, boxCorner, hε]
  have herr (k : Fin 6) : |entries sign x k - (cornerLo b sign ε k : ℝ)| ≤
      (cornerError b sign ε k : ℝ) := by
    have hok := List.all_eq_true.mp hval k (List.mem_finRange k)
    have hb := checked_bounds (cornerVal b sign ε k) (pad_mem hx) hok
    change Between (cornerVal b sign ε k)
      (value (pad x) (Checked.expr (cornerVal b sign ε k))) at hb
    unfold cornerVal at hb
    rw [signed_matrix_replay_semantics] at hb
    change (cornerLo b sign ε k : ℝ) ≤ entries sign x k ∧
      entries sign x k ≤ (Checked.hi (cornerVal b sign ε k) : ℝ) at hb
    rw [abs_of_nonneg (sub_nonneg.mpr hb.1), cornerError, Rat.cast_sub]
    exact sub_le_sub_right hb.2 _
  have hperturb := quad3_entries_sub_row_error_le (entries sign x)
    (fun k => (cornerLo b sign ε k : ℝ)) (fun k => (cornerError b sign ε k : ℝ)) herr u v w
  simp only [get_ofFn] at hpivots
  have hpos := positivePivots_sound hpivots u v w hn
  rw [subtractRowErrors_spec] at hpos
  simp only [quad3RowError, Rat.cast_add] at hpos hperturb ⊢
  linarith only [hpos, hperturb]

private def allCorners (p : (Fin 4 → Bool) → Bool) : Bool :=
  [false, true].all fun a => [false, true].all fun b => [false, true].all fun c =>
    [false, true].all fun d => p ![a, b, c, d]

private theorem allCorners_sound {p : (Fin 4 → Bool) → Bool} (h : allCorners p = true)
    (ε : Fin 4 → Bool) : p ε = true := by
  have hm (a : Bool) : a ∈ [false, true] := by cases a <;> simp
  have ha := List.all_eq_true.mp h (ε 0) (hm _)
  have hb := List.all_eq_true.mp ha (ε 1) (hm _)
  have hc := List.all_eq_true.mp hb (ε 2) (hm _)
  have hd := List.all_eq_true.mp hc (ε 3) (hm _)
  have he : ![ε 0, ε 1, ε 2, ε 3] = ε := by
    funext i
    fin_cases i <;> rfl
  simpa only [he] using hd

private def checkSign (b : Box) (sign : ℚ) : Bool :=
  ((List.finRange 4).all fun i => (List.finRange 6).all fun k =>
    Jet.ok (jetSignedMatrixEntry b i sign k)) &&
    let errors := Vector.ofFn (totalError b sign)
    allCorners (fun ε => cornerCheck b sign ε errors)

/-- A cell is accepted when both signed matrices pass their corner pivot
and directional second-derivative checks. -/
def check (b : Box) : Bool :=
  checkSign b (-1) && checkSign b 1

private theorem checkSign_sound (b : Box) (sign : ℚ) (h : checkSign b sign = true)
    {x : Fin 4 → ℝ} (hx : InCell b x) : (focalMatrix sign x).PosDef := by
  obtain ⟨hjet, hcorner⟩ := Bool.and_eq_true_iff.mp h
  apply posDef_of_corners b sign hx
  · intro i k
    exact List.all_eq_true.mp (List.all_eq_true.mp hjet i (List.mem_finRange i)) k
      (List.mem_finRange k)
  · intro ε
    exact cornerCheck_sound b sign ε (allCorners_sound hcorner ε)

/-- On the entire closed box accepted by the checker, including its faces,
both signed Wu focal matrices are strictly positive definite. -/
theorem check_sound {b : Box} (h : check b = true) {x : Fin 4 → ℝ} (hx : InCell b x) :
    (focalMatrix (-1) x).PosDef ∧ (focalMatrix 1 x).PosDef := by
  obtain ⟨hm, hp⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨checkSign_sound b (-1) hm hx, checkSign_sound b 1 hp hx⟩

/-- The first accepted leaf of the exact upper focal subdivision. -/
def firstLeaf : Box :=
  ![(1049 / 1000, 33719 / 32000), (0, 1 / 256), (-1 / 128, -1 / 256), (0, 1 / 4)]

-- Check all derivative and corner bounds by kernel reduction.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Whole-cell normalization checks the four curvature bounds and all corners for each sign.
theorem firstLeaf_checked : check firstLeaf = true := by decide +kernel

theorem firstLeaf_posDef {x : Fin 4 → ℝ} (hx : InCell firstLeaf x) :
    (focalMatrix (-1) x).PosDef ∧ (focalMatrix 1 x).PosDef :=
  check_sound firstLeaf_checked hx

/--
info: 'D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells.firstLeaf_posDef' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms firstLeaf_posDef

end D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells

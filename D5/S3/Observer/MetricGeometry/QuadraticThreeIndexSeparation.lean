/- GID: D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent quadratic calibrations have an attained sharp three-coordinate separation. -/

import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-! Exact separation of two independent quadratic calibration families on three indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation

/-- Three original real reports, with the ordinary Pi supremum norm. -/
abbrev Reports := Fin 3 → ℝ

/-- The original indices, without any change of observation coordinates. -/
def nodes (u v : ℝ) : Reports := ![0, u, v]

/-- A quadratic report with its own gain and offset. -/
def report (u v t A B : ℝ) : Reports := fun j => A * (nodes u v j + t) ^ 2 + B

/-- Right directional coefficient, including the first closed junction. -/
def kRight (u v r : ℝ) : ℝ :=
  if r ≤ (v - u) / 2 then u * v / (u + 2 * r) else u * (v - u) / (2 * r)

/-- Left directional coefficient, with the reflected internal spacing. -/
def kLeft (u v r : ℝ) : ℝ :=
  if r ≤ u / 2 then (v - u) * v / (v - u + 2 * r) else u * (v - u) / (2 * r)

/-- The claimed sharp value in the original observation norm. -/
def sharpValue (u v m s t : ℝ) : ℝ :=
  m * (t - s) * min (kRight u v (max (s + v / 2) 0))
    (kLeft u v (max (-t - v / 2) 0))

/-- Exactly the source offset, computed from the full uncentered difference. -/
def center (q : Reports) : ℝ :=
  -(max (q 0) (max (q 1) (q 2)) + min (q 0) (min (q 1) (q 2))) / 2

/-- All distances from independently legal calibrations, with no upper gain bound. -/
def distances (u v m s t : ℝ) : Set ℝ :=
  {e | ∃ A A' B B' : ℝ, m ≤ A ∧ m ≤ A' ∧
    e = ‖report u v s A B - report u v t A' B'‖}

/-- Legality and equality for this exact gain pair, using the full source center. -/
def Attains (u v m s t A A' : ℝ) : Prop :=
  m ≤ A ∧ m ≤ A' ∧
    ‖report u v s A (center (report u v s A 0 - report u v t A' 0)) -
      report u v t A' 0‖ = sharpValue u v m s t

private lemma coordinate_bounds (e : Reports) (i : Fin 3) :
    -‖e‖ ≤ e i ∧ e i ≤ ‖e‖ :=
  abs_le.mp (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm e i)

private lemma center_le (q : Reports) (c b : ℝ)
    (hc : 0 ≤ c) (hb : ∀ i, -c ≤ q i + b ∧ q i + b ≤ c) :
    ‖fun i => q i + center q‖ ≤ c := by
  let hi := max (q 0) (max (q 1) (q 2))
  let lo := min (q 0) (min (q 1) (q 2))
  have hhi : hi + b ≤ c := by
    dsimp [hi]
    apply (le_sub_iff_add_le).mp
    exact max_le ((by linarith [(hb 0).2]))
      (max_le (by linarith [(hb 1).2]) (by linarith [(hb 2).2]))
  have hlo : -c ≤ lo + b := by
    dsimp [lo]
    rw [← sub_le_iff_le_add]
    exact le_min (by linarith [(hb 0).1])
      (le_min (by linarith [(hb 1).1]) (by linarith [(hb 2).1]))
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro i
  have bounds : lo ≤ q i ∧ q i ≤ hi := by
    fin_cases i <;> dsimp [lo, hi] <;>
      constructor <;> simp only [min_le_iff, le_max_iff] <;> aesop
  change |q i + center q| ≤ c
  apply abs_le.mpr
  change -c ≤ q i + -(hi + lo) / 2 ∧ q i + -(hi + lo) / 2 ≤ c
  constructor <;> linarith

private lemma centered_upper (u v s t A A' c b : ℝ) (hc : 0 ≤ c)
    (hb : ∀ i, -c ≤ (report u v s A 0 - report u v t A' 0) i + b ∧
      (report u v s A 0 - report u v t A' 0) i + b ≤ c) :
    ‖report u v s A (center (report u v s A 0 - report u v t A' 0)) -
      report u v t A' 0‖ ≤ c := by
  convert center_le (report u v s A 0 - report u v t A' 0) c b hc hb using 1
  congr 1
  funext i
  simp [report]
  ring

private lemma right_lower (u v m s t A A' B B' : ℝ)
    (hu : 0 < u) (huv : u < v) (hm : 0 < m) (hst : s < t)
    (hA' : m ≤ A') (hs : -v / 2 < s) :
    m * (t - s) * kRight u v (s + v / 2) ≤
      ‖report u v s A B - report u v t A' B'‖ := by
  let e := report u v s A B - report u v t A' B'
  let E := ‖e‖
  let f := u * (u + 2 * s)
  let g := v * (v + 2 * s)
  have hw : 0 < v - u := sub_pos.mpr huv
  have hv : 0 < v := hu.trans huv
  have hg : 0 < g := mul_pos hv (by linarith)
  have hgf : 0 < g - f := by
    dsimp [g, f]
    nlinarith [mul_pos hw (show 0 < u + v + 2 * s by linarith)]
  have identity : (g - f) * e 0 - g * e 1 + f * e 2 =
      2 * A' * (t - s) * u * v * (v - u) := by
    dsimp [e, report, nodes, g, f]
    norm_num
    ring
  have h0 := coordinate_bounds e 0
  have h1 := coordinate_bounds e 1
  have h2 := coordinate_bounds e 2
  change -E ≤ e 0 ∧ e 0 ≤ E at h0
  change -E ≤ e 1 ∧ e 1 ≤ E at h1
  change -E ≤ e 2 ∧ e 2 ≤ E at h2
  have hmass : m * (t - s) ≤ A' * (t - s) :=
    mul_le_mul_of_nonneg_right hA' (sub_pos.mpr hst).le
  unfold kRight
  split_ifs with hnear
  · have hf : f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith)
    have bound : 2 * A' * (t - s) * u * v * (v - u) ≤ 2 * E * (g - f) := by
      nlinarith only [identity, mul_nonneg hgf.le (sub_nonneg.mpr h0.2),
        mul_nonneg hg.le (show 0 ≤ e 1 + E by linarith),
        mul_nonneg (neg_nonneg.mpr hf) (show 0 ≤ e 2 + E by linarith)]
    have hp : 0 < u + 2 * (s + v / 2) := by linarith
    have canceled : A' * (t - s) * u * v ≤ E * (u + 2 * (s + v / 2)) := by
      apply (mul_le_mul_iff_left₀ hw).mp
      dsimp [g, f] at bound
      nlinarith only [bound]
    have hmuv := mul_le_mul_of_nonneg_right hmass (mul_pos hu hv).le
    calc
      m * (t - s) * (u * v / (u + 2 * (s + v / 2))) =
          (m * (t - s) * u * v) / (u + 2 * (s + v / 2)) := by ring
      _ ≤ E := (div_le_iff₀ hp).2 (by nlinarith only [canceled, hmuv])
  · have hf : 0 ≤ f := mul_nonneg hu.le (by linarith)
    have bound : 2 * A' * (t - s) * u * v * (v - u) ≤ 2 * E * g := by
      nlinarith only [identity, mul_nonneg hgf.le (sub_nonneg.mpr h0.2),
        mul_nonneg hg.le (show 0 ≤ e 1 + E by linarith),
        mul_nonneg hf (sub_nonneg.mpr h2.2)]
    have hp : 0 < 2 * (s + v / 2) := by linarith
    have canceled : A' * (t - s) * u * (v - u) ≤ E * (2 * (s + v / 2)) := by
      apply (mul_le_mul_iff_left₀ hv).mp
      dsimp [g] at bound
      nlinarith only [bound]
    have hmuw := mul_le_mul_of_nonneg_right hmass (mul_pos hu hw).le
    calc
      m * (t - s) * (u * (v - u) / (2 * (s + v / 2))) =
          (m * (t - s) * u * (v - u)) / (2 * (s + v / 2)) := by ring
      _ ≤ E := (div_le_iff₀ hp).2 (by nlinarith only [canceled, hmuw])

private lemma k_right_le (u v r : ℝ) (hu : 0 < u) (huv : u < v) (hr : 0 ≤ r) :
    kRight u v r ≤ v := by
  have hv : 0 < v := hu.trans huv
  unfold kRight
  split_ifs with h
  · apply (div_le_iff₀ (by linarith : 0 < u + 2 * r)).2
    nlinarith [mul_nonneg hv.le hr]
  · apply (div_le_iff₀ (by linarith : 0 < 2 * r)).2
    nlinarith [mul_nonneg (sub_pos.mpr huv).le (show 0 ≤ v - u by linarith)]

private lemma value_right (u v m s t : ℝ) (hu : 0 < u) (huv : u < v)
    (hst : s < t) (hs : -v / 2 < s) :
    sharpValue u v m s t = m * (t - s) * kRight u v (s + v / 2) := by
  have hL : max (-t - v / 2) 0 = 0 := max_eq_right (by linarith)
  have hR : max (s + v / 2) 0 = s + v / 2 := max_eq_left (by linarith)
  have hz : kLeft u v 0 = v := by
    rw [kLeft, if_pos (by linarith)]
    field_simp <;> ring
  rw [sharpValue, hL, hR, hz, min_eq_left (k_right_le u v _ hu huv (by linarith))]

private lemma reflected_norm (u v s t A A' B B' : ℝ) :
    ‖report (v - u) v (-t - v) A' B' - report (v - u) v (-s - v) A B‖ =
      ‖report u v s A B - report u v t A' B'‖ := by
  let e := report u v s A B - report u v t A' B'
  have he : report (v - u) v (-t - v) A' B' -
      report (v - u) v (-s - v) A B = fun i => -e i.rev := by
    funext i
    fin_cases i <;> norm_num [e, report, nodes, Fin.rev] <;> ring
  rw [he]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg e)).2
    intro i
    simpa only [norm_neg] using norm_le_pi_norm e i.rev
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i : Fin 3 => -e i.rev))).2
    intro i
    simpa only [Fin.rev_rev, norm_neg] using
      norm_le_pi_norm (fun j : Fin 3 => -e j.rev) i.rev

private lemma value_reflected (u v m s t : ℝ) :
    sharpValue (v - u) v m (-t - v) (-s - v) = sharpValue u v m s t := by
  have hR (r : ℝ) : kRight (v - u) v r = kLeft u v r := by
    simp only [kRight, kLeft, show v - (v - u) = u by ring]
    split_ifs <;> ring
  have hL (r : ℝ) : kLeft (v - u) v r = kRight u v r := by
    simp only [kRight, kLeft, show v - (v - u) = u by ring]
    split_ifs <;> ring
  have h1 : -t - v + v / 2 = -t - v / 2 := by ring
  have h2 : -(-s - v) - v / 2 = s + v / 2 := by ring
  simp only [sharpValue, h1, h2, hR, hL, min_comm]
  ring

private lemma lower (u v m s t A A' B B' : ℝ)
    (hu : 0 < u) (huv : u < v) (hm : 0 < m) (hst : s < t)
    (hA : m ≤ A) (hA' : m ≤ A') :
    sharpValue u v m s t ≤ ‖report u v s A B - report u v t A' B'‖ := by
  by_cases hs : -v / 2 < s
  · rw [value_right u v m s t hu huv hst hs]
    exact right_lower u v m s t A A' B B' hu huv hm hst hA' hs
  by_cases ht : t < -v / 2
  · rw [← value_reflected u v m s t, ← reflected_norm u v s t A A' B B']
    rw [value_right _ _ _ _ _ (sub_pos.mpr huv) (by linarith) (by linarith)
      (by linarith)]
    exact right_lower _ _ _ _ _ _ _ _ _ (sub_pos.mpr huv) (by linarith) hm
      (by linarith) hA (by linarith)
  · have hs0 : max (s + v / 2) 0 = 0 := max_eq_right (by linarith)
    have ht0 : max (-t - v / 2) 0 = 0 := max_eq_right (by linarith)
    have hKR : kRight u v 0 = v := by
      rw [kRight, if_pos (by linarith)]
      field_simp <;> ring
    have hKL : kLeft u v 0 = v := by
      rw [kLeft, if_pos (by linarith)]
      field_simp <;> ring
    rw [sharpValue, hs0, ht0, hKR, hKL, min_self]
    let e := report u v s A B - report u v t A' B'
    have h0 := coordinate_bounds e 0
    have h2 := coordinate_bounds e 2
    have hv : 0 < v := hu.trans huv
    have hsm := mul_nonneg (sub_nonneg.mpr hA)
      (show 0 ≤ -(v + 2 * s) by linarith)
    have htm := mul_nonneg (sub_nonneg.mpr hA')
      (show 0 ≤ v + 2 * t by linarith)
    have ident : e 0 - e 2 = v * (A' * (v + 2 * t) - A * (v + 2 * s)) := by
      dsimp [e, report, nodes]
      norm_num
      ring
    have hh : 2 * m * (t - s) ≤ A' * (v + 2 * t) - A * (v + 2 * s) := by
      nlinarith only [hsm, htm]
    have := mul_le_mul_of_nonneg_left hh hv.le
    change m * (t - s) * v ≤ ‖e‖
    nlinarith only [this, ident, h0.2, h2.1]

private lemma upper_right_near (u v m s t : ℝ) (hu : 0 < u) (huv : u < v)
    (hm : 0 < m) (hst : s < t) (hs : -v / 2 < s) :
    let z := 2 / (u + 2 * (s + v / 2))
    let A := m * (1 + (t - s) * z)
    ‖report u v s A (center (report u v s A 0 - report u v t m 0)) -
      report u v t m 0‖ ≤ m * (t - s) * (u * v / (u + 2 * (s + v / 2))) := by
  dsimp only
  let D := u + 2 * (s + v / 2)
  let A := m * (1 + (t - s) * (2 / D))
  let c := m * (t - s) * (u * v / D)
  have hD : 0 < D := by dsimp [D]; linarith
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg hm.le (sub_pos.mpr hst).le)
      (div_nonneg (mul_pos hu (hu.trans huv)).le hD.le)
  apply centered_upper u v s t A m c (c - (A * s ^ 2 - m * t ^ 2)) hc
  intro i
  have he : (report u v s A 0 - report u v t m 0) i +
      (c - (A * s ^ 2 - m * t ^ 2)) = if i = 0 then c else -c := by
    fin_cases i <;> norm_num [report, nodes] <;> dsimp only [A, c] <;>
      field_simp [ne_of_gt hD] <;> dsimp only [D] <;> ring
  rw [he]
  split_ifs <;> constructor <;> linarith

private lemma upper_right_far (u v m s t : ℝ) (hu : 0 < u) (huv : u < v)
    (hm : 0 < m) (hst : s < t) (hs : -v / 2 < s) :
    let z := 1 / (s + v / 2)
    let A := m * (1 + (t - s) * z)
    ‖report u v s A (center (report u v s A 0 - report u v t m 0)) -
      report u v t m 0‖ ≤ m * (t - s) * (u * (v - u) / (2 * (s + v / 2))) := by
  dsimp only
  let R := s + v / 2
  let A := m * (1 + (t - s) * (1 / R))
  let c := m * (t - s) * (u * (v - u) / (2 * R))
  have hR : 0 < R := by dsimp [R]; linarith
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg hm.le (sub_pos.mpr hst).le)
      (div_nonneg (mul_pos hu (sub_pos.mpr huv)).le (by linarith))
  apply centered_upper u v s t A m c (c - (A * s ^ 2 - m * t ^ 2)) hc
  intro i
  have he : (report u v s A 0 - report u v t m 0) i +
      (c - (A * s ^ 2 - m * t ^ 2)) = if i = 1 then -c else c := by
    fin_cases i <;> norm_num [report, nodes] <;> dsimp only [A, c] <;>
      field_simp [ne_of_gt hR] <;> dsimp only [R] <;> ring
  rw [he]
  split_ifs <;> constructor <;> linarith

private lemma centered_minimal (u v s t A A' B B' : ℝ) :
    ‖report u v s A (center (report u v s A 0 - report u v t A' 0)) -
      report u v t A' 0‖ ≤ ‖report u v s A B - report u v t A' B'‖ := by
  apply centered_upper u v s t A A' _ (B - B') (norm_nonneg _)
  intro i
  convert coordinate_bounds (report u v s A B - report u v t A' B') i using 1 <;>
    simp only [report, Pi.sub_apply] <;> constructor <;> intro h <;> linarith

private lemma attain_right_near (u v m s t : ℝ) (hu : 0 < u) (huv : u < v)
    (hm : 0 < m) (hst : s < t) (hs : -v / 2 < s)
    (hr : s + v / 2 ≤ (v - u) / 2) :
    Attains u v m s t (m * (1 + (t - s) * (2 / (u + 2 * (s + v / 2))))) m := by
  have hD : 0 < u + 2 * (s + v / 2) := by linarith
  have hgain : m ≤ m * (1 + (t - s) * (2 / (u + 2 * (s + v / 2)))) := by
    have hstep : 0 ≤ m * ((t - s) * (2 / (u + 2 * (s + v / 2)))) :=
      mul_nonneg hm.le (mul_nonneg (sub_pos.mpr hst).le
      (div_nonneg (by norm_num) hD.le))
    nlinarith only [hstep]
  refine ⟨hgain, le_rfl, le_antisymm ?_ (lower _ _ _ _ _ _ _ _ _ hu huv hm hst hgain le_rfl)⟩
  rw [value_right u v m s t hu huv hst hs, kRight, if_pos hr]
  exact upper_right_near u v m s t hu huv hm hst hs

private lemma attain_right_far (u v m s t : ℝ) (hu : 0 < u) (huv : u < v)
    (hm : 0 < m) (hst : s < t) (hs : -v / 2 < s)
    (hr : (v - u) / 2 ≤ s + v / 2) :
    Attains u v m s t (m * (1 + (t - s) * (1 / (s + v / 2)))) m := by
  have hR : 0 < s + v / 2 := by linarith
  have hgain : m ≤ m * (1 + (t - s) * (1 / (s + v / 2))) := by
    have := mul_nonneg hm.le (mul_nonneg (sub_pos.mpr hst).le (inv_nonneg.mpr hR.le))
    simp only [one_div] at *
    nlinarith only [this]
  refine ⟨hgain, le_rfl, le_antisymm ?_ (lower _ _ _ _ _ _ _ _ _ hu huv hm hst hgain le_rfl)⟩
  have hk : kRight u v (s + v / 2) = u * (v - u) / (2 * (s + v / 2)) := by
    unfold kRight
    split_ifs with h
    · have he : s + v / 2 = (v - u) / 2 := le_antisymm h hr
      rw [he]
      field_simp
      <;> ring
    · rfl
  rw [value_right u v m s t hu huv hst hs, hk]
  exact upper_right_far u v m s t hu huv hm hst hs

private lemma attain_reflected (u v m s t A A' : ℝ) (hu : 0 < u) (huv : u < v)
    (hm : 0 < m) (hst : s < t)
    (h : Attains (v - u) v m (-t - v) (-s - v) A' A) :
    Attains u v m s t A A' := by
  refine ⟨h.2.1, h.1, le_antisymm ?_
    (lower _ _ _ _ _ _ _ _ _ hu huv hm hst h.2.1 h.1)⟩
  let b := center (report (v - u) v (-t - v) A' 0 -
    report (v - u) v (-s - v) A 0)
  calc
    _ ≤ ‖report u v s A 0 - report u v t A' b‖ := centered_minimal _ _ _ _ _ _ 0 b
    _ = ‖report (v - u) v (-t - v) A' b - report (v - u) v (-s - v) A 0‖ :=
      (reflected_norm _ _ _ _ _ _ 0 b).symm
    _ = sharpValue (v - u) v m (-t - v) (-s - v) := h.2.2
    _ = sharpValue u v m s t := value_reflected _ _ _ _ _

private lemma attain_center (u v m s t : ℝ) (hu : 0 < u) (huv : u < v)
    (hm : 0 < m) (hst : s < t) (hs : s ≤ -v / 2) (ht : -v / 2 ≤ t) :
    Attains u v m s t m m := by
  have hR : max (s + v / 2) 0 = 0 := max_eq_right (by linarith)
  have hL : max (-t - v / 2) 0 = 0 := max_eq_right (by linarith)
  have hv : 0 < v := hu.trans huv
  have hvalue : sharpValue u v m s t = m * (t - s) * v := by
    rw [sharpValue, hR, hL]
    have h1 : kRight u v 0 = v := by
      rw [kRight, if_pos (by linarith)]
      field_simp <;> ring
    have h2 : kLeft u v 0 = v := by
      rw [kLeft, if_pos (by linarith)]
      field_simp <;> ring
    rw [h1, h2, min_self]
  refine ⟨le_rfl, le_rfl, le_antisymm ?_
    (lower _ _ _ _ _ _ _ _ _ hu huv hm hst le_rfl le_rfl)⟩
  rw [hvalue]
  apply centered_upper u v s t m m (m * (t - s) * v)
    (m * (t ^ 2 - s ^ 2) + m * (t - s) * v) (by positivity)
  intro i
  have hn : 0 ≤ nodes u v i ∧ nodes u v i ≤ v := by
    fin_cases i <;> norm_num [nodes] <;> (try constructor) <;> linarith
  have hprod := mul_nonneg (mul_nonneg hm.le (sub_pos.mpr hst).le) hn.1
  have hprod' := mul_nonneg (mul_nonneg hm.le (sub_pos.mpr hst).le)
    (sub_nonneg.mpr hn.2)
  simp only [report, Pi.sub_apply, add_zero]
  constructor <;> nlinarith only [hprod, hprod']

/-- The exact least original sup-norm distance and every displayed finite attaining
gain choice. Both alternatives retain their closed junctions and their own center. -/
theorem quadratic_three_index_separation (u v : ℕ) (hu : 1 ≤ u) (huv : u < v)
    (m s t : ℝ) (hm : 0 < m) (hst : s < t) :
    IsLeast (distances u v m s t) (sharpValue u v m s t) ∧
    (s ≤ -(v : ℝ) / 2 → -(v : ℝ) / 2 ≤ t → Attains u v m s t m m) ∧
    (-(v : ℝ) / 2 < s → s + v / 2 ≤ ((v : ℝ) - u) / 2 →
      Attains u v m s t (m * (1 + (t - s) * (2 / (u + 2 * (s + v / 2))))) m) ∧
    (-(v : ℝ) / 2 < s → ((v : ℝ) - u) / 2 ≤ s + v / 2 →
      Attains u v m s t (m * (1 + (t - s) * (1 / (s + v / 2)))) m) ∧
    (t < -(v : ℝ) / 2 → -t - v / 2 ≤ (u : ℝ) / 2 →
      Attains u v m s t m (m * (1 + (t - s) * (2 / ((v : ℝ) - u + 2 * (-t - v / 2)))))) ∧
    (t < -(v : ℝ) / 2 → (u : ℝ) / 2 ≤ -t - v / 2 →
      Attains u v m s t m (m * (1 + (t - s) * (1 / (-t - v / 2))))) := by
  have hu' : 0 < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  have huv' : (u : ℝ) < v := by exact_mod_cast huv
  have hleftNear (ht : t < -(v : ℝ) / 2) (hr : -t - v / 2 ≤ (u : ℝ) / 2) :
      Attains u v m s t m (m * (1 + (t - s) * (2 / ((v : ℝ) - u + 2 * (-t - v / 2))))) := by
    have h := attain_right_near ((v : ℝ) - u) v m (-t - v) (-s - v)
      (by linarith) (by linarith) hm (by linarith) (by linarith) (by linarith)
    have h' := attain_reflected u v m s t m _ hu' huv' hm hst h
    convert h' using 1 <;> congr 2 <;> ring
  have hleftFar (ht : t < -(v : ℝ) / 2) (hr : (u : ℝ) / 2 ≤ -t - v / 2) :
      Attains u v m s t m (m * (1 + (t - s) * (1 / (-t - v / 2)))) := by
    have h := attain_right_far ((v : ℝ) - u) v m (-t - v) (-s - v)
      (by linarith) (by linarith) hm (by linarith) (by linarith) (by linarith)
    have h' := attain_reflected u v m s t m _ hu' huv' hm hst h
    convert h' using 1 <;> congr 2 <;> ring
  have attained : ∃ A A' : ℝ, Attains u v m s t A A' := by
    by_cases hs : -(v : ℝ) / 2 < s
    · by_cases hr : s + v / 2 ≤ ((v : ℝ) - u) / 2
      · exact ⟨_, _, attain_right_near u v m s t hu' huv' hm hst hs hr⟩
      · exact ⟨_, _, attain_right_far u v m s t hu' huv' hm hst hs (le_of_not_ge hr)⟩
    · by_cases ht : t < -(v : ℝ) / 2
      · by_cases hr : -t - v / 2 ≤ (u : ℝ) / 2
        · exact ⟨_, _, hleftNear ht hr⟩
        · exact ⟨_, _, hleftFar ht (le_of_not_ge hr)⟩
      · exact ⟨_, _, attain_center u v m s t hu' huv' hm hst (le_of_not_gt hs)
          (le_of_not_gt ht)⟩
  refine ⟨⟨?_, ?_⟩, attain_center u v m s t hu' huv' hm hst,
    attain_right_near u v m s t hu' huv' hm hst,
    attain_right_far u v m s t hu' huv' hm hst, hleftNear, hleftFar⟩
  · obtain ⟨A, A', h⟩ := attained
    exact ⟨A, A', center (report u v s A 0 - report u v t A' 0), 0, h.1, h.2.1, h.2.2.symm⟩
  · rintro e ⟨A, A', B, B', hA, hA', rfl⟩
    exact lower u v m s t A A' B B' hu' huv' hm hst hA hA'

#print axioms quadratic_three_index_separation

end D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation

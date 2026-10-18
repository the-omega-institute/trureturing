/- GID: D5/S3/StatisticalMechanics/ThreeLabelCoalescent
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ThreeLabelCoalescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forward equations and association certificates for a three-label pure coalescence chain. -/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! # Three-label pure coalescence and its association determinant -/

noncomputable section
namespace D5.S3.StatisticalMechanics.ThreeLabelCoalescent
open Set Filter
open scoped Topology

/-- Order: N = 1|2|3, A = 12|3, B = 23|1, T = 123, C = 13|2. -/
def initial : Fin 5 → ℝ := ![1, 0, 0, 0, 0]

def K (h : ℝ) : ℝ := 4 + h

def ell (h : ℝ) : ℝ := 17 / 4 + h

/-- The forward operator, with exactly the seven stated off-diagonal rates. -/
def forward (h : ℝ) (q : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![-ell h * q 0, 3 * q 0 - q 1 / 4, q 0 - ell h * q 2,
    h * q 0 + q 1 / 4 + ell h * q 2 + q 4 / 4, q 0 / 4 - q 4 / 4]

/-- An independently specified initial-value problem, with no closed-form premise. -/
structure ForwardLaw (h : ℝ) (p : ℝ → Fin 5 → ℝ) : Prop where
  start : p 0 = initial
  equation : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => p s i) (forward h (p t) i) t

def u (t : ℝ) : ℝ := Real.exp (-t / 4)
def v (h t : ℝ) : ℝ := Real.exp (-ell h * t)

/-- A candidate solution, subsequently checked against the forward equations. -/
def explicit (h t : ℝ) : Fin 5 → ℝ :=
  ![v h t, 3 * (u t - v h t) / K h, t * v h t,
    1 - v h t - 3 * (u t - v h t) / K h - t * v h t -
      (u t - v h t) / (4 * K h), (u t - v h t) / (4 * K h)]

/-- Determinant of the two binary merge events after removing the C atom. -/
def delta (q : Fin 5 → ℝ) : ℝ := q 0 * q 3 - q 1 * q 2

def H (h t : ℝ) : ℝ :=
  1 - ((13 / 4 + 3 * t) / K h) * u t -
    ((h + 3 / 4 + (1 + h) * t) / K h) * v h t

private lemma du (t : ℝ) : HasDerivAt u (-u t / 4) t := by
  convert (((hasDerivAt_id t).neg.div_const 4).exp) using 1
  · ext s; simp [u]
  · simp [u]; ring

private lemma dv (h t : ℝ) : HasDerivAt (v h) (-ell h * v h t) t := by
  convert ((hasDerivAt_id t).const_mul (-ell h)).exp using 1
  · ext s; simp [v]
  · simp [v]; ring

private lemma explicit_derivative (h : ℝ) (hk : K h ≠ 0) (t : ℝ) (i : Fin 5) :
    HasDerivAt (fun s => explicit h s i) (forward h (explicit h t) i) t := by
  have hkp : 4 + h ≠ 0 := hk
  have hn := dv h t
  have ha := ((du t).sub hn).const_mul 3 |>.div_const (K h)
  have hb := (hasDerivAt_id t).mul hn
  have hc := ((du t).sub hn).div_const (4 * K h)
  have ht := ((((hasDerivAt_const t (1 : ℝ)).sub hn).sub ha).sub hb).sub hc
  fin_cases i
  · simpa [explicit, forward] using hn
  · convert ha using 1
    · ext s; simp [explicit]
    · dsimp [explicit, forward, ell, K]; field_simp [hkp]; ring
  · convert hb using 1
    · ext s; simp [explicit]
    · simp [explicit, forward]; ring
  · convert ht using 1
    · ext s; simp [explicit]
    · dsimp [explicit, forward, ell, K]; field_simp [hkp]; ring
  · convert hc using 1
    · ext s; simp [explicit]
    · dsimp [explicit, forward, ell, K]; field_simp [hkp]; ring

private lemma scalar_unique {f g : ℝ → ℝ} (c : ℝ) (h0 : f 0 = g 0)
    (hd : ∀ t, 0 ≤ t → HasDerivAt (fun s => f s - g s) (c * (f t - g t)) t)
    (t : ℝ) (ht : 0 ≤ t) : f t = g t := by
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun s => f s - g s) (f' := fun s => c * (f s - g s))
    (K := |c|) (a := 0) (b := t)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hd s hs.1).hasDerivWithinAt)
    (sub_eq_zero.mpr h0)
    (fun s _ => by rw [norm_mul, Real.norm_eq_abs])
    t ⟨ht, le_rfl⟩
  exact sub_eq_zero.mp hz

private lemma solution_unique (h : ℝ) {p q : ℝ → Fin 5 → ℝ}
    (hp : ForwardLaw h p) (hq : ForwardLaw h q) (t : ℝ) (ht : 0 ≤ t) : p t = q t := by
  have h0 (i : Fin 5) : p 0 i = q 0 i := congrFun (hp.start.trans hq.start.symm) i
  have hn (s : ℝ) (hs : 0 ≤ s) : p s 0 = q s 0 := by
    apply scalar_unique (-ell h) (h0 0) _ s hs
    intro r hr
    convert (hp.equation r hr 0).sub (hq.equation r hr 0) using 1 <;>
      simp [forward] <;> ring
  have ha (s : ℝ) (hs : 0 ≤ s) : p s 1 = q s 1 := by
    apply scalar_unique (-1 / 4) (h0 1) _ s hs
    intro r hr
    convert (hp.equation r hr 1).sub (hq.equation r hr 1) using 1 <;>
      simp [forward, hn r hr] <;> ring
  have hb (s : ℝ) (hs : 0 ≤ s) : p s 2 = q s 2 := by
    apply scalar_unique (-ell h) (h0 2) _ s hs
    intro r hr
    convert (hp.equation r hr 2).sub (hq.equation r hr 2) using 1 <;>
      simp [forward, hn r hr] <;> ring
  have hc (s : ℝ) (hs : 0 ≤ s) : p s 4 = q s 4 := by
    apply scalar_unique (-1 / 4) (h0 4) _ s hs
    intro r hr
    convert (hp.equation r hr 4).sub (hq.equation r hr 4) using 1 <;>
      simp [forward, hn r hr] <;> ring
  have hT : p t 3 = q t 3 := by
    apply scalar_unique 0 (h0 3) _ t ht
    intro r hr
    convert (hp.equation r hr 3).sub (hq.equation r hr 3) using 1 <;>
      simp [forward, hn r hr, ha r hr, hb r hr, hc r hr] <;> ring
  funext i
  fin_cases i
  · exact hn t ht
  · exact ha t ht
  · exact hb t ht
  · exact hT
  · exact hc t ht

private lemma explicit_forward (h : ℝ) (hk : K h ≠ 0) : ForwardLaw h (explicit h) := by
  refine ⟨?_, fun t _ i => explicit_derivative h hk t i⟩
  ext i
  fin_cases i <;> norm_num [explicit, initial, u, v]

/-- Solving the independently given initial-value problem determines all five masses
and the association determinant, including the resonant B mass t exp(-ell t). -/
theorem forward_solution (h : ℝ) (hh : 0 < h) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardLaw h p) (t : ℝ) (ht : 0 ≤ t) :
    p t = explicit h t ∧ delta (p t) = v h t * H h t := by
  have hk : K h ≠ 0 := ne_of_gt (by dsimp [K]; linarith)
  have he := solution_unique h hp (explicit_forward h hk) t ht
  refine ⟨he, ?_⟩
  rw [he]
  simp [delta, explicit, H]
  field_simp [hk]
  dsimp [K]
  ring

private lemma uv_gap (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ u t - v h t := by
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  dsimp [ell]
  nlinarith

private lemma uv_gap_pos (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : 0 < t) :
    0 < u t - v h t := by
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  dsimp [ell]
  nlinarith

private lemma explicit_nonneg (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : 0 ≤ t) :
    0 < explicit h t 0 ∧ 0 ≤ explicit h t 1 ∧
      0 ≤ explicit h t 2 ∧ 0 ≤ explicit h t 4 := by
  have hk : 0 < K h := by dsimp [K]; linarith
  have hg := uv_gap h hh t ht
  have hv : 0 < v h t := Real.exp_pos _
  change 0 < v h t ∧ 0 ≤ 3 * (u t - v h t) / K h ∧
    0 ≤ t * v h t ∧ 0 ≤ (u t - v h t) / (4 * K h)
  exact ⟨hv, by positivity, by positivity, by positivity⟩

private lemma explicit_positive (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : 0 < t) :
    ∀ i, 0 < explicit h t i := by
  have hk : 0 < K h := by dsimp [K]; linarith
  have hkn : K h ≠ 0 := ne_of_gt hk
  have hv : 0 < v h t := Real.exp_pos _
  have hg := uv_gap_pos h hh t ht
  have hT : StrictMonoOn (fun s => explicit h s 3) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro s _
      exact (explicit_derivative h hkn s 3).continuousAt.continuousWithinAt
    · intro s hs
      rw [(explicit_derivative h hkn s 3).deriv]
      have hsn : 0 ≤ s := interior_subset hs
      obtain ⟨hn, ha, hb, hc⟩ := explicit_nonneg h hh s hsn
      change 0 < h * explicit h s 0 + explicit h s 1 / 4 +
        ell h * explicit h s 2 + explicit h s 4 / 4
      have he : 0 < ell h := by dsimp [ell]; linarith
      positivity
  have hz : explicit h 0 3 = 0 := by norm_num [explicit, u, v]
  have htp := hT (show (0 : ℝ) ∈ Ici 0 by simp) ht.le ht
  change explicit h 0 3 < explicit h t 3 at htp
  rw [hz] at htp
  intro i
  fin_cases i
  · exact hv
  · change 0 < 3 * (u t - v h t) / K h; positivity
  · change 0 < t * v h t; positivity
  · exact htp
  · change 0 < (u t - v h t) / (4 * K h); positivity

/-- The independent forward system has a solution; every solution has a normalized,
strictly positive five-atom law at each positive time and the stated determinant. -/
theorem positive_probability_solution (h : ℝ) (hh : 0 < h) :
    ForwardLaw h (explicit h) ∧
    ∀ (p : ℝ → Fin 5 → ℝ), ForwardLaw h p → ∀ t, 0 < t →
      p t = explicit h t ∧ (∑ i, p t i) = 1 ∧ (∀ i, 0 < p t i) ∧
      delta (p t) = v h t * H h t := by
  have hk : K h ≠ 0 := ne_of_gt (by dsimp [K]; linarith)
  refine ⟨explicit_forward h hk, ?_⟩
  intro p hp t ht
  obtain ⟨he, hd⟩ := forward_solution h hh p hp t ht.le
  refine ⟨he, ?_, ?_, hd⟩
  · rw [he]
    simp [explicit, Fin.sum_univ_succ]
  · rw [he]
    exact explicit_positive h hh t ht

/-- Coefficients of the exponentially damped part of the derivative certificate. -/
def V (h : ℝ) : ℝ := 35 / 16 + K h * h
def W (h : ℝ) : ℝ := ell h * (1 + h)
def G (h t : ℝ) : ℝ :=
  3 * t / 4 - 35 / 16 + (V h + W h * t) * Real.exp (-K h * t)
def Gfirst (h t : ℝ) : ℝ :=
  3 / 4 + (W h - K h * (V h + W h * t)) * Real.exp (-K h * t)
def Gsecond (h t : ℝ) : ℝ :=
  K h * Real.exp (-K h * t) * (K h * V h - 2 * W h + K h * W h * t)

private lemma dG (h t : ℝ) : HasDerivAt (G h) (Gfirst h t) t := by
  have he := ((hasDerivAt_id t).const_mul (-K h)).exp
  have hp := (hasDerivAt_const t (V h)).add ((hasDerivAt_id t).const_mul (W h))
  have hd := (((hasDerivAt_id t).const_mul 3).div_const 4).sub_const (35 / 16)
  convert hd.add (hp.mul he) using 1
  · ext s; simp [G]
  · dsimp [Gfirst]; ring

private lemma ddG (h t : ℝ) : HasDerivAt (Gfirst h) (Gsecond h t) t := by
  have he := ((hasDerivAt_id t).const_mul (-K h)).exp
  have hp := (hasDerivAt_const t (W h)).sub
    (((hasDerivAt_const t (V h)).add ((hasDerivAt_id t).const_mul (W h))).const_mul (K h))
  convert (hasDerivAt_const t (3 / 4 : ℝ)).add (hp.mul he) using 1
  · ext s; simp [Gfirst]
  · dsimp [Gsecond]; ring

private lemma dH (h : ℝ) (hk : K h ≠ 0) (t : ℝ) :
    HasDerivAt (H h) (u t * G h t / K h) t := by
  have ha := ((hasDerivAt_const t (13 / 4 : ℝ)).add
    ((hasDerivAt_id t).const_mul 3)).div_const (K h)
  have hb := ((hasDerivAt_const t (h + 3 / 4)).add
    ((hasDerivAt_id t).const_mul (1 + h))).div_const (K h)
  have he : u t * Real.exp (-K h * t) = v h t := by
    rw [u, ← Real.exp_add]
    congr 1
    dsimp [K, ell]
    ring
  convert ((hasDerivAt_const t (1 : ℝ)).sub (ha.mul (du t))).sub (hb.mul (dv h t)) using 1
  · ext s; simp [H]
  · dsimp [G]
    have heq : u t * ((V h + W h * t) * Real.exp (-K h * t)) =
        (V h + W h * t) * v h t := by
      calc
        _ = (V h + W h * t) * (u t * Real.exp (-K h * t)) := by ring
        _ = _ := by rw [he]
    rw [mul_add, heq]
    dsimp [V, W, ell]
    field_simp [hk]
    dsimp [K]
    ring

private lemma Gsecond_positive (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : 0 ≤ t) :
    0 < Gsecond h t := by
  have hk : 0 < K h := by dsimp [K]; linarith
  have hw : 0 < W h := by dsimp [W, ell]; positivity
  have hid : K h * V h - 2 * W h = 1 / 4 + 123 * h / 16 + 6 * h ^ 2 + h ^ 3 := by
    dsimp [K, V, W, ell]; ring
  dsimp [Gsecond]
  rw [hid]
  positivity

private lemma G_strictConvex (h : ℝ) (hh : 0 < h) : StrictConvexOn ℝ (Ici 0) (G h) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
  · intro t _; exact (dG h t).continuousAt.continuousWithinAt
  · intro t ht
    have h1 : deriv (G h) = Gfirst h := funext fun s => (dG h s).deriv
    change 0 < deriv (deriv (G h)) t
    rw [h1, (ddG h t).deriv]
    exact Gsecond_positive h hh t (interior_subset ht)

private lemma G_no_three (h : ℝ) (hh : 0 < h) (x y z : ℝ)
    (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z)
    (hxx : G h x = 0) (hyy : G h y = 0) (hzz : G h z = 0) : False := by
  have hxz := hxy.trans hyz
  have hym : y ∈ openSegment ℝ x z := by
    rw [openSegment_eq_Ioo hxz]
    exact ⟨hxy, hyz⟩
  have hlt := (G_strictConvex h hh).lt_on_openSegment hx
    (show z ∈ Ici (0 : ℝ) from (lt_of_le_of_lt hx hxz).le) (ne_of_lt hxz) hym
  rw [hxx, hyy, hzz, max_self] at hlt
  exact lt_irrefl 0 hlt

private lemma H_zero (h : ℝ) (hk : K h ≠ 0) : H h 0 = 0 := by
  simp [H, u, v]
  field_simp [hk]
  dsimp [K]
  ring

private lemma H_slope_zero (h : ℝ) (hk : K h ≠ 0) : HasDerivAt (H h) h 0 := by
  convert dH h hk 0 using 1
  simp [G, V, u]
  field_simp [hk]

private lemma H_near_zero (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < H h t := by
  have hk : K h ≠ 0 := ne_of_gt (by dsimp [K]; linarith)
  have hs := (H_slope_zero h hk).tendsto_slope_zero_right.eventually (Ioi_mem_nhds hh)
  filter_upwards [hs, self_mem_nhdsWithin] with t hs ht
  have htp : 0 < t := ht
  simp only [zero_add, H_zero h hk, sub_zero, smul_eq_mul, mem_Ioi] at hs
  exact (mul_pos_iff.mp hs).resolve_right (by intro hn; exact (not_lt_of_ge (inv_nonneg.mpr htp.le)) hn.1) |>.2

private lemma H_atTop (h : ℝ) (hh : 0 < h) : Tendsto (H h) atTop (𝓝 1) := by
  have he (b : ℝ) (hb : 0 < b) :
      Tendsto (fun t => Real.exp (-b * t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb
  have hte (b : ℝ) (hb : 0 < b) :
      Tendsto (fun t => t * Real.exp (-b * t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
  have hl : 0 < ell h := by dsimp [ell]; linarith
  have hu : Tendsto u atTop (𝓝 0) := by
    convert he (1 / 4) (by norm_num) using 1
    ext t; dsimp [u]; congr 1 <;> ring
  have htu : Tendsto (fun t => t * u t) atTop (𝓝 0) := by
    convert hte (1 / 4) (by norm_num) using 1
    ext t; dsimp [u]; congr 2 <;> ring
  have hv : Tendsto (v h) atTop (𝓝 0) := he (ell h) hl
  have htv : Tendsto (fun t => t * v h t) atTop (𝓝 0) := hte (ell h) hl
  have ha := ((hu.const_mul (13 / 4)).add (htu.const_mul 3)).div_const (K h)
  have hb := ((hv.const_mul (h + 3 / 4)).add (htv.const_mul (1 + h))).div_const (K h)
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  convert (hc.sub ha).sub hb using 1
  · ext t; dsimp [H]; ring
  · simp

private lemma H_parameter_derivative (h t : ℝ) (hk : K h ≠ 0) :
    HasDerivAt (fun k => H k t)
      (((13 / 4 + 3 * t) / K h ^ 2) * (u t - v h t) +
        ((h + 3 / 4 + (1 + h) * t) / K h) * t * v h t) h := by
  have hdK : HasDerivAt K 1 h := by
    change HasDerivAt (fun k : ℝ => 4 + k) 1 h
    exact (hasDerivAt_id h).const_add 4
  have hdv : HasDerivAt (fun k => v k t) (-t * v h t) h := by
    convert (((hasDerivAt_id h).const_add (17 / 4)).neg.mul_const t).exp using 1
    · ext k; simp [v, ell]
    · dsimp [v, ell]; ring
  have ha := (hasDerivAt_const h (13 / 4 + 3 * t)).div hdK hk
  have hb := (((hasDerivAt_id h).add_const (3 / 4)).add
    (((hasDerivAt_id h).const_add 1).mul_const t)).div hdK hk
  convert ((hasDerivAt_const h (1 : ℝ)).sub (ha.mul_const (u t))).sub (hb.mul hdv) using 1
  · ext k; simp [H]
  · have hkp : 4 + h ≠ 0 := hk
    dsimp [K]
    field_simp [hkp]
    ring

private lemma H_strictMono_parameter (t : ℝ) (ht : 0 < t) :
    StrictMonoOn (fun h => H h t) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro h hh
    exact (H_parameter_derivative h t (ne_of_gt (by dsimp [K]; linarith [show 0 < h from hh]))).continuousAt.continuousWithinAt
  · intro h hh
    have hhp : 0 < h := interior_subset hh
    have hk : 0 < K h := by dsimp [K]; linarith
    rw [(H_parameter_derivative h t (ne_of_gt hk)).deriv]
    have hg := uv_gap_pos h hhp t ht
    have hv : 0 < v h t := Real.exp_pos _
    positivity

private lemma H_small_parameter (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) : H h 2 < 0 := by
  have hk : 0 < K h := by dsimp [K]; linarith
  have hk5 : K h ≤ 5 := by dsimp [K]; linarith
  have hu : 0 < u 2 := Real.exp_pos _
  have hv : 0 < v h 2 := Real.exp_pos _
  have hesq : Real.exp (1 / 2 : ℝ) ^ 2 < 3 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
    exact Real.exp_one_lt_three
  have he : Real.exp (1 / 2 : ℝ) < 7 / 4 := by
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have heprod : u 2 * Real.exp (1 / 2 : ℝ) = 1 := by
    rw [u, ← Real.exp_add]
    norm_num
  have hua : (37 / 20 : ℝ) * u 2 > 1 := by
    nlinarith [mul_pos hu (show (0 : ℝ) < 37 / 20 - 7 / 4 by norm_num)]
  have ha : (37 / 20 : ℝ) ≤ (13 / 4 + 3 * 2) / K h := by
    apply (le_div_iff₀ hk).mpr
    nlinarith
  have hb : 0 < (h + 3 / 4 + (1 + h) * 2) / K h := by positivity
  dsimp [H]
  have hm := mul_le_mul_of_nonneg_right ha hu.le
  have hn := mul_pos hb hv
  nlinarith

private lemma H_large_parameter (h : ℝ) (hh : 8 ≤ h) (t : ℝ) (ht : 0 < t) :
    0 < H h t := by
  have hhp : 0 < h := by linarith
  have hk : 12 ≤ K h := by dsimp [K]; linarith
  have hkpos : 0 < K h := by linarith
  have hu : 0 < u t := Real.exp_pos _
  have hd : 0 < 1 + K h * t := by positivity
  have hE : Real.exp (-K h * t) ≤ 1 / (1 + K h * t) := by
    rw [neg_mul, Real.exp_neg, one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) hd).mpr
    simpa [mul_comm, add_comm] using Real.add_one_le_exp (K h * t)
  have huv : v h t = u t * Real.exp (-K h * t) := by
    rw [v, u, ← Real.exp_add]
    congr 1; dsimp [K, ell]; ring
  let A := (13 / 4 + 3 * t) / K h
  let B := (h + 3 / 4 + (1 + h) * t) / K h
  have hb : 0 < B := by dsimp [B]; positivity
  have hid : A + B / (1 + K h * t) =
      (1 + 17 / 4 * t + 3 * t ^ 2) / (1 + K h * t) := by
    dsimp [A, B]
    field_simp [ne_of_gt hkpos, ne_of_gt hd]
    dsimp [K]; ring
  have hbound : H h t ≥
      1 - u t * ((1 + 17 / 4 * t + 3 * t ^ 2) / (1 + K h * t)) := by
    change 1 - A * u t - B * v h t ≥ _
    rw [huv, ← hid]
    have hm := mul_le_mul_of_nonneg_left hE (mul_nonneg hb.le hu.le)
    simp only [div_eq_mul_inv] at *
    nlinarith only [hm]
  have hep : 1 + t / 4 < Real.exp (t / 4) := by
    simpa [add_comm] using Real.add_one_lt_exp (ne_of_gt (show 0 < t / 4 by positivity))
  have hui : u t * Real.exp (t / 4) = 1 := by
    rw [u, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hpoly : 1 + 17 / 4 * t + 3 * t ^ 2 <
      (1 + K h * t) * Real.exp (t / 4) := by
    have hm := mul_lt_mul_of_pos_left hep hd
    have hkt := mul_nonneg (sub_nonneg.mpr hk) ht.le
    have hktt := mul_nonneg hkt ht.le
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hpoly hu
  have heq : u t * ((1 + K h * t) * Real.exp (t / 4)) = 1 + K h * t := by
    calc
      _ = (1 + K h * t) * (u t * Real.exp (t / 4)) := by ring
      _ = _ := by rw [hui]; ring
  rw [heq] at hmul
  have hlt : u t * ((1 + 17 / 4 * t + 3 * t ^ 2) / (1 + K h * t)) < 1 := by
    rw [← mul_div_assoc]
    exact (div_lt_one hd).mpr hmul
  linarith

private lemma H_two_roots (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : 0 < t)
    (hn : H h t < 0) : ∃ a b : ℝ, 0 < a ∧ a < t ∧ t < b ∧ H h a = 0 ∧ H h b = 0 := by
  have hk : K h ≠ 0 := ne_of_gt (by dsimp [K]; linarith)
  have hc : Continuous (H h) := continuous_iff_continuousAt.mpr fun r => (dH h hk r).continuousAt
  have hs : ∀ᶠ s in 𝓝[>] (0 : ℝ), (0 < s ∧ s < t) ∧ 0 < H h s := by
    filter_upwards [H_near_zero h hh, self_mem_nhdsWithin,
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht))] with s hp h0 hst
    exact ⟨⟨h0, hst⟩, hp⟩
  obtain ⟨s, ⟨hs0, hst⟩, hsp⟩ := hs.exists
  obtain ⟨r, hrp, htr⟩ := ((H_atTop h hh).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
    (eventually_gt_atTop t) |>.exists
  obtain ⟨a, ha, hza⟩ := intermediate_value_Icc' hst.le hc.continuousOn ⟨hn.le, hsp.le⟩
  obtain ⟨b, hb, hzb⟩ := intermediate_value_Icc htr.le hc.continuousOn ⟨hn.le, hrp.le⟩
  refine ⟨a, b, lt_of_lt_of_le hs0 ha.1, ?_, ?_, hza, hzb⟩
  · exact lt_of_le_of_ne ha.2 (by intro he; rw [he] at hza; linarith)
  · exact lt_of_le_of_ne hb.1 (by intro he; rw [← he] at hzb; linarith)

/-- The association determinant of a forward solution cannot have three distinct
positive zeros. Its derivative certificate is strictly convex on nonnegative time. -/
theorem no_three_positive_zeros (h : ℝ) (hh : 0 < h)
    (p : ℝ → Fin 5 → ℝ) (hp : ForwardLaw h p)
    (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hza : delta (p a) = 0) (hzb : delta (p b) = 0) : delta (p c) ≠ 0 := by
  intro hzc
  have hk : K h ≠ 0 := ne_of_gt (by dsimp [K]; linarith)
  have hcH : Continuous (H h) := continuous_iff_continuousAt.mpr fun t => (dH h hk t).continuousAt
  have hz (t : ℝ) (ht : 0 ≤ t) (hd : delta (p t) = 0) : H h t = 0 := by
    rw [(forward_solution h hh p hp t ht).2] at hd
    exact (mul_eq_zero.mp hd).resolve_left (ne_of_gt (Real.exp_pos _))
  have h0 : H h 0 = 0 := by simp [H, u, v]; field_simp [hk]; dsimp [K]; ring
  obtain ⟨x, hx, hxz⟩ := exists_hasDerivAt_eq_zero ha hcH.continuousOn
    (h0.trans (hz a ha.le hza).symm) (fun t _ => dH h hk t)
  obtain ⟨y, hy, hyz⟩ := exists_hasDerivAt_eq_zero hab hcH.continuousOn
    ((hz a ha.le hza).trans (hz b (by linarith) hzb).symm) (fun t _ => dH h hk t)
  obtain ⟨z, hzmem, hzz⟩ := exists_hasDerivAt_eq_zero hbc hcH.continuousOn
    ((hz b (by linarith) hzb).trans (hz c (by linarith) hzc).symm) (fun t _ => dH h hk t)
  have gz (s : ℝ) (hs : u s * G h s / K h = 0) : G h s = 0 := by
    exact (mul_eq_zero.mp ((div_eq_zero_iff).mp hs |>.resolve_right hk)).resolve_left
      (ne_of_gt (Real.exp_pos _))
  exact G_no_three h hh x y z hx.1.le (hx.2.trans hy.1) (hy.2.trans hzmem.1)
    (gz x hxz) (gz y hyz) (gz z hzz)

private lemma H_no_three (h : ℝ) (hh : 0 < h) (a b c : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hza : H h a = 0) (hzb : H h b = 0) :
    H h c ≠ 0 := by
  have hp := (positive_probability_solution h hh).1
  have hd (t : ℝ) (ht : 0 ≤ t) (hz : H h t = 0) : delta (explicit h t) = 0 := by
    have he := (forward_solution h hh (explicit h) hp t ht).2
    rw [hz, mul_zero] at he
    exact he
  have hna := hd a ha.le hza
  have hnb := hd b (by linarith) hzb
  intro hzc
  exact no_three_positive_zeros h hh (explicit h) hp a b c ha hab hbc hna hnb (hd c (by linarith) hzc)

private lemma positive_on_connected {S : Set ℝ} {f : ℝ → ℝ}
    (hS : IsPreconnected S) (hc : ContinuousOn f S) (hn : ∀ t ∈ S, f t ≠ 0)
    (a : ℝ) (ha : a ∈ S) (hp : 0 < f a) : ∀ t ∈ S, 0 < f t := by
  intro t ht
  by_contra hnot
  obtain ⟨z, hz, he⟩ := hS.intermediate_value₂ ht ha hc continuousOn_const
    (le_of_not_gt hnot) hp.le
  exact hn z hz he

private lemma H_roots_simple (h : ℝ) (hh : 0 < h) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hza : H h a = 0) (hzb : H h b = 0) :
    deriv (H h) a ≠ 0 ∧ deriv (H h) b ≠ 0 := by
  have hk : K h ≠ 0 := ne_of_gt (by dsimp [K]; linarith)
  have hc : Continuous (H h) := continuous_iff_continuousAt.mpr fun t => (dH h hk t).continuousAt
  obtain ⟨x, hx, hxz⟩ := exists_hasDerivAt_eq_zero ha hc.continuousOn
    ((H_zero h hk).trans hza.symm) (fun t _ => dH h hk t)
  obtain ⟨y, hy, hyz⟩ := exists_hasDerivAt_eq_zero hab hc.continuousOn
    (hza.trans hzb.symm) (fun t _ => dH h hk t)
  have gz (s : ℝ) (hs : u s * G h s / K h = 0) : G h s = 0 := by
    exact (mul_eq_zero.mp ((div_eq_zero_iff).mp hs |>.resolve_right hk)).resolve_left
      (ne_of_gt (Real.exp_pos _))
  constructor
  · intro hz
    rw [(dH h hk a).deriv] at hz
    exact G_no_three h hh x a y hx.1.le hx.2 hy.1 (gz x hxz) (gz a hz) (gz y hyz)
  · intro hz
    rw [(dH h hk b).deriv] at hz
    exact G_no_three h hh x y b hx.1.le (hx.2.trans hy.1) hy.2
      (gz x hxz) (gz y hyz) (gz b hz)

/-- Two simple positive zeros, with the full three-interval sign classification. -/
def TwoCrossings (h : ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a < b ∧ H h a = 0 ∧ H h b = 0 ∧
    deriv (H h) a ≠ 0 ∧ deriv (H h) b ≠ 0 ∧
    (∀ t, 0 < t → t < a → 0 < H h t) ∧
    (∀ t, a < t → t < b → H h t < 0) ∧
    (∀ t, b < t → 0 < H h t)

private lemma H_negative_classification (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : 0 < t)
    (hn : H h t < 0) : TwoCrossings h := by
  obtain ⟨a, b, ha, hat, htb, hza, hzb⟩ := H_two_roots h hh t ht hn
  have hab := hat.trans htb
  have hk : K h ≠ 0 := ne_of_gt (by dsimp [K]; linarith)
  have hc : Continuous (H h) := continuous_iff_continuousAt.mpr fun t => (dH h hk t).continuousAt
  have hother (r : ℝ) (hr : 0 < r) (hra : r ≠ a) (hrb : r ≠ b) : H h r ≠ 0 := by
    rcases lt_or_gt_of_ne hra with hlt | hgt
    · intro hz
      exact H_no_three h hh r a b hr hlt hab hz hza hzb
    · rcases lt_or_gt_of_ne hrb with h' | h'
      · intro hz
        exact H_no_three h hh a r b ha hgt h' hza hz hzb
      · exact H_no_three h hh a b r ha hab h' hza hzb
  have hm : ∀ r ∈ Ioo a b, H h r < 0 := by
    have hneg : ∀ r ∈ Ioo a b, (-H h r) ≠ 0 := by
      intro r hr
      exact neg_ne_zero.mpr (hother r (ha.trans hr.1) (ne_of_gt hr.1) (ne_of_lt hr.2))
    have hpos := positive_on_connected isPreconnected_Ioo hc.neg.continuousOn hneg
      t ⟨hat, htb⟩ (neg_pos.mpr hn)
    intro r hr
    exact neg_pos.mp (hpos r hr)
  have hearly : ∀ r ∈ Ioo 0 a, 0 < H h r := by
    have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 a ∧ 0 < H h r := by
      filter_upwards [H_near_zero h hh, self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ha)] with r hp h0 hlt
      exact ⟨⟨h0, hlt⟩, hp⟩
    obtain ⟨r, hr, hp⟩ := he.exists
    exact positive_on_connected isPreconnected_Ioo hc.continuousOn
      (fun s hs => hother s hs.1 (ne_of_lt hs.2) (ne_of_lt (hs.2.trans hab))) r hr hp
  have hlate : ∀ r ∈ Ioi b, 0 < H h r := by
    obtain ⟨r, hrp, hrb⟩ := ((H_atTop h hh).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
      (eventually_gt_atTop b) |>.exists
    exact positive_on_connected isPreconnected_Ioi hc.continuousOn
      (fun s hs => hother s (ha.trans (hab.trans hs)) (ne_of_gt (hab.trans hs)) (ne_of_gt hs))
      r hrb hrp
  obtain ⟨hsa, hsb⟩ := H_roots_simple h hh a b ha hab hza hzb
  exact ⟨a, b, ha, hab, hza, hzb, hsa, hsb,
    fun r hr hra => hearly r ⟨hr, hra⟩, fun r hra hrb => hm r ⟨hra, hrb⟩,
    fun r hr => hlate r hr⟩

private lemma H_joint_continuous :
    ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) {q | 1 ≤ q.1} := by
  intro q hq
  have hk : 4 + q.1 ≠ 0 := by dsimp at hq; linarith
  apply ContinuousAt.continuousWithinAt
  dsimp [H, K, u, v, ell]
  fun_prop (disch := assumption)

private lemma critical_exists : ∃ h τ : ℝ, 1 < h ∧ h < 8 ∧ 0 < τ ∧
    H h τ = 0 ∧ deriv (H h) τ = 0 ∧ (∀ t, 0 < t → 0 ≤ H h t) := by
  obtain ⟨ε, hε, hearly⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (H_near_zero 1 (by norm_num))
  obtain ⟨T, hlate⟩ := eventually_atTop.mp
    ((H_atTop 1 (by norm_num)).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  have hbound (h t : ℝ) (hh : h ∈ Icc 1 8) (ht : 0 < t) (hz : H h t = 0) : t ∈ Icc ε T := by
    have hmono : H 1 t ≤ H h t := (H_strictMono_parameter t ht).monotoneOn
      (by norm_num) (show 0 < h by linarith [hh.1]) hh.1
    constructor
    · by_contra hn
      have hp := hearly ⟨ht, lt_of_not_ge hn⟩
      dsimp at hp
      rw [hz] at hmono
      linarith
    · by_contra hn
      have hp := hlate t (le_of_lt (lt_of_not_ge hn))
      rw [hz] at hmono
      linarith
  have hpc : ContinuousOn (fun h => H h 2) (Icc 1 8) := by
    intro h hh
    exact (H_parameter_derivative h 2 (ne_of_gt (by dsimp [K]; linarith [hh.1]))).continuousAt.continuousWithinAt
  obtain ⟨h₀, hh₀, hz₀⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 8) hpc
    ⟨(H_small_parameter 1 (by norm_num) le_rfl).le,
      (H_large_parameter 8 le_rfl 2 (by norm_num)).le⟩
  have h₀gt : 1 < h₀ := lt_of_le_of_ne hh₀.1 (by
    intro he
    have hn := H_small_parameter 1 (by norm_num) le_rfl
    rw [← he] at hz₀
    linarith)
  let box : Set (ℝ × ℝ) := Icc 1 8 ×ˢ Icc ε T
  let zeros : Set (ℝ × ℝ) := {q ∈ box | H q.1 q.2 = 0}
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) box :=
    H_joint_continuous.mono (fun q hq => hq.1.1)
  have hclosed : IsClosed zeros := hbox.isClosed.isClosed_eq hc continuousOn_const
  have hcomp : IsCompact zeros := hbox.of_isClosed_subset hclosed (fun q hq => hq.1)
  have hnon : zeros.Nonempty := ⟨(h₀, 2), ⟨hh₀, hbound h₀ 2 hh₀ (by norm_num) hz₀⟩, hz₀⟩
  obtain ⟨q, hq, hmax⟩ := hcomp.exists_isMaxOn hnon continuous_fst.continuousOn
  have hhq : q.1 ∈ Icc 1 8 := hq.1.1
  have hτ : 0 < q.2 := lt_of_lt_of_le hε hq.1.2.1
  have hhz : H q.1 q.2 = 0 := hq.2
  have hhgt : 1 < q.1 := lt_of_lt_of_le h₀gt (hmax (show (h₀, 2) ∈ zeros from ⟨⟨hh₀, hbound h₀ 2 hh₀ (by norm_num) hz₀⟩, hz₀⟩))
  have hhlt : q.1 < 8 := lt_of_le_of_ne hhq.2 (by
    intro he
    rw [he] at hhz
    linarith [H_large_parameter 8 le_rfl q.2 hτ])
  have hnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ H q.1 t := by
    by_contra hn
    have hn' : H q.1 t < 0 := lt_of_not_ge hn
    have hpc' : ContinuousOn (fun h => H h t) (Icc q.1 8) := by
      intro h hh
      exact (H_parameter_derivative h t (ne_of_gt (by dsimp [K]; linarith [hh.1, hhgt]))).continuousAt.continuousWithinAt
    obtain ⟨h', hh', hz'⟩ := intermediate_value_Icc hhlt.le hpc'
      ⟨hn'.le, (H_large_parameter 8 le_rfl t ht).le⟩
    have h'gt : q.1 < h' := lt_of_le_of_ne hh'.1 (by intro he; rw [← he] at hz'; linarith)
    have h'in : h' ∈ Icc 1 8 := ⟨by linarith, hh'.2⟩
    have hm := hmax (show (h', t) ∈ zeros from ⟨⟨h'in, hbound h' t h'in ht hz'⟩, hz'⟩)
    exact (not_le_of_gt h'gt) hm
  have hmin : IsLocalMin (H q.1) q.2 := by
    filter_upwards [Ioi_mem_nhds hτ] with t ht
    change H q.1 q.2 ≤ H q.1 t
    rw [hhz]
    exact hnonneg t ht
  exact ⟨q.1, q.2, hhgt, hhlt, hτ, hhz, hmin.deriv_eq_zero, hnonneg⟩

private lemma stationary_of_nonnegative (h : ℝ) (hnon : ∀ t, 0 < t → 0 ≤ H h t)
    (τ : ℝ) (hτ : 0 < τ) (hz : H h τ = 0) : deriv (H h) τ = 0 := by
  have hm : IsLocalMin (H h) τ := by
    filter_upwards [Ioi_mem_nhds hτ] with t ht
    change H h τ ≤ H h t
    rw [hz]
    exact hnon t ht
  exact hm.deriv_eq_zero

private lemma nonnegative_zero_unique (h : ℝ) (hh : 0 < h)
    (hnon : ∀ t, 0 < t → 0 ≤ H h t) (τ : ℝ) (hτ : 0 < τ) (hz : H h τ = 0)
    (t : ℝ) (ht : 0 < t) (hzt : H h t = 0) : t = τ := by
  rcases lt_trichotomy t τ with hlt | he | hgt
  · exact ((H_roots_simple h hh t τ ht hlt hzt hz).1
      (stationary_of_nonnegative h hnon t ht hzt)).elim
  · exact he
  · exact ((H_roots_simple h hh τ t hτ hgt hz hzt).1
      (stationary_of_nonnegative h hnon τ hτ hz)).elim

private lemma critical_second_positive (h : ℝ) (hh : 0 < h) (τ : ℝ) (hτ : 0 < τ)
    (hz : H h τ = 0) (hdz : deriv (H h) τ = 0) :
    0 < deriv (deriv (H h)) τ := by
  have hk : 0 < K h := by dsimp [K]; linarith
  have hkn := ne_of_gt hk
  have gz (s : ℝ) (hs : u s * G h s / K h = 0) : G h s = 0 := by
    exact (mul_eq_zero.mp ((div_eq_zero_iff).mp hs |>.resolve_right hkn)).resolve_left
      (ne_of_gt (Real.exp_pos _))
  have hgz : G h τ = 0 := gz τ (by rwa [(dH h hkn τ).deriv] at hdz)
  have hc : Continuous (H h) := continuous_iff_continuousAt.mpr fun t => (dH h hkn t).continuousAt
  obtain ⟨x, hx, hxz⟩ := exists_hasDerivAt_eq_zero hτ hc.continuousOn
    ((H_zero h hkn).trans hz.symm) (fun t _ => dH h hkn t)
  have hgp := (G_strictConvex h hh).slope_lt_deriv hx.1.le hτ.le hx.2 (dG h τ).differentiableAt
  have hgx := gz x hxz
  simp only [slope_def_field, hgx, hgz, sub_self, zero_div] at hgp
  rw [(dG h τ).deriv] at hgp
  have he : deriv (H h) = fun s => u s * G h s / K h := funext fun s => (dH h hkn s).deriv
  rw [he]
  have hd := ((du τ).mul (dG h τ)).div_const (K h)
  change 0 < deriv (fun s => (u * G h) s / K h) τ
  rw [hd.deriv]
  rw [hgz]
  simp only [mul_zero, add_zero, zero_add]
  exact div_pos (mul_pos (Real.exp_pos _) hgp) hk

private lemma crossings_simple (h : ℝ) (hc : TwoCrossings h) (t : ℝ)
    (ht : 0 < t) (hz : H h t = 0) : deriv (H h) t ≠ 0 := by
  obtain ⟨a, b, ha, hab, hza, hzb, hda, hdb, hearly, hmid, hlate⟩ := hc
  rcases lt_trichotomy t a with hlt | he | hgt
  · exact (ne_of_gt (hearly t ht hlt) hz).elim
  · simpa [he] using hda
  · rcases lt_trichotomy t b with hlt' | he' | hgt'
    · exact (ne_of_lt (hmid t hgt hlt') hz).elim
    · simpa [he'] using hdb
    · exact (ne_of_gt (hlate t hgt') hz).elim

/-- A unique fold in (1,8) separates two simple association crossings from strict
positivity. At the fold the sole positive zero has strictly positive second derivative. -/
theorem unique_fold_classification :
    ∃ hc τc : ℝ, hc ∈ Ioo 1 8 ∧ 0 < τc ∧ H hc τc = 0 ∧ deriv (H hc) τc = 0 ∧
      0 < deriv (deriv (H hc)) τc ∧
      (∀ h t : ℝ, 0 < h → 0 < t → H h t = 0 → deriv (H h) t = 0 → h = hc ∧ t = τc) ∧
      (∀ h : ℝ, 0 < h → h < hc → TwoCrossings h) ∧
      (∀ t : ℝ, 0 < t → t ≠ τc → 0 < H hc t) ∧
      (∀ h : ℝ, hc < h → ∀ t : ℝ, 0 < t → 0 < H h t) := by
  obtain ⟨hc, τc, hc1, hc8, hτ, hz, hdz, hnon⟩ := critical_exists
  have hcp : 0 < hc := by linarith
  have low (h : ℝ) (hh : 0 < h) (hlt : h < hc) : TwoCrossings h := by
    have hneg := H_strictMono_parameter τc hτ hh hcp hlt
    change H h τc < H hc τc at hneg
    rw [hz] at hneg
    exact H_negative_classification h hh τc hτ hneg
  have high (h : ℝ) (hgt : hc < h) (t : ℝ) (ht : 0 < t) : 0 < H h t := by
    exact lt_of_le_of_lt (hnon t ht)
      (H_strictMono_parameter t ht hcp (show 0 < h by linarith) hgt)
  have only (t : ℝ) (ht : 0 < t) (hzt : H hc t = 0) : t = τc :=
    nonnegative_zero_unique hc hcp hnon τc hτ hz t ht hzt
  refine ⟨hc, τc, ⟨hc1, hc8⟩, hτ, hz, hdz,
    critical_second_positive hc hcp τc hτ hz hdz, ?_, low, ?_, high⟩
  · intro h t hh ht hzt hdzt
    rcases lt_trichotomy h hc with hlt | he | hgt
    · exact (crossings_simple h (low h hh hlt) t ht hzt hdzt).elim
    · subst h
      exact ⟨rfl, only t ht hzt⟩
    · exact (ne_of_gt (high h hgt t ht) hzt).elim
  · intro t ht hne
    exact lt_of_le_of_ne (hnon t ht) (Ne.symm (fun he => hne (only t ht he)))

/-- Seven rates in the order alpha,beta,gamma,zeta,d,e,f. -/
def outgoing (r : Fin 7 → ℝ) : ℝ := r 0 + r 1 + r 2 + r 3

def generalForward (r : Fin 7 → ℝ) (q : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![-outgoing r * q 0, r 0 * q 0 - r 4 * q 1, r 1 * q 0 - r 5 * q 2,
    r 3 * q 0 + r 4 * q 1 + r 5 * q 2 + r 6 * q 4, r 2 * q 0 - r 6 * q 4]

/-- A probability trajectory independently anchored by the seven-rate generator. -/
structure GeneralForwardLaw (r : Fin 7 → ℝ) (p : ℝ → Fin 5 → ℝ) : Prop where
  start : p 0 = initial
  equation : ∀ t, 0 ≤ t → ∀ i,
    HasDerivAt (fun s => p s i) (generalForward r (p t) i) t
  nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ p t i
  normalized : ∀ t, 0 ≤ t → ∑ i, p t i = 1

def baseRates (h : ℝ) : Fin 7 → ℝ := ![3, 1, 1 / 4, h, 1 / 4, ell h, 1 / 4]

private lemma general_N (r : Fin 7 → ℝ) (p : ℝ → Fin 5 → ℝ)
    (hp : GeneralForwardLaw r p) (t : ℝ) (ht : 0 ≤ t) :
    p t 0 = Real.exp (-outgoing r * t) := by
  apply scalar_unique (-outgoing r) _ _ t ht
  · simpa [initial] using congrFun hp.start 0
  · intro s hs
    have he := ((hasDerivAt_id s).const_mul (-outgoing r)).exp
    convert (hp.equation s hs 0).sub he using 1
    · ext x; simp
    · simp [generalForward]; ring

private lemma incoming_bound (r : Fin 7 → ℝ) (p : ℝ → Fin 5 → ℝ)
    (hp : GeneralForwardLaw r p) (i : Fin 5) (a d : ℝ) (ha : 0 ≤ a)
    (hz : p 0 i = 0)
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun t => p t i) (a * p s 0 - d * p s i) s)
    (t : ℝ) (ht : 0 ≤ t) :
    p t i ≤ a * t * Real.exp (-min d (outgoing r) * t) := by
  let m := min d (outgoing r)
  let F := fun s => Real.exp (m * s) * p s i
  have hder (s : ℝ) (hs : 0 ≤ s) : HasDerivAt F
      (a * Real.exp ((m - outgoing r) * s) +
        (m - d) * Real.exp (m * s) * p s i) s := by
    have he := ((hasDerivAt_id s).const_mul m).exp
    convert he.mul (hd s hs) using 1
    · ext x; simp [F]
    · dsimp
      rw [general_N r p hp s hs]
      rw [show Real.exp ((m - outgoing r) * s) =
        Real.exp (m * s) * Real.exp (-outgoing r * s) by
          rw [← Real.exp_add]; congr 1; ring]
      ring
  have hbound (s : ℝ) (hs : 0 ≤ s) : deriv F s ≤ a := by
    rw [(hder s hs).deriv]
    have hmL : m ≤ outgoing r := min_le_right _ _
    have hmd : m ≤ d := min_le_left _ _
    have he : Real.exp ((m - outgoing r) * s) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmL) hs)
    have hn : (m - d) * Real.exp (m * s) * p s i ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmd) (Real.exp_pos _).le)
        (hp.nonneg s hs i)
    nlinarith [mul_le_mul_of_nonneg_left he ha]
  have hb := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => hbound s (interior_subset hs)) 0 (by simp) t ht ht
  have hF0 : F 0 = 0 := by simp [F, hz]
  rw [hF0, sub_zero, sub_zero] at hb
  have hepos := Real.exp_pos (m * t)
  have hmul : Real.exp (m * t) * (a * t * Real.exp (-m * t)) = a * t := by
    rw [show -m * t = -(m * t) by ring, Real.exp_neg]
    field_simp
  change p t i ≤ a * t * Real.exp (-m * t)
  have hb' : Real.exp (m * t) * p t i ≤
      Real.exp (m * t) * (a * t * Real.exp (-m * t)) := by
    rw [hmul]
    exact hb
  exact (mul_le_mul_iff_right₀ hepos).mp hb'

/-- Global tail control and the initial association derivative for arbitrary
positive seven-rate probability trajectories, with the resonant family embedded. -/
theorem seven_rate_endpoint_certificates (r : Fin 7 → ℝ) (hr : ∀ i, 0 < r i)
    (p : ℝ → Fin 5 → ℝ) (hp : GeneralForwardLaw r p) :
    (∀ t, 0 ≤ t → p t 0 = Real.exp (-outgoing r * t)) ∧
    (∀ t, 0 ≤ t → p t 1 * p t 2 / p t 0 ≤
      r 0 * r 1 * t ^ 2 *
        Real.exp (-(min (r 4) (outgoing r) + min (r 5) (outgoing r) - outgoing r) * t)) ∧
    (∀ t, 0 ≤ t →
      p t 1 ≤ r 0 * t * Real.exp (-min (r 4) (outgoing r) * t) ∧
      p t 2 ≤ r 1 * t * Real.exp (-min (r 5) (outgoing r) * t) ∧
      p t 4 ≤ r 2 * t * Real.exp (-min (r 6) (outgoing r) * t)) ∧
    HasDerivAt (fun t => delta (p t)) (r 3) 0 ∧
    (∀ h, 0 < h →
      min (baseRates h 4) (outgoing (baseRates h)) +
        min (baseRates h 5) (outgoing (baseRates h)) - outgoing (baseRates h) = 1 / 4 ∧
      ∀ q, ForwardLaw h q → GeneralForwardLaw (baseRates h) q) := by
  refine ⟨general_N r p hp, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ha := incoming_bound r p hp 1 (r 0) (r 4) (hr 0).le
      (by simpa [initial] using congrFun hp.start 1)
      (fun s hs => by simpa [generalForward] using hp.equation s hs 1) t ht
    have hb := incoming_bound r p hp 2 (r 1) (r 5) (hr 1).le
      (by simpa [initial] using congrFun hp.start 2)
      (fun s hs => by simpa [generalForward] using hp.equation s hs 2) t ht
    have hap : 0 ≤ r 0 * t * Real.exp (-min (r 4) (outgoing r) * t) :=
      mul_nonneg (mul_nonneg (hr 0).le ht) (Real.exp_pos _).le
    have hab := mul_le_mul ha hb (hp.nonneg t ht 2) hap
    rw [general_N r p hp t ht]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    convert hab using 1
    calc
      _ = (r 0 * r 1 * t ^ 2) *
          (Real.exp (-(min (r 4) (outgoing r) + min (r 5) (outgoing r) - outgoing r) * t) *
            Real.exp (-outgoing r * t)) := by ring
      _ = (r 0 * r 1 * t ^ 2) *
          (Real.exp (-min (r 4) (outgoing r) * t) *
            Real.exp (-min (r 5) (outgoing r) * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2 <;> ring
      _ = _ := by ring
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · exact incoming_bound r p hp 1 (r 0) (r 4) (hr 0).le
        (by simpa [initial] using congrFun hp.start 1)
        (fun s hs => by simpa [generalForward] using hp.equation s hs 1) t ht
    · exact incoming_bound r p hp 2 (r 1) (r 5) (hr 1).le
        (by simpa [initial] using congrFun hp.start 2)
        (fun s hs => by simpa [generalForward] using hp.equation s hs 2) t ht
    · exact incoming_bound r p hp 4 (r 2) (r 6) (hr 2).le
        (by simpa [initial] using congrFun hp.start 4)
        (fun s hs => by simpa [generalForward] using hp.equation s hs 4) t ht
  · have hn := hp.equation 0 le_rfl 0
    have ha := hp.equation 0 le_rfl 1
    have hb := hp.equation 0 le_rfl 2
    have ht := hp.equation 0 le_rfl 3
    convert (hn.mul ht).sub (ha.mul hb) using 1
    · ext t; rfl
    · simp [hp.start, initial, generalForward]
  · intro h hh
    have hL : outgoing (baseRates h) = ell h := by dsimp [outgoing, baseRates, ell]; ring
    have hl : (1 : ℝ) / 4 ≤ ell h := by dsimp [ell]; linarith
    refine ⟨?_, ?_⟩
    · rw [hL]
      change min (1 / 4 : ℝ) (ell h) + min (ell h) (ell h) - ell h = 1 / 4
      rw [min_eq_left hl, min_self]
      ring
    · intro q hq
      refine ⟨hq.start, ?_, ?_, ?_⟩
      · intro t ht i
        convert hq.equation t ht i using 1
        fin_cases i <;> simp only [generalForward, forward, hL] <;>
          simp [baseRates] <;> ring
      · intro t ht i
        rcases eq_or_lt_of_le ht with he | he
        · rw [← he, hq.start]; fin_cases i <;> norm_num [initial]
        · exact ((positive_probability_solution h hh).2 q hq t he).2.2.1 i |>.le
      · intro t ht
        rcases eq_or_lt_of_le ht with he | he
        · rw [← he, hq.start]; norm_num [initial, Fin.sum_univ_succ]
        · exact ((positive_probability_solution h hh).2 q hq t he).2.1

#print axioms seven_rate_endpoint_certificates
#print axioms forward_solution
#print axioms positive_probability_solution
#print axioms no_three_positive_zeros
#print axioms unique_fold_classification
end D5.S3.StatisticalMechanics.ThreeLabelCoalescent

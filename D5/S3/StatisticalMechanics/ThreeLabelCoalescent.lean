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
  have hxz' : x < z := by linarith [hx.2, hy.1, hy.2, hzmem.1]
  have hym : y ∈ openSegment ℝ x z := by
    rw [openSegment_eq_Ioo hxz']
    exact ⟨hx.2.trans hy.1, hy.2.trans hzmem.1⟩
  have hlt := (G_strictConvex h hh).lt_on_openSegment
    (show x ∈ Ici (0 : ℝ) from hx.1.le)
    (show z ∈ Ici (0 : ℝ) from (lt_trans hx.1 hxz').le)
    (ne_of_lt hxz') hym
  rw [gz x hxz, gz y hyz, gz z hzz, max_self] at hlt
  exact lt_irrefl 0 hlt

#print axioms forward_solution
#print axioms positive_probability_solution
#print axioms no_three_positive_zeros
end D5.S3.StatisticalMechanics.ThreeLabelCoalescent

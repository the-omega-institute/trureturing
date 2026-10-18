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
import Mathlib.Tactic

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
  convert (((hasDerivAt_id t).neg.div_const 4).exp) using 1 <;> simp [u] <;> ring

private lemma dv (h t : ℝ) : HasDerivAt (v h) (-ell h * v h t) t := by
  convert ((hasDerivAt_id t).const_mul (-ell h)).exp using 1 <;> simp [v] <;> ring

private lemma explicit_derivative (h : ℝ) (hk : K h ≠ 0) (t : ℝ) (i : Fin 5) :
    HasDerivAt (fun s => explicit h s i) (forward h (explicit h t) i) t := by
  have hn := dv h t
  have ha := ((du t).sub hn).const_mul 3 |>.div_const (K h)
  have hb := (hasDerivAt_id t).mul hn
  have hc := ((du t).sub hn).div_const (4 * K h)
  have ht := ((((hasDerivAt_const t (1 : ℝ)).sub hn).sub ha).sub hb).sub hc
  fin_cases i
  · simpa [explicit, forward] using hn
  · convert ha using 1 <;> simp [explicit, forward, ell, K] <;> field_simp [K, hk] <;> ring
  · convert hb using 1 <;> simp [explicit, forward] <;> ring
  · convert ht using 1 <;> simp [explicit, forward, ell, K] <;> field_simp [K, hk] <;> ring
  · convert hc using 1 <;> simp [explicit, forward, ell, K] <;> field_simp [K, hk] <;> ring

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
  ring

#print axioms forward_solution
end D5.S3.StatisticalMechanics.ThreeLabelCoalescent

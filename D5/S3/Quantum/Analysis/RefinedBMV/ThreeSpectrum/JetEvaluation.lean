/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/JetEvaluation
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine exponential rates and their derivative values. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.ExponentialChain
import D5.S3.Quantum.Analysis.RefinedBMVUniformDiscriminant
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.UniformExpansion
import Mathlib.Algebra.Polynomial.Eval.Algebra

/-! Affine exponential rates for the uniform refined BMV discriminant. -/

open scoped BigOperators
open Polynomial

noncomputable section

namespace RefinedBMV.DividedDifference.SparseExpansion

abbrev Rate := ℕ × ℕ

def Term.rateX (t : Term) : Rate :=
  (3 * (t.exponents.x + t.exponents.y), t.exponents.u + t.exponents.v)

def Term.rateY (t : Term) : Rate := (3 * t.exponents.y, t.exponents.v)

def Rate.atP (a : Rate) (p : ℝ) : ℝ :=
  a.1 + a.2 * p

/-- Rate differences, as polynomials in the degree less one. -/
def Rate.shifted (a : Rate) : Polynomial ℤ :=
  C (a.1 + a.2 : ℤ) + C (a.2 : ℤ) * X

def rateFactor (a : Rate) (roots : List Rate) : Polynomial ℤ :=
  (roots.map fun b => Rate.shifted a - Rate.shifted b).prod

def jet (ts : List Term) (rootsX rootsY : List Rate) : Polynomial ℤ :=
  (ts.map fun t => C t.coefficient * (1 + X)^t.exponents.p *
    rateFactor t.rateX rootsX * rateFactor t.rateY rootsY).sum

theorem shifted_rate_eval (a : Rate) (p : ℝ) :
    (Rate.shifted a).eval₂ (Int.castRingHom ℝ) (p - 1) = Rate.atP a p := by
  rcases a with ⟨u, v⟩
  simp [Rate.shifted, Rate.atP, Polynomial.eval₂_add, Polynomial.eval₂_mul]
  ring

theorem eval_rateFactor (a : Rate) (roots : List Rate) (p : ℝ) :
    (rateFactor a roots).eval₂ (Int.castRingHom ℝ) (p - 1) =
      (roots.map fun b => Rate.atP a p - Rate.atP b p).prod := by
  induction roots with
  | nil => simp [rateFactor]
  | cons b bs ih =>
      simp only [rateFactor, List.map_cons, List.prod_cons, Polynomial.eval₂_mul,
        Polynomial.eval₂_sub, shifted_rate_eval] at ih ⊢
      rw [ih]

theorem eval_jet (ts : List Term) (rootsX rootsY : List Rate) (p : ℝ) :
    (jet ts rootsX rootsY).eval₂ (Int.castRingHom ℝ) (p - 1) =
      (ts.map fun t => (t.coefficient : ℝ) * p^t.exponents.p *
        (rootsX.map fun b => Rate.atP t.rateX p - Rate.atP b p).prod *
        (rootsY.map fun b => Rate.atP t.rateY p - Rate.atP b p).prod).sum := by
  induction ts with
  | nil => simp [jet]
  | cons t ts ih =>
    simp only [jet, List.map_cons, List.sum_cons, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_one, Polynomial.eval₂_add,
      Polynomial.eval₂_X, eval_rateFactor] at ih ⊢
    rw [ih, show 1 + (p-1) = p by ring]
    rfl

theorem term_eval_log_gaps (t : Term) (p s u : ℝ) :
    t.eval p (Real.exp (3*s)) (Real.exp (3*(s+u)))
      (Real.exp (p*s)) (Real.exp (p*(s+u))) =
      (t.coefficient : ℝ) * p^t.exponents.p *
        Real.exp (Rate.atP t.rateX p * s + Rate.atP t.rateY p * u) := by
  unfold Term.eval
  simp only [← Real.exp_nat_mul]
  have h : Rate.atP t.rateX p * s + Rate.atP t.rateY p * u =
      (t.exponents.x : ℝ) * (3*s) + (t.exponents.y : ℝ) * (3*(s+u)) +
        (t.exponents.u : ℝ) * (p*s) + (t.exponents.v : ℝ) * (p*(s+u)) := by
    unfold Rate.atP Term.rateX Term.rateY
    push_cast
    ring
  rw [h]
  simp only [Real.exp_add]
  ring

theorem eval_log_gaps (ts : List Term) (p s u : ℝ) :
    evalTerms p (Real.exp (3*s)) (Real.exp (3*(s+u)))
      (Real.exp (p*s)) (Real.exp (p*(s+u))) ts =
      (ts.map fun t => (t.coefficient : ℝ) * p^t.exponents.p *
        Real.exp (Rate.atP t.rateX p * s + Rate.atP t.rateY p * u)).sum := by
  unfold evalTerms
  apply congrArg List.sum
  exact List.map_congr_left fun t _ => term_eval_log_gaps t p s u

private theorem sum_get {T S : Type*} [AddCommMonoid S] (ts : List T) (f : T → S) :
    (∑ i : Fin ts.length, f (ts.get i)) = (ts.map f).sum := by
  rw [← List.sum_ofFn, ← List.ofFn_getElem (xs := ts)]
  simp

theorem quartic_nonneg_of_jets (ts : List Term)
    (heval : ∀ p x y u v : ℝ, evalTerms p x y u v ts = clearedQuartic p x y u v)
    (rootsX rootsY : List Rate)
    (supportX : ∀ t ∈ ts, t.rateX ∈ rootsX)
    (supportY : ∀ t ∈ ts, t.rateY ∈ rootsY)
    (hjet : ∀ k < rootsX.length, ∀ l < rootsY.length, ∀ z : ℝ, 0 ≤ z →
      0 ≤ (jet ts (rootsX.take k) (rootsY.take l)).eval₂
        (Int.castRingHom ℝ) z)
    (p s u : ℝ) (hp : 1 ≤ p) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    0 ≤ clearedQuartic p (Real.exp (3*s)) (Real.exp (3*(s+u))) (Real.exp (p*s))
      (Real.exp (p*(s+u))) := by
  rw [← heval, eval_log_gaps]
  let rx (i : Fin ts.length) := Rate.atP (ts.get i).rateX p
  let ry (i : Fin ts.length) := Rate.atP (ts.get i).rateY p
  let ax := rootsX.map fun a => Rate.atP a p
  let ay := rootsY.map fun a => Rate.atP a p
  have hX (i : Fin ts.length) : rx i ∈ ax :=
    List.mem_map.mpr ⟨(ts.get i).rateX, supportX (ts.get i) (List.get_mem ts i), rfl⟩
  have hY (i : Fin ts.length) : ry i ∈ ay :=
    List.mem_map.mpr ⟨(ts.get i).rateY, supportY (ts.get i) (List.get_mem ts i), rfl⟩
  have hm (k : ℕ) (hk : k < ax.length) (l : ℕ) (hl : l < ay.length) :
      0 ≤ ∑ i : Fin ts.length,
        (((ts.get i).coefficient : ℝ) * p^(ts.get i).exponents.p) *
          ExponentialChain.factors (ax.take k) (rx i) *
          ExponentialChain.factors (ay.take l) (ry i) := by
    have h := hjet k (by simpa [ax] using hk) l (by simpa [ay] using hl)
      (p - 1) (sub_nonneg.mpr hp)
    rw [eval_jet] at h
    simp only [ExponentialChain.factors, ax, ay, rx, ry, ← List.map_take,
      List.map_map, Function.comp_def]
    rw [sum_get ts (fun t => (t.coefficient : ℝ) * p^t.exponents.p *
      (rootsX.take k |>.map fun b => Rate.atP t.rateX p - Rate.atP b p).prod *
      (rootsY.take l |>.map fun b => Rate.atP t.rateY p - Rate.atP b p).prod)]
    exact h
  have hpos := ExponentialChain.termwise_sum_nonneg_of_mixed_prefix
    rx ry ax ay hX hY (fun i => ((ts.get i).coefficient : ℝ) * p^(ts.get i).exponents.p)
    hm s u hs hu
  dsimp only [rx, ry] at hpos
  rw [sum_get ts (fun t => (t.coefficient : ℝ) * p^t.exponents.p *
    Real.exp (Rate.atP t.rateX p * s + Rate.atP t.rateY p * u))] at hpos
  exact hpos

end RefinedBMV.DividedDifference.SparseExpansion

/- GID: D5/S3/Fourier/BiquadraticKroneckerTimes
   generality: G
   mirror-B: D5/B/S3/Fourier/BiquadraticKroneckerTimes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Biquadratic nonsquare obstructions give independence and dense integer times. -/

/-
proof_shape: biquadratic_independent: content; consumers: PathDoubleBlowUpPGSTRefutation.sqrt_two_three_six_independent.
proof_shape: dense_circle_sequence: bind-only; consumer: PathDoubleBlowUpPGSTRefutation.approximation_times.
proof_shape: irrational_linear: bind-only; consumer: biquadratic_independent.
proof_shape: nonsquare_ratio: bind-only; consumer: biquadratic_independent.
escape_witness: biquadratic_independent: its public conclusion, obtained by
  coefficient elimination and the nonsquare obstructions for q and p*q.
escape_witness: dense_circle_sequence: none; consumed bind-only consequence.
admission_basis: escape-witness
Direct frozen dependencies:
  D5.S3.Fourier.TorusOrbitClosure.result:
    declaration statement_id: sha256:caf0494154aac8e0e431192bd01a4b6b70a6325fb74ca65873470e5c2843bcb7
Utility none: the coefficient elimination and torus consequence quantify over
  arbitrary parameters, without bounded enumeration, a checker, a numerical
  reduction or a certified instance.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.NumberTheory.Real.Irrational
import D5.S3.Fourier.TorusOrbitClosure

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Fourier.BiquadraticKroneckerTimes
open Filter Set Real
open scoped Topology BigOperators

private theorem irrational_linear (x : ℝ) (hx : Irrational x) (a b : ℚ)
    (h : (a : ℝ) + b * x = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · simp only [hb, Rat.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, hb⟩
  · exfalso
    apply hx.ne_rat (-a / b)
    push_cast
    apply (eq_div_iff (by exact_mod_cast hb : (b : ℝ) ≠ 0)).mpr
    linarith

private theorem nonsquare_ratio (p a d : ℚ) (hp : ¬ IsSquare p)
    (h : a^2 = p*d^2) : d = 0 := by
  by_contra hd
  apply hp
  refine ⟨a/d, ?_⟩
  field_simp
  nlinarith

theorem biquadratic_independent (p q : ℚ) (x y : ℝ)
    (hx : x^2 = (p : ℝ)) (hy : y^2 = (q : ℝ))
    (hix : Irrational x) (hq : ¬ IsSquare q) (hpq : ¬ IsSquare (p*q))
    (a b c d : ℚ) (h : (a : ℝ) + b*x + c*y + d*(x*y) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have he :
      ((a^2 + p*b^2 - q*c^2 - p*q*d^2 : ℚ) : ℝ) +
        ((2*a*b - 2*q*c*d : ℚ) : ℝ)*x = 0 := by
    have hs : ((a : ℝ)+b*x)^2 = (((c : ℝ)+d*x)*y)^2 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mpr
      right
      linear_combination h
    simp only [mul_pow, add_sq, hx, hy] at hs
    push_cast
    linear_combination hs
  obtain ⟨hA, hB⟩ := irrational_linear x hix _ _ he
  have hab : a*b = q*c*d := by linarith
  have hd : d = 0 := by
    by_contra hd
    have hprod : (a^2-p*q*d^2)*(b^2-q*d^2) = 0 := by
      linear_combination (a*b+q*c*d)*hab - q*d^2*hA
    rcases mul_eq_zero.mp hprod with h1 | h2
    · exact hd (nonsquare_ratio (p*q) a d hpq (by linarith))
    · exact hd (nonsquare_ratio q b d hq (by linarith))
  have hab0 : a*b = 0 := by simpa [hd] using hab
  have hc : c = 0 := by
    rcases mul_eq_zero.mp hab0 with ha | hb
    · have hbrel : b^2 = (p*q)*(c/p)^2 := by
        have hp : p ≠ 0 := by
          intro hp; apply hpq; simp [hp]
        field_simp
        rw [ha,hd] at hA
        linear_combination hA
      have hcp := nonsquare_ratio (p*q) b (c/p) hpq hbrel
      exact (div_eq_zero_iff.mp hcp).resolve_right (by
        intro hp; apply hpq; simp [hp])
    · exact nonsquare_ratio q a c hq (by rw [hb,hd] at hA; nlinarith [hA])
  have hfinal : (a : ℝ) + b*x = 0 := by simpa [hc,hd] using h
  obtain ⟨ha,hb⟩ := irrational_linear x hix a b hfinal
  exact ⟨ha,hb,hc,hd⟩


theorem dense_circle_sequence {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (hind : ∀ (k : ι → ℤ) (m : ℤ),
      (∑ i, (k i : ℝ)*a i) = m → (∀ i, k i = 0))
    (z : ι → Circle) :
    ∃ m : ℕ → ℕ, Tendsto (fun n i => Circle.exp (2*Real.pi*a i)^(m n)) atTop (𝓝 z) := by
  classical
  let g : ι → Circle := fun i => Circle.exp (2*Real.pi*a i)
  have hcl : z ∈ closure (range (fun n : ℕ => g^n)) := by
    apply (D5.S3.Fourier.TorusOrbitClosure.result g z).mpr
    intro k hk
    have hprod : (∏ i, g i ^ k i) = Circle.exp (2*Real.pi*∑ i, (k i : ℝ)*a i) := by
      simp_rw [g, ← Circle.exp_intCast_mul]
      have hsum : (∑ i, (k i : ℝ)*(2*Real.pi*a i)) =
          2*Real.pi*∑ i, (k i : ℝ)*a i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi; ring
      rw [← hsum]
      exact (map_sum Circle.expHom _ _).symm
    rw [hprod] at hk
    obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hk
    have hrel : (∑ i, (k i : ℝ)*a i) = m := by
      have hpi := Real.pi_ne_zero
      apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
      linear_combination hm
    have hk0 := hind k m hrel
    simp [hk0]
  obtain ⟨f,hf,ht⟩ := mem_closure_iff_seq_limit.mp hcl
  choose m hm using hf
  refine ⟨m, ?_⟩
  have heq : (fun n i => Circle.exp (2*Real.pi*a i)^(m n)) = f := by
    funext n
    exact hm n
  rwa [heq]

end D5.S3.Fourier.BiquadraticKroneckerTimes

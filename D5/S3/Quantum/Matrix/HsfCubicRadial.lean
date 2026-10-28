/- GID: D5/S3/Quantum/Matrix/HsfCubicRadial
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfCubicRadial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Sharp cubic compatibility for Hermitian matrix pencils with radial denominator. -/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic

/-! The alpha=3 radial restriction of the He--Saunderson--Fawzi problem:
   arXiv:2502.05627v1, Conjecture 6.2; DOI 10.1007/s10107-025-02314-0,
   Conjecture 1. The general nonradial, arbitrary-alpha conjecture remains open.
   These are general analytic inequalities, not finite enumeration or numerical reduction.
   No physical CFC congruence bridge or novelty claim is asserted here. -/

@[expose] public section

noncomputable section
open Matrix Filter
open scoped ComplexOrder Topology

namespace D5.S3.Quantum.Matrix.HsfCubicRadial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual rational trace function; the denominator is nonzero near zero. -/
def cubicRadialTrace (A B : Matrix n n ℂ) (k t : ℝ) : ℝ :=
  (Matrix.trace ((A + t • B) ^ 3)).re / (1 + k * t) ^ 2

private theorem scalar_derivatives (a b c d k : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => (a + b*t + c*t^2 + d*t^3) / (1+k*t)^2) 0 =
      2*c - 4*k*b + 6*k^2*a ∧
    iteratedDeriv 3 (fun t : ℝ => (a + b*t + c*t^2 + d*t^3) / (1+k*t)^2) 0 =
      6*d - 12*k*c + 18*k^2*b - 24*k^3*a := by
  let p := fun t : ℝ => a + b*t + c*t^2 + d*t^3
  let p1 := fun t : ℝ => b + 2*c*t + 3*d*t^2
  let p2 := fun t : ℝ => 2*c + 6*d*t
  let s := fun t : ℝ => 1 + k*t
  let f0 := fun t => p t / (s t)^2
  let f1 := fun t => p1 t / (s t)^2 - 2*k*p t / (s t)^3
  let f2 := fun t => p2 t / (s t)^2 - 4*k*p1 t / (s t)^3 +
    6*k^2*p t / (s t)^4
  let f3 := fun t => 6*d / (s t)^2 - 6*k*p2 t / (s t)^3 +
    18*k^2*p1 t / (s t)^4 - 24*k^3*p t / (s t)^5
  have hp (t : ℝ) : HasDerivAt p (p1 t) t := by
    convert (((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b)).add
      (((hasDerivAt_id t).pow 2).const_mul c)).add
      (((hasDerivAt_id t).pow 3).const_mul d) using 1 <;>
      (try funext x) <;> simp only [p,p1, Pi.add_apply, Pi.pow_apply, id_eq] <;> ring
  have hp1 (t : ℝ) : HasDerivAt p1 (p2 t) t := by
    convert ((hasDerivAt_const t b).add ((hasDerivAt_id t).const_mul (2*c))).add
      (((hasDerivAt_id t).pow 2).const_mul (3*d)) using 1 <;>
      (try funext x) <;> simp only [p1,p2, Pi.add_apply, Pi.pow_apply, id_eq] <;> ring
  have hp2 (t : ℝ) : HasDerivAt p2 (6*d) t := by
    convert (hasDerivAt_const t (2*c)).add ((hasDerivAt_id t).const_mul (6*d)) using 1 <;>
      (try funext x) <;>
      simp only [p2, Pi.add_apply, id_eq, mul_one, zero_add]
  have hs (t : ℝ) : HasDerivAt s k t := by
    convert (hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul k) using 1 <;>
      (try funext x) <;>
      simp only [s, Pi.add_apply, id_eq, mul_one, zero_add]
  have h0 (t : ℝ) (ht : s t ≠ 0) : HasDerivAt f0 (f1 t) t := by
    convert (hp t).div ((hs t).pow 2) (pow_ne_zero 2 ht) using 1 <;>
      dsimp [f0,f1] <;> field_simp [ht] <;> ring
  have h1 (t : ℝ) (ht : s t ≠ 0) : HasDerivAt f1 (f2 t) t := by
    convert ((hp1 t).div ((hs t).pow 2) (pow_ne_zero 2 ht)).sub
      (((hp t).const_mul (2*k)).div ((hs t).pow 3) (pow_ne_zero 3 ht)) using 1 <;>
      dsimp [f1,f2] <;> field_simp [ht] <;> ring
  have h2 (t : ℝ) (ht : s t ≠ 0) : HasDerivAt f2 (f3 t) t := by
    convert (((hp2 t).div ((hs t).pow 2) (pow_ne_zero 2 ht)).sub
      (((hp1 t).const_mul (4*k)).div ((hs t).pow 3) (pow_ne_zero 3 ht))).add
      (((hp t).const_mul (6*k^2)).div ((hs t).pow 4) (pow_ne_zero 4 ht)) using 1 <;>
      dsimp [f2,f3] <;> field_simp [ht] <;> ring
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), s t ≠ 0 :=
    (hs 0).continuousAt.eventually_ne (by simp [s])
  have he1 : deriv f0 =ᶠ[𝓝 (0 : ℝ)] f1 := hn.mono fun t ht => (h0 t ht).deriv
  have he2 : deriv (deriv f0) =ᶠ[𝓝 (0 : ℝ)] f2 :=
    he1.deriv.trans (hn.mono fun t ht => (h1 t ht).deriv)
  have e2 : iteratedDeriv 2 f0 0 = f2 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he2.eq_of_nhds
  have e3 : iteratedDeriv 3 f0 0 = f3 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      he2.deriv_eq.trans (h2 0 (by simp [s])).deriv
  constructor
  · simpa [f0,p,s,f2,p1,p2] using e2
  · convert e3 using 1 <;> simp [p,s,f3,p1,p2] <;> ring

private theorem trace_cubic (A B : Matrix n n ℂ) (t : ℝ) :
    (Matrix.trace ((A + t • B)^3)).re =
      (Matrix.trace (A^3)).re + 3*(Matrix.trace (A*A*B)).re*t +
      3*(Matrix.trace (A*B*B)).re*t^2 + (Matrix.trace (B^3)).re*t^3 := by
  have h1 := Matrix.trace_mul_cycle A B A
  have h2 := Matrix.trace_mul_cycle B A A
  have h3 := Matrix.trace_mul_cycle B A B
  have h4 := Matrix.trace_mul_cycle B B A
  simp only [pow_succ, pow_zero, mul_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_add, Matrix.trace_smul,
    ← Matrix.mul_assoc, Complex.add_re, Complex.real_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, zero_add, one_mul]
  rw [h1] at h2
  simp only [h1, h2, h3, h4]
  ring

/-- Actual second and third derivatives of the trace pencil, without commutation. -/
theorem cubic_derivatives (A B : Matrix n n ℂ) (k : ℝ) :
    iteratedDeriv 2 (cubicRadialTrace A B k) 0 =
      6 * (Matrix.trace (A * (B - k • A)^2)).re ∧
    iteratedDeriv 3 (cubicRadialTrace A B k) 0 =
      6 * (Matrix.trace ((B - (4*k) • A) * (B - k • A)^2)).re := by
  have he : cubicRadialTrace A B k = fun t : ℝ =>
      ((Matrix.trace (A^3)).re + 3*(Matrix.trace (A*A*B)).re*t +
      3*(Matrix.trace (A*B*B)).re*t^2 + (Matrix.trace (B^3)).re*t^3) / (1+k*t)^2 :=
    funext fun t => by rw [cubicRadialTrace, trace_cubic]
  rw [he]
  have hh := scalar_derivatives (Matrix.trace (A^3)).re
    (3*(Matrix.trace (A*A*B)).re) (3*(Matrix.trace (A*B*B)).re)
    (Matrix.trace (B^3)).re k
  have h1 := Matrix.trace_mul_cycle A B A
  have h2 := Matrix.trace_mul_cycle B A A
  have h3 := Matrix.trace_mul_cycle B A B
  have h4 := Matrix.trace_mul_cycle B B A
  rw [h1] at h2
  constructor <;> [rw [hh.1]; rw [hh.2]] <;>
    simp only [pow_succ, pow_zero, mul_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_sub,
      Matrix.trace_smul, ← Matrix.mul_assoc, Complex.sub_re, Complex.real_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, zero_add, one_mul] <;> simp only [h1, h2, h3, h4] <;> ring

private theorem trace_weight_square_nonneg (W E : Matrix n n ℂ)
    (hW : W.PosSemidef) (hE : E.IsHermitian) :
    0 ≤ (Matrix.trace (W * E^2)).re := by
  have h := (hW.conjTranspose_mul_mul_same E).trace_nonneg
  rw [hE.eq, ← Matrix.trace_mul_cycle W E E] at h
  simpa only [pow_two, Matrix.mul_assoc] using (Complex.nonneg_iff.mp h).1

/-- The cubic radial estimate includes zero Hessian, singular endpoints and empty dimensions.
The stronger coefficient is valid for every real k, without a restriction on its magnitude. -/
theorem cubic_radial_compatibility (A B : Matrix n n ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hplus : (A + B).PosSemidef) (hminus : (A - B).PosSemidef) :
    0 ≤ iteratedDeriv 2 (cubicRadialTrace A B k) 0 ∧
    |iteratedDeriv 3 (cubicRadialTrace A B k) 0| ≤
      (1 + 4*|k|) * iteratedDeriv 2 (cubicRadialTrace A B k) 0 := by
  let E := B - k • A
  let a := (Matrix.trace (A * E^2)).re
  let b := (Matrix.trace (B * E^2)).re
  have hE : E.IsHermitian := hB.sub (hA.smul (show IsSelfAdjoint k from rfl))
  have hp := trace_weight_square_nonneg (A+B) E hplus hE
  have hm := trace_weight_square_nonneg (A-B) E hminus hE
  simp only [Matrix.add_mul, Matrix.trace_add, Complex.add_re] at hp
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hm
  have hab : |b| ≤ a := abs_le.mpr ⟨by dsimp [a,b]; linarith, by dsimp [a,b]; linarith⟩
  have ha : 0 ≤ a := (abs_nonneg b).trans hab
  obtain ⟨hd2,hd3⟩ := cubic_derivatives A B k
  have ht : (Matrix.trace ((B - (4*k) • A) * E^2)).re = b - 4*k*a := by
    simp [a,b, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, Complex.mul_re]
  rw [hd2,hd3]
  change 0 ≤ 6*a ∧ |6*(Matrix.trace ((B - (4*k) • A) * E^2)).re| ≤
    (1+4*|k|)*(6*a)
  rw [ht]
  refine ⟨mul_nonneg (by norm_num) ha, ?_⟩
  calc
    |6*(b-4*k*a)| = 6*|b-4*k*a| := by rw [abs_mul]; norm_num
    _ ≤ 6*(|b|+|4*k*a|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ = 6*(|b|+4*|k| *a) := by rw [abs_mul, abs_mul, abs_of_nonneg ha]; norm_num
    _ ≤ (1+4*|k|)*(6*a) := by nlinarith [hab]

/-- A uniform constant for all finite PSD pencils in the radial interval. -/
def UniversalCubicBound (C : ℝ) : Prop :=
  ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ) (k : ℝ),
    A.PosSemidef → B.IsHermitian → (A+B).PosSemidef → (A-B).PosSemidef → |k| ≤ 1 →
    |iteratedDeriv 3 (cubicRadialTrace A B k) 0| ≤
      C * iteratedDeriv 2 (cubicRadialTrace A B k) 0

/-- Five is precisely the least uniform constant, even though the pencils may be noncommuting. -/
theorem universal_constant_iff (C : ℝ) : UniversalCubicBound C ↔ 5 ≤ C := by
  constructor
  · intro h
    have hp : ((1 : Matrix (Fin 1) (Fin 1) ℂ) + -1).PosSemidef := by simpa using Matrix.PosSemidef.zero
    have hm : ((1 : Matrix (Fin 1) (Fin 1) ℂ) - -1).PosSemidef := by
      simpa only [sub_neg_eq_add] using
        (Matrix.PosSemidef.one.add Matrix.PosSemidef.one :
          ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 1).PosSemidef)
    have hh := h 1 1 (-1) 1 Matrix.PosSemidef.one (by simp) hp hm (by norm_num)
    obtain ⟨hd2,hd3⟩ := cubic_derivatives (1 : Matrix (Fin 1) (Fin 1) ℂ) (-1) 1
    norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.ofNat_apply] at hd2 hd3
    rw [hd2,hd3] at hh
    norm_num at hh
    linarith
  · intro hC m A B k hA hB hp hm hk
    obtain ⟨h2,h3⟩ := cubic_radial_compatibility A B k hA.isHermitian hB hp hm
    exact h3.trans (mul_le_mul_of_nonneg_right (by linarith : 1+4*|k| ≤ C) h2)

#print axioms cubic_derivatives
#print axioms cubic_radial_compatibility
#print axioms universal_constant_iff

end D5.S3.Quantum.Matrix.HsfCubicRadial

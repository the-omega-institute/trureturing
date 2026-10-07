/- GID: D5/S3/Quantum/Analysis/PhysicalHermiteTests
   generality: I
   mirror-B: D5/B/S3/Quantum/Analysis/PhysicalHermiteTests
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical tensor Hermite functions have actual Schwartz eigenaction and compact graph tests. -/

/-
Adapted from Leonardo Pedro, Timepiece at
61595bca99e3b8d8b8df51a2c3043b64597e24f9,
BookProof/ChapterHermiteFunctions.lean, the Hermite differential equation
and polynomial times half-Gaussian derivative calculations.
Copyright 2026 Leonardo Pedro
Released under Apache 2.0 license; the complete root grant and terms are in
 docs/reports/oscillator-suppliers/timepiece-LICENSE.txt.
Changes: retain the scalar calculations inside the physical tensor proof;
construct normalized anisotropic complex Schwartz functions, differentiate
actual coordinates, and obtain simultaneous compact-test L2 limits.
The authenticated Timepiece tree has no NOTICE-named file.
Retirement: replace this source adaptation by an equivalent directly
applicable construction at this repository's own pinned Mathlib revision
when the physical graph consumers validate.
GaussianSchwartz and SchwartzCutoffGraph supply the Gaussian and cutoff
constructions with their preserved PhysLean and W21 license/NOTICE chains.
-/

import D5.S3.Quantum.Analysis.GaussianSchwartz
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import D5.S3.Quantum.Analysis.SchwartzCutoffGraph
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

open SchwartzMap MeasureTheory LineDeriv Filter Polynomial
open scoped Topology LineDeriv ENNReal
noncomputable section
namespace D5.S3.Quantum.Analysis.PhysicalHermiteTests
open D5.S3.Quantum.Analysis.GaussianSchwartz
open D5.S3.Quantum.Analysis.SchwartzCutoffGraph

def width (h : ℝ) (m w : ℝ) := Real.sqrt (h / (m * w))
def value (d : ℕ) (h : ℝ) (m w : Fin d → ℝ) (n : Fin d → ℕ) (x : Space d) : ℂ :=
  ((∏ j, ((hermite (n j)).map (Int.castRingHom ℝ)).eval
    (Real.sqrt 2 / width h (m j) (w j) * x j) *
    Real.exp (-x j^2 / (2 * width h (m j) (w j)^2)) /
    Real.sqrt (Real.sqrt Real.pi * width h (m j) (w j) * (n j).factorial) : ℝ) : ℂ)

set_option backward.isDefEq.respectTransparency false in
-- Tensor products, two coordinate derivatives and complex transport elaborate together.
set_option maxHeartbeats 800000 in
theorem physical_hermite_tests (d : ℕ) (h : ℝ) (m w : Fin d → ℝ) (hh : 0 < h)
    (hm : ∀ j, 0 < m j) (hw : ∀ j, 0 < w j) (n : Fin d → ℕ) :
    ∃ φ : 𝓢(Space d, ℂ), (∀ x, φ x = value d h m w n x) ∧
      differential d (fun j => h^2 / (2*m j)) (fun j => m j * w j^2 / 2) φ =
        (∑ j, h*w j*((n j : ℝ)+1/2)) • φ ∧
      ∃ ψ : ℕ → 𝓢(Space d, ℂ), (∀ N, HasCompactSupport (ψ N)) ∧
        Tendsto (fun N => (ψ N).toLp 2 volume) atTop (𝓝 (φ.toLp 2 volume)) ∧
        Tendsto (fun N => (differential d (fun j => h^2/(2*m j))
          (fun j => m j*w j^2/2) (ψ N)).toLp 2 volume) atTop
          (𝓝 ((∑ j, h*w j*((n j : ℝ)+1/2)) • φ.toLp 2 volume)) := by
  classical
  let ell : Fin d → ℝ := fun j => width h (m j) (w j)
  let r : Fin d → ℝ := fun j => (ell j)⁻¹
  let s : Fin d → ℝ := fun j => Real.sqrt 2 / ell j
  let ν : Fin d → ℝ := fun j =>
    (Real.sqrt (Real.sqrt Real.pi * ell j * (n j).factorial))⁻¹
  let P : Fin d → Polynomial ℝ := fun j => (hermite (n j)).map (Int.castRingHom ℝ)
  have hell (j : Fin d) : 0 < ell j := Real.sqrt_pos.mpr (div_pos hh (mul_pos (hm j) (hw j)))
  have hellsq (j : Fin d) : (ell j)^2 = h / (m j * w j) :=
    Real.sq_sqrt (le_of_lt (div_pos hh (mul_pos (hm j) (hw j))))
  let A : Space d ≃L[ℝ] Space d := (EuclideanSpace.equiv (Fin d) ℝ).trans
    ((ContinuousLinearEquiv.piCongrRight fun j =>
      (Units.mk0 (r j) (inv_ne_zero (hell j).ne')) • ContinuousLinearEquiv.refl ℝ ℝ).trans
      (EuclideanSpace.equiv (Fin d) ℝ).symm)
  have hA (x : Space d) (j : Fin d) : A x j = r j * x j := rfl
  obtain ⟨G, hG⟩ := exists_gaussian_schwartz (Space d)
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A G
  have hg (x : Space d) : g x = ∏ j, Real.exp (-(s j * x j)^2 / 4) := by
    change G (A x) = _
    rw [hG, EuclideanSpace.real_norm_sq_eq, ← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hA]
    dsimp [s, r]
    simp only [mul_pow, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  have hpoly (p : Polynomial ℝ) (j : Fin d) :
      (fun x : Space d => p.eval (s j * x j)).HasTemperateGrowth := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add, Pi.add_apply] using hp.fun_add hq
    | monomial k c =>
      have ht : (fun x : Space d => s j * x j).HasTemperateGrowth :=
        (Function.HasTemperateGrowth.const (s j)).mul (EuclideanSpace.proj j).hasTemperateGrowth
      simpa only [Polynomial.eval_monomial, Pi.mul_apply, Pi.pow_apply] using (Function.HasTemperateGrowth.const c).fun_mul (ht.pow k)
  have hprod (F : Fin d → Space d → ℝ) (hF : ∀ j, (F j).HasTemperateGrowth)
      (S : Finset (Fin d)) : (fun x => ∏ j ∈ S, F j x).HasTemperateGrowth := by
    induction S using Finset.induction_on with
    | empty => simpa using Function.HasTemperateGrowth.const (1 : ℝ)
    | insert j S hj ih => simpa only [Finset.prod_insert hj, Pi.mul_apply] using (hF j).fun_mul ih
  have hweight (p : Fin d → Polynomial ℝ) :
      (fun x : Space d => ∏ j, ν j * (p j).eval (s j*x j)).HasTemperateGrowth :=
    hprod _ (fun j => (Function.HasTemperateGrowth.const (ν j)).mul (hpoly (p j) j)) Finset.univ
  let Φ (p : Fin d → Polynomial ℝ) : 𝓢(Space d, ℂ) :=
    (SchwartzMap.smulLeftCLM ℝ (fun x : Space d => ∏ j, ν j * (p j).eval (s j*x j)) g).postcompCLM
      Complex.ofRealCLM
  let φ := Φ P
  let B (p : Polynomial ℝ) (u : ℝ) := p.eval u * Real.exp (-u^2/4)
  let Q (p : Polynomial ℝ) := derivative p - C (1/2 : ℝ) * (X*p)
  let F (p : Fin d → Polynomial ℝ) (x : Space d) := ∏ j, ν j * B (p j) (s j*x j)
  have hΦ (p : Fin d → Polynomial ℝ) (x : Space d) : Φ p x = (F p x : ℂ) := by
    simp only [Φ, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
      SchwartzMap.smulLeftCLM_apply_apply (hweight p), hg, smul_eq_mul, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    simp [F, B, mul_assoc]
  have hφ (x : Space d) : φ x = (F P x : ℂ) := hΦ P x
  have hval (x : Space d) : φ x = value d h m w n x := by
    rw [hφ]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    change ν j * B (P j) (s j*x j) = _
    have hg' : -(s j*x j)^2/4 = -x j^2/(2*(ell j)^2) := by
      dsimp [s]
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
      field_simp [(hell j).ne']
      <;> ring
    dsimp [B]
    rw [hg']
    dsimp [ν, P, s, ell, value]
    ring
  have hB (p : Polynomial ℝ) (u : ℝ) : HasDerivAt (B p) (B (Q p) u) u := by
    have hg' : HasDerivAt (fun t : ℝ => Real.exp (-t^2/4))
        (-(u/2)*Real.exp (-u^2/4)) u := by
      convert (((hasDerivAt_pow 2 u).neg).div_const 4).exp using 1 <;> simp <;> ring
    convert (p.hasDerivAt u).mul hg' using 1 <;>
      first | rfl | (simp only [B, Q, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]; ring)
  have hsplit (p : Fin d → Polynomial ℝ) (j : Fin d) (x : Space d) :
      F p x = (∏ i ∈ Finset.univ.erase j, ν i * B (p i) (s i*x i)) *
        (ν j * B (p j) (s j*x j)) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
  have hline (p : Fin d → Polynomial ℝ) (j : Fin d) (x : Space d) :
      HasLineDerivAt ℝ (F p) (s j * F (Function.update p j (Q (p j))) x) x
        ((EuclideanSpace.basisFun (Fin d) ℝ) j) := by
    let Cx := ∏ i ∈ Finset.univ.erase j, ν i * B (p i) (s i*x i)
    have hpath : (fun t : ℝ => F p (x+t • (EuclideanSpace.basisFun (Fin d) ℝ) j)) =
        fun t => Cx * (ν j * B (p j) (s j*(x j+t))) := by
      funext t
      rw [hsplit]
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        simp [EuclideanSpace.basisFun_apply, hij]
      · simp [EuclideanSpace.basisFun_apply]
    change HasDerivAt _ _ 0
    rw [hpath]
    have ht : HasDerivAt (fun t : ℝ => s j*(x j+t)) (s j) 0 :=
      by simpa using ((hasDerivAt_id 0).const_add (x j)).const_mul (s j)
    have hcomp := (hB (p j) (s j*(x j+0))).comp 0 ht
    convert (hcomp.const_mul (ν j)).const_mul Cx using 1 <;> try rfl
    rw [hsplit]
    have hp : (∏ i ∈ Finset.univ.erase j, ν i * B ((Function.update p j (Q (p j))) i) (s i*x i)) = Cx := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
    rw [hp, Function.update_self]
    ring
  have hfirst (p : Fin d → Polynomial ℝ) (j : Fin d) (x : Space d) :
      (∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j} (Φ p)) x =
        ((s j * F (Function.update p j (Q (p j))) x : ℝ) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply]
    have h := hline p j x
    change HasDerivAt _ _ 0 at h
    have h' := h.ofReal_comp
    have hf : (Φ p : Space d → ℂ) = fun x => (F p x : ℂ) := funext (hΦ p)
    rw [hf]
    exact (show HasLineDerivAt ℝ (fun x : Space d => (F p x : ℂ))
      ((s j * F (Function.update p j (Q (p j))) x : ℝ) : ℂ) x
      ((EuclideanSpace.basisFun (Fin d) ℝ) j) from h').lineDeriv
  have hfirstMap (p : Fin d → Polynomial ℝ) (j : Fin d) :
      ∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j} (Φ p) =
        s j • Φ (Function.update p j (Q (p j))) := by
    ext x
    rw [hfirst, SchwartzMap.smul_apply, hΦ]
    simp [Complex.real_smul]
  have hsecond (j : Fin d) (x : Space d) :
      (∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j}
        (∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j} φ)) x =
        ((s j^2 * F (Function.update P j (Q (Q (P j)))) x : ℝ) : ℂ) := by
    change (∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j}
      (∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j} (Φ P))) x = _
    rw [hfirstMap, lineDerivOp_smul, hfirstMap]
    simp only [Function.update_self, Function.update_idem, SchwartzMap.smul_apply, hΦ,
      smul_smul, smul_eq_mul, Complex.real_smul, ← Complex.ofReal_mul, pow_two, mul_assoc]
    rw [Function.update_self]
  have hode (j : Fin d) : derivative (derivative (P j)) - X * derivative (P j) +
      C (n j : ℝ) * P j = 0 := by
    have : derivative ((hermite (n j + 1)).map (Int.castRingHom ℝ)) =
        C ((n j : ℝ) + 1) * (hermite (n j)).map (Int.castRingHom ℝ) := by
      have : derivative (hermite (n j + 1)) =
          C (n j + 1 : ℤ) * hermite (n j) := by
        apply Polynomial.ext
        intro k
        rw [Polynomial.coeff_derivative, Polynomial.coeff_C_mul]
        by_cases hk : n j < k
        · rw [Polynomial.coeff_hermite_of_lt (show n j + 1 < k + 1 by omega),
            Polynomial.coeff_hermite_of_lt hk]
          ring
        · by_cases hp : Even (n j + k)
          · have : Even ((n j + 1) + (k + 1)) := by
              rcases hp with ⟨m, hm⟩
              refine ⟨m + 1, ?_⟩
              omega
            rw [Polynomial.coeff_hermite_of_even_add this,
              Polynomial.coeff_hermite_of_even_add hp,
              (show n j + 1 - (k + 1) = n j - k by omega)]
            let A : ℤ := (-1 : ℤ) ^ ((n j - k) / 2) *
              ((n j - k - 1).doubleFactorial : ℤ)
            have : (n j + 1 : ℤ) * (Nat.choose (n j) k : ℤ) =
                (Nat.choose (n j + 1) (k + 1) : ℤ) * (k + 1 : ℤ) := by
              exact_mod_cast Nat.add_one_mul_choose_eq (n j) k
            calc
              _ = A * ((Nat.choose (n j + 1) (k + 1) : ℤ) * (k + 1 : ℤ)) := by
                dsimp [A]
                ring
              _ = A * ((n j + 1 : ℤ) * (Nat.choose (n j) k : ℤ)) := by rw [← this]
              _ = _ := by
                dsimp [A]
                ring
          · have : ¬ Even ((n j + 1) + (k + 1)) := by
              rintro ⟨m, hm⟩
              apply hp
              refine ⟨m - 1, ?_⟩
              omega
            rw [Polynomial.coeff_hermite (n j + 1) (k + 1),
              Polynomial.coeff_hermite (n j) k, if_neg this, if_neg hp]
            ring
      have := congrArg (fun p : Polynomial ℤ => p.map (Int.castRingHom ℝ)) this
      rw [Polynomial.derivative_map]
      simpa only [Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom,
        Int.cast_add, Int.cast_natCast, Int.cast_one] using this
    have hrec : ((hermite (n j+1)).map (Int.castRingHom ℝ)) =
        X * P j - derivative (P j) := by simp [P, Polynomial.hermite_succ, Polynomial.derivative_map]
    rw [hrec, derivative_sub, derivative_mul, derivative_X] at this
    have hC : (C ((n j : ℝ)+1) : Polynomial ℝ) = C (n j : ℝ)+1 := by rw [map_add, map_one]
    rw [hC] at this
    linear_combination -this
  have hos (j : Fin d) (u : ℝ) :
      -B (Q (Q (P j))) u + u^2/4*B (P j) u = ((n j : ℝ)+1/2)*B (P j) u := by
    have ht := congrArg (Polynomial.eval u) (hode j)
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero] at ht
    dsimp [B, Q]
    simp only [derivative_sub, derivative_C_mul, derivative_mul, derivative_X,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, derivative_C, zero_mul, Polynomial.eval_zero]
    linear_combination (-Real.exp (-u^2/4))*ht
  have hs (j : Fin d) : (s j)^2 = 2*m j*w j/h := by
    dsimp [s]
    rw [div_pow, Real.sq_sqrt (by norm_num), hellsq]
    field_simp
  have ha (j : Fin d) : (h^2/(2*m j))*(s j)^2 = h*w j := by
    rw [hs]
    field_simp [hh.ne', (hm j).ne']
    <;> ring
  have hb (j : Fin d) : m j*w j^2/2 = h*w j*(s j)^2/4 := by
    rw [hs]
    field_simp [hh.ne', (hm j).ne']
    <;> ring
  have hreplace (j : Fin d) (p : Polynomial ℝ) (x : Space d) :
      F (Function.update P j p) x =
        (∏ i ∈ Finset.univ.erase j, ν i * B (P i) (s i*x i))*(ν j*B p (s j*x j)) := by
    rw [hsplit, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have hphysical (j : Fin d) (x : Space d) :
      -(h^2/(2*m j))*(s j)^2*F (Function.update P j (Q (Q (P j)))) x +
        (m j*w j^2/2)*x j^2*F P x = h*w j*((n j : ℝ)+1/2)*F P x := by
    rw [hreplace, hsplit P j x, neg_mul (h^2/(2*m j)) ((s j)^2), ha, hb]
    linear_combination
      (h*w j*(∏ i ∈ Finset.univ.erase j, ν i * B (P i) (s i*x i))*ν j) * hos j (s j*x j)
  have heigen : differential d (fun j => h^2/(2*m j)) (fun j => m j*w j^2/2) φ =
      (∑ j, h*w j*((n j : ℝ)+1/2)) • φ := by
    ext x
    have ht (j : Fin d) : (fun x : Space d => x j^2).HasTemperateGrowth :=
      (EuclideanSpace.proj j).hasTemperateGrowth.pow 2
    simp only [differential, SchwartzMap.sum_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply,
      hsecond, SchwartzMap.smulLeftCLM_apply_apply (ht _), hφ, smul_eq_mul]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hc := congrArg Complex.ofReal (hphysical j x)
    push_cast at hc
    push_cast
    linear_combination hc
  refine ⟨φ, hval, heigen, ?_⟩
  let c : ContDiffBump (0 : Space d) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ := c.hasCompactSupport.toSchwartzMap c.contDiff
  have hc : HasCompactSupport χ := c.hasCompactSupport
  have hz : χ 0 = 1 := c.one_of_mem_closedBall (by simp [c])
  have hbχ : ∀ x, ‖χ x‖ ≤ 1 := fun x => by
    change ‖c x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg c.nonneg]
    exact c.le_one
  obtain ⟨ψ, _, hp, hv, hi⟩ := scaled_cutoff_graph d (fun j => h^2/(2*m j))
    (fun j => m j*w j^2/2) φ χ hc hz hbχ
  refine ⟨ψ, hp, hv, ?_⟩
  convert hi using 1
  rw [heigen]
  congr 1

#print axioms physical_hermite_tests
end D5.S3.Quantum.Analysis.PhysicalHermiteTests

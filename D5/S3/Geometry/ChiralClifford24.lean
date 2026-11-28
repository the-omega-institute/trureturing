/- GID: D5/S3/Geometry/ChiralClifford24
   generality: G
   mirror-B: none(waiver:covered-by-conformal-group-so24-in4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complex chiral blocks of a six-dimensional Clifford module can be computed over Gaussian integers before scalar extension. -/

import OmegaBuild.Commands
import D5.S3.Geometry.OrthogonalMatrixGenerators
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Omega original.

The complex chiral blocks of a six-dimensional Clifford module can be computed
over Gaussian integers before scalar extension. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix ComplexConjugate BigOperators

namespace OmegaMath.ChiralClifford24

abbrev GaussianMat4 := Matrix (Fin 4) (Fin 4) GaussianInt
abbrev DiracMatrix := Matrix (Fin 4) (Fin 4) ℂ
abbrev WeylPair := OrthogonalMatrixGenerators.OrderedPair (Fin 6)

def gaussianI : GaussianInt := ⟨0, 1⟩
def twistorGammaZ : Fin 4 → GaussianMat4 :=
  ![!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0],
    !![0, 0, 0, -gaussianI; 0, 0, gaussianI, 0;
       0, gaussianI, 0, 0; -gaussianI, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]]

def twistorGamma5Z : GaussianMat4 := diagonal ![-1, -1, 1, 1]

def metricTwistorZ (A B : Fin 6) : GaussianInt :=
  if A = B then (![1, -1, -1, -1, -1, 1] : Fin 6 → GaussianInt) A else 0

private def gammaChiralZ (last : GaussianInt) : Fin 6 → GaussianMat4 :=
  ![twistorGammaZ 0, twistorGammaZ 1, twistorGammaZ 2, twistorGammaZ 3,
    (-gaussianI) • twistorGamma5Z, last • 1]

def spinGeneratorZ (A B : Fin 6) : GaussianMat4 :=
  gammaChiralZ (-gaussianI) A * gammaChiralZ gaussianI B - metricTwistorZ A B • 1

set_option maxRecDepth 8192 in
theorem spinGeneratorZ_mem (A B : Fin 6) :
    (spinGeneratorZ A B)ᴴ * twistorGammaZ 0 +
      twistorGammaZ 0 * spinGeneratorZ A B = 0 ∧ (spinGeneratorZ A B).trace = 0 := by
  have h : ∀ a b, (spinGeneratorZ a b)ᴴ * twistorGammaZ 0 +
      twistorGammaZ 0 * spinGeneratorZ a b = 0 ∧ (spinGeneratorZ a b).trace = 0 := by decide
  exact h A B

private abbrev chiralLeft (A : Fin 6) := gammaChiralZ (-gaussianI) A
private abbrev chiralRight (A : Fin 6) := gammaChiralZ gaussianI A

set_option maxRecDepth 8192 in
private theorem chiral_left_relation (A B : Fin 6) :
    chiralLeft A * chiralRight B + chiralLeft B * chiralRight A =
      (2 * metricTwistorZ A B) • (1 : GaussianMat4) := by
  have h : ∀ a b, chiralLeft a * chiralRight b + chiralLeft b * chiralRight a =
      (2 * metricTwistorZ a b) • (1 : GaussianMat4) := by decide
  exact h A B

set_option maxRecDepth 8192 in
private theorem chiral_right_relation (A B : Fin 6) :
    chiralRight A * chiralLeft B + chiralRight B * chiralLeft A =
      (2 * metricTwistorZ A B) • (1 : GaussianMat4) := by
  have h : ∀ a b, chiralRight a * chiralLeft b + chiralRight b * chiralLeft a =
      (2 * metricTwistorZ a b) • (1 : GaussianMat4) := by decide
  exact h A B

theorem spinGeneratorZ_bracket (A B C D : Fin 6) :
    spinGeneratorZ A B * spinGeneratorZ C D - spinGeneratorZ C D * spinGeneratorZ A B =
      (2 : GaussianInt) • (metricTwistorZ B C • spinGeneratorZ A D -
        metricTwistorZ A C • spinGeneratorZ B D - metricTwistorZ B D • spinGeneratorZ A C +
        metricTwistorZ A D • spinGeneratorZ B C) := by
  let W (a b : Fin 6) := chiralLeft a * chiralRight b
  let t (a b : Fin 6) := 2 * metricTwistorZ a b
  have swap (a b : Fin 6) : W a b = t a b • 1 - W b a :=
    eq_sub_of_add_eq (chiral_left_relation a b)
  have product (a b c d : Fin 6) :
      W a b * W c d = t b c • W a d - W a c * W b d := by
    have middle := eq_sub_of_add_eq (chiral_right_relation b c)
    calc
      W a b * W c d = chiralLeft a * (chiralRight b * chiralLeft c) * chiralRight d := by
        simp only [W, mul_assoc]
      _ = t b c • W a d - W a c * W b d := by
        rw [middle]
        simp only [W, t, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, mul_assoc]
  change (W A B - _ • (1 : GaussianMat4)) * (W C D - _ • (1 : GaussianMat4)) -
    (W C D - _ • (1 : GaussianMat4)) * (W A B - _ • (1 : GaussianMat4)) = _
  calc
    _ = W A B * W C D - W C D * W A B := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.one_mul, smul_sub, smul_smul]
      module
    _ = _ := by
      have hmetric (a b : Fin 6) : metricTwistorZ a b = metricTwistorZ b a := by
        by_cases h : a = b
        · subst b
          rfl
        · simp [metricTwistorZ, h, Ne.symm h]
      rw [product A B C D, product C D A B, swap C A, swap D B, swap C B]
      simp only [W, spinGeneratorZ, t, hmetric D A, hmetric C A,
        hmetric D B, hmetric C B, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_sub, smul_add, smul_smul]
      module

def twistorFrameZ : Option (OrthogonalMatrixGenerators.OrderedPair (Fin 6)) → GaussianMat4
  | none => 1
  | some p => spinGeneratorZ p.val.1 p.val.2

set_option maxRecDepth 8192 in
theorem spinGeneratorZ_swap (A B : Fin 6) : spinGeneratorZ B A = -spinGeneratorZ A B := by
  have h : ∀ a b, spinGeneratorZ b a = -spinGeneratorZ a b := by decide
  exact h A B

theorem spinGeneratorZ_diag (A : Fin 6) : spinGeneratorZ A A = 0 := by
  have h : ∀ a, spinGeneratorZ a a = 0 := by decide
  exact h A

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem twistorFrameZ_orthogonal (p q : Option (OrthogonalMatrixGenerators.OrderedPair (Fin 6))) :
    ((twistorFrameZ p)ᴴ * twistorFrameZ q).trace = if p = q then 4 else 0 := by
  have h : ∀ p q : Option (OrthogonalMatrixGenerators.OrderedPair (Fin 6)),
      ((twistorFrameZ p)ᴴ * twistorFrameZ q).trace = if p = q then 4 else 0 := by decide
  exact h p q

private abbrev spaceTime (μ : Fin 4) : Fin 6 := μ.castSucc.castSucc

set_option maxRecDepth 8192 in
/-- The doubled spin generators in Lorentz, chiral and dilation coordinates. -/
theorem spinGeneratorZ_conformal (μ ν : Fin 4) :
    (2 : GaussianInt) • spinGeneratorZ (spaceTime μ) (spaceTime ν) =
      twistorGammaZ μ * twistorGammaZ ν - twistorGammaZ ν * twistorGammaZ μ ∧
    spinGeneratorZ 4 5 = twistorGamma5Z ∧
    spinGeneratorZ (spaceTime μ) 4 + spinGeneratorZ (spaceTime μ) 5 =
      gaussianI • (twistorGammaZ μ * (1 - twistorGamma5Z)) ∧
    spinGeneratorZ (spaceTime μ) 4 - spinGeneratorZ (spaceTime μ) 5 =
      (-gaussianI) • (twistorGammaZ μ * (1 + twistorGamma5Z)) := by
  have h : ∀ μ ν : Fin 4,
      (2 : GaussianInt) • spinGeneratorZ (spaceTime μ) (spaceTime ν) =
        twistorGammaZ μ * twistorGammaZ ν - twistorGammaZ ν * twistorGammaZ μ ∧
      spinGeneratorZ 4 5 = twistorGamma5Z ∧
      spinGeneratorZ (spaceTime μ) 4 + spinGeneratorZ (spaceTime μ) 5 =
        gaussianI • (twistorGammaZ μ * (1 - twistorGamma5Z)) ∧
      spinGeneratorZ (spaceTime μ) 4 - spinGeneratorZ (spaceTime μ) 5 =
        (-gaussianI) • (twistorGammaZ μ * (1 + twistorGamma5Z)) := by decide
  exact h μ ν

def toComplexMatrix : GaussianMat4 →+* DiracMatrix := GaussianInt.toComplex.mapMatrix

theorem toComplexMatrix_gaussian_smul (z : GaussianInt) (X : GaussianMat4) :
    toComplexMatrix (z • X) = (z : ℂ) • toComplexMatrix X := by
  ext i j
  exact map_mul GaussianInt.toComplex _ _

private theorem toComplexMatrix_dagger (X : GaussianMat4) :
    toComplexMatrix Xᴴ = (toComplexMatrix X)ᴴ := by
  ext i j
  exact GaussianInt.toComplex_star _

private theorem toComplexMatrix_trace (X : GaussianMat4) :
    ((X.trace : GaussianInt) : ℂ) = (toComplexMatrix X).trace :=
  map_sum GaussianInt.toComplex _ _

theorem gaussianI_cast : (gaussianI : ℂ) = Complex.I := by
  simp [gaussianI, GaussianInt.toComplex_def']

def diracTime : DiracMatrix := toComplexMatrix (twistorGammaZ 0)

private theorem diracTime_def : diracTime = toComplexMatrix (twistorGammaZ 0) := rfl

def spinGenerator (A B : Fin 6) : DiracMatrix :=
  (1 / 2 : ℂ) • toComplexMatrix (spinGeneratorZ A B)

/-- Trace-free endomorphisms that are skew-adjoint for the Dirac Hermitian form. -/
def DiracSkewTraceFree (X : DiracMatrix) : Prop :=
  Xᴴ * diracTime + diracTime * X = 0 ∧ X.trace = 0

theorem spinGenerator_mem (A B : Fin 6) : DiracSkewTraceFree (spinGenerator A B) := by
  obtain ⟨hs, ht⟩ := spinGeneratorZ_mem A B
  constructor
  · have hz := congrArg toComplexMatrix hs
    simp only [map_add, map_mul, map_zero, toComplexMatrix_dagger, ← diracTime_def] at hz
    simp [spinGenerator, Matrix.conjTranspose_smul, ← smul_add, hz]
  · rw [spinGenerator, Matrix.trace_smul, ← toComplexMatrix_trace, ht,
      GaussianInt.toComplex_zero, smul_zero]

theorem mat4_real_smul (r : ℝ) (M : DiracMatrix) : r • M = (r : ℂ) • M := by
  ext i j
  exact Complex.real_smul

def diracSkewSubspace : Submodule ℝ DiracMatrix where
  carrier := {X | DiracSkewTraceFree X}
  zero_mem' := by simp [DiracSkewTraceFree]
  add_mem' := by
    intro X Y hX hY
    change DiracSkewTraceFree X at hX
    change DiracSkewTraceFree Y at hY
    constructor
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm,
        hX.1, hY.1, add_zero]
    · rw [Matrix.trace_add, hX.2, hY.2, add_zero]
  smul_mem' := by
    intro r X hX
    change DiracSkewTraceFree X at hX
    constructor
    · rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
        ← smul_add, hX.1, smul_zero]
    · rw [Matrix.trace_smul, hX.2, smul_zero]

private def twistorFrame (p : Option WeylPair) : DiracMatrix :=
  toComplexMatrix (twistorFrameZ p)

private theorem twistorFrame_orthogonal (p q : Option WeylPair) :
    ((twistorFrame p)ᴴ * twistorFrame q).trace = if p = q then 4 else 0 := by
  simpa only [toComplexMatrix_trace, map_mul, toComplexMatrix_dagger, twistorFrame,
    apply_ite GaussianInt.toComplex, map_ofNat, map_zero] using
    congrArg GaussianInt.toComplex (twistorFrameZ_orthogonal p q)

private theorem twistorFrame_independent : LinearIndependent ℂ twistorFrame := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  have h := congrArg (fun X : DiracMatrix => ((twistorFrame p)ᴴ * X).trace) hc
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    twistorFrame_orthogonal, smul_eq_mul, mul_ite, mul_zero,
    Matrix.trace_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  exact (mul_eq_zero.mp h).resolve_right (by norm_num)

theorem spinGenerator_independent :
    LinearIndependent ℂ (fun p : WeylPair => spinGenerator p.val.1 p.val.2) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  have h := Fintype.linearIndependent_iff.mp
    (twistorFrame_independent.comp (f := Option.some) (Option.some_injective _))
  exact (mul_eq_zero.mp (h (fun q => c q * (1 / 2 : ℂ)) (by
    simpa only [spinGenerator, twistorFrame, twistorFrameZ, smul_smul,
      Function.comp_apply] using hc) p)).resolve_right
    (by norm_num)

private def twistorComplexBasis : Module.Basis (Option WeylPair) ℂ DiracMatrix :=
  basisOfLinearIndependentOfCardEqFinrank twistorFrame_independent
    (by rw [Module.finrank_matrix, Module.finrank_self]; decide)

private theorem twistorComplexBasis_apply (p : Option WeylPair) :
    twistorComplexBasis p = twistorFrame p := by
  simp [twistorComplexBasis]

private theorem twistorFrame_skew (p : WeylPair) :
    (twistorFrame (some p))ᴴ * diracTime = -(diracTime * twistorFrame (some p)) := by
  have h := congrArg toComplexMatrix (spinGeneratorZ_mem p.val.1 p.val.2).1
  simp only [map_add, map_mul, map_zero, toComplexMatrix_dagger, ← diracTime_def] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem twistorFrame_trace (p : WeylPair) : (twistorFrame (some p)).trace = 0 := by
  rw [twistorFrame, twistorFrameZ, ← toComplexMatrix_trace,
    (spinGeneratorZ_mem p.val.1 p.val.2).2, GaussianInt.toComplex_zero]

private theorem diracTime_sq : diracTime * diracTime = 1 := by
  have h : twistorGammaZ 0 * twistorGammaZ 0 = 1 := by decide
  simpa only [map_mul, map_one, ← diracTime_def] using congrArg toComplexMatrix h

theorem twistor_su22_real_expansion (Y : DiracMatrix) (hY : DiracSkewTraceFree Y) :
    ∃ c : WeylPair → ℝ, ∑ p : WeylPair, c p • spinGenerator p.val.1 p.val.2 = Y := by
  let coeff := twistorComplexBasis.repr Y
  have hexpand : ∑ p : Option WeylPair, coeff p • twistorFrame p = Y := by
    simpa only [twistorComplexBasis_apply] using twistorComplexBasis.sum_repr Y
  have hnone : coeff none = 0 := by
    have h := congrArg (fun X : DiracMatrix => X.trace) hexpand
    change (∑ p : Option WeylPair, coeff p • twistorFrame p).trace = Y.trace at h
    rw [Fintype.sum_option, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum] at h
    have htrace : (twistorFrame none).trace = 4 := by
      simp [twistorFrame, twistorFrameZ, Matrix.trace_one]
    rw [htrace, hY.2] at h
    simp only [Matrix.trace_smul, twistorFrame_trace, smul_eq_mul, mul_zero,
      Finset.sum_const_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (by norm_num)
  have hs : ∑ p : WeylPair, coeff (some p) • twistorFrame (some p) = Y := by
    simpa only [Fintype.sum_option, hnone, zero_smul, zero_add] using hexpand
  have hskew := hY.1
  rw [← hs] at hskew
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, twistorFrame_skew] at hskew
  have hz := congrArg (fun X : DiracMatrix => diracTime * X) hskew
  simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul, Matrix.mul_neg, ← mul_assoc,
    diracTime_sq, Matrix.one_mul, Matrix.mul_zero, smul_neg] at hz
  have he : ∑ p : WeylPair,
      (star (coeff (some p)) - coeff (some p)) • twistorFrame (some p) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [Finset.sum_neg_distrib, ← sub_eq_neg_add] at hz
    exact sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
  have hr (p : WeylPair) : (↑(coeff (some p)).re : ℂ) = coeff (some p) := by
    apply Complex.conj_eq_iff_re.mp
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp
      (twistorFrame_independent.comp (f := Option.some) (Option.some_injective _))) _ he p)
  refine ⟨fun p => 2 * (coeff (some p)).re, ?_⟩
  rw [← hs]
  apply Finset.sum_congr rfl
  intro p _
  simp only [mat4_real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, hr, spinGenerator,
    smul_smul, twistorFrame, twistorFrameZ]
  congr 1
  ring

end OmegaMath.ChiralClifford24

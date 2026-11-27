/- GID: D5/S3/Quantum/Gauge/FiniteSpectralTripleSM
   generality: I
   mirror-B: D5/B/S3/Quantum/Gauge/FiniteSpectralTripleSM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite real spectral triple for one generation of Standard Model fermions. -/

import OmegaBuild.Commands
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import D5.S3.QuantumContext.ThreeAnchorGram
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix
open scoped Quaternion InnerProductSpace ComplexConjugate Kronecker
noncomputable section

namespace D5.S3.Quantum.Gauge.FiniteSpectralTripleSM

abbrev Weak := Fin 2
abbrev Color := Fin 3
abbrev W := Matrix Weak Weak ℂ
abbrev C := Matrix Color Color ℂ
abbrev A := ℂ × ℍ[ℝ] × C
/-- The weak matrix of a real quaternion. -/
def quatMatrix (h : ℍ[ℝ]) : W :=
  !![⟨h.re, h.imI⟩, ⟨h.imJ, h.imK⟩; ⟨-h.imJ, h.imK⟩, ⟨h.re, -h.imI⟩]
private theorem quat_one : quatMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMatrix]
private theorem quat_add (h k : ℍ[ℝ]) :
    quatMatrix (h + k) = quatMatrix h + quatMatrix k := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMatrix] <;> ring
private theorem quat_smul (r : ℝ) (h : ℍ[ℝ]) :
    quatMatrix (r • h) = r • quatMatrix h := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMatrix, mul_neg]
private theorem quat_mul (h k : ℍ[ℝ]) :
    quatMatrix (h * k) = quatMatrix h * quatMatrix k := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quatMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring
private theorem quat_star (h : ℍ[ℝ]) : quatMatrix (star h) = (quatMatrix h)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMatrix]
/-- The quaternion map preserves the real algebra operations and the involution. -/
def quatHom : ℍ[ℝ] →⋆ₐ[ℝ] W where
  toFun := quatMatrix
  map_one' := quat_one
  map_mul' := quat_mul
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMatrix]
  map_add' := quat_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, quat_smul, quat_one]
  map_star' := quat_star
theorem quatMatrix_injective : Function.Injective quatMatrix := by
  intro h k e
  exact Quaternion.ext h k
    (congrArg (fun M : W => (M 0 0).re) e) (congrArg (fun M : W => (M 0 0).im) e)
    (congrArg (fun M : W => (M 0 1).re) e) (congrArg (fun M : W => (M 0 1).im) e)
theorem quatMatrix_det (h : ℍ[ℝ]) : (quatMatrix h).det = Quaternion.normSq h := by
  rw [Quaternion.normSq_def']
  apply Complex.ext <;> simp [Matrix.det_fin_two, quatMatrix, Complex.mul_re, Complex.mul_im, pow_two] <;> ring
private theorem quat_norm (h : ℍ[ℝ]) :
    (quatMatrix h)ᴴ * quatMatrix h = (↑(Quaternion.normSq h) : ℂ) • (1 : W) := by
  rw [← quat_star, ← quat_mul, Quaternion.star_mul_self]
  change quatMatrix (algebraMap ℝ ℍ[ℝ] (Quaternion.normSq h)) = _
  rw [show quatMatrix (algebraMap ℝ ℍ[ℝ] (Quaternion.normSq h)) =
      algebraMap ℝ W (Quaternion.normSq h) from quatHom.commutes _]
  ext i j
  simp [Algebra.algebraMap_eq_smul_one, Complex.real_smul]
theorem quatMatrix_specialUnitary (U : W) :
    U ∈ unitary W ∧ U.det = 1 ↔ ∃ h : ℍ[ℝ], Quaternion.normSq h = 1 ∧ quatMatrix h = U := by
  constructor
  · rintro ⟨hu, hd⟩
    have he : Uᴴ = U.adjugate := by
      calc
        Uᴴ = Uᴴ * (U * U.adjugate) := by rw [Matrix.mul_adjugate, hd, one_smul, mul_one]
        _ = U.adjugate := by rw [← mul_assoc, ← Matrix.star_eq_conjTranspose, Unitary.star_mul_self_of_mem hu, one_mul]
    have ha := congrArg (fun M : W => M 0 0) he
    have hb := congrArg (fun M : W => M 1 0) he
    simp [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] at ha hb
    have hb' : -conj (U 0 1) = U 1 0 := neg_eq_iff_eq_neg.mpr hb
    let h : ℍ[ℝ] := ⟨(U 0 0).re, (U 0 0).im, (U 0 1).re, (U 0 1).im⟩
    have hh : quatMatrix h = U := by
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [quatMatrix, h, ← ha, ← hb']
    exact ⟨h, Complex.ofReal_injective (by rw [← quatMatrix_det, hh, hd, Complex.ofReal_one]), hh⟩
  · rintro ⟨h, hn, rfl⟩
    refine ⟨Unitary.mem_iff.mpr ⟨?_, ?_⟩, by simp [quatMatrix_det, hn]⟩
    · simp [Matrix.star_eq_conjTranspose, quat_norm, hn]
    · rw [Matrix.star_eq_conjTranspose, ← quat_star, ← quat_mul, Quaternion.self_mul_star, hn, Quaternion.coe_one, quat_one]
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (inner_eq_components)
open D5.S3.QuantumContext.ThreeAnchorGram
theorem quatMatrix_hs_inner (h k : ℍ[ℝ]) :
    ((quatMatrix h)ᴴ * quatMatrix k).trace.re / 2 = ⟪h, k⟫_ℝ := by
  simp [inner_eq_components, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, quatMatrix,
    Complex.mul_re]
  ring
/-- The three imaginary axes are independent in the normalized Hilbert–Schmidt metric. -/
theorem weak_generators_independent :
    LinearIndependent ℝ (![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 3 → ℍ[ℝ]) := by
  apply (three_anchor_gram_det_pos_iff _ _ _).mp
  norm_num [threeAnchorGram, Matrix.gram, Matrix.det_fin_three, inner_eq_components]

/-- Lepton coordinates, followed by the weak–color tensor product of quark coordinates. -/
abbrev Sector := Weak ⊕ (Weak × Color)
abbrev Particle := Sector ⊕ Sector
abbrev Fermion := Particle ⊕ Particle
abbrev Mat := Matrix Fermion Fermion ℂ
abbrev H := Fermion → ℂ
private abbrev S := Matrix Sector Sector ℂ
private abbrev P := Matrix Particle Particle ℂ
theorem fermion_dimension : Module.finrank ℂ H = 32 := by
  rw [Module.finrank_fintype_fun_eq_card]
  decide
private abbrev block {ι κ : Type} (x : Matrix ι ι ℂ) (y : Matrix κ κ ℂ) :=
  Matrix.fromBlocks x 0 0 y
private theorem blocks_sub {ι κ : Type} (a e : Matrix ι ι ℂ) (b f : Matrix ι κ ℂ)
    (c g : Matrix κ ι ℂ) (d h : Matrix κ κ ℂ) :
    fromBlocks a b c d - fromBlocks e f g h = fromBlocks (a-e) (b-f) (c-g) (d-h) := by
  ext i j
  cases i <;> cases j <;> rfl
private abbrev bar {ι κ : Type} (M : Matrix ι κ ℂ) := M.map (starRingEnd ℂ)
private theorem bar_mul {ι : Type} [Fintype ι] [DecidableEq ι] (x y : Matrix ι ι ℂ) :
    bar (x * y) = bar x * bar y := map_mul (starRingEnd ℂ).mapMatrix x y
private theorem bar_kron {ι κ : Type} (x : Matrix ι ι ℂ) (y : Matrix κ κ ℂ) :
    bar (x ⊗ₖ y) = bar x ⊗ₖ bar y := by
  ext i j
  exact map_mul (starRingEnd ℂ) _ _
private theorem bar_star {ι : Type} (x : Matrix ι ι ℂ) : bar xᴴ = (bar x)ᴴ := rfl
attribute [local simp] Matrix.fromBlocks_multiply Matrix.fromBlocks_conjTranspose
  Matrix.fromBlocks_one Matrix.fromBlocks_zero Matrix.fromBlocks_map
  Matrix.fromBlocks_inj Matrix.one_kronecker_one
  Matrix.conjTranspose_kronecker Matrix.zero_kronecker bar_kron bar_star
private def weakBlock (x z : W) : S := block x (z ⊗ₖ (1 : C))
private def colorBlock (z₀ : ℂ) (m : C) : S := block (z₀ • (1 : W)) ((1 : W) ⊗ₖ m)
private def scalarQuat (z : ℂ) : ℍ[ℝ] := ⟨z.re, z.im, 0, 0⟩
private def scalarWeak (z : ℂ) : W := diagonal ![z, conj z]
private theorem scalar_weak (z : ℂ) : scalarWeak z = quatMatrix (scalarQuat z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [scalarWeak, quatMatrix, scalarQuat]
private def particleRep (a : A) : P :=
  block (weakBlock (scalarWeak a.1) (scalarWeak a.1))
    (weakBlock (quatMatrix a.2.1) (quatMatrix a.2.1))
private def antiRep (a : A) : P := block (colorBlock a.1 a.2.2) (colorBlock a.1 a.2.2)
private def repMatrix (a : A) : Mat := block (particleRep a) (antiRep a)
private theorem scalarWeak_mul (z w : ℂ) : scalarWeak (z*w) = scalarWeak z * scalarWeak w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarWeak]
private theorem scalarWeak_add (z w : ℂ) : scalarWeak (z+w) = scalarWeak z + scalarWeak w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarWeak]
private theorem scalarWeak_smul (r : ℝ) (z : ℂ) : scalarWeak (r • z) = r • scalarWeak z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarWeak, Complex.real_smul]
private theorem scalarWeak_star (z : ℂ) : scalarWeak (star z) = (scalarWeak z)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarWeak]
private theorem scalarWeak_one : scalarWeak 1 = 1 := by
  rw [scalar_weak, ← quat_one]
  congr 1
private theorem scalarWeak_zero : scalarWeak 0 = 0 := by
  rw [scalar_weak]
  exact quatHom.map_zero

/-- The faithful left action of the real algebra on particle and antiparticle coordinates. -/
def rep : A →⋆ₐ[ℝ] Mat where
  toFun := repMatrix
  map_one' := by simp [repMatrix, antiRep, particleRep, weakBlock, colorBlock, scalarWeak_one, quat_one]
  map_zero' := by
    have hz : quatMatrix 0 = 0 := quatHom.map_zero
    simp [repMatrix, antiRep, particleRep, weakBlock, colorBlock, scalarWeak_zero, hz]
  map_add' a b := by
    simp [repMatrix, antiRep, particleRep, weakBlock, colorBlock, scalarWeak_add, quat_add,
      Matrix.fromBlocks_add, Matrix.add_kronecker, Matrix.kronecker_add, add_smul]
  map_mul' a b := by
    simp [repMatrix, antiRep, particleRep, weakBlock, colorBlock, scalarWeak_mul, quat_mul,
      ← Matrix.mul_kronecker_mul, Matrix.mul_smul, smul_smul, mul_comm]
  commutes' r := by
    have ho : repMatrix 1 = 1 := by
      simp [repMatrix, antiRep, particleRep, weakBlock, colorBlock, scalarWeak_one, quat_one]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← ho]
    change repMatrix ((r • (1 : ℂ)), r • (1 : ℍ[ℝ]), r • (1 : C)) = _
    have hr : scalarWeak (↑r) = r • scalarWeak 1 := by simpa using scalarWeak_smul r 1
    simp [repMatrix, antiRep, particleRep, weakBlock, colorBlock, hr, quat_smul,
      Matrix.fromBlocks_smul, Matrix.smul_kronecker, Matrix.kronecker_smul]
    have hs {ι κ : Type} [DecidableEq ι] [DecidableEq κ] :
        block (r • (1 : Matrix ι ι ℂ)) (r • (1 : Matrix κ κ ℂ)) = r • 1 := by
      simpa only [Matrix.fromBlocks_smul, smul_zero] using
        congrArg (fun M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ => r • M) (Matrix.fromBlocks_one (l := ι) (m := κ) (α := ℂ))
    rw [hs, hs]
  map_star' a := by
    change repMatrix (star a.1, star a.2.1, star a.2.2) = _
    have hs : scalarWeak (conj a.1) = (scalarWeak a.1)ᴴ := scalarWeak_star a.1
    simp [repMatrix, antiRep, particleRep, weakBlock, colorBlock, hs, quat_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul]
theorem rep_injective : Function.Injective rep := by
  intro a b hab
  change repMatrix a = repMatrix b at hab
  have hl := congrArg (fun M : Mat => M (.inr (.inl (.inl 0))) (.inr (.inl (.inl 0)))) hab
  have hq : quatMatrix a.2.1 = quatMatrix b.2.1 := by
    ext i j
    exact congrArg (fun M : Mat => M (.inl (.inr (.inl i))) (.inl (.inr (.inl j)))) hab
  exact Prod.ext (by simpa [repMatrix, antiRep, colorBlock] using hl)
    (Prod.ext (quatMatrix_injective hq) (by
      ext i j
      have hm := congrArg (fun M : Mat => M (.inr (.inl (.inr (0,i))))
        (.inr (.inl (.inr (0,j))))) hab
      simpa [repMatrix, antiRep, colorBlock, Matrix.kronecker_apply] using hm))

private def swap : Fermion ≃ Fermion := Equiv.sumComm Particle Particle
/-- Charge conjugation swaps particles with antiparticles and conjugates coordinates. -/
def J_F (v : H) : H := fun i => conj (v (swap i))
/-- Conjugation of a complex-linear operator by the real structure. -/
def j (T : Mat) : Mat := (bar T).submatrix swap swap
theorem jj (v : H) : J_F (J_F v) = v := by
  funext i
  cases i <;> simp [J_F, swap]
theorem realStructure_antiunitary (z : ℂ) (v w : H) :
    J_F (z • v + w) = conj z • J_F v + J_F w ∧
      (∑ i, conj (J_F v i) * J_F w i) = conj (∑ i, conj (v i) * w i) := by
  constructor
  · funext i
    simp [J_F]
  · simp only [J_F, map_sum, map_mul, Complex.conj_conj]
    exact swap.sum_comp (fun i => v i * conj (w i))
private theorem j_blocks (a b c d : P) :
    j (fromBlocks a b c d) = fromBlocks (bar d) (bar c) (bar b) (bar a) := by
  ext i j
  cases i <;> cases j <;> rfl
theorem realStructure_mulVec (T : Mat) (v : H) :
    J_F (T *ᵥ v) = j T *ᵥ J_F v := by
  funext i
  simp only [J_F, j, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.submatrix_apply,
    Matrix.map_apply]
  exact (swap.sum_comp (fun k => conj (T (swap i) k) * conj (v k))).symm
def opposite (a : A) : Mat := j (rep a)ᴴ
def comm (x y : Mat) : Mat := x * y - y * x
private theorem bar_smul_one {ι : Type} [DecidableEq ι] (z : ℂ) :
    bar (z • (1 : Matrix ι ι ℂ)) = conj z • 1 := by
  ext i j
  by_cases h : i = j <;> simp [h]
attribute [local simp] bar_smul_one Matrix.fromBlocks_add Matrix.fromBlocks_smul
  Matrix.fromBlocks_neg blocks_sub
theorem order_zero (a b : A) : comm (rep a) (opposite b) = 0 := by
  change repMatrix a * j (repMatrix b)ᴴ - j (repMatrix b)ᴴ * repMatrix a = 0
  rw [sub_eq_zero]
  simp [repMatrix, particleRep, antiRep, j_blocks, weakBlock, colorBlock,
    Matrix.conjTranspose_smul, ← Matrix.mul_kronecker_mul, Matrix.mul_smul]

structure Yukawa where
  nu : ℂ
  electron : ℂ
  up : ℂ
  down : ℂ
private def yL (y : Yukawa) : W := diagonal ![y.nu, y.electron]
private def yQ (y : Yukawa) : W := diagonal ![y.up, y.down]
private def yBlock (y : Yukawa) : S := weakBlock (yL y) (yQ y)
private def liftWeak (x : W) : S := weakBlock x x
private def off (x : S) : P := fromBlocks 0 xᴴ x 0
private def nuProjection : P := block (block (diagonal ![1, 0] : W) 0) 0
private theorem nu_star : nuProjectionᴴ = nuProjection := by
  simp [nuProjection, Matrix.diagonal_conjTranspose]
private theorem nu_bar : bar nuProjection = nuProjection := by
  simp [nuProjection, Matrix.diagonal_map]
/-- The total Higgs field multiplies the Dirac Yukawa block from the left. -/
def higgsDirac (y : Yukawa) (μ : ℂ) (h : ℍ[ℝ]) : Mat :=
  let d := off (liftWeak (quatMatrix h) * yBlock y)
  fromBlocks d (μ • nuProjection) (conj μ • nuProjection) (bar d)
/-- The unfluctuated Dirac operator, including the right-neutrino Majorana term. -/
def D_F (y : Yukawa) (μ : ℂ) : Mat := higgsDirac y μ 1
def γ_F : Mat := block (block (1 : S) (-1)) (block (-1 : S) 1)
private theorem bar_smul {ι : Type} (z : ℂ) (M : Matrix ι ι ℂ) :
    bar (z • M) = conj z • bar M := by
  ext i j
  exact map_mul (starRingEnd ℂ) _ _
theorem dirac_star (y : Yukawa) (μ : ℂ) : (D_F y μ)ᴴ = D_F y μ := by
  simp [D_F, higgsDirac, off, Matrix.conjTranspose_smul, nu_star]
theorem gamma_star : γ_Fᴴ = γ_F := by simp [γ_F]
theorem gamma_sq : γ_F * γ_F = 1 := by simp [γ_F]
theorem jd (y : Yukawa) (μ : ℂ) : j (D_F y μ) = D_F y μ := by
  simp [D_F, higgsDirac, j_blocks, bar_smul, nu_bar, Function.comp_def]
theorem jgamma : j γ_F = -γ_F := by simp [γ_F, j_blocks, Matrix.map_neg]
theorem dirac_odd (y : Yukawa) (μ : ℂ) : D_F y μ * γ_F + γ_F * D_F y μ = 0 := by
  simp [D_F, higgsDirac, γ_F, off, nuProjection]
theorem rep_even (a : A) : comm (rep a) γ_F = 0 := by
  change comm (repMatrix a) γ_F = 0
  simp [comm, repMatrix, particleRep, antiRep, γ_F]
private theorem nu_comm (a : A) :
    nuProjection * antiRep a = particleRep a * nuProjection ∧
      nuProjection * particleRep a = antiRep a * nuProjection := by
  simp [nuProjection, antiRep, particleRep, weakBlock, colorBlock, scalarWeak,
    Matrix.mul_smul, Matrix.diagonal_mul_diagonal]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp
private def upper (y : Yukawa) (x : W) : S := (yBlock y)ᴴ * liftWeak x
private def lower (y : Yukawa) (x : W) : S := liftWeak x * yBlock y
private theorem sub_kron (a b : W) : (a-b) ⊗ₖ (1 : C) = a ⊗ₖ 1 - b ⊗ₖ 1 := by
  ext i j
  simp [sub_mul]
private theorem diag_weak_comm (v : Weak → ℂ) (z : ℂ) :
    Commute (diagonal v) (scalarWeak z) := by
  simp [Commute, SemiconjBy, scalarWeak, diagonal_mul_diagonal, mul_comm]
private theorem comm_dirac (y : Yukawa) (μ : ℂ) (a : A) :
    comm (D_F y μ) (rep a) =
      block (fromBlocks 0 (upper y (quatMatrix a.2.1 - scalarWeak a.1))
        (lower y (scalarWeak a.1 - quatMatrix a.2.1)) 0) 0 := by
  have h := nu_comm a
  have hl := (diag_weak_comm (star ![y.nu, y.electron]) a.1).eq
  have hq := (diag_weak_comm (star ![y.up, y.down]) a.1).eq
  have hl' := (diag_weak_comm ![y.nu, y.electron] a.1).eq
  have hq' := (diag_weak_comm ![y.up, y.down] a.1).eq
  change comm (D_F y μ) (repMatrix a) = _
  simp [comm, D_F, higgsDirac, liftWeak, quat_one, off, repMatrix, h.1, h.2]
  simp [particleRep, antiRep, yBlock, yL, yQ, weakBlock, colorBlock, upper, lower, liftWeak,
    ← Matrix.mul_kronecker_mul, Matrix.mul_smul, Matrix.diagonal_map, ← hl, ← hq, hl', hq',
    ← Matrix.mul_sub, ← Matrix.sub_mul, ← sub_kron]
theorem order_one (y : Yukawa) (μ : ℂ) (a b : A) :
    comm (comm (D_F y μ) (rep a)) (opposite b) = 0 := by
  rw [comm_dirac, comm, sub_eq_zero]
  change _ * j (repMatrix b)ᴴ = j (repMatrix b)ᴴ * _
  simp [repMatrix, antiRep, j_blocks, upper, lower, liftWeak, yBlock, weakBlock,
    colorBlock, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_smul,
    Matrix.mul_smul]
theorem finite_spectral_triple_ko6 (y : Yukawa) (μ : ℂ) :
    Function.Injective rep ∧ (∀ v, J_F (J_F v) = v) ∧
      j (D_F y μ) = D_F y μ ∧ j γ_F = -γ_F ∧ γ_F * γ_F = 1 ∧ γ_Fᴴ = γ_F ∧
      D_F y μ * γ_F + γ_F * D_F y μ = 0 ∧ (D_F y μ)ᴴ = D_F y μ ∧
      (∀ a, comm (rep a) γ_F = 0) ∧ (∀ a b, comm (rep a) (opposite b) = 0) ∧
      (∀ a b, comm (comm (D_F y μ) (rep a)) (opposite b) = 0) :=
  ⟨rep_injective, jj, jd y μ, jgamma, gamma_sq, gamma_star, dirac_odd y μ,
    dirac_star y μ, rep_even, order_zero, order_one y μ⟩

def gaugeLift (a : A) : Mat := rep a * j (rep a)
def reducedCharacter (a : A) : ℂ := a.1 * a.2.2.det
private theorem unit_components (a : A) (h : a ∈ unitary A) :
    a.1 * conj a.1 = 1 ∧ Quaternion.normSq a.2.1 = 1 ∧ a.2.2 ∈ unitary C := by
  have h₁ := Unitary.star_mul_self_of_mem h
  have h₂ := Unitary.mul_star_self_of_mem h
  refine ⟨congrArg Prod.fst h₂, ?_, Unitary.mem_iff.mpr
    ⟨congrArg (fun b : A => b.2.2) h₁, congrArg (fun b : A => b.2.2) h₂⟩⟩
  have e : star a.2.1 * a.2.1 = 1 := congrArg (fun b : A => b.2.1) h₁
  rw [Quaternion.star_mul_self] at e
  exact congrArg QuaternionAlgebra.re e
theorem rep_det (a : A) (ha : a ∈ unitary A) : (rep a).det = reducedCharacter a ^ 4 := by
  obtain ⟨hz, hq, _⟩ := unit_components a ha
  change (repMatrix a).det = _
  simp [repMatrix, particleRep, antiRep, weakBlock, colorBlock, reducedCharacter, scalarWeak,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_kronecker, Matrix.det_diagonal,
    quatMatrix_det, hq, Fin.prod_univ_two, hz, mul_pow]
  ring
theorem gaugeLift_det (a : A) (ha : a ∈ unitary A) : (gaugeLift a).det = 1 := by
  have hu := congrArg Matrix.det (congrArg rep (Unitary.mul_star_self_of_mem ha))
  have h : rep (1 : A) = (1 : Mat) := rep.toAlgHom.map_one
  rw [map_mul, map_star, h, Matrix.det_mul, Matrix.star_eq_conjTranspose,
    Matrix.det_conjTranspose, Matrix.det_one] at hu
  rw [gaugeLift, Matrix.det_mul, j, Matrix.det_submatrix_equiv_self]
  change (rep a).det * ((starRingEnd ℂ).mapMatrix (rep a)).det = 1
  rwa [← RingHom.map_det (starRingEnd ℂ)]
theorem unimodularity_witness :
    ∃ a : A, a ∈ unitary A ∧ (rep a).det = 1 ∧ (gaugeLift a).det = 1 ∧
      reducedCharacter a ≠ 1 := by
  let a : A := (1, 1, diagonal ![Complex.I, 1, 1])
  have h : a ∈ unitary A := by
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩ <;>
      apply Prod.ext (by simp [a]) <;>
      apply Prod.ext (by simp [a]) <;>
      simp only [a, Prod.snd_mul, Prod.snd_star, Prod.snd_one,
        Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] <;>
      rw [← Matrix.diagonal_one] <;> congr 1 <;> funext i <;> fin_cases i <;> simp
  refine ⟨a, h, ?_, gaugeLift_det a h, ?_⟩
  · rw [rep_det a h]
    simp [a, reducedCharacter, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ]
  · simp [a, reducedCharacter, Matrix.det_diagonal, Fin.prod_univ_three]
    intro he
    have hm := congrArg Complex.im he
    norm_num at hm

/-- The six all-left-handed fermions, with right-handed particles replaced by conjugates. -/
inductive Species where | QL | uc | dc | LL | ec | nuc
def phaseExponent : Species → ℤ
  | .QL => 1
  | .uc => -4
  | .dc => 2
  | .LL => -3
  | .ec => 6
  | .nuc => 0
def hypercharge (s : Species) : ℚ := phaseExponent s / 6
theorem hypercharge_table :
    hypercharge .QL = 1/6 ∧ hypercharge .uc = -2/3 ∧ hypercharge .dc = 1/3 ∧
      hypercharge .LL = -1/2 ∧ hypercharge .ec = 1 ∧ hypercharge .nuc = 0 := by
  norm_num [hypercharge, phaseExponent]
theorem anomaly_cancel :
    2 * hypercharge .QL + hypercharge .uc + hypercharge .dc = 0 ∧
    3 * hypercharge .QL + hypercharge .LL = 0 ∧
    6 * hypercharge .QL + 3 * hypercharge .uc + 3 * hypercharge .dc +
      2 * hypercharge .LL + hypercharge .ec + hypercharge .nuc = 0 ∧
    6 * hypercharge .QL ^ 3 + 3 * hypercharge .uc ^ 3 + 3 * hypercharge .dc ^ 3 +
      2 * hypercharge .LL ^ 3 + hypercharge .ec ^ 3 + hypercharge .nuc ^ 3 = 0 := by
  norm_num [hypercharge, phaseExponent]

/-- The cover assigns the phases t³ and t⁻¹ to the scalar and color factors. -/
def cover (t : ℂ) (q : ℍ[ℝ]) (g : C) : A := (t ^ 3, q, t⁻¹ • g)
theorem cover_reduced (t : ℂ) (q : ℍ[ℝ]) (g : C) (ht : t ≠ 0) (hg : g.det = 1) :
    reducedCharacter (cover t q g) = 1 := by
  simp [reducedCharacter, cover, hg, inv_pow, pow_ne_zero _ ht]
theorem reduced_cover (u : A) (hu : u ∈ unitary A) (hc : reducedCharacter u = 1) :
    ∃ t g, t * conj t = 1 ∧ g ∈ unitary C ∧ g.det = 1 ∧ cover t u.2.1 g = u := by
  obtain ⟨hz, _, hm⟩ := unit_components u hu
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq u.1 (by decide : 0 < 3)
  have ht₀ : t * conj t = 1 := by
    have h : (t * conj t)^3 = 1 := by rw [mul_pow, ← map_pow, ht, hz]
    rw [Complex.mul_conj, ← Complex.ofReal_pow, ← Complex.ofReal_one] at h
    rw [Complex.mul_conj, (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) (by decide)).mp
      (Complex.ofReal_injective h), Complex.ofReal_one]
  have htn : t ≠ 0 := by intro e; simp [e] at ht₀
  refine ⟨t, t • u.2.2, ht₀, Unitary.mem_iff.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · simp [smul_smul, ht₀, Unitary.star_mul_self_of_mem hm]
  · simp [smul_smul, mul_comm (conj t) t, ht₀, Unitary.mul_star_self_of_mem hm]
  · simpa [reducedCharacter, ← ht] using hc
  · exact Prod.ext ht (Prod.ext rfl (by simp [cover, smul_smul, htn]))
private theorem lift_blocks (a : A) :
    gaugeLift a = block (particleRep a * bar (antiRep a))
      (antiRep a * bar (particleRep a)) := by
  change repMatrix a * j (repMatrix a) = _
  simp [repMatrix, j_blocks]
private theorem cover_color (t : ℂ) (g : C) (ht : t * conj t = 1) :
    bar (t⁻¹ • g) = t • bar g := by
  have e : conj t = t⁻¹ := eq_inv_of_mul_eq_one_right ht
  rw [bar_smul, map_inv₀, e, inv_inv]
/-- Phase blocks on the particle coordinates, in the order ν, e, u, d, L, Q. -/
theorem lift_particle_phase (t : ℂ) (q : ℍ[ℝ]) (g : C) (ht : t * conj t = 1) :
    (gaugeLift (cover t q g)).toBlocks₁₁ =
      block (block (diagonal ![1, (t ^ 6)⁻¹])
        (diagonal ![t ^ 4, (t ^ 2)⁻¹] ⊗ₖ bar g))
      (block ((t ^ 3)⁻¹ • quatMatrix q) (t • (quatMatrix q ⊗ₖ bar g))) := by
  have ht₀ : t ≠ 0 := by intro e; simp [e] at ht
  have e : conj t = t⁻¹ := eq_inv_of_mul_eq_one_right ht
  rw [lift_blocks, toBlocks_fromBlocks₁₁]
  simp [particleRep, antiRep, cover, weakBlock, colorBlock, cover_color t g ht,
    bar_smul, ← Matrix.mul_kronecker_mul, Matrix.mul_smul, scalarWeak, e,
    ← inv_pow, ← Matrix.kronecker_smul]
  constructor
  · rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp <;> field_simp
  · rw [Matrix.kronecker_smul, ← Matrix.smul_kronecker, ← Matrix.diagonal_smul]
    congr 2
    funext i
    fin_cases i <;> simp <;> field_simp
private theorem block_eq_one {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (x : Matrix ι ι ℂ) (y : Matrix κ κ ℂ) :
    block x y = 1 ↔ x = 1 ∧ y = 1 := by
  rw [← Matrix.fromBlocks_one (l := ι) (m := κ) (α := ℂ)]
  exact Matrix.fromBlocks_inj.trans (by simp)
/-- Exact equations for the kernel on U(1) × SU(2) × SU(3). -/
theorem cover_kernel_iff (t : ℂ) (q : ℍ[ℝ]) (g : C) (ht : t * conj t = 1) :
    gaugeLift (cover t q g) = 1 ↔
      t ^ 6 = 1 ∧ quatMatrix q = t ^ 3 • (1 : W) ∧ g = t ^ 4 • (1 : C) := by
  have h₀ : t ≠ 0 := by intro h; simp [h] at ht
  have e : conj t = t⁻¹ := eq_inv_of_mul_eq_one_right ht
  have hphase := lift_particle_phase t q g ht
  rw [lift_blocks, toBlocks_fromBlocks₁₁] at hphase
  have ha (a : A) : bar (particleRep a * bar (antiRep a)) = antiRep a * bar (particleRep a) := by
    have hm (x : P) : bar (bar x) = x := by ext i j; simp
    rw [bar_mul, hm]
    simp [particleRep, antiRep, weakBlock, colorBlock, ← Matrix.mul_kronecker_mul,
      Matrix.mul_smul]
  rw [lift_blocks, ← ha, hphase, block_eq_one]
  constructor
  · rintro ⟨hp, _⟩
    rw [block_eq_one, block_eq_one, block_eq_one] at hp
    obtain ⟨⟨hl, hu⟩, hq, _⟩ := hp
    have h₆ := congrArg (fun M : W => M 1 1) hl
    simp at h₆
    have he := congrArg (fun M : W => t ^ 3 • M) hq
    have hm : bar g = (t ^ 4)⁻¹ • (1 : C) := by
      ext i j
      have hi := congrArg (fun M : Matrix (Weak × Color) (Weak × Color) ℂ => M (0,i) (0,j)) hu
      change t ^ 4 * bar g i j = _ at hi
      apply (mul_left_cancel₀ (pow_ne_zero 4 h₀))
      simpa [Matrix.one_apply, mul_assoc, pow_ne_zero 4 h₀] using hi
    refine ⟨h₆, ?_, ?_⟩
    · simpa [smul_smul, pow_ne_zero 3 h₀] using he
    · simpa [map_inv₀, e, ← inv_pow, Function.comp_def] using congrArg bar hm
  · rintro ⟨h₆, hq, rfl⟩
    rw [hq]
    suffices hp : _ = (1 : P) from ⟨hp, by rw [hp]; simp⟩
    rw [block_eq_one, block_eq_one, block_eq_one]
    have hpow : t * ((t ^ 4)⁻¹ * t ^ 3) = 1 := by
      rw [mul_comm ((t ^ 4)⁻¹), ← mul_assoc, ← pow_succ', mul_inv_cancel₀ (pow_ne_zero 4 h₀)]
    have hpow' : (t ^ 2)⁻¹ * (t ^ 4)⁻¹ = 1 := by rw [← mul_inv, ← pow_add, h₆, inv_one]
    have hg : bar (t ^ 4 • (1 : C)) = (t ^ 4)⁻¹ • 1 := by simp [e, inv_pow]
    have hd : diagonal ![t ^ 4, (t ^ 2)⁻¹] ⊗ₖ bar (t ^ 4 • (1 : C)) = 1 := by
      rw [hg, Matrix.kronecker_smul, ← Matrix.smul_kronecker, ← Matrix.diagonal_smul, ← Matrix.one_kronecker_one]
      congr 2
      funext i
      fin_cases i <;> simp [hpow', pow_ne_zero 4 h₀, mul_comm]
    have hdiag : diagonal (![1, 1] : Weak → ℂ) = 1 := by
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hd]
    simp [hg, h₆, hdiag, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
      hpow, pow_ne_zero _ h₀]

/-- The real span of represented elementary one-forms. -/
def oneForms (y : Yukawa) (μ : ℂ) : Submodule ℝ Mat :=
  Submodule.span ℝ (Set.range fun p : A × A => rep p.1 * comm (D_F y μ) (rep p.2))
private def form (y : Yukawa) (h k : ℍ[ℝ]) : Mat :=
  block (fromBlocks 0 (upper y (quatMatrix h)) (lower y (quatMatrix k)) 0) 0
private theorem elementary_form (y : Yukawa) (μ : ℂ) (a b : A) :
    rep a * comm (D_F y μ) (rep b) =
      form y (scalarQuat a.1 * (b.2.1 - scalarQuat b.1))
        (a.2.1 * (scalarQuat b.1 - b.2.1)) := by
  have hs (h k : ℍ[ℝ]) : quatMatrix (h-k) = quatMatrix h - quatMatrix k := quatHom.map_sub h k
  have hl := (diag_weak_comm (star ![y.nu, y.electron]) a.1).eq
  have hq := (diag_weak_comm (star ![y.up, y.down]) a.1).eq
  rw [comm_dirac]
  change repMatrix a * _ = _
  simp [form, repMatrix, particleRep, upper, lower, weakBlock, liftWeak,
    yBlock, yL, yQ, quat_mul, hs, ← scalar_weak, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_assoc, ← hl, ← hq]
private theorem weak_add (a b c d : W) :
    weakBlock a b + weakBlock c d = weakBlock (a+c) (b+d) := by
  simp [weakBlock, Matrix.add_kronecker]
private theorem weak_smul (r : ℝ) (a b : W) :
    r • weakBlock a b = weakBlock (r • a) (r • b) := by
  simp [weakBlock, Matrix.smul_kronecker]
private theorem form_span (y : Yukawa) (μ : ℂ) {T : Mat} (hT : T ∈ oneForms y μ) :
    ∃ h k, T = form y h k := by
  have hz : quatMatrix 0 = 0 := quatHom.map_zero
  induction hT using Submodule.span_induction with
  | mem T ht =>
    obtain ⟨⟨a,b⟩, rfl⟩ := ht
    exact ⟨_, _, elementary_form y μ a b⟩
  | zero => exact ⟨0, 0, by simp [form, upper, lower, liftWeak, weakBlock, hz]⟩
  | add T U _ _ ihT ihU =>
    obtain ⟨h,k,rfl⟩ := ihT
    obtain ⟨h',k',rfl⟩ := ihU
    exact ⟨h+h', k+k', by simp [form, upper, lower, liftWeak, quat_add,
      ← weak_add, Matrix.mul_add, Matrix.add_mul]⟩
  | smul r T _ ih =>
    obtain ⟨h,k,rfl⟩ := ih
    exact ⟨r • h, r • k, by simp [form, upper, lower, liftWeak, quat_smul,
      ← weak_smul]⟩
def higgsForm (y : Yukawa) (h : ℍ[ℝ]) : Mat := block (off (lower y (quatMatrix h))) 0
theorem inner_fluctuation_iff (y : Yukawa) (μ : ℂ) (T : Mat) :
    T ∈ oneForms y μ ∧ Tᴴ = T ↔ ∃ h, T = higgsForm y h := by
  constructor
  · rintro ⟨hmem, hsa⟩
    obtain ⟨p,q,rfl⟩ := form_span y μ hmem
    simp [form] at hsa
    exact ⟨q, by simp [form, higgsForm, off, hsa.1.symm]⟩
  · rintro ⟨h,rfl⟩
    let r : A := (1,0,0)
    let s : A := (0,h,0)
    let s' : A := (0,star h,0)
    have h₁ : rep s * comm (D_F y μ) (rep r) ∈ oneForms y μ :=
      Submodule.subset_span ⟨(s,r), rfl⟩
    have h₂ : rep r * comm (D_F y μ) (rep s') ∈ oneForms y μ :=
      Submodule.subset_span ⟨(r,s'), rfl⟩
    refine ⟨?_, by simp [higgsForm, off]⟩
    have hmem := (oneForms y μ).add_mem h₁ h₂
    rw [elementary_form, elementary_form] at hmem
    have hz : quatMatrix 0 = 0 := quatHom.map_zero
    have h0 : scalarQuat 0 = 0 := rfl
    have h1 : scalarQuat 1 = 1 := rfl
    simpa [r, s, s', h0, h1, higgsForm, off, form, upper, lower, liftWeak, weakBlock,
      hz, quat_star, Matrix.conjTranspose_mul] using hmem
private theorem quat_column_injective (i : Weak) :
    Function.Injective (fun h : ℍ[ℝ] => fun j => quatMatrix h j i) := by
  intro h k e
  have e₀ := congrFun e 0
  have e₁ := congrFun e 1
  fin_cases i
  · exact Quaternion.ext h k (congrArg Complex.re e₀) (congrArg Complex.im e₀)
      (neg_injective (congrArg Complex.re e₁)) (congrArg Complex.im e₁)
  · exact Quaternion.ext h k (congrArg Complex.re e₁) (neg_injective (congrArg Complex.im e₁))
      (congrArg Complex.re e₀) (congrArg Complex.im e₀)
theorem higgsForm_injective (y : Yukawa)
    (hy : y.nu ≠ 0 ∨ y.electron ≠ 0 ∨ y.up ≠ 0 ∨ y.down ≠ 0) :
    Function.Injective (higgsForm y) := by
  intro h k he
  simp [higgsForm, off, lower, liftWeak, yBlock, weakBlock,
    ← Matrix.mul_kronecker_mul] at he
  have hl : ∀ i j, quatMatrix h j i * ![y.nu, y.electron] i =
      quatMatrix k j i * ![y.nu, y.electron] i := fun i j => by
    simpa [yL] using congrArg (fun M : W => M j i) he.2.1
  have hq : ∀ i j, quatMatrix h j i * ![y.up, y.down] i =
      quatMatrix k j i * ![y.up, y.down] i := fun i j => by
    simpa [yQ, Matrix.kronecker_apply] using congrArg
      (fun M : Matrix (Weak × Color) (Weak × Color) ℂ => M (j,0) (i,0)) he.2.2
  rcases hy with hy | hy | hy | hy
  · exact quat_column_injective 0 (funext fun j => mul_right_cancel₀ hy (hl 0 j))
  · exact quat_column_injective 1 (funext fun j => mul_right_cancel₀ hy (hl 1 j))
  · exact quat_column_injective 0 (funext fun j => mul_right_cancel₀ hy (hq 0 j))
  · exact quat_column_injective 1 (funext fun j => mul_right_cancel₀ hy (hq 1 j))
theorem higgsDirac_fluctuation (y : Yukawa) (μ : ℂ) (h : ℍ[ℝ]) :
    higgsDirac y μ (1 + h) = D_F y μ + higgsForm y h + j (higgsForm y h) := by
  simp [higgsDirac, D_F, higgsForm, off, lower, liftWeak, yBlock, weakBlock,
    j_blocks, quat_add, Matrix.add_kronecker, Matrix.add_mul, Matrix.map_add,
    ← Matrix.mul_kronecker_mul]

def moment (y : Yukawa) (n : ℕ) : ℝ :=
  Complex.normSq y.nu ^ n + Complex.normSq y.electron ^ n +
    3 * Complex.normSq y.up ^ n + 3 * Complex.normSq y.down ^ n
def potential (a b : ℝ) (y : Yukawa) (μ : ℂ) (x : ℝ) : ℝ :=
  4*a*moment y 2*x^2 - 4*(b*moment y 1 - 2*a*Complex.normSq μ*Complex.normSq y.nu)*x +
    2*a*(Complex.normSq μ)^2 - 2*b*Complex.normSq μ
theorem higgs_minimum_iff (a b : ℝ) (y : Yukawa) (μ : ℂ) (ha : 0 < a)
    (hy : 0 < moment y 2) :
    (∃ x > 0, ∀ z ≥ 0, potential a b y μ x ≤ potential a b y μ z) ↔
      2*a*Complex.normSq μ*Complex.normSq y.nu < b*moment y 1 := by
  let c := b*moment y 1 - 2*a*Complex.normSq μ*Complex.normSq y.nu
  let d := 2*a*moment y 2
  have hd : 0 < d := by dsimp [d]; positivity
  have diff (x z : ℝ) : potential a b y μ z - potential a b y μ x =
      2*d*(z-x)^2 + 4*(d*x-c)*(z-x) := by dsimp [potential, c, d]; ring
  constructor
  · rintro ⟨x, hx, h⟩
    have hz := sub_nonneg.mpr (h 0 le_rfl)
    rw [diff] at hz
    rw [← sub_pos]
    change 0 < c
    by_contra! hc
    nlinarith [mul_pos hd (sq_pos_of_pos hx), mul_nonpos_of_nonpos_of_nonneg hc hx.le]
  · intro hc
    have hc' : 0 < c := sub_pos.mpr hc
    refine ⟨c/d, div_pos hc' hd, fun z _ => sub_nonneg.mp ?_⟩
    have he : d * (c/d) = c := by field_simp
    rw [diff, he, sub_self, mul_zero, zero_mul, add_zero]
    positivity

private theorem trace_blocks {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : Matrix ι ι ℂ) (b : Matrix ι κ ℂ) (c : Matrix κ ι ℂ) (d : Matrix κ κ ℂ) :
    (fromBlocks a b c d).trace = a.trace + d.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
theorem trace_dirac_sq (y : Yukawa) (μ : ℂ) (h : ℍ[ℝ]) :
    let d := higgsDirac y μ h
    (d * d).trace = Complex.ofReal (4*Quaternion.normSq h*moment y 1 + 2*Complex.normSq μ) := by
  dsimp only
  simp [higgsDirac, off, liftWeak, yBlock, weakBlock, nuProjection, trace_blocks,
    Matrix.trace_add, Matrix.trace_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.mul_smul, Matrix.diagonal_mul_diagonal]
  apply Complex.ext <;>
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul_apply,
      dotProduct, Fin.sum_univ_two, yL, yQ, quatMatrix,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Quaternion.normSq_def',
      Complex.normSq_apply, moment, pow_two] <;> ring
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem trace_dirac_four (y : Yukawa) (μ : ℂ) (h : ℍ[ℝ]) :
    let d := higgsDirac y μ h
    ((d * d) * (d * d)).trace = Complex.ofReal (4*(Quaternion.normSq h)^2*moment y 2 +
      8*Complex.normSq μ*Quaternion.normSq h*Complex.normSq y.nu + 2*(Complex.normSq μ)^2) := by
  dsimp only
  simp [higgsDirac, off, liftWeak, yBlock, weakBlock, nuProjection, trace_blocks,
    Matrix.trace_add, Matrix.trace_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.mul_smul, Matrix.diagonal_mul_diagonal]
  apply Complex.ext <;>
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul_apply,
      dotProduct, Fin.sum_univ_two, yL, yQ, quatMatrix,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Quaternion.normSq_def',
      Complex.normSq_apply, moment, pow_two] <;> ring
theorem potential_eq_spectral_action (a b : ℝ) (y : Yukawa) (μ : ℂ) (h : ℍ[ℝ]) :
    let d := higgsDirac y μ h
    a * ((d*d)*(d*d)).trace.re - b * (d*d).trace.re = potential a b y μ (Quaternion.normSq h) := by
  dsimp only
  rw [trace_dirac_sq, trace_dirac_four]
  simp only [Complex.ofReal_re, potential]
  ring
theorem higgs_minimum_massless (a b : ℝ) (y : Yukawa) (ha : 0 < a) (hb : 0 < b)
    (hy : y.nu ≠ 0 ∨ y.electron ≠ 0 ∨ y.up ≠ 0 ∨ y.down ≠ 0) :
    ∃ x > 0, ∀ z ≥ 0, potential a b y 0 x ≤ potential a b y 0 z := by
  have hp {z : ℂ} (hz : z ≠ 0) : 0 < Complex.normSq z :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (mt Complex.normSq_eq_zero.mp hz))
  have hm (n : ℕ) : 0 < moment y n := by
    have hn (z : ℂ) : 0 ≤ Complex.normSq z ^ n := pow_nonneg (Complex.normSq_nonneg z) n
    unfold moment
    rcases hy with h | h | h | h <;> have hpos := pow_pos (hp h) n <;>
      linarith [hn y.nu, hn y.electron, hn y.up, hn y.down]
  apply (higgs_minimum_iff a b y 0 ha (hm 2)).mpr
  simpa using mul_pos hb (hm 1)
/-- The parameter group of the central kernel equations is cyclic of order six. -/
def sixthRoots : Multiplicative (ZMod 6) ≃* rootsOfUnity 6 ℂ := by
  exact cast (congrArg (fun n => Multiplicative (ZMod n) ≃* rootsOfUnity 6 ℂ)
    (Complex.card_rootsOfUnity 6)) (zmodCyclicMulEquiv (rootsOfUnity.isCyclic ℂ 6))
end D5.S3.Quantum.Gauge.FiniteSpectralTripleSM

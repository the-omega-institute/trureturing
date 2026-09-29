/- GID: D5/S3/Observer/HiddenFlow/FastSchurGradientEnergy
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/FastSchurGradientEnergy
   mirror-E: none(waiver:finite-dimensional-gradient-flow)
   anchors: []
   digest: The actual epsilon-scaled block gradient flow dissipates its quadratic energy. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Ring.Ext
import Mathlib.Tactic

namespace D5.S3.Observer.HiddenFlow.FastSchurGradientEnergy

open Matrix
open WithLp
open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder

noncomputable section

variable {p r : ℕ}

abbrev State (p r : ℕ) := EuclideanSpace ℝ (Fin p ⊕ Fin r)

local instance (priority := 10000) : AddCommGroup ℝ :=
  Real.normedCommRing.toAddCommGroup

local instance (priority := 10000) : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule

def blockL (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin p ⊕ Fin r) (Fin p ⊕ Fin r) ℝ :=
  Matrix.fromBlocks A B Bᵀ C

def weight (ε : ℝ) : Matrix (Fin p ⊕ Fin r) (Fin p ⊕ Fin r) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ : Fin p => 1) (fun _ : Fin r => ε⁻¹))

def generator (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ) (ε : ℝ) :
    Matrix (Fin p ⊕ Fin r) (Fin p ⊕ Fin r) ℝ :=
  -(weight (p := p) (r := r) ε * blockL A B C)

def trajectory (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ) (ε : ℝ) (u₀ : State p r) (t : ℝ) : State p r :=
  let F : State p r →L[ℝ] State p r :=
    (generator A B C ε).toEuclideanLin.toContinuousLinearMap
  (NormedSpace.exp (t • F)) u₀

def energy (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ) (u : State p r) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ u ((blockL A B C).toEuclideanLin u)

def visibleRow (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin r) ℝ) :
    Matrix (Fin p) (Fin p ⊕ Fin r) ℝ :=
  Matrix.of fun i j => Sum.elim (A i) (B i) j

def hiddenRow (B : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin r) (Fin p ⊕ Fin r) ℝ :=
  Matrix.of fun i j => Sum.elim (fun k => B k i) (C i) j

def visiblePart (u : State p r) : EuclideanSpace ℝ (Fin p) :=
  toLp 2 fun i => u (Sum.inl i)

def hiddenPart (u : State p r) : EuclideanSpace ℝ (Fin r) :=
  toLp 2 fun i => u (Sum.inr i)

def leastEigenvalue (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ) (hp : 0 < p) (hL : (blockL A B C).PosDef) : ℝ :=
  (Finset.univ : Finset (Fin p ⊕ Fin r)).inf'
    ⟨Sum.inl ⟨0, hp⟩, Finset.mem_univ _⟩ hL.isHermitian.eigenvalues

/-- The actual coupled exponential gradient flow has exact dissipation and
uniform state and visible-velocity bounds from the least block eigenvalue. -/
theorem coupled_energy_state_velocity
    (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ) (hp : 0 < p) (_hr : 0 < r)
    (hL : (blockL A B C).PosDef) (ε : ℝ) (hε : 0 < ε)
    (u₀ : State p r) :
    let ell := leastEigenvalue A B C hp hL
    0 < ell ∧ Antitone (fun t => energy A B C (trajectory A B C ε u₀ t)) ∧
      trajectory A B C ε u₀ 0 = u₀ ∧ ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (trajectory A B C ε u₀)
        ((generator A B C ε).toEuclideanLin (trajectory A B C ε u₀ t)) t ∧
      (∀ i : Fin p, HasDerivAt (fun s => trajectory A B C ε u₀ s (Sum.inl i))
        (-((visibleRow A B).toEuclideanLin (trajectory A B C ε u₀ t) i)) t) ∧
      (∀ i : Fin r, HasDerivAt (fun s => trajectory A B C ε u₀ s (Sum.inr i))
        (-(ε⁻¹ * (hiddenRow B C).toEuclideanLin (trajectory A B C ε u₀ t) i)) t) ∧
      HasDerivAt (fun s => energy A B C (trajectory A B C ε u₀ s))
        (-‖(visibleRow A B).toEuclideanLin (trajectory A B C ε u₀ t)‖ ^ 2 -
          ε⁻¹ * ‖(hiddenRow B C).toEuclideanLin (trajectory A B C ε u₀ t)‖ ^ 2) t ∧
      energy A B C (trajectory A B C ε u₀ t) ≤ energy A B C u₀ ∧
      ‖trajectory A B C ε u₀ t‖ ≤
        Real.sqrt (2 * energy A B C u₀ / ell) ∧
      ‖(visibleRow A B).toEuclideanLin (trajectory A B C ε u₀ t)‖ ≤
        ‖visibleRow A B‖ * Real.sqrt (2 * energy A B C u₀ / ell) := by
  classical
  let K : State p r →L[ℝ] State p r :=
    (blockL A B C).toEuclideanLin.toContinuousLinearMap
  let hb := hL.isHermitian.eigenvectorBasis
  let lam := hL.isHermitian.eigenvalues
  let ell := leastEigenvalue A B C hp hL
  have hell : 0 < ell := by
    apply (Finset.lt_inf'_iff _).2
    intro i _
    exact hL.eigenvalues_pos i
  have hle (i : Fin p ⊕ Fin r) : ell ≤ lam i :=
    Finset.inf'_le (fun i => lam i) (Finset.mem_univ i)
  have hsym : ∀ v w : State p r, inner ℝ (K v) w = inner ℝ v (K w) :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hL.isHermitian
  have heig (i : Fin p ⊕ Fin r) :
      K (hb i) = (lam i) • hb i := by
    ext j
    simpa [K, hb, lam, Matrix.toLpLin_apply] using
      congrFun (hL.isHermitian.mulVec_eigenvectorBasis i) j
  have hquad (v : State p r) :
      inner ℝ v (K v) = ∑ i, lam i * (inner ℝ (hb i) v) ^ 2 := by
    calc
      inner ℝ v (K v) = inner ℝ (K v) v := real_inner_comm _ _
      _ = ∑ i, inner ℝ (K v) (hb i) * inner ℝ (hb i) v :=
        (hb.sum_inner_mul_inner (K v) v).symm
      _ = ∑ i, lam i * (inner ℝ (hb i) v) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsym, heig, real_inner_smul_right, real_inner_comm]
        ring
  have hcoercive (v : State p r) : ell * ‖v‖ ^ 2 ≤ 2 * energy A B C v := by
    calc
      ell * ‖v‖ ^ 2 = ∑ i, ell * (inner ℝ (hb i) v) ^ 2 := by
        rw [← hb.sum_sq_inner_right v, Finset.mul_sum]
      _ ≤ ∑ i, lam i * (inner ℝ (hb i) v) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)
      _ = 2 * energy A B C v := by
        rw [← hquad]
        simp [energy, K]
  have hvisible (v : State p r) :
      (visibleRow A B).toEuclideanLin v = visiblePart (K v) := by
    ext i
    simp [visibleRow, visiblePart, K, blockL, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hhidden (v : State p r) :
      (hiddenRow B C).toEuclideanLin v = hiddenPart (K v) := by
    ext i
    simp [hiddenRow, hiddenPart, K, blockL, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hWsplit (v : State p r) :
      inner ℝ v ((weight (p := p) (r := r) ε).toEuclideanLin v) =
        ‖visiblePart v‖ ^ 2 + ε⁻¹ * ‖hiddenPart v‖ ^ 2 := by
    have hvnorm : ‖visiblePart v‖ ^ 2 = ∑ i : Fin p, (v (Sum.inl i)) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp [visiblePart, Real.norm_eq_abs, sq_abs]
    have hznorm : ‖hiddenPart v‖ ^ 2 = ∑ i : Fin r, (v (Sum.inr i)) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp [hiddenPart, Real.norm_eq_abs, sq_abs]
    rw [hvnorm, hznorm]
    simp [PiLp.inner_apply, weight, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal, Fintype.sum_sum_type, Finset.mul_sum,
      mul_comm, mul_left_comm, pow_two]
  have hW : (weight (p := p) (r := r) ε).PosSemidef := by
    apply (Matrix.posSemidef_diagonal_iff).2
    intro i
    cases i with
    | inl j => simp
    | inr j => simpa [weight] using (inv_nonneg.mpr (le_of_lt hε))
  have hnonneg (v : State p r) :
      0 ≤ inner ℝ v ((weight (p := p) (r := r) ε).toEuclideanLin v) := by
    have hv := hW.re_dotProduct_nonneg v.ofLp
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      dotProduct_comm] using hv
  have hderiv (t : ℝ) :
      HasDerivAt (fun s => energy A B C (trajectory A B C ε u₀ s))
        (-inner ℝ ((blockL A B C).toEuclideanLin (trajectory A B C ε u₀ t))
          ((weight (p := p) (r := r) ε).toEuclideanLin
            ((blockL A B C).toEuclideanLin (trajectory A B C ε u₀ t)))) t := by
    let W : State p r →L[ℝ] State p r :=
      (weight (p := p) (r := r) ε).toEuclideanLin.toContinuousLinearMap
    let F : State p r →L[ℝ] State p r :=
      (generator A B C ε).toEuclideanLin.toContinuousLinearMap
    let u : ℝ → State p r := fun s => (NormedSpace.exp (s • F)) u₀
    have hu : HasDerivAt u (F (u t)) t := by
      have h := (hasDerivAt_exp_smul_const' F t).clm_apply (hasDerivAt_const t u₀)
      simpa only [u, mul_apply_eq_comp, ContinuousLinearMap.comp_apply, map_zero,
        add_zero] using h
    have hKu : HasDerivAt (fun s => K (u s)) (K (F (u t))) t :=
      K.hasFDerivAt.comp_hasDerivAt t hu
    have hinner := (hu.inner ℝ hKu).const_mul (1 / 2 : ℝ)
    have hFK : F = -(W.comp K) := by
      apply ContinuousLinearMap.ext
      intro v
      simp [F, W, K, generator, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    convert hinner using 1
    · apply AddCommGroup.ext
      rfl
    · apply Module.ext
      funext a x
      rfl
    · funext s
      rfl
    · change -inner ℝ (K (u t)) (W (K (u t))) =
        1 / 2 * (inner ℝ (u t) (K (F (u t))) + inner ℝ (F (u t)) (K (u t)))
      have hs : inner ℝ (u t) (K (F (u t))) = inner ℝ (F (u t)) (K (u t)) := by
        rw [← hsym (u t) (F (u t)), real_inner_comm]
      rw [hs]
      have hf : F (u t) = -W (K (u t)) := by simp [hFK]
      rw [hf, real_inner_comm]
      simp
      ring
  have hanti : Antitone (fun t => energy A B C (trajectory A B C ε u₀ t)) := by
    apply antitone_of_hasDerivAt_nonpos
    · intro t
      exact hderiv t
    · intro t
      exact neg_nonpos.mpr (hnonneg _)
  have hinit : trajectory A B C ε u₀ 0 = u₀ := by
    simp [trajectory]
  let W : State p r →L[ℝ] State p r :=
    (weight (p := p) (r := r) ε).toEuclideanLin.toContinuousLinearMap
  let F : State p r →L[ℝ] State p r :=
    (generator A B C ε).toEuclideanLin.toContinuousLinearMap
  have hFK : F = -(W.comp K) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [F, W, K, generator, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hu (s : ℝ) : HasDerivAt (trajectory A B C ε u₀)
      (F (trajectory A B C ε u₀ s)) s := by
    let u : ℝ → State p r := fun q => (NormedSpace.exp (q • F)) u₀
    have h := (hasDerivAt_exp_smul_const' F s).clm_apply (hasDerivAt_const s u₀)
    have hlocal : HasDerivAt u (F (u s)) s := by
      simpa only [u, mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
        map_zero, add_zero] using h
    convert hlocal using 1
    · funext q
      rfl
    · rfl
  have hvisibleODE (s : ℝ) (i : Fin p) :
      HasDerivAt (fun q => trajectory A B C ε u₀ q (Sum.inl i))
        (-((visibleRow A B).toEuclideanLin (trajectory A B C ε u₀ s) i)) s := by
    have hd := (EuclideanSpace.proj (Sum.inl i)).hasFDerivAt.comp_hasDerivAt s (hu s)
    have hforce : (F (trajectory A B C ε u₀ s)) (Sum.inl i) =
        -((visibleRow A B).toEuclideanLin (trajectory A B C ε u₀ s) i) := by
      rw [hFK]
      simp only [neg_apply, ContinuousLinearMap.comp_apply]
      rw [hvisible]
      simp [W, weight, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, visiblePart]
    simpa only [EuclideanSpace.coe_proj, Function.comp_def, hforce] using hd
  have hhiddenODE (s : ℝ) (i : Fin r) :
      HasDerivAt (fun q => trajectory A B C ε u₀ q (Sum.inr i))
        (-(ε⁻¹ * (hiddenRow B C).toEuclideanLin (trajectory A B C ε u₀ s) i)) s := by
    have hd := (EuclideanSpace.proj (Sum.inr i)).hasFDerivAt.comp_hasDerivAt s (hu s)
    have hforce : (F (trajectory A B C ε u₀ s)) (Sum.inr i) =
        -(ε⁻¹ * (hiddenRow B C).toEuclideanLin (trajectory A B C ε u₀ s) i) := by
      rw [hFK]
      simp only [neg_apply, ContinuousLinearMap.comp_apply]
      rw [hhidden]
      simp [W, weight, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, hiddenPart]
    simpa only [EuclideanSpace.coe_proj, Function.comp_def, hforce] using hd
  have hdiss (s : ℝ) :
      HasDerivAt (fun q => energy A B C (trajectory A B C ε u₀ q))
        (-‖(visibleRow A B).toEuclideanLin (trajectory A B C ε u₀ s)‖ ^ 2 -
          ε⁻¹ * ‖(hiddenRow B C).toEuclideanLin (trajectory A B C ε u₀ s)‖ ^ 2) s := by
    convert hderiv s using 1
    rw [hvisible, hhidden]
    change -‖visiblePart (K (trajectory A B C ε u₀ s))‖ ^ 2 -
        ε⁻¹ * ‖hiddenPart (K (trajectory A B C ε u₀ s))‖ ^ 2 =
      -inner ℝ (K (trajectory A B C ε u₀ s))
        ((weight (p := p) (r := r) ε).toEuclideanLin
          (K (trajectory A B C ε u₀ s)))
    rw [hWsplit]
    ring
  refine ⟨hell, hanti, hinit, ?_⟩
  intro t ht
  have hU : energy A B C (trajectory A B C ε u₀ t) ≤ energy A B C u₀ := by
    simpa [hinit] using hanti ht
  have hnormsq : ‖trajectory A B C ε u₀ t‖ ^ 2 ≤
      2 * energy A B C u₀ / ell := by
    apply (le_div_iff₀ hell).2
    nlinarith [hcoercive (trajectory A B C ε u₀ t)]
  have hnorm : ‖trajectory A B C ε u₀ t‖ ≤
      Real.sqrt (2 * energy A B C u₀ / ell) := by
    have hratio : 0 ≤ 2 * energy A B C u₀ / ell :=
      (sq_nonneg _).trans hnormsq
    exact (Real.le_sqrt (norm_nonneg _) hratio).2 hnormsq
  refine ⟨hu t, hvisibleODE t, hhiddenODE t, hdiss t, hU, hnorm, ?_⟩
  calc
    ‖(visibleRow A B).toEuclideanLin (trajectory A B C ε u₀ t)‖ ≤
        ‖visibleRow A B‖ * ‖trajectory A B C ε u₀ t‖ := by
      exact (visibleRow A B).l2_opNorm_mulVec _
    _ ≤ ‖visibleRow A B‖ * Real.sqrt (2 * energy A B C u₀ / ell) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

#print axioms coupled_energy_state_velocity

end

end D5.S3.Observer.HiddenFlow.FastSchurGradientEnergy

/- GID: D5/S3/Observer/Hankel/InfiniteHankelGramian
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/InfiniteHankelGramian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the actual half-line observation, reachability and Hankel operators and identify their Gramians. -/

import D5.S3.Observer.Hankel.ExactGramianSeries
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.InfiniteHankelGramian

open Matrix
open D5.S3.Observer.Hankel.ExactGramianSeries
open D5.S3.Observer.Hankel.BalancedSteinEnergy
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

/-- Euclidean-valued square-summable signals on the whole nonnegative half-line. -/
abbrev Signal (ι : Type) [Fintype ι] := lp (fun _ : ℕ => EuclideanSpace ℝ ι) 2

variable {ι κ η : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]

/-- The actual entire future-output sequence, made continuous from its
finite-dimensional state domain. Membership in l2 is proved from the series. -/
def futureOutput (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) :
    EuclideanSpace ℝ ι →L[ℝ] Signal κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ⟨fun k => (C * A ^ k).toEuclideanLin x, by
        apply memℓp_gen
        have hs := observation_energy_summable A C hA (WithLp.ofLp x)
        simpa [EuclideanSpace.real_norm_sq_eq, squareSum, Matrix.toLpLin_apply,
          Real.rpow_natCast] using hs⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext k
        exact (C * A ^ k).toEuclideanLin.map_add x y
      map_smul' := by
        intro a x
        apply lp.ext
        funext k
        exact (C * A ^ k).toEuclideanLin.map_smul a x }

@[simp] theorem futureOutput_apply (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (x : EuclideanSpace ℝ ι) (k : ℕ) :
    futureOutput A C hA x k = (C * A ^ k).toEuclideanLin x := rfl

/-- The norm of the actual l2 output equals the actual infinite Gramian energy. -/
theorem futureOutput_norm_sq (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (x : EuclideanSpace ℝ ι) :
    ‖futureOutput A C hA x‖ ^ 2 = quadratic (observationGramian A C) (WithLp.ofLp x) := by
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (futureOutput A C hA x)
  norm_num at he
  rw [he, observationGramian_energy A C hA]
  apply tsum_congr
  intro k
  simpa only [futureOutput_apply, Matrix.toLpLin_apply, squareSum] using
    EuclideanSpace.real_norm_sq_eq ((C * A ^ k).toEuclideanLin x)

/-- Polarization identifies the full Gram bilinear form, including cross terms. -/
theorem futureOutput_inner (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (x y : EuclideanSpace ℝ ι) :
    ⟪futureOutput A C hA x, futureOutput A C hA y⟫ =
      WithLp.ofLp x ⬝ᵥ (observationGramian A C).mulVec (WithLp.ofLp y) := by
  let Q := observationGramian A C
  have hQt : Qᵀ = Q := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (observationGramian_posSemidef A C hA).isHermitian
  have hs : WithLp.ofLp y ⬝ᵥ Q.mulVec (WithLp.ofLp x) =
      WithLp.ofLp x ⬝ᵥ Q.mulVec (WithLp.ofLp y) := by
    calc
      _ = WithLp.ofLp y ⬝ᵥ Qᵀ.mulVec (WithLp.ofLp x) := by rw [hQt]
      _ = _ := by rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hp := futureOutput_norm_sq A C hA (x + y)
  rw [map_add, norm_add_sq_real, futureOutput_norm_sq, futureOutput_norm_sq] at hp
  simp only [quadratic, WithLp.ofLp_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct] at hp
  change ⟪futureOutput A C hA x, futureOutput A C hA y⟫ = _
  dsimp only [Q] at hs
  nlinarith [hs]

/-- The infinite observation operator has exactly the constructed matrix Gramian. -/
theorem futureOutput_gramian (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) :
    (futureOutput A C hA).adjoint.comp (futureOutput A C hA) =
      Matrix.toEuclideanCLM (observationGramian A C) := by
  ext x
  apply ext_inner_left ℝ
  intro y
  change ⟪y, (futureOutput A C hA).adjoint (futureOutput A C hA x)⟫ = _
  rw [ContinuousLinearMap.adjoint_inner_right, futureOutput_inner, Matrix.inner_toEuclideanCLM]

/-- The actual past-to-state map is the adjoint of the dual-system future map. -/
def pastInput (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) : Signal κ →L[ℝ] EuclideanSpace ℝ ι :=
  (futureOutput Aᴴ Bᴴ (adjoint_power_square_summable A hA)).adjoint

/-- The actual infinite past-to-future Hankel operator. -/
def hankel (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) : Signal κ →L[ℝ] Signal η :=
  (futureOutput A C hA).comp (pastInput A B hA)

/-- The past-to-state operator has exactly the constructed controllability Gramian. -/
theorem pastInput_gramian (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) :
    (pastInput A B hA).comp (pastInput A B hA).adjoint =
      Matrix.toEuclideanCLM (controlGramian A B) := by
  simpa only [pastInput, ContinuousLinearMap.adjoint_adjoint, controlGramian] using
    futureOutput_gramian Aᴴ Bᴴ (adjoint_power_square_summable A hA)

/-- A single input at past age j reaches the actual state A^j B u. -/
theorem pastInput_single (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (j : ℕ) (v : EuclideanSpace ℝ κ) :
    pastInput A B hA (lp.single 2 j v) = (A ^ j * B).toEuclideanLin v := by
  apply ext_inner_left ℝ
  intro x
  rw [pastInput, ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right, futureOutput_apply]
  have he : (Bᴴ * Aᴴ ^ j).toEuclideanLin = (A ^ j * B).toEuclideanLin.adjoint := by
    rw [← conjTranspose_pow, ← conjTranspose_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [he, LinearMap.adjoint_inner_left]

/-- Every block of the constructed infinite operator is the genuine Markov
Hankel block C A^(i+j) B. This fixes its past/future indexing convention. -/
theorem hankel_single (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (i j : ℕ) (v : EuclideanSpace ℝ κ) :
    hankel A B C hA (lp.single 2 j v) i = (C * A ^ (i + j) * B).toEuclideanLin v := by
  change futureOutput A C hA (pastInput A B hA (lp.single 2 j v)) i = _
  rw [pastInput_single, futureOutput_apply]
  change WithLp.toLp 2 ((C * A ^ i).mulVec ((A ^ j * B).mulVec (WithLp.ofLp v))) =
    WithLp.toLp 2 ((C * A ^ (i + j) * B).mulVec (WithLp.ofLp v))
  rw [mulVec_mulVec, pow_add]
  simp only [Matrix.mul_assoc]

/-- The full infinite Hankel action is determined by its actual Markov blocks:
finite single-input sums converge to every l2 input, and boundedness transports
that convergence through the constructed operator. -/
theorem hankel_hasSum (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (u : Signal κ) :
    HasSum (fun j : ℕ => hankel A B C hA (lp.single 2 j (u j))) (hankel A B C hA u) :=
  (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u).map
    (hankel A B C hA) (hankel A B C hA).continuous

#print axioms futureOutput_gramian
#print axioms pastInput_gramian
#print axioms hankel_single

end D5.S3.Observer.Hankel.InfiniteHankelGramian

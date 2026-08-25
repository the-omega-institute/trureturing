/- GID: D5/S3/Observer/Completion/ResidualProgressMeasure
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/ResidualProgressMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict full-size tails; norm/test descent incl. empty tests; kernels lack stage order. -/

/- Library-search audit trail (2026-08-25):
   * The ten repository modules under `D5/S3/Quantum/Completion` were read first.
     The exact hit `TransfiniteBasisResidualTower.residualEquiv` identifies every
     proper initially indexed residual with the ambient Hilbert space and is used below.
   * The same module's `transfinite_basis_residual_tower` supplies the orthogonal
     successor splitting used to prove that the concrete natural-numbered chain is strict.
   * Pinned-Mathlib search found `Submodule.starProjection_comp_starProjection_of_le`
     and `Submodule.norm_starProjection_apply_le`; they directly prove pointwise descent.
   * Repository and pinned-Mathlib searches for a packaged residual-progress theorem
     or a projection-norm monotonicity theorem returned no exact combined hit. -/

import D5.S3.Quantum.Completion.TransfiniteBasisResidualTower
import Mathlib.Data.ENNReal.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Cardinal Ordinal
open scoped ENNReal lp

namespace D5.S3.Observer.Completion.ResidualProgressMeasure

open D5.S3.Quantum.Completion.TransfiniteBasisResidualTower

/-- The extended supremum of projection residual norms over a test family. Using `ENNReal`
makes the definition total for unbounded and empty test families. -/
def testResidualSize {K H : Type*} [RCLike K] [NormedAddCommGroup H]
    [InnerProductSpace K H] (R : Submodule K H) [R.HasOrthogonalProjection]
    (T : Set H) : ℝ≥0∞ :=
  ⨆ x : T, ENNReal.ofReal ‖R.starProjection (x : H)‖

private lemma projection_norm_mono_of_le
    {K H : Type*} [RCLike K] [NormedAddCommGroup H] [InnerProductSpace K H]
    {U V : Submodule K H} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) (x : H) : ‖U.starProjection x‖ ≤ ‖V.starProjection x‖ := by
  have hcomp : U.starProjection ∘L V.starProjection = U.starProjection :=
    U.starProjection_comp_starProjection_of_le hUV
  rw [← congrArg (fun p : H →L[K] H => p x) hcomp]
  exact U.norm_starProjection_apply_le (V.starProjection x)

/-- In the concrete Hilbert space `ℓ²(ℕ)`, the closed coordinate tails start at the whole
space and form a strictly decreasing chain. Every tail is linearly isometric to the ambient
space, and the ambient space is infinite-dimensional. Thus Hilbert dimension does not change
while genuine stage progress occurs. -/
theorem bare_dimension_not_progress :
    let H := lp (fun _ : Nat => Real) 2
    ∃ R : Nat → ClosedSubmodule Real H,
      R 0 = ⊤ ∧
        (∀ n, R (n + 1) < R n) ∧
        Antitone R ∧
        (∀ n, Nonempty ((R n).toSubmodule ≃ₗᵢ[Real] H)) ∧
        ¬ FiniteDimensional Real H := by
  dsimp only
  let H := lp (fun _ : Nat => Real) 2
  let b : HilbertBasis Nat Real H := default
  let R : Nat → ClosedSubmodule Real H := fun n => basisResidual b (Set.Iio n)
  have hInitial : Cardinal.ord (#Nat) = typeLT Nat := by simp
  have hTower := transfinite_basis_residual_tower b hInitial
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · change basisResidual b (Set.Iio 0) = ⊤
    rw [basisResidual]
    have hPrefix : basisPrefix b (Set.Iio 0) = ⊥ := by
      have hIio : Set.Iio (0 : Nat) = ∅ := by
        ext k
        simp
      rw [basisPrefix, hIio, Set.image_empty, Submodule.span_empty]
      ext x
      change x ∈ (⊥ : Submodule Real H).topologicalClosure ↔ x ∈ (⊥ : Submodule Real H)
      rw [Submodule.topologicalClosure_eq_self]
    rw [hPrefix]
    exact ClosedSubmodule.bot_orthogonal_eq_top
  · intro n
    have hSet : Set.Iic n = Set.Iio (n + 1) := by
      ext k
      simp
    have hCurrent :
        (R n).toSubmodule =
          Real ∙ b n ⊔ (R (n + 1)).toSubmodule := by
      dsimp [R]
      simpa only [hSet] using (hTower.1 n).1
    have hOrthogonal : Real ∙ b n ⟂ (R (n + 1)).toSubmodule := by
      dsimp [R]
      simpa only [hSet] using (hTower.1 n).2
    have hle : R (n + 1) ≤ R n := by
      change (R (n + 1)).toSubmodule ≤ (R n).toSubmodule
      rw [hCurrent]
      exact le_sup_right
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hbNext : b n ∈ (R (n + 1)).toSubmodule := by
      rw [hEq, hCurrent]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self (b n))
    have hbBot : b n ∈ (⊥ : Submodule Real H) :=
      hOrthogonal.disjoint.le_bot
        ⟨Submodule.mem_span_singleton_self (b n), hbNext⟩
    have hbZero : b n = 0 := by simpa using hbBot
    have hbNorm := b.orthonormal.norm_eq_one n
    rw [hbZero, norm_zero] at hbNorm
    exact zero_ne_one hbNorm
  · apply antitone_nat_of_succ_le
    intro n
    have hSet : Set.Iic n = Set.Iio (n + 1) := by
      ext k
      simp
    have hCurrent :
        (R n).toSubmodule =
          Real ∙ b n ⊔ (R (n + 1)).toSubmodule := by
      dsimp [R]
      simpa only [hSet] using (hTower.1 n).1
    change (R (n + 1)).toSubmodule ≤ (R n).toSubmodule
    rw [hCurrent]
    exact le_sup_right
  · intro n
    exact ⟨residualEquiv b hInitial n⟩
  · intro hFinite
    letI : FiniteDimensional Real H := hFinite
    exact Module.Finite.not_linearIndependent_of_infinite
      b b.orthonormal.linearIndependent

#print axioms bare_dimension_not_progress

/-- For an antitone family of orthogonally complemented residual subspaces, the norm of the
residual projection is antitone at every fixed target vector. The extended supremum over any
test family is antitone as well; no boundedness or nonemptiness hypothesis on the family is
needed. -/
theorem target_residual_measures_antitone
    {K H I : Type*} [RCLike K] [NormedAddCommGroup H] [InnerProductSpace K H]
    [Preorder I] (R : I → Submodule K H)
    [∀ i, (R i).HasOrthogonalProjection] (hR : Antitone R) (T : Set H) :
    (∀ x, Antitone (fun i => ‖(R i).starProjection x‖)) ∧
      Antitone (fun i => testResidualSize (R i) T) := by
  have hPointwise : ∀ x, Antitone (fun i => ‖(R i).starProjection x‖) := by
    intro x i j hij
    exact projection_norm_mono_of_le (hR hij) x
  refine ⟨hPointwise, ?_⟩
  intro i j hij
  exact iSup_mono fun x => ENNReal.ofReal_le_ofReal (hPointwise x hij)

#print axioms target_residual_measures_antitone

/-- The antitone-chain hypothesis is necessary: on the two-stage real Hilbert space, the chain
from zero to the whole space makes the projection norm of `1` increase from zero to one. -/
theorem antitone_residual_chain_is_necessary :
    let R : Bool → ClosedSubmodule Real Real := fun i =>
      if i = true then ⊤ else ⊥
    ¬ Antitone R ∧
      ¬ Antitone (fun i => ‖(R i).toSubmodule.starProjection (1 : Real)‖) := by
  dsimp only
  constructor
  · intro h
    have hbad := h (show false ≤ true by decide)
    change (⊤ : Submodule Real Real) ≤ ⊥ at hbad
    have hone : (1 : Real) ∈ (⊥ : Submodule Real Real) := hbad (by simp)
    have : (1 : Real) = 0 := (Submodule.mem_bot Real).mp hone
    exact one_ne_zero this
  · intro h
    have hbad := h (show false ≤ true by decide)
    change ‖(⊤ : Submodule Real Real).starProjection (1 : Real)‖ ≤
      ‖(⊥ : Submodule Real Real).starProjection (1 : Real)‖ at hbad
    rw [Submodule.starProjection_top, Submodule.starProjection_bot] at hbad
    have : (1 : Real) ≤ 0 := by simpa using hbad
    exact (not_le_of_gt zero_lt_one) this

#print axioms antitone_residual_chain_is_necessary

/- Degenerate audit: empty indices, empty tests, zero projections, identity projections, and
the zero vector all preserve the claimed monotonicity. The `n = 0` tail is `⊤` in the witness. -/
example :
    Antitone (fun _ : PEmpty =>
      ‖(⊥ : Submodule Real Real).starProjection (0 : Real)‖) :=
  antitone_const

example :
    testResidualSize (⊥ : Submodule Real Real) ∅ = 0 ∧
      testResidualSize (⊤ : Submodule Real Real) {0} = 0 := by
  constructor <;> simp [testResidualSize]

example :
    Antitone (fun _ : PUnit =>
      ‖(⊤ : Submodule Real Real).starProjection (1 : Real)‖) :=
  antitone_const

end D5.S3.Observer.Completion.ResidualProgressMeasure

/- GID: D5/S3/Observer/Completion/FourTypedCompletionHierarchy
   generality: I
   mirror-B: D5/B/S3/Observer/Completion/FourTypedCompletionHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four typed completion modes with strict countermodels and algebra independence. -/

/- Library-search audit trail (2026-09-02):
   * Exact D5 hit HilbertResolutionHierarchy.hilbert_resolution_hierarchy supplies both forward
     implications on the canonical residual-size carrier and is applied directly.
   * Exact D5 hits WindowGeneration.window_generators_adjoin_top and
     PrimeDiagonalSaturation.observable_membership_is_necessary supply the full and proper
     operational-algebra witnesses; uniform_completion_obstruction supplies nonconvergence.
   * Pinned Mathlib supplies the projection, orthogonal-complement, limit-uniqueness, and algebra
     APIs used below, but has no theorem combining the four source completion notions.
   * GitHub Lean searches for the hierarchy and its projection/algebra combination found only
     uniform-space completions, Mathlib mirrors, and unrelated projection convergence results. -/

import D5.S3.Observer.Completion.HilbertResolutionHierarchy
import D5.S3.Observer.WindowAlgebra.WindowGeneration
import D5.S3.Quantum.FixedAlgebra.PrimeDiagonalSaturation

open Filter Topology
open scoped ENNReal

open D5.S3.Observer.Completion.HilbertResolutionHierarchy
open D5.S3.Observer.Completion.ResidualProgressMeasure
open D5.S3.Observer.WindowAlgebra.WindowGeneration
open D5.S3.Quantum.Completion.UniformCompletionObstruction
open D5.S3.Quantum.FixedAlgebra.PrimeDiagonalSaturation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Completion.FourTypedCompletionHierarchy

/-- Uniform Hilbert resolution implies state-family resolution, which implies member-target
resolution. Concrete shared-object countermodels make both converses strict. Full clock-and-shift
generation can coexist with failure of all three Hilbert resolution modes, while all three Hilbert
modes can coexist with a proper operational algebra that misses the constructed observable. -/
theorem four_typed_completion_hierarchy
    {K H : Type*} [RCLike K] [NormedAddCommGroup H] [InnerProductSpace K H]
    (V : Nat -> Submodule K H) [forall n, (V n).HasOrthogonalProjection]
    (T : Set H) (x : H) :
    ((Tendsto
        (fun n => ‖ContinuousLinearMap.id K H - (V n).starProjection‖)
        atTop (nhds 0) ->
      Tendsto (fun n => testResidualSize ((V n)ᗮ) T) atTop (nhds 0)) /\
    (x ∈ T ->
      Tendsto (fun n => testResidualSize ((V n)ᗮ) T) atTop (nhds 0) ->
      Tendsto (fun n => ENNReal.ofReal ‖((V n)ᗮ).starProjection x‖)
        atTop (nhds 0))) /\
    (let V0 : Nat -> Submodule Real Real := fun _ => ⊥
     let T0 : Set Real := {0, 1}
     Tendsto (fun n => ENNReal.ofReal ‖((V0 n)ᗮ).starProjection (0 : Real)‖)
        atTop (nhds 0) /\
      ¬ Tendsto (fun n => testResidualSize ((V0 n)ᗮ) T0) atTop (nhds 0)) /\
    (let e0 : EuclideanSpace Complex (Fin 2) := WithLp.toLp 2 ![1, 0]
     let W : Submodule Complex (EuclideanSpace Complex (Fin 2)) := Complex ∙ e0
     let V1 : Nat -> Submodule Complex (EuclideanSpace Complex (Fin 2)) := fun _ => W
     let T1 : Set (EuclideanSpace Complex (Fin 2)) := {e0}
     Tendsto (fun n => testResidualSize ((V1 n)ᗮ) T1) atTop (nhds 0) /\
      ¬ Tendsto
        (fun n => ‖ContinuousLinearMap.id Complex (EuclideanSpace Complex (Fin 2)) -
          (V1 n).starProjection‖) atTop (nhds 0)) /\
    (let observable : Matrix (ZMod 2) (ZMod 2) Complex :=
        Matrix.single 0 1 1
     let state : EuclideanSpace Complex (Fin 2) :=
        WithLp.toLp 2 ![observable 0 0, observable 0 1]
     let V2 : Nat -> Submodule Complex (EuclideanSpace Complex (Fin 2)) :=
        fun _ => ⊥
     let T2 : Set (EuclideanSpace Complex (Fin 2)) := {state}
     observable ∈ windowGeneratedAlgebra 2 /\
      windowGeneratedAlgebra 2 = ⊤ /\
      state = WithLp.toLp 2 ![0, 1] /\
      ¬ Tendsto (fun n => ENNReal.ofReal ‖((V2 n)ᗮ).starProjection state‖)
        atTop (nhds 0) /\
      ¬ Tendsto (fun n => testResidualSize (K := Complex) ((V2 n)ᗮ) T2)
        atTop (nhds 0) /\
      ¬ Tendsto
        (fun n => ‖ContinuousLinearMap.id Complex (EuclideanSpace Complex (Fin 2)) -
          (V2 n).starProjection‖) atTop (nhds 0)) /\
    (let observable : Matrix (Fin 2) (Fin 2) Complex := Matrix.single 1 0 1
     let state : EuclideanSpace Complex (Fin 2) :=
        WithLp.toLp 2 ![observable 1 0, observable 1 1]
     let V3 : Nat -> Submodule Complex (EuclideanSpace Complex (Fin 2)) :=
        fun _ => ⊤
     let T3 : Set (EuclideanSpace Complex (Fin 2)) := {state}
     Tendsto
        (fun n => ‖ContinuousLinearMap.id Complex (EuclideanSpace Complex (Fin 2)) -
          (V3 n).starProjection‖) atTop (nhds 0) /\
      Tendsto (fun n => testResidualSize (K := Complex) ((V3 n)ᗮ) T3)
        atTop (nhds 0) /\
      Tendsto (fun n => ENNReal.ofReal
        ‖(((V3 n)ᗮ : Submodule Complex (EuclideanSpace Complex (Fin 2)))).starProjection state‖)
        atTop (nhds 0) /\
      primeDiagonalAlgebra 2 ∅ ≠ ⊤ /\
      observable ∉ primeDiagonalAlgebra 2 ∅) := by
  have hierarchy := hilbert_resolution_hierarchy V T x
  refine ⟨⟨hierarchy.1, hierarchy.2.1⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only
    constructor
    · simp
    · intro hFamily
      have hMember :=
        (hilbert_resolution_hierarchy
          (fun _ : Nat => (⊥ : Submodule Real Real)) ({0, 1} : Set Real) (1 : Real)).2.1
          (by simp) hFamily
      have hZero : (⊤ : Submodule Real Real).starProjection (1 : Real) = 0 := by
        simpa using hMember
      rw [Submodule.starProjection_top] at hZero
      exact one_ne_zero hZero
  · dsimp only
    let e0 : EuclideanSpace Complex (Fin 2) := WithLp.toLp 2 ![1, 0]
    let e1 : EuclideanSpace Complex (Fin 2) := WithLp.toLp 2 ![0, 1]
    let W : Submodule Complex (EuclideanSpace Complex (Fin 2)) := Complex ∙ e0
    have he0 : e0 ∈ W := Submodule.mem_span_singleton_self e0
    have hResidual : Wᗮ.starProjection e0 = 0 :=
      Submodule.starProjection_orthogonal_apply_eq_zero he0
    have hFamily : Tendsto
        (fun _ : Nat => testResidualSize Wᗮ ({e0} : Set (EuclideanSpace Complex (Fin 2))))
        atTop (nhds 0) := by
      have hzero : testResidualSize Wᗮ ({e0} : Set (EuclideanSpace Complex (Fin 2))) = 0 := by
        apply le_antisymm
        · rw [testResidualSize]
          apply iSup_le
          intro y
          have hy : (y : EuclideanSpace Complex (Fin 2)) = e0 := y.property
          rw [hy, hResidual]
          simp
        · exact bot_le
      simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0))
    have hProper : W ≠ ⊤ := by
      intro htop
      have he1 : e1 ∈ W := by rw [htop]; exact Submodule.mem_top
      rcases (Submodule.mem_span_singleton.mp he1) with ⟨c, hc⟩
      have hfirst := congrArg (fun v : EuclideanSpace Complex (Fin 2) => v 0) hc
      have hsecond := congrArg (fun v : EuclideanSpace Complex (Fin 2) => v 1) hc
      simp [e0, e1] at hfirst hsecond
    exact ⟨hFamily,
      (uniform_completion_obstruction (fun _ : Nat => W) atTop (fun _ => hProper)).2⟩
  · dsimp only
    refine ⟨window_two_off_diagonal_mem_generated,
      window_generators_adjoin_top 2, ?_, ?_, ?_, ?_⟩
    · simp
    · intro hTarget
      simp [Submodule.bot_orthogonal_eq_top, Submodule.starProjection_top] at hTarget
    · intro hFamily
      have hTarget :=
        (hilbert_resolution_hierarchy
          (fun _ : Nat => (⊥ : Submodule Complex (EuclideanSpace Complex (Fin 2))))
          ({WithLp.toLp 2 ![0, 1]} : Set (EuclideanSpace Complex (Fin 2)))
          (WithLp.toLp 2 ![0, 1])).2.1 (by simp) hFamily
      simp [Submodule.bot_orthogonal_eq_top, Submodule.starProjection_top] at hTarget
    · exact
        (uniform_completion_obstruction
          (fun _ : Nat => (⊥ : Submodule Complex (EuclideanSpace Complex (Fin 2))))
          atTop (fun _ => bot_ne_top)).2
  · dsimp only
    have hMissing : Matrix.single 1 0 1 ∉ primeDiagonalAlgebra 2 ∅ :=
      observable_membership_is_necessary.1
    refine ⟨?_, ?_, ?_, ?_, hMissing⟩
    · have hProjection :
          (⊤ : Submodule Complex (EuclideanSpace Complex (Fin 2))).starProjection =
            ContinuousLinearMap.id Complex (EuclideanSpace Complex (Fin 2)) :=
          Submodule.starProjection_top
      simp [hProjection]
    · simp [testResidualSize]
    · simp
    · intro htop
      apply hMissing
      rw [htop]
      trivial

#print axioms four_typed_completion_hierarchy

end D5.S3.Observer.Completion.FourTypedCompletionHierarchy

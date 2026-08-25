/- GID: D5/S3/Quantum/PredictionDepth/CenteredEffectStabilityDepthBound
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/CenteredEffectStabilityDepthBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The centered-effect tower reaches its terminal space within its dimension gap. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Fibers.MinimalPredictiveSummary
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/- Library-search audit trail (2026-08-25):
   * Exact family hits `HermitianTraceZero`, `towerSpace`, and `predictiveSpace`
     supply the source carrier, finite stages, and infinite visible span.
   * Repository body-shape searches for an `sInf` or `Nat.find` stability depth
     and for an `iSup` of `towerSpace` found no existing declaration.
   * Exact repository hit `trace_zero_hermitian_finrank` supplies the ambient
     real dimension after the private direct/nested subtype equivalence below.
   * Pinned Mathlib has no exact theorem packaging all three public clauses.
     The proof applies `Nat.sInf_mem`, `Nat.sInf_le`,
     `monotone_nat_of_le_succ`, `Submodule.finrank_strictMono`, and
     `Submodule.eq_of_le_of_finrank_eq` directly. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PredictionDepth.CenteredEffectStabilityDepthBound

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Fibers.CenteredEffectTowerStability
open D5.S3.Quantum.Fibers.MinimalPredictiveSummary
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

private noncomputable def directTraceZeroEquiv (d : Nat) :
    HermitianTraceZero (d := Fin d) ≃ₗ[ℝ] traceZeroHermitian d where
  toFun X := ⟨⟨X.1, X.2.1⟩, X.2.2⟩
  invFun X := ⟨X.1.1, X.1.2, X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem direct_trace_zero_finrank (d : Nat) [NeZero d] :
    Module.finrank ℝ (HermitianTraceZero (d := Fin d)) = d ^ 2 - 1 := by
  rw [(directTraceZeroEquiv d).finrank_eq]
  exact trace_zero_hermitian_finrank d

private theorem towerSpace_le_succ {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d)) (n : Nat) :
    towerSpace heisenberg effects n ≤ towerSpace heisenberg effects (n + 1) := by
  change towerSpace heisenberg effects n ≤
    towerSpace heisenberg effects n ⊔
      Submodule.map heisenberg (towerSpace heisenberg effects n)
  exact le_sup_left

private theorem towerSpace_mono {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d)) :
    Monotone (towerSpace heisenberg effects) :=
  monotone_nat_of_le_succ (towerSpace_le_succ heisenberg effects)

private theorem heisenberg_map_predictiveSpace_le {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d)) :
    Submodule.map heisenberg (predictiveSpace heisenberg effects) ≤
      predictiveSpace heisenberg effects := by
  rintro _ ⟨X, hX, rfl⟩
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hX
  · rintro _ ⟨⟨n, i⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨n + 1, i⟩, ?_⟩
    simp only [Function.iterate_succ_apply']
  · intro X Y _ _ hX hY
    simpa using add_mem hX hY
  · intro scalar X _ hX
    simpa using Submodule.smul_mem _ scalar hX

private theorem towerSpace_le_predictiveSpace {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d)) (n : Nat) :
    towerSpace heisenberg effects n ≤ predictiveSpace heisenberg effects := by
  induction n with
  | zero =>
      change Submodule.span ℝ (Set.range effects) ≤ predictiveSpace heisenberg effects
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨0, i⟩, ?_⟩
      rfl
  | succ n ih =>
      rw [towerSpace]
      exact sup_le ih (le_trans (Submodule.map_mono ih)
        (heisenberg_map_predictiveSpace_le heisenberg effects))

private theorem iterated_effect_mem_towerSpace {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d))
    (n : Nat) (i : Fin (r + 1)) :
    (heisenberg^[n]) (effects i) ∈ towerSpace heisenberg effects n := by
  induction n with
  | zero =>
      apply Submodule.subset_span
      exact ⟨i, rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change heisenberg ((heisenberg^[n]) (effects i)) ∈
        towerSpace heisenberg effects n ⊔
          Submodule.map heisenberg (towerSpace heisenberg effects n)
      apply (show Submodule.map heisenberg (towerSpace heisenberg effects n) ≤
        towerSpace heisenberg effects n ⊔
          Submodule.map heisenberg (towerSpace heisenberg effects n) from le_sup_right)
      exact ⟨_, ih, rfl⟩

private theorem predictiveSpace_eq_iSup_towerSpace {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d)) :
    predictiveSpace heisenberg effects = ⨆ n, towerSpace heisenberg effects n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨n, i⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem n
      (iterated_effect_mem_towerSpace heisenberg effects n i)
  · exact iSup_le fun n => towerSpace_le_predictiveSpace heisenberg effects n

private theorem bounded_monotone_has_equal_step
    (rankAt : Nat → Nat) (terminalRank : Nat)
    (hmono : Monotone rankAt) (hbound : ∀ n, rankAt n ≤ terminalRank) :
    ∃ m ≤ terminalRank - rankAt 0, rankAt m = rankAt (m + 1) := by
  by_contra h
  push Not at h
  let gap := terminalRank - rankAt 0
  have hgrow : ∀ n ≤ gap + 1, rankAt 0 + n ≤ rankAt n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnGap : n ≤ gap := by omega
        have hle : rankAt n ≤ rankAt (n + 1) := hmono (Nat.le_succ n)
        have hne := h n hnGap
        have hlt : rankAt n < rankAt (n + 1) := lt_of_le_of_ne hle hne
        have hprev := ih (by omega)
        calc
          rankAt 0 + n.succ = (rankAt 0 + n) + 1 := by omega
          _ ≤ rankAt n + 1 := Nat.add_le_add_right hprev 1
          _ ≤ rankAt (n + 1) := hlt
  have hzero := hbound 0
  have hlast := hbound (gap + 1)
  have := hgrow (gap + 1) (by omega)
  dsimp [gap] at this hlast
  omega

/-- The first stage satisfying the source's one-step stability test. -/
def stabilityDepth {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d)) : Nat :=
  sInf {m | towerSpace heisenberg effects m =
    towerSpace heisenberg effects (m + 1)}

/-- The least stable centered-effect depth is bounded by the terminal dimension
gain, the gain is bounded by the trace-zero Hermitian carrier dimension, and
the terminal predictive space is exactly the least stable stage. -/
theorem centered_effect_stability_depth_bound {d r : Nat} [NeZero d]
    (heisenberg : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := Fin d)) :
    stabilityDepth heisenberg effects ≤
        Module.finrank ℝ (predictiveSpace heisenberg effects) -
          Module.finrank ℝ (towerSpace heisenberg effects 0) ∧
      Module.finrank ℝ (predictiveSpace heisenberg effects) -
          Module.finrank ℝ (towerSpace heisenberg effects 0) ≤
        d ^ 2 - 1 - Module.finrank ℝ (towerSpace heisenberg effects 0) ∧
      predictiveSpace heisenberg effects =
        (⨆ n, towerSpace heisenberg effects n) ∧
      (⨆ n, towerSpace heisenberg effects n) =
        towerSpace heisenberg effects (stabilityDepth heisenberg effects) := by
  let terminalRank := Module.finrank ℝ (predictiveSpace heisenberg effects)
  let rankAt := fun n => Module.finrank ℝ (towerSpace heisenberg effects n)
  have hspaceMono := towerSpace_mono heisenberg effects
  have hrankMono : Monotone rankAt := fun m n hmn =>
    Submodule.finrank_mono (hspaceMono hmn)
  have hrankBound : ∀ n, rankAt n ≤ terminalRank := fun n =>
    Submodule.finrank_mono (towerSpace_le_predictiveSpace heisenberg effects n)
  obtain ⟨stableIndex, hstableBound, hstableRank⟩ :=
    bounded_monotone_has_equal_step rankAt terminalRank hrankMono hrankBound
  have hstableSpace : towerSpace heisenberg effects stableIndex =
      towerSpace heisenberg effects (stableIndex + 1) :=
    Submodule.eq_of_le_of_finrank_eq
      (towerSpace_le_succ heisenberg effects stableIndex) hstableRank
  have hstableSet : {m | towerSpace heisenberg effects m =
      towerSpace heisenberg effects (m + 1)}.Nonempty := ⟨stableIndex, hstableSpace⟩
  have hdepthStable : towerSpace heisenberg effects (stabilityDepth heisenberg effects) =
      towerSpace heisenberg effects (stabilityDepth heisenberg effects + 1) := by
    exact Nat.sInf_mem hstableSet
  have hdepthBound : stabilityDepth heisenberg effects ≤ terminalRank - rankAt 0 :=
    le_trans (Nat.sInf_le hstableSpace) hstableBound
  have hterminalRank : terminalRank ≤ d ^ 2 - 1 := by
    calc
      terminalRank ≤ Module.finrank ℝ (HermitianTraceZero (d := Fin d)) :=
        Submodule.finrank_le _
      _ = d ^ 2 - 1 := direct_trace_zero_finrank d
  have hgapBound : terminalRank - rankAt 0 ≤ d ^ 2 - 1 - rankAt 0 :=
    Nat.sub_le_sub_right hterminalRank _
  have hpermanent :=
    (heisenberg_tower_once_stable_permanently heisenberg effects hdepthStable).1
  have hiSupLe : (⨆ n, towerSpace heisenberg effects n) ≤
      towerSpace heisenberg effects (stabilityDepth heisenberg effects) := by
    apply iSup_le
    intro n
    rcases le_total n (stabilityDepth heisenberg effects) with hn | hn
    · exact hspaceMono hn
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact le_of_eq (hpermanent s)
  have hpredictiveUnion := predictiveSpace_eq_iSup_towerSpace heisenberg effects
  have hunionStage : (⨆ n, towerSpace heisenberg effects n) =
      towerSpace heisenberg effects (stabilityDepth heisenberg effects) :=
    le_antisymm hiSupLe (le_iSup _ _)
  exact ⟨hdepthBound, hgapBound, hpredictiveUnion, hunionStage⟩

#print axioms centered_effect_stability_depth_bound

end D5.S3.Quantum.PredictionDepth.CenteredEffectStabilityDepthBound

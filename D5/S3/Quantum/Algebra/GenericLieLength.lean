/- GID: D5/S3/Quantum/Algebra/GenericLieLength
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/GenericLieLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Jia-Capel generic Lie length conjecture formalization. -/
/- admission_basis: open-problem-resolution (#15954; Proved)
   Direct frozen dependencies: none; every D5 proof dependency is in this delivery.
   escape_witness: GenericLieLengthConstruction.anchored_units_mem, GenericLieLengthGenericity.ae_span_top_of_witness, GenericLieLengthFiltration.card_words_le.
   The claim retains the prescribed suSet, layer and Lebesgue-coordinate definitions.
   Heap depth uses Nat.size; coordinate and matrix operations use their Mathlib owners.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16180
   extendedPair: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,extendedPair_span_top.
   extendedPair_span_top: proof_shape: content; escape_witness: GenericLieLengthConstruction.anchored_units_mem; consumers: ae_rightSpan_eq.
   coordinateLinearMap: proof_shape: bind-only; escape_witness: none; consumers: suCoordinateMap_measurableEmbedding.
   suCoordinateMap_measurableEmbedding: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq.
   ae_rightSpan_eq: proof_shape: content; escape_witness: GenericLieLengthGenericity.ae_span_top_of_witness; consumers: result.
   claim: proof_shape: bind-only; escape_witness: none; consumers: result.
   result: proof_shape: content; escape_witness: GenericLieLengthConstruction.anchored_units_mem, GenericLieLengthGenericity.ae_span_top_of_witness, GenericLieLengthFiltration.card_words_le; consumers: terminal.
-/


import D5.S3.Quantum.Algebra.GenericLieLengthConstruction
import D5.S3.Quantum.Algebra.GenericLieLengthGenericity



namespace D5.S3.Quantum.Algebra.GenericLieLength

noncomputable section


open D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLengthConstruction
  D5.S3.Quantum.Algebra.GenericLieLengthGenericity D5.S3.Quantum.Algebra.GenericLieLengthFiltration MeasureTheory
attribute [local instance] LieRing.ofAssociativeRing


private def extendedPair (g n : ℕ) (i : Fin g) : suSet (n + 2) :=
    if h : i.val < 2 then compactPair n ⟨i.val, h⟩ else 0

private theorem extendedPair_span_top (g n : ℕ) (hg : 2 ≤ g) :
    rightSpan (K := ℝ) (extendedPair g n) (16 * (1 + Nat.log 2 (n + 1))) = ⊤ := by
  apply top_unique
  rw [← compactPair_span_top n]
  apply rightSpan_reindex_le (Fin.castLE hg)
  intro i
  simp [extendedPair, i.isLt]

private def coordinateLinearMap (g n : ℕ) :
    (Fin g → Fin (Module.finrank ℝ (suSet n)) → ℝ) →ₗ[ℝ]
      (Fin g → Fin n → Fin n → ℂ) :=
  LinearMap.pi fun i => (suSet n).subtype.comp
    ((Module.finBasis ℝ (suSet n)).equivFun.symm.toLinearMap.comp (LinearMap.proj i))


private theorem suCoordinateMap_measurableEmbedding (g n : ℕ) :
    MeasurableEmbedding (show (Fin g → Fin (Module.finrank ℝ (suSet n)) → ℝ) →
      (Fin g → Fin n → Fin n → ℂ) from suCoordinateMap g n) := by
  have hinj : Function.Injective (coordinateLinearMap g n) := by
    intro x y h
    funext i
    have hi := congrArg (fun S : Fin g → (Matrix (Fin n) (Fin n) ℂ) => S i) h
    apply ((Module.finBasis ℝ (suSet n))).equivFun.symm.injective
    exact Subtype.ext hi
  exact ((coordinateLinearMap g n).isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)).measurableEmbedding


private theorem ae_rightSpan_eq (g n : ℕ) (hg : 2 ≤ g) :
    ∀ᵐ (S : Fin g → Fin (n + 2) → Fin (n + 2) → ℂ) ∂(suPairMeasure g (n + 2)),
      rightSpan (K := ℝ)
        (show Fin g → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ from S)
        (16 * (1 + Nat.log 2 (n + 1))) = suSet (n + 2) := by
  have hh := ae_span_top_of_witness ((Module.finBasis ℝ (suSet (n + 2)))) (extendedPair g n)
    (extendedPair_span_top g n hg)
  rw [suPairMeasure, (suCoordinateMap_measurableEmbedding g (n + 2)).ae_map_iff]
  filter_upwards [hh] with x hx
  have hm := congrArg (Submodule.map (suSet (n + 2)).subtype) hx
  rw [Submodule.map_subtype_top] at hm
  change Submodule.map (show suSet (n + 2) →ₗ⁅ℝ⁆ Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ
    from (suLie (n + 2)).incl).toLinearMap _ = _ at hm
  rw [rightSpan_map] at hm
  exact hm

open D5.S3.Quantum.Algebra.GenericLieLengthConstruction D5.S3.Quantum.Algebra.GenericLieLengthFiltration MeasureTheory

def claim : Prop := ∀ g ≥ 2, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ), n ≥ 2 →
  ∀ᵐ (S : Fin g → Fin n → Fin n → ℂ) ∂(suPairMeasure g n),
    c * Real.log n ≤ (lieLength n (Finset.univ.image S) : ℝ) ∧
    (lieLength n (Finset.univ.image S) : ℝ) ≤ C * Real.log n

set_option maxHeartbeats 800000 in
theorem result : claim := by
  intro g hg
  have hgl : 0 < Real.log ((g : ℝ) + 1) := Real.log_pos (by exact_mod_cast (show 1 < g + 1 by omega))
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log (g + 1), 32 / Real.log 2, div_pos zero_lt_one hgl,
    div_pos (by norm_num) h2, ?_⟩
  intro n hn
  let m := n - 2
  have he : n = m + 2 := by dsimp [m]; omega
  rw [he]
  filter_upwards [ae_rightSpan_eq g m hg] with S hS
  constructor
  · exact lower_lieLength_of_saturation (m + 2) g (16 * (1 + Nat.log 2 (m + 1))) (by omega) hg S
      (by  omega) hS
  · have hu := D5.S3.Quantum.Algebra.GenericLieLengthFiltration.lieLength_le_of_span S (by  omega : 1 ≤ 16 * (1 + Nat.log 2 (m + 1))) hS
    have hur : (lieLength (m + 2) (Finset.univ.image S) : ℝ) ≤
        16 * (1 + (Nat.log 2 (m + 1) : ℝ)) := by
      exact_mod_cast hu
    exact hur.trans (by simpa only [Nat.cast_add, Nat.cast_ofNat] using upper_log m)


end
end D5.S3.Quantum.Algebra.GenericLieLength

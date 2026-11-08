/- GID: D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Connected finite relations control squared distances in every normed additive group. -/

/-
admission_basis: escape-witness.
kraus_survival: proof_shape: bind-only; escape_witness: none; consumers: MayerKnillInfidelityScalingTransition.kraus_survival,MayerZeroFidelityTightness.process_trace,MayerZeroFidelityTightness.zero_trace,BurriReverseOverlap.purification_overlap,LiJiangPolarPairOptimalityRefutation.result.
eqvGen_squared_distance_bound: proof_shape: content; escape_witness: eqvGen_squared_distance_bound; consumers: finite_graph_squared_distance_bound.
finite_graph_squared_distance_bound: proof_shape: content; escape_witness: eqvGen_squared_distance_bound; consumers: general_channel_upper.
Direct frozen dependencies (declaration statement_id):
D5/S3/Quantum/Foundation/FiniteKrausChannel: D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_1 sha256:5dc7bcde8ce2ae710c058683e5324d31e0ca70317f167566967eee1cf3b23bbb; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_2 sha256:9b70ce4858eb731b17facafe93b167007eb9ca6533c641dc770fc553d31ddaa1.
D5/S3/Quantum/Measurement/ExactConditionalPreparationCost: D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.hsandwich sha256:4616bafe50788fc1638fe5ee07779d7b3af275d6a9575ebbe491c2bbeb6eafd9.
D5/S3/Quantum/PureState/PureStateHandshake: D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3.
No module statement_id is used as a declaration identity.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25592.
-/
import D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Foundation.FiniteKrausChannel

open Matrix D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open scoped BigOperators
noncomputable section
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingCore
theorem kraus_survival {a : Type*} [Fintype a] {r : ℕ}
    (ψ : a → ℂ) (K : Fin r → Matrix a a ℂ) :
    (star ψ ⬝ᵥ MatrixMap.of_kraus K K (rankOneDensity ψ) *ᵥ ψ).re =
      ∑ j, ‖star ψ ⬝ᵥ K j *ᵥ ψ‖ ^ 2 := by
  classical
  have hp (A : Matrix a a ℂ) : A * rankOneDensity ψ * Aᴴ = rankOneDensity (A *ᵥ ψ) := by
    simpa only [one_smul] using
      D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.hsandwich A ψ 1
  have hs (v : a → ℂ) : star ψ ⬝ᵥ rankOneDensity v *ᵥ ψ =
      (Complex.normSq (star ψ ⬝ᵥ v) : ℂ) := by
    simp only [rankOneDensity, vecMulVec_mulVec, dotProduct_smul, op_smul_eq_smul,
      smul_eq_mul]
    change (star v ⬝ᵥ ψ) * (star ψ ⬝ᵥ v) = _
    rw [star_dotProduct v ψ]
    rw [mul_comm]
    exact Complex.mul_conj _
  unfold MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, hp]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [hs, Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem eqvGen_squared_distance_bound {ι E : Type*} [NormedAddCommGroup E] (r : ι → ι → Prop) {i j : ι} (h : Relation.EqvGen r i j) : ∃ C : ℝ, 0 < C ∧ ∀ (v : ι → E) (η : ℝ), 0 ≤ η → (∀ a b, r a b → ‖v a - v b‖ ^ 2 ≤ η) → ‖v i - v j‖ ^ 2 ≤ C * η := by
  induction h with
  | rel i j h =>
      refine ⟨1, by norm_num, ?_⟩
      intro v η hη he
      simpa using he i j h
  | refl i =>
      refine ⟨1, by norm_num, ?_⟩
      intro v η hη he
      simpa using hη
  | symm i j h ih =>
      obtain ⟨C, hC, hb⟩ := ih
      refine ⟨C, hC, ?_⟩
      intro v η hη he
      rw [norm_sub_rev]
      exact hb v η hη he
  | trans i j k hij hjk ih ih' =>
      obtain ⟨C, hC, hb⟩ := ih
      obtain ⟨D, hD, hc⟩ := ih'
      refine ⟨2 * C + 2 * D, by positivity, ?_⟩
      intro v η hη he
      have hb' := hb v η hη he
      have hc' := hc v η hη he
      have htri : ‖v i - v k‖ ≤ ‖v i - v j‖ + ‖v j - v k‖ := by
        exact norm_sub_le_norm_sub_add_norm_sub (v i) (v j) (v k)
      have hs := pow_le_pow_left₀ (norm_nonneg (v i - v k)) htri 2
      nlinarith [sq_nonneg (‖v i - v j‖ - ‖v j - v k‖)]
theorem finite_graph_squared_distance_bound {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] (r : ι → ι → Prop) (hc : ∀ i j, Relation.EqvGen r i j) : ∃ C : ℝ, 0 < C ∧ ∀ (v : ι → E) (η : ℝ), 0 ≤ η → (∀ a b, r a b → ‖v a - v b‖ ^ 2 ≤ η) → ∀ i j, ‖v i - v j‖ ^ 2 ≤ C * η := by
  classical
  choose C hC hb using fun i j => eqvGen_squared_distance_bound (E := E) r (hc i j)
  have hsum : 0 ≤ ∑ i, ∑ j, C i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hC i j).le
  refine ⟨1 + ∑ i, ∑ j, C i j, by linarith, ?_⟩
  intro v η hη he i j
  have h1 : C i j ≤ ∑ b, C i b :=
    Finset.single_le_sum (fun b _ => (hC i b).le) (Finset.mem_univ j)
  have h2 : (∑ b, C i b) ≤ ∑ a, ∑ b, C a b :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => (hC a b).le)
      (Finset.mem_univ i)
  have hcle : C i j ≤ 1 + ∑ a, ∑ b, C a b := by linarith
  exact (hb i j v η hη he).trans (mul_le_mul_of_nonneg_right hcle hη)
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingCore

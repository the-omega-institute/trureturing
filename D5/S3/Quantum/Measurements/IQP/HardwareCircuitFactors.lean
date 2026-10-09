/- GID: D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/IQP/HardwareCircuitFactors
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hardware factors and periodic product-angle integration. -/
/-
proof_shape: pi_periodic_shift: content
escape_witness: D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound; D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence; D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence; D5/S3/Quantum/Information/PartialTraceMutualInformation; D5/S3/QuantumBounds/MerminMeasurementDependence/Model
Same-delivery dependencies: none
Declaration judgement:
hardwareAdj_decidable: proof_shape: definition; consumer: hardwareEdges.
edgeAdj_decidable: proof_shape: definition; consumer: localMatchingFlags.
local_degree_sum: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarCombinatorics.local_connector_agreement.
boundary_degree_sum: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarCombinatorics.local_connector_agreement.
local_connector_agreement: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.factor_block_twins.
local_internal_twin: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.factor_block_twins.
complement_degree: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.factor_complement_matching.
blockEquiv_val: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.block_encode, LidarRestrictedAnticoncentrationRefutation.OpLidarNonempty.local_factor_flags.
block_encode: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.hardware_adj_encoded, LidarRestrictedAnticoncentrationRefutation.OpLidarNonempty.connector_free_flags, LidarRestrictedAnticoncentrationRefutation.OpLidarNonempty.local_factor_flags.
local_neighbours_count: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.encoded_neighbours_card.
hardware_adj_encoded: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.hardware_adj_encoded_cycle.
cyclic_next_val: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.cyclic_next_iff, HardwareCircuitFactors.OpLidarHardware.cyclic_prev_iff.
cyclic_prev_iff: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.hardware_adj_encoded_cycle.
cyclic_next_iff: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.hardware_adj_encoded_cycle.
hardware_adj_encoded_cycle: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarHardware.encoded_neighbours_card, HardwareCircuitFactors.OpLidarLocalBridge.encoded_neighbours, HardwareCircuitFactors.OpLidarTwins.boundary_pair_twins, HardwareCircuitFactors.OpLidarTwins.hardware_internal_vertex.
encoded_neighbours_card: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.hardware_degree_five.
hardware_adj_symm: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.edgeAdj_hardware, HardwareCircuitFactors.OpLidarFactorBridge.hardware_incident_card, HardwareCircuitFactors.OpLidarFactorBridge.orderedEdge_hardware.
orderedEdge_hardware: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.hardware_incident_card, HardwareCircuitFactors.OpLidarTwins.factor_adj_of_matched.
hardware_incident_card: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.hardware_degree_five.
hardware_degree_five: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.factor_complement_matching.
factor_complement_matching: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.matching_neighbour_unique, HardwareCircuitFactors.OpLidarLocalBridge.actual_local_matching.
edgeAdj_hardware: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.subset_incident_card, HardwareCircuitFactors.OpLidarLocalBridge.subset_degree_local, HardwareCircuitFactors.OpLidarTwins.factor_adj_of_matched, HardwareCircuitFactors.OpLidarTwins.internal_pair_twins, LidarRestrictedAnticoncentrationRefutation.OpLidarGraphPhase.incident_phase_product.
edgeAdj_symm: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarLocalBridge.subset_degree_local, HardwareCircuitFactors.OpLidarTwins.internal_pair_twins.
subset_incident_card: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarFactorBridge.matching_neighbour_unique, HardwareCircuitFactors.OpLidarLocalBridge.subset_degree_local.
matching_neighbour_unique: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.factor_adj_of_matched.
local_edges_degree: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarLocalBridge.subset_degree_local.
encoded_neighbours: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarLocalBridge.subset_degree_local.
subset_degree_local: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarLocalBridge.actual_local_matching, LidarRestrictedAnticoncentrationRefutation.OpLidarNonempty.factor_nonempty.
actual_local_matching: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.factor_block_twins.
factor_adj_of_matched: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.boundary_pair_twins, HardwareCircuitFactors.OpLidarTwins.internal_pair_twins.
hardware_internal_vertex: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.internal_pair_twins, LidarRestrictedAnticoncentrationRefutation.OpLidarNonempty.local_factor_flags.
internal_pair_twins: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.factor_block_twins.
boundary_pair_twins: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarTwins.factor_block_twins.
factor_block_twins: proof_shape: bind-only; escape_witness: none; consumer: LidarRestrictedAnticoncentrationRefutation.OpLidarCoordinates.factor_permutations.
sqrt_quadratic_bound: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.q_le.
cos_product_mem: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.conditional_fractional_moment, HardwareCircuitFactors.OpLidarAnalysis.pair_sqrt_integrable, HardwareCircuitFactors.OpLidarAnalysis.q_le.
uniformAngle_probability: proof_shape: bind-only; escape_witness: none; consumer: q_le, product_pair_sqrt_integral, conditional_fractional_moment.
angle_integral_eq: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.angle_cos_mean, HardwareCircuitFactors.OpLidarAnalysis.angle_cos_sq_mean, HardwareCircuitFactors.OpLidarAnalysis.normalized_periodic_shift, HardwareCircuitFactors.OpLidarMeasurement.angle_sin_mean.
angle_integrable_of_continuous: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.pairCos_integrable, HardwareCircuitFactors.OpLidarAnalysis.pairCos_sq_integrable, HardwareCircuitFactors.OpLidarMeasurement.effect_integrable, HardwareCircuitFactors.OpLidarMeasurement.effect_mean.
angle_cos_mean: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.product_cos_mean, HardwareCircuitFactors.OpLidarMeasurement.effect_mean.
angle_cos_sq_mean: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.product_cos_sq_mean.
product_cos_mean: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.q_le.
product_cos_sq_mean: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.q_le.
pairCos_integrable: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.q_le.
pairCos_sq_integrable: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.q_le.
pair_sqrt_integrable: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.conditional_fractional_moment, HardwareCircuitFactors.OpLidarAnalysis.q_le.
q_le: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.conditional_fractional_moment.
q_nonneg: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.conditional_fractional_moment.
product_pair_sqrt_integral: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.conditional_fractional_moment.
integral_sqrt_le_sqrt_integral: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarAnalysis.conditional_fractional_moment.
fractional_markov: proof_shape: bind-only; escape_witness: none; consumer: LidarRestrictedAnticoncentrationRefutation.OpLidarSettlement.literal_tail_bound.
eventual_tail_bound: proof_shape: bind-only; escape_witness: none; consumer: LidarRestrictedAnticoncentrationRefutation.OpLidarSettlement.result.
normalized_periodic_shift: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift.
conditional_fractional_moment: proof_shape: bind-only; escape_witness: none; consumer: LidarRestrictedAnticoncentrationRefutation.OpLidarTwinMoment.twin_fractional_moment.
bounded_continuous_integrable: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift.
continuous_cons: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift.
split_pi_integral: proof_shape: bind-only; escape_witness: none; consumer: HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift.
pi_periodic_shift: proof_shape: content; escape_witness: D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift; consumer: LidarRestrictedAnticoncentrationRefutation.OpLidarGraphAnalysis.graph_sqrt_shift; measurement_tensor: proof_shape: bind-only; escape_witness: none; consumer: LidarRestrictedAnticoncentrationRefutation.OpLidarReindex.measurement_tensor_transpose; effect_integrable: proof_shape: bind-only; escape_witness: none; consumer: LidarRestrictedAnticoncentrationRefutation.OpLidarAveraging.densityProbability_integrable.
pair_density_entry: proof_shape: bind-only; escape_witness: none; consumer: pair_measurement, reindexed_twin_marginal.
effect_entry: proof_shape: bind-only; escape_witness: none; consumer: pair_measurement, effect_integrable, effect_mean.
Registration is paused under CLAUDE.md §3.9 (信息逃逸登记暂缓).
-/
import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import D5.S3.QuantumBounds.MerminMeasurementDependence.Model
import D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence (hadamard s2)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (tensorOp pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open scoped BigOperators ENNReal Kronecker ComplexOrder
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors
open scoped BigOperators ENNReal
open MeasureTheory
namespace OpLidar
open D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section
def connector {m : ℕ} (u v : (Fin (6 * m))) : Prop := ((u.cast (Nat.mul_comm 6 m)).modNat).val = 5 ∧ ((v.cast (Nat.mul_comm 6 m)).modNat).val = 4 ∧ ((v.cast (Nat.mul_comm 6 m)).divNat).val = (((u.cast (Nat.mul_comm 6 m)).divNat).val + 1) % m
def hardwareAdj {m : ℕ} (u v : (Fin (6 * m))) : Prop := u ≠ v ∧ ((((u.cast (Nat.mul_comm 6 m)).divNat).val = ((v.cast (Nat.mul_comm 6 m)).divNat).val ∧ ¬ ((((u.cast (Nat.mul_comm 6 m)).modNat).val = 4 ∧ ((v.cast (Nat.mul_comm 6 m)).modNat).val = 5) ∨ (((u.cast (Nat.mul_comm 6 m)).modNat).val = 5 ∧ ((v.cast (Nat.mul_comm 6 m)).modNat).val = 4))) ∨ connector u v ∨ connector v u)
private instance hardwareAdj_decidable {m : ℕ} : DecidableRel (@hardwareAdj m) := fun _ _ => by unfold hardwareAdj connector; infer_instance
def H (m : ℕ) : SimpleGraph ((Fin (6 * m))) where
  Adj := hardwareAdj
  symm := ⟨by
    intro u v h
    rcases h with ⟨hne, h | h | h⟩
    · exact ⟨hne.symm, Or.inl ⟨h.1.symm, by tauto⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inr h)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl h)⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩
def hardwareEdges (m : ℕ) : Finset ((Fin (6 * m) × Fin (6 * m))) := Finset.univ.filter fun e => e.1.val < e.2.val ∧ hardwareAdj e.1 e.2
def edgeDegree {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (v : (Fin (6 * m))) : ℕ := (G.filter fun e => v ∈ s(e.1, e.2)).card
def F4 (m : ℕ) : Finset (Finset ((Fin (6 * m) × Fin (6 * m)))) := (hardwareEdges m).powerset.filter fun G => ∀ v, edgeDegree G v = 4
def randomLayer (m : ℕ) (θ : Fin (6 * m) → ℝ) : Matrix (Fin (6 * m) → Bool) (Fin (6 * m) → Bool) ℂ :=
  (tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (θ i))).submatrix
    (fun s i => if s i then 1 else 0) (fun z i => if z i then 1 else 0)
def HZ {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (z : (Fin (6 * m) → Bool)) : ℝ := (∑ i, (Real.pi / 7) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i)) + (Real.pi / 4) * ∑ e ∈ G, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.1) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.2)
def circuit {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) : Matrix ((Fin (6 * m) → Bool)) ((Fin (6 * m) → Bool)) ℂ := randomLayer m θ * Matrix.diagonal (fun z => Complex.exp (-Complex.I * (HZ G z : ℂ))) * (tensorOp (fun _ : Fin (6 * m) => hadamard)).submatrix (fun (s : Fin (6 * m) → Bool) i => if s i then 1 else 0) (fun (z : Fin (6 * m) → Bool) i => if z i then 1 else 0)
def outputProbability {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) (s : (Fin (6 * m) → Bool)) : ℝ := Complex.normSq (circuit G θ s (fun _ => false))
def uniformAngles (m : ℕ) : Measure ((Fin (6 * m)) → ℝ) := Measure.pi fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))
attribute [reducible] uniformAngles
def joint (m : ℕ) : Measure (Finset ((Fin (6 * m) × Fin (6 * m))) × ((Fin (6 * m)) → ℝ)) := ((ProbabilityTheory.uniformOn (↑(F4 m)))).prod (uniformAngles m)
def tailProbability (m : ℕ) (a : ℝ) (s : (Fin (6 * m) → Bool)) : ℝ := (joint m).real {ω | a * ((2 : ℝ) ^ (6 * m))⁻¹ ≤ outputProbability ω.1 ω.2 s}
end
end OpLidar
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000
namespace OpLidarCombinatorics
abbrev localEdges : Fin 14 → Fin 6 × Fin 6 := ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5)]
def localDegree (M : Fin 14 → Bool) (v : Fin 6) : ℕ := ∑ e : Fin 14, if M e && (decide ((localEdges e).1 = v) || decide ((localEdges e).2 = v)) then 1 else 0
def boundaryDegree (incoming outgoing : Bool) (v : Fin 6) : ℕ := (if v = 4 && incoming then 1 else 0) + (if v = 5 && outgoing then 1 else 0)
def LocalMatching (M : Fin 14 → Bool) (incoming outgoing : Bool) : Prop := ∀ v, localDegree M v + boundaryDegree incoming outgoing v = 1
private lemma local_degree_sum (M : Fin 14 → Bool) : (∑ v : Fin 6, localDegree M v) = 2 * ∑ e : Fin 14, if M e then 1 else 0 := by
  unfold localDegree
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  fin_cases e <;> simp only [Fin.sum_univ_succ] <;> simp [localEdges] <;> split_ifs <;> omega
private lemma boundary_degree_sum (incoming outgoing : Bool) : (∑ v : Fin 6, boundaryDegree incoming outgoing v) = (if incoming then 1 else 0) + (if outgoing then 1 else 0) := by
  cases incoming <;> cases outgoing <;> decide
private lemma local_connector_agreement : ∀ (M : Fin 14 → Bool) (incoming outgoing : Bool), LocalMatching M incoming outgoing → incoming = outgoing := by
  intro M incoming outgoing h
  change ∀ v, localDegree M v + boundaryDegree incoming outgoing v = 1 at h
  have hsum : (∑ v : Fin 6, (localDegree M v + boundaryDegree incoming outgoing v)) = 6 := by
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_add_distrib, local_degree_sum, boundary_degree_sum] at hsum
  cases incoming <;> cases outgoing <;> simp_all <;> omega
private lemma local_internal_twin : ∀ (M : Fin 14 → Bool), LocalMatching M false false → ∃ e : Fin 14, M e = true ∧ (localEdges e).1.val < 4 ∧ (localEdges e).2.val < 4 := by
  intro M h
  by_contra hn
  have hz : ∀ e : Fin 14, (localEdges e).1.val < 4 → (localEdges e).2.val < 4 → M e = false := by
    intro e he1 he2
    cases hb : M e
    · rfl
    · exact False.elim (hn ⟨e, hb, he1, he2⟩)
  have h0 := hz 0 (by decide) (by decide)
  have h1 := hz 1 (by decide) (by decide)
  have h2 := hz 2 (by decide) (by decide)
  have h5 := hz 5 (by decide) (by decide)
  have h6 := hz 6 (by decide) (by decide)
  have h9 := hz 9 (by decide) (by decide)
  simp only [LocalMatching, Fin.forall_fin_succ] at h
  simp only [localDegree, Fin.sum_univ_succ] at h
  simp [boundaryDegree, localEdges, h0, h1, h2, h5, h6, h9] at h
  omega
private lemma complement_degree {V : Type*} [DecidableEq V] (H G : Finset (V × V)) (hsub : G ⊆ H) (v : V) (hdH : (H.filter (fun e => e.1 = v ∨ e.2 = v)).card = 5) (hdG : (G.filter (fun e => e.1 = v ∨ e.2 = v)).card = 4) : ((H \ G).filter (fun e => e.1 = v ∨ e.2 = v)).card = 1 := by
  have heq : ((H \ G).filter (fun e => e.1 = v ∨ e.2 = v)) = (H.filter (fun e => e.1 = v ∨ e.2 = v)) \ (G.filter (fun e => e.1 = v ∨ e.2 = v)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [heq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hsub), hdH, hdG]
end OpLidarCombinatorics
namespace OpLidarHardware
open OpLidar
noncomputable section
def blockEquiv (m : ℕ) : (Fin m × Fin 6) ≃ (Fin (6 * m)) := finProdFinEquiv.trans (finCongr (Nat.mul_comm m 6))
lemma blockEquiv_val (m : ℕ) (i : Fin m) (v : Fin 6) : (blockEquiv m (i,v)).val = 6 * i.val + v.val := by
  simp [blockEquiv, finProdFinEquiv]
  omega
lemma block_encode (m : ℕ) (i : Fin m) (v : Fin 6) : (((blockEquiv m (i,v)).cast (Nat.mul_comm 6 m)).divNat).val = i.val ∧ (((blockEquiv m (i,v)).cast (Nat.mul_comm 6 m)).modNat).val = v.val := by
  change (blockEquiv m (i,v)).val / 6 = i.val ∧ (blockEquiv m (i,v)).val % 6 = v.val
  rw [blockEquiv_val]
  constructor <;> omega
def localNeighbours (v : Fin 6) : Finset (Fin 6) := Finset.univ.filter fun w => v ≠ w ∧ ¬ ((v = 4 ∧ w = 5) ∨ (v = 5 ∧ w = 4))
private lemma local_neighbours_count (v : Fin 6) : (localNeighbours v).card = if v.val < 4 then 5 else 4 := by
  fin_cases v <;> decide
lemma hardware_adj_encoded (m : ℕ) (i j : Fin m) (r t : Fin 6) : hardwareAdj (blockEquiv m (i,r)) (blockEquiv m (j,t)) ↔ (i = j ∧ t ∈ localNeighbours r) ∨ (r = 5 ∧ t = 4 ∧ j.val = (i.val + 1) % m) ∨ (t = 5 ∧ r = 4 ∧ i.val = (j.val + 1) % m) := by
  have hbr := block_encode m i r
  have hbt := block_encode m j t
  have henc : blockEquiv m (i,r) = blockEquiv m (j,t) ↔ i = j ∧ r = t := by
    constructor
    · intro h
      exact Prod.mk.inj ((blockEquiv m).injective h)
    · rintro ⟨rfl,rfl⟩; rfl
  change ((blockEquiv m (i,r) ≠ blockEquiv m (j,t)) ∧ (((((blockEquiv m (i,r)).cast (Nat.mul_comm 6 m)).divNat).val = (((blockEquiv m (j,t)).cast (Nat.mul_comm 6 m)).divNat).val ∧ ¬ (((((blockEquiv m (i,r)).cast (Nat.mul_comm 6 m)).modNat).val = 4 ∧ (((blockEquiv m (j,t)).cast (Nat.mul_comm 6 m)).modNat).val = 5) ∨ ((((blockEquiv m (i,r)).cast (Nat.mul_comm 6 m)).modNat).val = 5 ∧ (((blockEquiv m (j,t)).cast (Nat.mul_comm 6 m)).modNat).val = 4))) ∨ connector (blockEquiv m (i,r)) (blockEquiv m (j,t)) ∨ connector (blockEquiv m (j,t)) (blockEquiv m (i,r)))) ↔ _
  simp only [ne_eq, henc]
  simp only [connector, hbr.1, hbr.2, hbt.1, hbt.2, localNeighbours, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
  norm_num only [Fin.reduceFinMk]
  constructor
  · rintro ⟨hne, h | h | h⟩
    · exact Or.inl ⟨h.1, by tauto⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro h
    constructor
    · rcases h with h | h | h <;> omega
    · tauto
lemma cyclic_next_val {m : ℕ} [NeZero m] (hm : 1 < m) (i : Fin m) : (i + 1).val = (i.val + 1) % m := by
  simp [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hm]
lemma cyclic_prev_iff {m : ℕ} [NeZero m] (hm : 1 < m) (i j : Fin m) : i.val = (j.val + 1) % m ↔ j = i - 1 := by
  rw [← cyclic_next_val hm, ← Fin.ext_iff]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    rw [h]
    simp
lemma cyclic_next_iff {m : ℕ} [NeZero m] (hm : 1 < m) (i j : Fin m) : j.val = (i.val + 1) % m ↔ j = i + 1 := by
  rw [← cyclic_next_val hm, ← Fin.ext_iff]
lemma hardware_adj_encoded_cycle {m : ℕ} [NeZero m] (hm : 1 < m) (i j : Fin m) (r t : Fin 6) : hardwareAdj (blockEquiv m (i,r)) (blockEquiv m (j,t)) ↔ (i = j ∧ t ∈ localNeighbours r) ∨ (r = 5 ∧ t = 4 ∧ j = i + 1) ∨ (t = 5 ∧ r = 4 ∧ j = i - 1) := by
  rw [hardware_adj_encoded, cyclic_prev_iff hm i j, cyclic_next_iff hm i j]
lemma encoded_neighbours_card {m : ℕ} [NeZero m] (hm : 1 < m) (i : Fin m) (r : Fin 6) : (Finset.univ.filter (fun w : Fin m × Fin 6 => hardwareAdj (blockEquiv m (i,r)) (blockEquiv m w))).card = 5 := by
  classical
  let L := (localNeighbours r).image (fun t : Fin 6 => (i,t))
  have hL : L.card = (localNeighbours r).card := by
    apply Finset.card_image_of_injective
    intro x y h
    exact Prod.mk.inj h |>.2
  have hex : (Finset.univ.filter (fun w : Fin m × Fin 6 => hardwareAdj (blockEquiv m (i,r)) (blockEquiv m w))) = if r = 4 then insert (i - 1, 5) L else if r = 5 then insert (i + 1, 4) L else L := by
    ext w
    obtain ⟨j,t⟩ := w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hardware_adj_encoded_cycle hm]
    dsimp [L]
    split_ifs <;> simp_all [Finset.mem_insert, Finset.mem_image, localNeighbours] <;> tauto
  rw [hex]
  split_ifs with hr4 hr5
  · have hn : (i - 1, (5 : Fin 6)) ∉ L := by
      simp [L, localNeighbours, hr4]
    rw [Finset.card_insert_of_notMem hn, hL, local_neighbours_count]
    simp [hr4]
  · have hn : (i + 1, (4 : Fin 6)) ∉ L := by
      simp [L, localNeighbours, hr5]
    rw [Finset.card_insert_of_notMem hn, hL, local_neighbours_count]
    simp [hr5]
  · rw [hL, local_neighbours_count]
    have hlt : r.val < 4 := by
      have hr := r.isLt
      have h4 : r.val ≠ 4 := by exact fun h => hr4 (Fin.ext h)
      have h5 : r.val ≠ 5 := by exact fun h => hr5 (Fin.ext h)
      omega
    simp [hlt]
end
end OpLidarHardware
namespace OpLidarFactorBridge
open OpLidar OpLidarHardware OpLidarCombinatorics
noncomputable section
private lemma hardware_adj_symm {m : ℕ} {u v : (Fin (6 * m))} (h : hardwareAdj u v) : hardwareAdj v u := (H m).adj_symm h
lemma orderedEdge_hardware {m : ℕ} (u v : (Fin (6 * m))) (h : hardwareAdj u v) : (Sym2.sortEquiv s(u, v)).val ∈ hardwareEdges m := by
  have hn := h.1
  change (min u v, max u v) ∈ hardwareEdges m
  rcases le_total u v with huv | hvu
  · have hlt : u.val < v.val := by
      have hval : u.val ≠ v.val := fun he => hn (Fin.ext he)
      have := Fin.le_iff_val_le_val.mp huv
      omega
    simpa only [min_eq_left huv, max_eq_right huv, hardwareEdges, Finset.mem_filter, Finset.mem_univ, true_and] using And.intro hlt h
  · have hlt : v.val < u.val := by
      have hval : v.val ≠ u.val := fun he => hn (Fin.ext he.symm)
      have := Fin.le_iff_val_le_val.mp hvu
      omega
    simpa only [min_eq_right hvu, max_eq_left hvu, hardwareEdges, Finset.mem_filter, Finset.mem_univ, true_and] using And.intro hlt (hardware_adj_symm h)
lemma hardware_incident_card {m : ℕ} (v : (Fin (6 * m))) : edgeDegree (hardwareEdges m) v = (Finset.univ.filter (fun w => hardwareAdj v w)).card := by
  classical
  unfold edgeDegree
  refine Finset.card_bij (s := (hardwareEdges m).filter fun e => v ∈ s(e.1, e.2)) (t := Finset.univ.filter fun w => hardwareAdj v w) (fun e _ => if e.1 = v then e.2 else e.1) ?_ ?_ ?_
  · intro e he
    obtain ⟨heH,heinc⟩ := Finset.mem_filter.mp he
    obtain ⟨hlt,hadj⟩ := (Finset.mem_filter.mp heH).2
    have heinc : e.1 = v ∨ e.2 = v := (Sym2.mem_iff.mp heinc).imp Eq.symm Eq.symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases heinc with hleft | hright
    · simpa [hleft] using hadj
    · have hne : e.1 ≠ v := by intro h; rw [h, hright] at hlt; omega
      simpa [hne, hright] using hardware_adj_symm hadj
  · intro e he f hf heq
    obtain ⟨heH,heinc⟩ := Finset.mem_filter.mp he
    obtain ⟨hfH,hfinc⟩ := Finset.mem_filter.mp hf
    have hel := (Finset.mem_filter.mp heH).2.1
    have hfl := (Finset.mem_filter.mp hfH).2.1
    have heinc : e.1 = v ∨ e.2 = v := (Sym2.mem_iff.mp heinc).imp Eq.symm Eq.symm
    have hfinc : f.1 = v ∨ f.2 = v := (Sym2.mem_iff.mp hfinc).imp Eq.symm Eq.symm
    rcases heinc with he1 | he2 <;> rcases hfinc with hf1 | hf2
    · simp only [he1, hf1, if_true] at heq
      exact Prod.ext (he1.trans hf1.symm) heq
    · have hfn : f.1 ≠ v := by intro h; rw [h,hf2] at hfl; omega
      simp only [he1, if_true, hfn, if_false] at heq
      have : v.val < e.2.val := by simpa [he1] using hel
      have : e.2.val < v.val := by simpa [heq,hf2] using hfl
      omega
    · have hen : e.1 ≠ v := by intro h; rw [h,he2] at hel; omega
      simp only [hf1, if_true, hen, if_false] at heq
      have : e.1.val < v.val := by simpa [he2] using hel
      have : v.val < e.1.val := by simpa [heq,hf1] using hfl
      omega
    · have hen : e.1 ≠ v := by intro h; rw [h,he2] at hel; omega
      have hfn : f.1 ≠ v := by intro h; rw [h,hf2] at hfl; omega
      simp only [hen, hfn, if_false] at heq
      exact Prod.ext heq (he2.trans hf2.symm)
  · intro w hw
    have hadj : hardwareAdj v w := by simpa using hw
    refine ⟨(Sym2.sortEquiv s(v, w)).val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨orderedEdge_hardware v w hadj, by change v ∈ s(min v w, max v w); rcases le_total v w with h | h <;> simp [min_eq_left h, max_eq_right h, min_eq_right h, max_eq_left h]⟩
    · have hn : w ≠ v := hadj.1.symm
      change (if min v w = v then max v w else min v w) = w
      rcases le_total v w with h | h <;> simp_all [min_eq_left h, max_eq_right h, min_eq_right h, max_eq_left h]
lemma hardware_degree_five {m : ℕ} [NeZero m] (hm : 1 < m) (v : (Fin (6 * m))) : edgeDegree (hardwareEdges m) v = 5 := by
  rw [hardware_incident_card]
  obtain ⟨⟨i,r⟩,rfl⟩ := (blockEquiv m).surjective v
  have hc := encoded_neighbours_card hm i r
  have hb : (Finset.univ.filter (fun w : Fin m × Fin 6 => hardwareAdj (blockEquiv m (i,r)) (blockEquiv m w))).card = (Finset.univ.filter (fun w : (Fin (6 * m)) => hardwareAdj (blockEquiv m (i,r)) w)).card := by
    exact Finset.card_equiv (blockEquiv m) (by intro w; simp)
  exact hb.symm.trans hc
lemma factor_complement_matching {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) : ∀ v, edgeDegree (hardwareEdges m \ G) v = 1 := by
  have hf : G ⊆ hardwareEdges m ∧ ∀ v, edgeDegree G v = 4 := by
    simpa only [F4, Finset.mem_filter, Finset.mem_powerset] using hG
  intro v
  simpa only [edgeDegree, Sym2.mem_iff, eq_comm] using complement_degree _ _ hf.1 v (by simpa only [edgeDegree, Sym2.mem_iff, eq_comm] using hardware_degree_five hm v) (by simpa only [edgeDegree, Sym2.mem_iff, eq_comm] using hf.2 v)
def edgeAdj {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (u v : (Fin (6 * m))) : Prop := (Sym2.sortEquiv s(u, v)).val ∈ E
private instance edgeAdj_decidable {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) : DecidableRel (edgeAdj E) := fun _ _ => inferInstanceAs (Decidable (_ ∈ E))
lemma edgeAdj_hardware {m : ℕ} {E : Finset ((Fin (6 * m) × Fin (6 * m)))} (hE : E ⊆ hardwareEdges m) {u v : (Fin (6 * m))} (h : edgeAdj E u v) : hardwareAdj u v := by
  have hh := (Finset.mem_filter.mp (hE h)).2.2
  change hardwareAdj (min u v) (max u v) at hh
  rcases le_total u v with huv | hvu
  · simpa only [min_eq_left huv, max_eq_right huv] using hh
  · exact hardware_adj_symm (by simpa only [min_eq_right hvu, max_eq_left hvu] using hh)
lemma edgeAdj_symm {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (u v : (Fin (6 * m))) : edgeAdj E u v ↔ edgeAdj E v u := by unfold edgeAdj; rw [Sym2.eq_swap]
lemma subset_incident_card {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (hE : E ⊆ hardwareEdges m) (v : (Fin (6 * m))) : edgeDegree E v = (Finset.univ.filter (fun w => edgeAdj E v w)).card := by
  classical
  unfold edgeDegree
  refine Finset.card_bij (s := E.filter fun e => v ∈ s(e.1, e.2)) (t := Finset.univ.filter fun w => edgeAdj E v w) (fun e _ => if e.1 = v then e.2 else e.1) ?_ ?_ ?_
  · intro e he
    obtain ⟨heE,heinc⟩ := Finset.mem_filter.mp he
    have hlt := (Finset.mem_filter.mp (hE heE)).2.1
    have heinc : e.1 = v ∨ e.2 = v := (Sym2.mem_iff.mp heinc).imp Eq.symm Eq.symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases heinc with hleft | hright
    · change (Sym2.sortEquiv s(v, (if e.1 = v then e.2 else e.1))).val ∈ E
      rw [if_pos hleft, ← hleft]
      simpa [Sym2.sortEquiv, Fin.le_iff_val_le_val.mpr hlt.le] using heE
    · have hne : e.1 ≠ v := by intro h; rw [h,hright] at hlt; omega
      change (Sym2.sortEquiv s(v, (if e.1 = v then e.2 else e.1))).val ∈ E
      rw [if_neg hne, ← hright, Sym2.eq_swap]
      simpa [Sym2.sortEquiv, Fin.le_iff_val_le_val.mpr hlt.le] using heE
  · intro e he f hf heq
    obtain ⟨heH,heinc⟩ := Finset.mem_filter.mp he
    obtain ⟨hfH,hfinc⟩ := Finset.mem_filter.mp hf
    have hel := (Finset.mem_filter.mp (hE heH)).2.1
    have hfl := (Finset.mem_filter.mp (hE hfH)).2.1
    have heinc : e.1 = v ∨ e.2 = v := (Sym2.mem_iff.mp heinc).imp Eq.symm Eq.symm
    have hfinc : f.1 = v ∨ f.2 = v := (Sym2.mem_iff.mp hfinc).imp Eq.symm Eq.symm
    rcases heinc with he1 | he2 <;> rcases hfinc with hf1 | hf2
    · simp only [he1, hf1, if_true] at heq
      exact Prod.ext (he1.trans hf1.symm) heq
    · have hfn : f.1 ≠ v := by intro h; rw [h,hf2] at hfl; omega
      simp only [he1, if_true, hfn, if_false] at heq
      have : v.val < e.2.val := by simpa [he1] using hel
      have : e.2.val < v.val := by simpa [heq,hf2] using hfl
      omega
    · have hen : e.1 ≠ v := by intro h; rw [h,he2] at hel; omega
      simp only [hf1, if_true, hen, if_false] at heq
      have : e.1.val < v.val := by simpa [he2] using hel
      have : v.val < e.1.val := by simpa [heq,hf1] using hfl
      omega
    · have hen : e.1 ≠ v := by intro h; rw [h,he2] at hel; omega
      have hfn : f.1 ≠ v := by intro h; rw [h,hf2] at hfl; omega
      simp only [hen, hfn, if_false] at heq
      exact Prod.ext heq (he2.trans hf2.symm)
  · intro w hw
    have hmem : (Sym2.sortEquiv s(v, w)).val ∈ E := (Finset.mem_filter.mp hw).2
    have hadj : hardwareAdj v w := edgeAdj_hardware hE hmem
    refine ⟨(Sym2.sortEquiv s(v, w)).val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hmem, by change v ∈ s(min v w, max v w); rcases le_total v w with h | h <;> simp [min_eq_left h, max_eq_right h, min_eq_right h, max_eq_left h]⟩
    · have hn : w ≠ v := hadj.1.symm
      change (if min v w = v then max v w else min v w) = w
      rcases le_total v w with h | h <;> simp_all [min_eq_left h, max_eq_right h, min_eq_right h, max_eq_left h]
lemma matching_neighbour_unique {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (v : (Fin (6 * m))) : ∃! w, edgeAdj (hardwareEdges m \ G) v w := by
  have hs : hardwareEdges m \ G ⊆ hardwareEdges m := Finset.sdiff_subset
  have hc := (subset_incident_card _ hs v).symm.trans (factor_complement_matching hm G hG v)
  simpa using Finset.card_eq_one_iff_existsUnique.mp hc
end
end OpLidarFactorBridge
open scoped BigOperators
namespace OpLidarLocalBridge
open OpLidar OpLidarHardware OpLidarCombinatorics OpLidarFactorBridge
noncomputable section
private lemma local_edges_degree (A : Fin 6 → Fin 6 → Bool) (hs : ∀ r t, A r t = A t r) (v : Fin 6) : localDegree (fun e => A (localEdges e).1 (localEdges e).2) v = ((localNeighbours v).filter fun w => A v w = true).card := by
  classical
  rw [localNeighbours, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
  fin_cases v <;>
    simp only [localDegree, Fin.sum_univ_succ] <;>
    dsimp +instances [localEdges] <;>
    norm_num <;> (try simp [Fin.ext_iff]) <;>
    (try simp only [hs 1 0, hs 2 0, hs 2 1, hs 3 0, hs 3 1, hs 3 2, hs 4 0, hs 4 1, hs 4 2, hs 4 3, hs 5 0, hs 5 1, hs 5 2, hs 5 3, hs 5 4]) <;> omega
private lemma encoded_neighbours {m : ℕ} [NeZero m] (hm : 1 < m) (i : Fin m) (r : Fin 6) : (Finset.univ.filter (fun w : Fin m × Fin 6 => hardwareAdj (blockEquiv m (i,r)) (blockEquiv m w))) = if r = 4 then insert (i - 1, 5) ((localNeighbours r).image (fun t => (i,t))) else if r = 5 then insert (i + 1, 4) ((localNeighbours r).image (fun t => (i,t))) else (localNeighbours r).image (fun t => (i,t)) := by
  ext w
  obtain ⟨j,t⟩ := w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hardware_adj_encoded_cycle hm]
  split_ifs <;> simp_all [Finset.mem_insert, Finset.mem_image, localNeighbours] <;> tauto
def localMatchingFlags {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (i : Fin m) : Fin 14 → Bool := fun e => decide (edgeAdj E (blockEquiv m (i,(localEdges e).1)) (blockEquiv m (i,(localEdges e).2)))
def connectorFlag {m : ℕ} [NeZero m] (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (i : Fin m) : Bool :=
  decide (edgeAdj E (blockEquiv m (i,5)) (blockEquiv m (i+1,4)))
lemma subset_degree_local {m : ℕ} [NeZero m] (hm : 1 < m) (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (hE : E ⊆ hardwareEdges m) (i : Fin m) (r : Fin 6) : edgeDegree E (blockEquiv m (i,r)) = localDegree (localMatchingFlags E i) r + boundaryDegree (connectorFlag E (i-1)) (connectorFlag E i) r := by
  classical
  let A : Fin 6 → Fin 6 → Bool := fun r t =>
    decide (edgeAdj E (blockEquiv m (i,r)) (blockEquiv m (i,t)))
  let L := (localNeighbours r).image (fun t : Fin 6 => (i,t))
  let P : Fin m × Fin 6 → Prop := fun w => edgeAdj E (blockEquiv m (i,r)) (blockEquiv m w)
  have hcard : edgeDegree E (blockEquiv m (i,r)) = (Finset.univ.filter P).card := by
    rw [subset_incident_card E hE]
    exact (Finset.card_equiv (blockEquiv m) (by intro w; simp [P])).symm
  have hfilter : Finset.univ.filter P = (Finset.univ.filter (fun w : Fin m × Fin 6 => hardwareAdj (blockEquiv m (i,r)) (blockEquiv m w))).filter P := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨edgeAdj_hardware hE h,h⟩,fun h => h.2⟩
  have hL : (L.filter P).card = localDegree (localMatchingFlags E i) r := by
    have himg : L.filter P = ((localNeighbours r).filter fun t => A r t = true).image (fun t => (i,t)) := by
      simp [L, Finset.filter_image, A, P]
    rw [himg, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
    exact (local_edges_degree A (fun a b => by
      apply Bool.eq_iff_iff.2
      simp only [A,decide_eq_true_eq]
      exact edgeAdj_symm E _ _) r).symm
  rw [hcard,hfilter,encoded_neighbours hm]
  change ((if r = 4 then insert (i-1,5) L else if r = 5 then insert (i+1,4) L else L).filter P).card = _
  split_ifs with hr4 hr5
  · have hn : (i-1,(5 : Fin 6)) ∉ L := by simp [L,localNeighbours,hr4]
    rw [Finset.filter_insert]
    split_ifs with hp
    · rw [Finset.card_insert_of_notMem (fun h => hn ((Finset.mem_filter.mp h).1)), hL]
      simp [boundaryDegree,hr4,connectorFlag,P,edgeAdj_symm]
      simpa [P,hr4] using hp
    · rw [hL]
      simp [boundaryDegree,hr4,connectorFlag,P,edgeAdj_symm] at hp ⊢
      simp [hp]
  · have hn : (i+1,(4 : Fin 6)) ∉ L := by simp [L,localNeighbours,hr5]
    rw [Finset.filter_insert]
    split_ifs with hp
    · rw [Finset.card_insert_of_notMem (fun h => hn ((Finset.mem_filter.mp h).1)), hL]
      simp [boundaryDegree,hr5,connectorFlag,P]
      simpa [P,hr5] using hp
    · rw [hL]
      simp [boundaryDegree,hr5,connectorFlag,P]
      simpa [P,hr5] using hp
  · rw [hL]
    simp [boundaryDegree,hr4,hr5]
private lemma actual_local_matching {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (i : Fin m) : LocalMatching (localMatchingFlags (hardwareEdges m \ G) i) (connectorFlag (hardwareEdges m \ G) (i-1)) (connectorFlag (hardwareEdges m \ G) i) := by
  intro r
  rw [← subset_degree_local hm _ Finset.sdiff_subset i r]
  exact factor_complement_matching hm G hG _
end
end OpLidarLocalBridge
namespace OpLidarTwins
open OpLidar OpLidarHardware OpLidarCombinatorics OpLidarFactorBridge OpLidarLocalBridge
noncomputable section
set_option maxHeartbeats 2000000
private lemma factor_adj_of_matched {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (u v : (Fin (6 * m))) (hM : edgeAdj (hardwareEdges m \ G) u v) (w : (Fin (6 * m))) : edgeAdj G u w ↔ hardwareAdj u w ∧ w ≠ v := by
  have hf : G ⊆ hardwareEdges m ∧ ∀ v, edgeDegree G v = 4 := by
    simpa only [F4,Finset.mem_filter,Finset.mem_powerset] using hG
  constructor
  · intro h
    refine ⟨edgeAdj_hardware hf.1 h, ?_⟩
    intro heq
    rw [heq] at h
    exact (Finset.mem_sdiff.mp hM).2 h
  · rintro ⟨hw,hne⟩
    have hH := orderedEdge_hardware u w hw
    by_contra hGuw
    have hMw : edgeAdj (hardwareEdges m \ G) u w := Finset.mem_sdiff.mpr ⟨hH,hGuw⟩
    obtain ⟨v0,hv0,hu⟩ := matching_neighbour_unique hm G hG u
    exact hne ((hu w hMw).trans (hu v hM).symm)
lemma hardware_internal_vertex {m : ℕ} [NeZero m] (hm : 1 < m) (i j : Fin m) (r w : Fin 6) (hr : r.val < 4) : hardwareAdj (blockEquiv m (i,r)) (blockEquiv m (j,w)) ↔ i = j ∧ w ≠ r := by
  rw [hardware_adj_encoded_cycle hm]
  have hr4 : r ≠ 4 := by intro h; simp [h] at hr
  have hr5 : r ≠ 5 := by intro h; simp [h] at hr
  simp [localNeighbours, hr4, hr5, ne_comm]
private lemma internal_pair_twins {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (i : Fin m) (r t : Fin 6) (hr : r.val < 4) (ht : t.val < 4) (hM : edgeAdj (hardwareEdges m \ G) (blockEquiv m (i,r)) (blockEquiv m (i,t))) : r ≠ t ∧ (∀ j w, edgeAdj G (blockEquiv m (i,r)) (blockEquiv m (j,w)) ↔ i = j ∧ w ≠ r ∧ w ≠ t) ∧ (∀ j w, edgeAdj G (blockEquiv m (i,t)) (blockEquiv m (j,w)) ↔ i = j ∧ w ≠ r ∧ w ≠ t) := by
  have hne : r ≠ t := by
    intro heq
    exact (edgeAdj_hardware Finset.sdiff_subset hM).1 (by rw [heq])
  refine ⟨hne, ?_, ?_⟩
  · intro j w
    rw [factor_adj_of_matched hm G hG _ _ hM, hardware_internal_vertex hm i j r w hr]
    have heq : blockEquiv m (j,w) = blockEquiv m (i,t) ↔ j = i ∧ w = t := by
      constructor
      · intro h; exact Prod.mk.inj ((blockEquiv m).injective h)
      · rintro ⟨rfl,rfl⟩; rfl
    simp only [ne_eq,heq]
    tauto
  · intro j w
    have hMt : edgeAdj (hardwareEdges m \ G) (blockEquiv m (i,t)) (blockEquiv m (i,r)) := (edgeAdj_symm _ _ _).mp hM
    rw [factor_adj_of_matched hm G hG _ _ hMt, hardware_internal_vertex hm i j t w ht]
    have heq : blockEquiv m (j,w) = blockEquiv m (i,r) ↔ j = i ∧ w = r := by
      constructor
      · intro h; exact Prod.mk.inj ((blockEquiv m).injective h)
      · rintro ⟨rfl,rfl⟩; rfl
    simp only [ne_eq,heq]
    tauto
private lemma boundary_pair_twins {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (i : Fin m) (hin : connectorFlag (hardwareEdges m \ G) (i-1) = true) (hout : connectorFlag (hardwareEdges m \ G) i = true) : (∀ j w, edgeAdj G (blockEquiv m (i,4)) (blockEquiv m (j,w)) ↔ i = j ∧ w ≠ 4 ∧ w ≠ 5) ∧ (∀ j w, edgeAdj G (blockEquiv m (i,5)) (blockEquiv m (j,w)) ↔ i = j ∧ w ≠ 4 ∧ w ≠ 5) := by
  have hMi : edgeAdj (hardwareEdges m \ G) (blockEquiv m (i,4)) (blockEquiv m (i-1,5)) := by
    simpa [connectorFlag,edgeAdj_symm] using hin
  have hMo : edgeAdj (hardwareEdges m \ G) (blockEquiv m (i,5)) (blockEquiv m (i+1,4)) := by
    simpa [connectorFlag] using hout
  constructor
  · intro j w
    rw [factor_adj_of_matched hm G hG _ _ hMi, hardware_adj_encoded_cycle hm]
    have heq : blockEquiv m (j,w) = blockEquiv m (i-1,5) ↔ j = i-1 ∧ w = 5 := by
      constructor
      · intro h; exact Prod.mk.inj ((blockEquiv m).injective h)
      · rintro ⟨rfl,rfl⟩; rfl
    simp only [ne_eq,heq]
    simp only [localNeighbours, Finset.mem_filter, Finset.mem_univ, true_and]
    norm_num only [Fin.reduceEq]
    simp only [ne_comm]
    tauto
  · intro j w
    rw [factor_adj_of_matched hm G hG _ _ hMo, hardware_adj_encoded_cycle hm]
    have heq : blockEquiv m (j,w) = blockEquiv m (i+1,4) ↔ j = i+1 ∧ w = 4 := by
      constructor
      · intro h; exact Prod.mk.inj ((blockEquiv m).injective h)
      · rintro ⟨rfl,rfl⟩; rfl
    simp only [ne_eq,heq]
    simp only [localNeighbours, Finset.mem_filter, Finset.mem_univ, true_and]
    norm_num only [Fin.reduceEq]
    simp only [ne_comm]
    tauto
lemma factor_block_twins {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (i : Fin m) : ∃ r t : Fin 6, r ≠ t ∧ (∀ j w, edgeAdj G (blockEquiv m (i,r)) (blockEquiv m (j,w)) ↔ i = j ∧ w ≠ r ∧ w ≠ t) ∧ (∀ j w, edgeAdj G (blockEquiv m (i,t)) (blockEquiv m (j,w)) ↔ i = j ∧ w ≠ r ∧ w ≠ t) := by
  have hl := actual_local_matching hm G hG i
  have hag := local_connector_agreement _ _ _ hl
  cases hb : connectorFlag (hardwareEdges m \ G) i
  · have hin : connectorFlag (hardwareEdges m \ G) (i-1) = false := hag.trans hb
    rw [hin,hb] at hl
    obtain ⟨e,he,hr,ht⟩ := local_internal_twin _ hl
    have hM : edgeAdj (hardwareEdges m \ G) (blockEquiv m (i,(localEdges e).1)) (blockEquiv m (i,(localEdges e).2)) := by simpa [localMatchingFlags] using he
    exact ⟨_,_,internal_pair_twins hm G hG i _ _ hr ht hM⟩
  · have hin : connectorFlag (hardwareEdges m \ G) (i-1) = true := hag.trans hb
    exact ⟨4,5,by decide,boundary_pair_twins hm G hG i hin hb⟩
end
end OpLidarTwins
end D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors
namespace D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors
open MeasureTheory
namespace OpLidarAnalysis
noncomputable section
private lemma sqrt_quadratic_bound (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) : Real.sqrt (1 + t) ≤ 1 + t / 2 - t ^ 2 / 12 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]
  have hR : 0 ≤ 1 + t / 2 - t ^ 2 / 12 := by nlinarith
  have hpoly : 0 ≤ t ^ 2 * (t ^ 2 - 12 * t + 12) := by
    exact mul_nonneg (sq_nonneg t) (by nlinarith [sq_nonneg t])
  apply (Real.sqrt_le_iff).2
  constructor
  · exact hR
  · nlinarith
private lemma cos_product_mem (α β : ℝ) : -1 ≤ Real.cos α * Real.cos β ∧ Real.cos α * Real.cos β ≤ 1 := by
  have ha := Real.abs_cos_le_one α
  have hb := Real.abs_cos_le_one β
  have h : |Real.cos α * Real.cos β| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact abs_le.mp h
private lemma uniformAngle_probability : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) := by
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by rw [Real.volume_Ico, sub_zero]; positivity) (by rw [Real.volume_Ico, sub_zero]; exact ENNReal.ofReal_ne_top)
attribute [instance] uniformAngle_probability
lemma angle_integral_eq (f : ℝ → ℝ) : (∫ x, f x ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) = (2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
  rw [ProbabilityTheory.cond, integral_smul_measure, Real.volume_Ico, sub_zero, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi)]
lemma angle_integrable_of_continuous {f : ℝ → ℝ} (hf : Continuous f) : Integrable f (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) := by
  unfold ProbabilityTheory.cond
  exact (hf.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self).smul_measure (by rw [Real.volume_Ico, sub_zero]; exact ENNReal.inv_ne_top.mpr (by positivity))
lemma angle_cos_mean : (∫ x, Real.cos x ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) = 0 := by
  rw [angle_integral_eq, integral_cos]
  simp
private lemma angle_cos_sq_mean : (∫ x, Real.cos x ^ 2 ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) = 1 / 2 := by
  rw [angle_integral_eq, integral_cos_sq]
  simp
  field_simp
private lemma product_cos_mean : (∫ x : ℝ × ℝ, Real.cos x.1 * Real.cos x.2 ∂((ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))).prod (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = 0 := by
  rw [integral_prod_mul, angle_cos_mean]
  simp
private lemma product_cos_sq_mean : (∫ x : ℝ × ℝ, (Real.cos x.1 * Real.cos x.2) ^ 2 ∂((ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))).prod (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = 1 / 4 := by
  simp_rw [mul_pow]
  rw [integral_prod_mul (fun x : ℝ => Real.cos x ^ 2) (fun x : ℝ => Real.cos x ^ 2), angle_cos_sq_mean]
  norm_num
def pairAngle : Measure (ℝ × ℝ) := (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))).prod (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))
attribute [reducible] pairAngle
def pairCos (x : ℝ × ℝ) : ℝ := Real.cos x.1 * Real.cos x.2
private def q : ℝ := ∫ x, Real.sqrt (1 + pairCos x) ∂pairAngle
private lemma pairCos_integrable : Integrable pairCos pairAngle := by
  exact (angle_integrable_of_continuous Real.continuous_cos).mul_prod (angle_integrable_of_continuous Real.continuous_cos)
private lemma pairCos_sq_integrable : Integrable (fun x => pairCos x ^ 2) pairAngle := by
  have h := (angle_integrable_of_continuous (Real.continuous_cos.pow 2)).mul_prod (angle_integrable_of_continuous (Real.continuous_cos.pow 2))
  simpa only [pairCos, pairAngle, mul_pow, Pi.pow_apply] using h
private lemma pair_sqrt_integrable : Integrable (fun x => Real.sqrt (1 + pairCos x)) pairAngle := by
  have hc : Continuous (fun x : ℝ × ℝ => Real.sqrt (1 + pairCos x)) := Real.continuous_sqrt.comp (continuous_const.add ((Real.continuous_cos.comp continuous_fst).mul (Real.continuous_cos.comp continuous_snd)))
  refine (integrable_const (2 : ℝ)).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_iff).2
  exact ⟨by norm_num, by have h := (cos_product_mem x.1 x.2).2; dsimp [pairCos]; linarith⟩
private lemma q_le : q ≤ 47 / 48 := by
  have hi : Integrable (fun x => 1 + pairCos x / 2) pairAngle := (integrable_const (1 : ℝ)).add (pairCos_integrable.div_const 2)
  have hR : Integrable (fun x => 1 + pairCos x / 2 - pairCos x ^ 2 / 12) pairAngle := hi.sub (pairCos_sq_integrable.div_const 12)
  have h := integral_mono pair_sqrt_integrable hR (fun x => sqrt_quadratic_bound (pairCos x) (cos_product_mem x.1 x.2).1 (cos_product_mem x.1 x.2).2)
  unfold q
  refine h.trans_eq ?_
  rw [integral_sub hi (pairCos_sq_integrable.div_const 12), integral_add (integrable_const (1 : ℝ)) (pairCos_integrable.div_const 2), integral_div, integral_div]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [show (∫ x, pairCos x ∂pairAngle) = 0 from product_cos_mean,
    show (∫ x, pairCos x ^ 2 ∂pairAngle) = 1 / 4 from product_cos_sq_mean]
  norm_num
private lemma q_nonneg : 0 ≤ q := integral_nonneg (fun _ => Real.sqrt_nonneg _)
private lemma product_pair_sqrt_integral (m : ℕ) : (∫ x : Fin m → (ℝ × ℝ), ∏ i, Real.sqrt (1 + pairCos (x i)) ∂Measure.pi (fun _ => pairAngle)) = q ^ m := by
  simpa [q] using integral_fintype_prod_eq_pow (ι := Fin m) (μ := pairAngle) (fun x => Real.sqrt (1 + pairCos x))
private lemma integral_sqrt_le_sqrt_integral {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] (f : A → ℝ) (h0 : ∀ x, 0 ≤ f x) (hf : Integrable f μ) (hs : Integrable (fun x => Real.sqrt (f x)) μ) : (∫ x, Real.sqrt (f x) ∂μ) ≤ Real.sqrt (∫ x, f x ∂μ) := by
  have heq : (fun x => Real.sqrt (f x) ^ 2) = f := by
    funext x
    exact Real.sq_sqrt (h0 x)
  have hf2 : MemLp (fun x => Real.sqrt (f x)) 2 μ := (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).2 (by simpa only [heq] using hf)
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg (f x))) (Filter.Eventually.of_forall (fun _ : A => (by norm_num : (0 : ℝ) ≤ 1))) (by simpa using hf2) (memLp_const (1 : ℝ))
  simp only [mul_one, Real.rpow_two, integral_const, probReal_univ, smul_eq_mul, one_mul, Real.one_rpow] at h
  rw [heq, ← Real.sqrt_eq_rpow] at h
  simpa only [one_pow, Real.one_rpow, mul_one] using h
lemma fractional_markov {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] (Z : A → ℝ) (hZ : ∀ x, 0 ≤ Z x) (hs : Integrable (fun x => Real.sqrt (Z x)) μ) (m : ℕ) (hmoment : (∫ x, Real.sqrt (Z x) ∂μ) ≤ (47 / 48 : ℝ) ^ m) (a : ℝ) (ha : 0 < a) : μ.real {x | a ≤ Z x} ≤ (Real.sqrt a)⁻¹ * (47 / 48 : ℝ) ^ m := by
  have hsets : {x | a ≤ Z x} = {x | Real.sqrt a ≤ Real.sqrt (Z x)} := by
    ext x
    change a ≤ Z x ↔ Real.sqrt a ≤ Real.sqrt (Z x)
    exact (Real.sqrt_le_sqrt_iff (hZ x)).symm
  rw [hsets]
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg (Z x))) hs (Real.sqrt a)
  have hapos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  rw [mul_comm (Real.sqrt a)⁻¹, ← div_eq_mul_inv]
  apply (le_div_iff₀ hapos).2
  simpa only [mul_comm] using hmark.trans hmoment
lemma eventual_tail_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ∃ m : ℕ, 3 ≤ m ∧ (Real.sqrt a)⁻¹ * (47 / 48 : ℝ) ^ m < b := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 47 / 48) (by norm_num : (47 / 48 : ℝ) < 1)).const_mul (Real.sqrt a)⁻¹
  have he : ∀ᶠ m : ℕ in Filter.atTop, (Real.sqrt a)⁻¹ * (47 / 48 : ℝ) ^ m < b := by
    have hlim : Filter.Tendsto (fun m : ℕ => (Real.sqrt a)⁻¹ * (47 / 48 : ℝ) ^ m) Filter.atTop (nhds 0) := by simpa using ht
    exact hlim.eventually (gt_mem_nhds hb)
  obtain ⟨m, hlt⟩ := Filter.eventually_atTop.1 he
  exact ⟨max m 3, le_max_right _ _, hlt _ (le_max_left _ _)⟩
lemma normalized_periodic_shift (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi)) (d : ℝ) : (∫ x, f (x + d) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) = ∫ x, f x ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) := by
  rw [angle_integral_eq, angle_integral_eq, intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add, add_comm d (2 * Real.pi), zero_add] using hf.intervalIntegral_add_eq d 0
lemma conditional_fractional_moment {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν] (m : ℕ) (Z : (Fin m → (ℝ × ℝ)) × Y → ℝ) (hZ : ∀ w, 0 ≤ Z w) (hsections : ∀ x, Integrable (fun y => Z (x, y)) ν ∧ Integrable (fun y => Real.sqrt (Z (x, y))) ν) (hs : Integrable (fun w => Real.sqrt (Z w)) ((Measure.pi fun _ : Fin m => pairAngle).prod ν)) (hmean : ∀ x, (∫ y, Z (x, y) ∂ν) = ∏ i, (1 + pairCos (x i))) : (∫ w, Real.sqrt (Z w) ∂((Measure.pi fun _ : Fin m => pairAngle).prod ν)) ≤ (47 / 48 : ℝ) ^ m := by
  have hpoint : ∀ x, (∫ y, Real.sqrt (Z (x, y)) ∂ν) ≤ ∏ i, Real.sqrt (1 + pairCos (x i)) := by
    intro x
    have h := integral_sqrt_le_sqrt_integral ν (fun y => Z (x, y)) (fun y => hZ (x, y)) (hsections x).1 (hsections x).2
    rw [hmean x, Real.sqrt_prod _ (fun i _ => by
      have hi := (cos_product_mem (x i).1 (x i).2).1
      dsimp [pairCos]; linarith)] at h
    exact h
  have hi : Integrable (fun x : Fin m → (ℝ × ℝ) => ∏ i, Real.sqrt (1 + pairCos (x i))) (Measure.pi fun _ => pairAngle) := Integrable.fintype_prod (fun _ => pair_sqrt_integrable)
  rw [integral_prod _ hs]
  calc _ ≤ ∫ x : Fin m → (ℝ × ℝ), ∏ i, Real.sqrt (1 + pairCos (x i)) ∂Measure.pi (fun _ => pairAngle) := integral_mono hs.integral_prod_left hi hpoint
    _ = q ^ m := product_pair_sqrt_integral m
    _ ≤ (47 / 48 : ℝ) ^ m := pow_le_pow_left₀ q_nonneg q_le m
end
end OpLidarAnalysis
open scoped BigOperators
end D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors
namespace D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors
namespace OpLidarProductShift
open MeasureTheory OpLidar OpLidarAnalysis
noncomputable section
set_option maxHeartbeats 2000000
private lemma bounded_continuous_integrable {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] (f : A → ℝ) (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ := (integrable_const C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
private lemma continuous_cons (n : ℕ) : Continuous (fun w : ℝ × (Fin n → ℝ) => (Fin.cons w.1 w.2 : Fin (n+1) → ℝ)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simpa [Function.comp_def] using (continuous_apply j).comp (continuous_snd : Continuous (fun w : ℝ × (Fin n → ℝ) => w.2))
private lemma split_pi_integral (n : ℕ) (f : (Fin (n+1) → ℝ) → ℝ) : (∫ x, f x ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = ∫ w : ℝ × (Fin n → ℝ), f (Fin.cons w.1 w.2) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))).prod (Measure.pi fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) := by
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero,Equiv.coe_fn_mk,Fin.zero_succAbove,cast_eq]
lemma pi_periodic_shift (n : ℕ) (f : (Fin n → ℝ) → ℝ) (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (hp : ∀ x i, Function.Periodic (fun t => f (Function.update x i t)) (2 * Real.pi)) (d : Fin n → ℝ) : (∫ x, f (fun i => x i + d i) ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = ∫ x, f x ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) := by
  induction n with
  | zero =>
    congr 1
    funext x
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have hcons := continuous_cons n
    have hshift : Continuous (fun w : ℝ × (Fin n → ℝ) => f (fun i => (Fin.cons w.1 w.2 : Fin (n+1) → ℝ) i + d i)) := by
      apply hc.comp
      apply continuous_pi
      intro i
      exact ((continuous_apply i).comp hcons).add continuous_const
    have hbase : Continuous (fun w : ℝ × (Fin n → ℝ) => f (Fin.cons w.1 w.2)) := hc.comp hcons
    rw [split_pi_integral,split_pi_integral, integral_prod _ (bounded_continuous_integrable _ _ hshift C (fun w => hb _)), integral_prod _ (bounded_continuous_integrable _ _ hbase C (fun w => hb _))]
    have hfun : ∀ x : ℝ, (∫ y : Fin n → ℝ, f (fun i => (Fin.cons x y : Fin (n+1) → ℝ) i + d i) ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = ∫ y : Fin n → ℝ, f (Fin.cons (x+d 0) y) ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) := by
      intro x
      have hc' : Continuous (fun y : Fin n → ℝ => f (Fin.cons (x+d 0) y)) := hc.comp (hcons.comp (continuous_const.prodMk continuous_id))
      have hp' : ∀ y i, Function.Periodic (fun t => f (Fin.cons (x+d 0) (Function.update y i t))) (2 * Real.pi) := by
        intro y i
        simpa only [Fin.cons_update] using hp (Fin.cons (x+d 0) y) i.succ
      have he : (fun y : Fin n → ℝ => f (fun i => (Fin.cons x y : Fin (n+1) → ℝ) i+d i)) = (fun y => f (Fin.cons (x+d 0) (fun i => y i+d i.succ))) := by
        funext y
        congr 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [he]
      exact ih _ hc' (fun y => hb _) hp' (fun i => d i.succ)
    simp_rw [hfun]
    apply normalized_periodic_shift (fun x => ∫ y : Fin n → ℝ, f (Fin.cons x y) ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) ?_ (d 0)
    intro x
    apply integral_congr_ae
    filter_upwards [] with y
    have h := hp (Fin.cons x y) 0 x
    simpa only [Fin.update_cons_zero] using h
end
end OpLidarProductShift
open scoped BigOperators
end D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors

namespace D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors
namespace OpLidarReduced
noncomputable section
lemma sign_product (b c : Bool) : (Int.negOnePow (b.toNat : ℤ) : ℤ)* (Int.negOnePow (c.toNat : ℤ) : ℤ)= (Int.negOnePow ((b ^^ c).toNat : ℤ) : ℤ) := by
  cases b <;> cases c <;> decide
private lemma pair_character_sum (r t r' t' : Bool) :
    (∑ y : Fin 4 → Bool,
      (Int.negOnePow (((r ^^ t) && (List.foldl Bool.xor (y 0) [y 1, y 2, y 3])).toNat : ℤ) : ℤ) * (Int.negOnePow (((r' ^^ t') && (List.foldl Bool.xor (y 0) [y 1, y 2, y 3])).toNat : ℤ) : ℤ)) =
    if (r ^^ t) = (r' ^^ t') then 16 else 0 := by
  cases r <;> cases t <;> cases r' <;> cases t' <;> decide
def twinPhase (m : ℕ) (qC : (Fin m → (Fin 4 → Bool)) → Bool)
    (x : Fin m → Bool × Bool) (y : Fin m → (Fin 4 → Bool)) : ℤ :=
  (Int.negOnePow ((qC y).toNat : ℤ) : ℤ) * ∏ i, (Int.negOnePow ((((x i).1 ^^ (x i).2) && (List.foldl Bool.xor ((y i) 0) [(y i) 1, (y i) 2, (y i) 3])).toNat : ℤ) : ℤ)
private lemma gram_phase_cancels (m : ℕ)
    (qC : (Fin m → (Fin 4 → Bool)) → Bool)
    (x x' : Fin m → Bool × Bool) (y : Fin m → (Fin 4 → Bool)) :
    twinPhase m qC x y * twinPhase m qC x' y =
      ∏ i, (Int.negOnePow ((((x i).1 ^^ (x i).2) && (List.foldl Bool.xor ((y i) 0) [(y i) 1, (y i) 2, (y i) 3])).toNat : ℤ) : ℤ) *
        (Int.negOnePow ((((x' i).1 ^^ (x' i).2) && (List.foldl Bool.xor ((y i) 0) [(y i) 1, (y i) 2, (y i) 3])).toNat : ℤ) : ℤ) := by
  unfold twinPhase
  have hs : (Int.negOnePow ((qC y).toNat : ℤ) : ℤ) * (Int.negOnePow ((qC y).toNat : ℤ) : ℤ) = 1 := by cases qC y <;> decide
  rw [Finset.prod_mul_distrib]
  calc
    _ = ((Int.negOnePow ((qC y).toNat : ℤ) : ℤ) * (Int.negOnePow ((qC y).toNat : ℤ) : ℤ)) *
      ((∏ i, (Int.negOnePow ((((x i).1 ^^ (x i).2) && (List.foldl Bool.xor ((y i) 0) [(y i) 1, (y i) 2, (y i) 3])).toNat : ℤ) : ℤ)) *
        ∏ i, (Int.negOnePow ((((x' i).1 ^^ (x' i).2) && (List.foldl Bool.xor ((y i) 0) [(y i) 1, (y i) 2, (y i) 3])).toNat : ℤ) : ℤ)) := by ring
    _ = _ := by rw [hs, one_mul]
private lemma twin_gram_exact (m : ℕ)
    (qC : (Fin m → (Fin 4 → Bool)) → Bool)
    (x x' : Fin m → Bool × Bool) :
    (∑ y : Fin m → (Fin 4 → Bool), twinPhase m qC x y * twinPhase m qC x' y) =
    ∏ i, if ((x i).1 ^^ (x i).2) = ((x' i).1 ^^ (x' i).2) then 16 else 0 := by
  simp_rw [gram_phase_cancels]
  rw [← Fintype.prod_sum (fun i (y : Fin 4 → Bool) =>
    (Int.negOnePow ((((x i).1 ^^ (x i).2) && (List.foldl Bool.xor (y 0) [y 1, y 2, y 3])).toNat : ℤ) : ℤ) *
      (Int.negOnePow ((((x' i).1 ^^ (x' i).2) && (List.foldl Bool.xor (y 0) [y 1, y 2, y 3])).toNat : ℤ) : ℤ))]
  simp_rw [pair_character_sum]
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
def twinAmplitude (m : ℕ)
    (qC : (Fin m → (Fin 4 → Bool)) → Bool)
    (xy : (Fin m → Bool × Bool) × (Fin m → (Fin 4 → Bool))) : ℂ :=
  (((2 : ℝ)⁻¹ ^ (3 * m) : ℝ) : ℂ) * (twinPhase m qC xy.1 xy.2 : ℂ)
private lemma twin_density_gram (m : ℕ)
    (qC : (Fin m → (Fin 4 → Bool)) → Bool)
    (x x' : Fin m → Bool × Bool) :
    partialTraceRight (Matrix.vecMulVec (twinAmplitude m qC)
      (star (twinAmplitude m qC))) x x' =
    ((((2 : ℝ)⁻¹ ^ (3 * m)) ^ 2 : ℝ) : ℂ) *
      ((∏ i, if ((x i).1 ^^ (x i).2) = ((x' i).1 ^^ (x' i).2)
        then 16 else 0 : ℤ) : ℂ) := by
  rw [← twin_gram_exact]
  simp only [Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  unfold partialTraceRight
  apply Finset.sum_congr rfl
  intro y _
  have hcstar : star ((((2 : ℝ)⁻¹ ^ (3 * m)) : ℝ) : ℂ) =
      ((((2 : ℝ)⁻¹ ^ (3 * m)) : ℝ) : ℂ) := Complex.conj_ofReal _
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, twinAmplitude, star_mul,
    star_intCast]
  rw [hcstar]
  push_cast
  ring
lemma twin_density_tensor (m : ℕ)
    (qC : (Fin m → (Fin 4 → Bool)) → Bool)
    (x x' : Fin m → Bool × Bool) :
    partialTraceRight (Matrix.vecMulVec (twinAmplitude m qC)
      (star (twinAmplitude m qC))) x x' =
    ∏ i, if ((x i).1 ^^ (x i).2) = ((x' i).1 ^^ (x' i).2)
      then (1 / 4 : ℂ) else 0 := by
  rw [twin_density_gram]
  have hc : ((((2 : ℝ)⁻¹ ^ (3 * m)) ^ 2 : ℝ) : ℂ) = (1 / 64 : ℂ) ^ m := by
    push_cast
    rw [← pow_mul, show 3 * m * 2 = 6 * m by omega, pow_mul]
    norm_num
  rw [hc, Int.cast_prod]
  have hconst : (1 / 64 : ℂ) ^ m = ∏ _i : Fin m, (1 / 64 : ℂ) := by simp
  rw [hconst, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> norm_num
end
end OpLidarReduced
open scoped BigOperators ENNReal
open MeasureTheory
namespace OpLidarMeasurement
noncomputable section
def effect (α : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.vecMulVec (fun r => star ((hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 α) 0 (if r then 1 else 0)))
    (star (fun r => star ((hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 α) 0 (if r then 1 else 0))))
lemma effect_entry (α : ℝ) (r r' : Bool) : effect α r r' =
    if r = r' then 1 / 2 else ((Real.cos α : ℂ) + (if r then -1 else 1) * Complex.I * (Real.sin α : ℂ)) / 2 := by
  have hrow (b : Bool) : (hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 α) 0 (if b then 1 else 0) =
      (hadamard 0 (if b then 1 else 0)) * Complex.exp (-Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign b / 2 : ℝ) : ℂ)) := by
    cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation, Matrix.diagonal_apply, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign]
    all_goals left; congr 1; push_cast; ring
  have hw (b : Bool) : hadamard 0 (if b then 1 else 0) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    cases b <;> simp [hadamard, s2, pauliMatrix, qubitX, qubitZ]
  have hsq : (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ^ 2 = (1 / 2 : ℂ) := by
    have hr : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ)) hr
  simp only [effect, Matrix.vecMulVec_apply, Pi.star_apply, star_star]
  rw [hrow r, hrow r', hw r, hw r', star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  have he : (starRingEnd ℂ) (-Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r / 2 : ℝ) : ℂ)) = Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r / 2 : ℝ) : ℂ) := by
    rw [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [he]
  calc
    _ = (1 / 2 : ℂ) * Complex.exp (Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r / 2 : ℝ) : ℂ) - Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r' / 2 : ℝ) : ℂ)) := by
      rw [sub_eq_add_neg, Complex.exp_add, ← hsq]; ring
    _ = _ := by
      cases r <;> cases r' <;> simp only [D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, if_true, if_false, Bool.false_eq_true, Bool.true_eq_false]
      · simp <;> ring
      · have he : Complex.I * ((α * 1 / 2 : ℝ) : ℂ) - Complex.I * ((α * -1 / 2 : ℝ) : ℂ) = (α : ℂ) * Complex.I := by push_cast; ring
        rw [he, Complex.exp_ofReal_mul_I]; ring
      · have he : Complex.I * ((α * -1 / 2 : ℝ) : ℂ) - Complex.I * ((α * 1 / 2 : ℝ) : ℂ) = (-α : ℂ) * Complex.I := by push_cast; ring
        rw [he, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
        simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]; ring
      · simp <;> ring
def pairDensity : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (1 / 4 : ℂ) • ((1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) +
    (tensorOp (fun _ : Fin 2 => qubitX)).submatrix
      (fun x : Bool × Bool => ![if x.1 then 1 else 0, if x.2 then 1 else 0])
      (fun x : Bool × Bool => ![if x.1 then 1 else 0, if x.2 then 1 else 0]))
lemma pair_density_entry (x x' : Bool × Bool) : pairDensity x x' =
    if (x.1 ^^ x.2) = (x'.1 ^^ x'.2) then 1 / 4 else 0 := by
  obtain ⟨r,t⟩ := x; obtain ⟨r',t'⟩ := x'
  cases r <;> cases t <;> cases r' <;> cases t' <;>
    norm_num [pairDensity, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.submatrix_apply, tensorOp, Fin.prod_univ_two, qubitX]
private lemma pair_measurement (α β : ℝ) :
    (∑ x : Bool × Bool, ∑ x' : Bool × Bool,
      pairDensity x x' * effect α x.1 x'.1 * effect β x.2 x'.2) =
      ((1 + Real.cos α * Real.cos β) / 4 : ℝ) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pair_density_entry, effect_entry,
    Bool.xor_false, Bool.xor_true]
  norm_num
  ring
lemma measurement_tensor (m : ℕ) (α β : Fin m → ℝ) :
    (∑ x : Fin m → (Bool × Bool), ∑ x' : Fin m → (Bool × Bool),
      ∏ i, pairDensity (x i) (x' i) *
        effect (α i) (x i).1 (x' i).1 * effect (β i) (x i).2 (x' i).2) =
      ∏ i, (((1 + Real.cos (α i) * Real.cos (β i)) / 4 : ℝ) : ℂ) := by
  have hinner : ∀ x : Fin m → (Bool × Bool),
      (∑ x' : Fin m → (Bool × Bool), ∏ i,
        pairDensity (x i) (x' i) * effect (α i) (x i).1 (x' i).1 *
          effect (β i) (x i).2 (x' i).2) =
        ∏ i, ∑ x' : Bool × Bool,
          pairDensity (x i) x' * effect (α i) (x i).1 x'.1 * effect (β i) (x i).2 x'.2 := by
    intro x
    exact (Fintype.prod_sum (fun (i : Fin m) (x' : Bool × Bool) =>
      pairDensity (x i) x' * effect (α i) (x i).1 x'.1 * effect (β i) (x i).2 x'.2)).symm
  simp_rw [hinner]
  rw [← Fintype.prod_sum (fun i (x : Bool × Bool) =>
    ∑ x' : Bool × Bool, pairDensity x x' * effect (α i) x.1 x'.1 * effect (β i) x.2 x'.2)]
  simp_rw [pair_measurement]
open MeasureTheory OpLidarAnalysis
private lemma angle_sin_mean : (∫ α, Real.sin α ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) = 0 := by
  rw [angle_integral_eq, integral_sin]
  simp
lemma effect_integrable (r r' : Bool) :
    Integrable (fun α => effect α r r') (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) := by
  have hc : Integrable (fun α : ℝ => (Real.cos α : ℂ)) (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    (angle_integrable_of_continuous Real.continuous_cos).ofReal
  have hs : Integrable (fun α : ℝ => (Real.sin α : ℂ)) (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    (angle_integrable_of_continuous Real.continuous_sin).ofReal
  cases r <;> cases r' <;> simp only [effect_entry, Bool.false_eq_true, Bool.true_eq_false,
    if_true, if_false] <;> first
    | exact integrable_const _
    | exact (hc.add (hs.const_mul _)).div_const _
private lemma effect_mean (r r' : Bool) :
    (∫ α, effect α r r' ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) = if r = r' then (1 / 2 : ℂ) else 0 := by
  have hc : Integrable (fun α : ℝ => (Real.cos α : ℂ)) (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    (angle_integrable_of_continuous Real.continuous_cos).ofReal
  have hs : Integrable (fun α : ℝ => (Real.sin α : ℂ)) (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    (angle_integrable_of_continuous Real.continuous_sin).ofReal
  have hs1 : Integrable (fun α : ℝ => (1 : ℂ) * Complex.I * (Real.sin α : ℂ)) (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    hs.const_mul _
  have hsn : Integrable (fun α : ℝ => (-1 : ℂ) * Complex.I * (Real.sin α : ℂ)) (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    hs.const_mul _
  cases r <;> cases r' <;> simp only [effect_entry, Bool.false_eq_true, Bool.true_eq_false,
    if_true, if_false]
  · simp
  · rw [integral_div]
    have hsum : (∫ α : ℝ, (Real.cos α : ℂ) + 1 * Complex.I * (Real.sin α : ℂ) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) =
      (∫ α, (Real.cos α : ℂ) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) +
        ∫ α, 1 * Complex.I * (Real.sin α : ℂ) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) := integral_add hc hs1
    erw [hsum, integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal, angle_cos_mean, angle_sin_mean]
    simp
  · rw [integral_div]
    have hsum : (∫ α : ℝ, (Real.cos α : ℂ) + -1 * Complex.I * (Real.sin α : ℂ) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) =
      (∫ α, (Real.cos α : ℂ) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) +
        ∫ α, -1 * Complex.I * (Real.sin α : ℂ) ∂(ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) := integral_add hc hsn
    erw [hsum, integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal, angle_cos_mean, angle_sin_mean]
    simp
  · simp
lemma complementary_effect_mean (k : ℕ) (z z' : Fin k → Bool) :
    (∫ α : Fin k → ℝ, ∏ i, effect (α i) (z i) (z' i)
      ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) =
      ∏ i, if z i = z' i then (1 / 2 : ℂ) else 0 := by
  rw [integral_fintype_prod_eq_prod (fun i α => effect α (z i) (z' i))]
  simp_rw [effect_mean]
end
end OpLidarMeasurement
open scoped BigOperators
end D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors

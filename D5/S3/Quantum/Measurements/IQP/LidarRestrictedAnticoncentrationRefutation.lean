/- GID: D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Twin-pair marginal and Lidar anticoncentration refutation. -/
/- proof_shape: factor_literal_fractional_moment, literal_joint_fractional_moment, literal_tail_bound, result: content escape_witness: D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift admission_basis: open-problem-resolution (#13764; Refuted) graph_sqrt_shift: proof_shape: content; escape_witness: D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarProductShift.pi_periodic_shift; Registration is paused under CLAUDE.md §3.9 (信息逃逸登记暂缓). Direct frozen dependencies: D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound; D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence; D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence; D5/S3/Quantum/Information/PartialTraceMutualInformation; D5/S3/QuantumBounds/MerminMeasurementDependence/Model; D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation Same-delivery dependencies: D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors Declaration judgement: factor_literal_fractional_moment, literal_joint_fractional_moment, literal_tail_bound and result are content with live witness pi_periodic_shift; other helpers except graph_sqrt_shift are bind-only and name their consumers in the delivery review. gate_entry_exp: bind-only; consumers: random_layer_eq, measurement_row_exp, one_qubit_effect_zero, zero_gate_entry_exp. zero_gate_entry_exp: bind-only; consumers: gate_entry_norm_le_one, twinProbability_continuous, measurement_row_split. measurement_row_exp: bind-only; consumers: factor_circuit_graph_amplitude, measurement_row_effect_zero, graphProbability_continuous, measurement_row_effect_output. retained_row_prod: bind-only; consumers: retained_effect_prod, retainedRow_norm_le_one, twinProbability_continuous, measurement_row_split. retained_effect_prod: bind-only; consumer: twin_probability_conditional_mean. density_probability_sum: bind-only; consumers: densityProbability_integrable, complement_average, twin_probability_density. -/
import D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors
import D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence (hadamard s2)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (tensorOp pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open scoped BigOperators ENNReal Kronecker ComplexOrder
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation
open D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarReduced D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarMeasurement D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarAnalysis D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidarProductShift
namespace OpLidarCircuitBridge
open OpLidar
private lemma gate_entry_exp (s z : Bool) (θ : ℝ) : (hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 θ) (if s then 1 else 0) (if z then 1 else 0) = (hadamard (if s then 1 else 0) (if z then 1 else 0)) * Complex.exp (-Complex.I * ((θ * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign z / 2 : ℝ) : ℂ)) := by
  cases s <;> cases z <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation, Matrix.diagonal_apply, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign]
  all_goals left; congr 1 <;> push_cast <;> ring
private lemma zero_gate_entry_exp (α : ℝ) (b : Bool) : (hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 α) 0 (if b then 1 else 0) = hadamard 0 (if b then 1 else 0) * Complex.exp (-Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign b / 2 : ℝ) : ℂ)) := gate_entry_exp false b α
private lemma random_layer_eq {m : ℕ} (θ : (Fin (6 * m)) → ℝ) (s z : (Fin (6 * m) → Bool)) : randomLayer m θ s z = (tensorOp (fun _ : Fin (6 * m) => hadamard) (fun i => if s i then 1 else 0) (fun i => if z i then 1 else 0)) * Complex.exp (-Complex.I * ((∑ i, θ i * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i) / 2 : ℝ) : ℂ)) := by
  simp only [randomLayer, Matrix.submatrix_apply, tensorOp, Matrix.of_apply]
  simp_rw [OpLidarCircuitBridge.gate_entry_exp]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  simp [Complex.ofReal_sum, Finset.mul_sum]
lemma circuit_amplitude_literal {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) (s : (Fin (6 * m) → Bool)) : circuit G θ s (fun _ => false) = ∑ z : (Fin (6 * m) → Bool), (tensorOp (fun _ : Fin (6 * m) => hadamard) (fun i => if s i then 1 else 0) (fun i => if z i then 1 else 0)) * Complex.exp (-Complex.I * ((HZ G z + ∑ i, θ i * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i) / 2 : ℝ) : ℂ)) * (tensorOp (fun _ : Fin (6 * m) => hadamard) (fun i => if z i then 1 else 0) (fun i => if (fun _ => false) i then 1 else 0)) := by
  rw [circuit, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl; intro z _
  simp only [Matrix.of_apply, Matrix.submatrix_apply, random_layer_eq, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring
end OpLidarCircuitBridge
open OpLidarCircuitBridge
namespace OpLidarEntangler
open OpLidar
private lemma zz_bit (b c : Bool) : D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign b * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign c = 1 - 2 * (b.toNat : ℝ) - 2 * (c.toNat : ℝ) + 4 * (b.toNat : ℝ) * (c.toNat : ℝ) := by
  cases b <;> cases c <;> norm_num [D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign]
private lemma incidence_sum {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (V × V)) (f : V → ℝ) (hloop : ∀ e ∈ E, e.1 ≠ e.2) : (∑ e ∈ E, (f e.1 + f e.2)) = ∑ v, ((E.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * f v := by
  calc
    _ = ∑ e ∈ E, ∑ v, if e.1 = v ∨ e.2 = v then f v else 0 := by
      apply Finset.sum_congr rfl; intro e he
      rw [← Finset.sum_filter]
      have hsplit : (Finset.univ.filter (fun v => e.1 = v ∨ e.2 = v)) = {e.1, e.2} := by
        ext v
        simp [eq_comm]
      rw [hsplit]
      simp [hloop e he]
    _ = ∑ v, ∑ e ∈ E, if e.1 = v ∨ e.2 = v then f v else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro v _
      rw [← Finset.sum_filter]
      simp
private lemma entangler_energy {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (z : (Fin (6 * m) → Bool)) (hloop : ∀ e ∈ G, e.1 ≠ e.2) (hdegree : ∀ v, edgeDegree G v = 4) (hcard : G.card = 12 * m) : (∑ e ∈ G, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.1) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.2)) = (12 * m : ℝ) - 8 * (∑ v, (z v).toNat : ℕ) + 4 * (∑ e ∈ G, (z e.1).toNat * (z e.2).toNat : ℕ) := by
  simp_rw [zz_bit]
  have hi := incidence_sum G (fun v => ((z v).toNat : ℝ)) hloop
  replace hi : (∑ e ∈ G, (((z e.1).toNat : ℝ) + ((z e.2).toNat : ℝ))) = ∑ v, (edgeDegree G v : ℝ) * ((z v).toNat : ℝ) := by simpa only [edgeDegree, Sym2.mem_iff, eq_comm] using hi
  simp only [hdegree] at hi
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  push_cast at hi ⊢
  simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hi ⊢
  nlinarith
private lemma pi_entangler_phase (m k q : ℕ) : Complex.exp (-Complex.I * ((Real.pi / 4 * ((12 * m : ℝ) - 8 * k + 4 * q) : ℝ) : ℂ)) = (-1 : ℂ) ^ m * (-1 : ℂ) ^ q := by
  have hphase : -Complex.I * ((Real.pi / 4 * ((12 * m : ℝ) - 8 * k + 4 * q) : ℝ) : ℂ) = ((3 * m : ℕ) : ℂ) * (-(Real.pi * Complex.I)) + (k : ℂ) * (2 * Real.pi * Complex.I) + (q : ℂ) * (-(Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [hphase, Complex.exp_add, Complex.exp_add]
  simp only [Complex.exp_nat_mul, Complex.exp_neg_pi_mul_I, Complex.exp_two_pi_mul_I, one_pow, mul_one, pow_mul]
  norm_num
private lemma card_of_four_regular {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hloop : ∀ e ∈ G, e.1 ≠ e.2) (hdegree : ∀ v, edgeDegree G v = 4) : G.card = 12 * m := by
  have hi := incidence_sum G (fun _ => (1 : ℝ)) hloop
  replace hi : (∑ e ∈ G, (1 + 1 : ℝ)) = ∑ v, (edgeDegree G v : ℝ) * 1 := by simpa only [edgeDegree, Sym2.mem_iff, eq_comm] using hi
  simp only [hdegree, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi
  exact_mod_cast (show (G.card : ℝ) = 12 * m by push_cast at hi; nlinarith)
private lemma entangler_eq_CZ {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (z : (Fin (6 * m) → Bool)) (hloop : ∀ e ∈ G, e.1 ≠ e.2) (hdegree : ∀ v, edgeDegree G v = 4) (hcard : G.card = 12 * m) : Complex.exp (-Complex.I * ((Real.pi / 4 * (∑ e ∈ G, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.1) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.2)) : ℝ) : ℂ)) = (-1 : ℂ) ^ m * ∏ e ∈ G, (-1 : ℂ) ^ ((z e.1).toNat * (z e.2).toNat) := by
  rw [entangler_energy G z hloop hdegree hcard, pi_entangler_phase]
  rw [Finset.prod_pow_eq_pow_sum]
private lemma factor_entangler_eq_CZ {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (z : (Fin (6 * m) → Bool)) : Complex.exp (-Complex.I * ((Real.pi / 4 * (∑ e ∈ G, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.1) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.2)) : ℝ) : ℂ)) = (-1 : ℂ) ^ m * ∏ e ∈ G, (-1 : ℂ) ^ ((z e.1).toNat * (z e.2).toNat) := by
  have hf : G ⊆ hardwareEdges m ∧ ∀ v, edgeDegree G v = 4 := by
    simpa only [F4, Finset.mem_filter, Finset.mem_powerset] using hG
  have hloop : ∀ e ∈ G, e.1 ≠ e.2 := by
    intro e he
    have hh := hf.1 he
    simp only [hardwareEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    intro heq
    have hval := congrArg Fin.val heq
    omega
  exact entangler_eq_CZ G z hloop hf.2 (card_of_four_regular G hloop hf.2)
end OpLidarEntangler
namespace OpLidarGraphPhase
private def graphPhase {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (z : (Fin (6 * m) → Bool)) : ℂ := ∏ e ∈ E, (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z e.1) else (z e.2)))
end OpLidarGraphPhase
namespace OpLidarStateBridge
open OpLidar OpLidarCircuitBridge OpLidarEntangler OpLidarMeasurement
def graphAmplitude {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (z : (Fin (6 * m) → Bool)) : ℂ := (tensorOp (fun _ : Fin (6 * m) => hadamard) (fun i => if z i then 1 else 0) (fun i => if (fun _ => false) i then 1 else 0)) * OpLidarGraphPhase.graphPhase G z
def measurementRow {m : ℕ} (s : Fin (6 * m) → Bool) (φ : Fin (6 * m) → ℝ) : (Fin (6 * m) → Bool) → ℂ :=
  tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (φ i)) (fun i => if s i then 1 else 0) ∘ (fun z i => if z i then 1 else 0)
private lemma measurement_row_exp {m : ℕ} (s : Fin (6 * m) → Bool) (φ : Fin (6 * m) → ℝ) (z : Fin (6 * m) → Bool) : measurementRow s φ z = ∏ i, hadamard (if s i then 1 else 0) (if z i then 1 else 0) * Complex.exp (-Complex.I * ((φ i * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i) / 2 : ℝ) : ℂ)) := by
  simp only [measurementRow, tensorOp, Matrix.of_apply, Function.comp_apply, OpLidarCircuitBridge.gate_entry_exp]
private lemma phase_fields {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) (z : (Fin (6 * m) → Bool)) : Complex.exp (-Complex.I * ((HZ G z + ∑ i, θ i * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i) / 2 : ℝ) : ℂ)) = Complex.exp (-Complex.I * ((Real.pi / 4 * ∑ e ∈ G, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.1) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.2) : ℝ) : ℂ)) * ∏ i, Complex.exp (-Complex.I * (((θ i + 2 * (Real.pi / 7)) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i) / 2 : ℝ) : ℂ)) := by
  have hf : HZ G z + (∑ i, θ i * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i) / 2) = (Real.pi / 4) * (∑ e ∈ G, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.1) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z e.2)) + ∑ i, (θ i + 2 * (Real.pi / 7)) * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (z i) / 2 := by
    unfold HZ
    simp_rw [add_mul, add_div]
    rw [Finset.sum_add_distrib]
    ring
  rw [← Complex.exp_sum, ← Complex.exp_add, hf]
  congr 1
  simp [Complex.ofReal_add, Complex.ofReal_sum, mul_add, Finset.mul_sum]
private lemma factor_circuit_graph_amplitude {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (θ : (Fin (6 * m)) → ℝ) (s : (Fin (6 * m) → Bool)) : circuit G θ s (fun _ => false) = (-1 : ℂ) ^ m * ∑ z : (Fin (6 * m) → Bool), graphAmplitude G z * measurementRow s (fun i => θ i + 2 * (Real.pi / 7)) z := by
  rw [circuit_amplitude_literal, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  rw [phase_fields, factor_entangler_eq_CZ G hG z]
  rw [measurement_row_exp]
  unfold graphAmplitude tensorOp
  simp only [Matrix.of_apply, OpLidarGraphPhase.graphPhase, D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase, Sym2.lift_mk, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rw [Finset.prod_mul_distrib]
  ring
lemma factor_output_graph_probability {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (θ : (Fin (6 * m)) → ℝ) (s : (Fin (6 * m) → Bool)) : outputProbability G θ s = Complex.normSq (∑ z : (Fin (6 * m) → Bool), graphAmplitude G z * measurementRow s (fun i => θ i + 2 * (Real.pi / 7)) z) := by
  unfold outputProbability
  rw [factor_circuit_graph_amplitude G hG, Complex.normSq_mul, map_pow]
  norm_num
lemma W_false_squared : ((hadamard (if false then 1 else 0) (if false then 1 else 0))) ^ 2 = (1 / 2 : ℂ) := by
  have hsq : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simpa [hadamard, s2, pauliMatrix, qubitX, qubitZ, Complex.ofReal_pow, Complex.ofReal_div] using congrArg (fun x : ℝ => (x : ℂ)) hsq
lemma one_qubit_effect_zero (α : ℝ) (r r' : Bool) : ((hadamard (if false then 1 else 0) (if r then 1 else 0)) * Complex.exp (-Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r / 2 : ℝ) : ℂ))) * star ((hadamard (if false then 1 else 0) (if r' then 1 else 0)) * Complex.exp (-Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r' / 2 : ℝ) : ℂ))) = effect α r' r := by
  rw [← OpLidarCircuitBridge.gate_entry_exp false r α, ← OpLidarCircuitBridge.gate_entry_exp false r' α]
  simp only [effect, Matrix.vecMulVec_apply, Pi.star_apply, star_star, Bool.false_eq_true, if_false]
  ring
private lemma measurement_row_effect_zero {m : ℕ} (φ : (Fin (6 * m)) → ℝ) (z z' : (Fin (6 * m) → Bool)) : measurementRow (fun _ => false) φ z * star (measurementRow (fun _ => false) φ z') = ∏ i, effect (φ i) (z' i) (z i) := by
  simp_rw [measurement_row_exp]
  rw [star_prod, ← Finset.prod_mul_distrib]
  simp_rw [one_qubit_effect_zero]
lemma graph_probability_effect_zero {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (φ : (Fin (6 * m)) → ℝ) : (Complex.normSq (∑ z : (Fin (6 * m) → Bool), graphAmplitude G z * measurementRow (fun _ => false) φ z) : ℂ) = ∑ z : (Fin (6 * m) → Bool), ∑ z' : (Fin (6 * m) → Bool), graphAmplitude G z * star (graphAmplitude G z') * ∏ i, effect (φ i) (z' i) (z i) := by
  rw [Complex.normSq_eq_conj_mul_self]
  change star (∑ z : (Fin (6 * m) → Bool), graphAmplitude G z * measurementRow (fun _ => false) φ z) * _ = _
  rw [star_sum, Finset.sum_mul, Finset.sum_comm]
  simp_rw [Finset.mul_sum, star_mul]
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro z' _
  rw [← measurement_row_effect_zero]
  ring
end OpLidarStateBridge
open MeasureTheory
namespace OpLidarAveraging
open OpLidarMeasurement OpLidarReduced
def densityProbability {A : Type*} [Fintype A] (k : ℕ) (ρ : Matrix (A × (Fin k → Bool)) (A × (Fin k → Bool)) ℂ) (E : A → A → ℂ) (α : Fin k → ℝ) : ℂ :=
  Matrix.trace (ρ * ((Matrix.of E).transpose ⊗ₖ
    (tensorOp (fun i => Matrix.vecMulVec
      (fun r : Fin 2 => star ((hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) 0 r))
      (star (fun r : Fin 2 => star ((hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) 0 r))))).submatrix
      (fun z : Fin k → Bool => fun i => if z i then 1 else 0)
      (fun z : Fin k → Bool => fun i => if z i then 1 else 0)))
private lemma density_probability_sum {A : Type*} [Fintype A] (k : ℕ) (ρ : Matrix (A × (Fin k → Bool)) (A × (Fin k → Bool)) ℂ) (E : A → A → ℂ) (α : Fin k → ℝ) : densityProbability k ρ E α = ∑ x : A, ∑ x' : A, ∑ z : Fin k → Bool, ∑ z' : Fin k → Bool, ρ (x,z) (x',z') * E x x' * ∏ i, effect (α i) (z' i) (z i) := by
  simp only [densityProbability, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, Matrix.submatrix_apply, tensorOp, Matrix.of_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_star, Fintype.sum_prod_type, effect]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x' _
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro z' _
  ring
private lemma densityProbability_integrable {A : Type*} [Fintype A] (k : ℕ) (ρ : Matrix (A × (Fin k → Bool)) (A × (Fin k → Bool)) ℂ) (E : A → A → ℂ) : Integrable (densityProbability k ρ E) (Measure.pi fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) := by
  change Integrable (fun α => densityProbability k ρ E α) _
  simp_rw [density_probability_sum]
  repeat apply integrable_finsetSum; intro _ _
  exact (Integrable.fintype_prod (fun i => effect_integrable _ _)).const_mul _
private lemma complement_average {A : Type*} [Fintype A] (k : ℕ) (ρ : Matrix (A × (Fin k → Bool)) (A × (Fin k → Bool)) ℂ) (E : A → A → ℂ) : (∫ α, densityProbability k ρ E α ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = (1 / 2 : ℂ) ^ k * ∑ x : A, ∑ x' : A, D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight ρ x x' * E x x' := by
  simp_rw [density_probability_sum]
  have hi : ∀ x x' z z', Integrable (fun α : Fin k → ℝ => ρ (x,z) (x',z') * E x x' * ∏ i, effect (α i) (z' i) (z i)) (Measure.pi fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) := by
    intro x x' z z'
    exact (Integrable.fintype_prod (fun i => effect_integrable _ _)).const_mul _
  simp_rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun x' _ => integrable_finsetSum _ (fun z _ => integrable_finsetSum _ (fun z' _ => hi x x' z z')))), integral_finsetSum _ (fun x' _ => integrable_finsetSum _ (fun z _ => integrable_finsetSum _ (fun z' _ => hi _ x' z z'))), integral_finsetSum _ (fun z _ => integrable_finsetSum _ (fun z' _ => hi _ _ z z')), integral_finsetSum _ (fun z' _ => hi _ _ _ z'), integral_const_mul, complementary_effect_mean]
  have hp : ∀ z z' : Fin k → Bool, (∏ i, if z i = z' i then (1 / 2 : ℂ) else 0) = if z = z' then (1 / 2 : ℂ) ^ k else 0 := by
    intro z z'
    by_cases h : z = z'
    · simp [h]
    · obtain ⟨i,hi⟩ := Function.ne_iff.1 h
      rw [if_neg h]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  simp_rw [hp]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro x' _
  apply Finset.sum_congr rfl; intro z _
  ring
end OpLidarAveraging
namespace OpLidarReindex
open OpLidarReduced OpLidarMeasurement OpLidarAveraging
def complementEquiv (m : ℕ) : (Fin (4*m) → Bool) ≃ (Fin m → Fin 4 → Bool) := ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 4))).symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.curry (Fin m) (Fin 4) Bool)
def reindexedTwinAmplitude (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (xz : (Fin m → Bool × Bool) × (Fin (4*m) → Bool)) : ℂ := twinAmplitude m qC (xz.1, complementEquiv m xz.2)
lemma reindexed_twin_marginal (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (x x' : Fin m → Bool × Bool) : D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (Matrix.vecMulVec (reindexedTwinAmplitude m qC) (star (reindexedTwinAmplitude m qC))) x x' = ∏ i, pairDensity (x i) (x' i) := by
  classical
  simp only [pair_density_entry]
  rw [← twin_density_tensor m qC x x']
  unfold D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
  exact Fintype.sum_equiv (complementEquiv m) _ _ (by intro z; rfl)
private lemma measurement_tensor_transpose (m : ℕ) (α β : Fin m → ℝ) : (∑ x : Fin m → (Bool × Bool), ∑ x' : Fin m → (Bool × Bool), ∏ i, pairDensity (x i) (x' i) * effect (α i) (x' i).1 (x i).1 * effect (β i) (x' i).2 (x i).2) = ∏ i, (((1 + Real.cos (α i) * Real.cos (β i)) / 4 : ℝ) : ℂ) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : Fin m → (Bool × Bool), ∑ x' : Fin m → (Bool × Bool), ∏ i, pairDensity (x i) (x' i) * effect (α i) (x i).1 (x' i).1 * effect (β i) (x i).2 (x' i).2 := by
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro x' _
      apply Finset.prod_congr rfl; intro i _
      have hd : pairDensity (x' i) (x i) = pairDensity (x i) (x' i) := by
        simp only [pair_density_entry, eq_comm]
      rw [hd]
    _ = _ := measurement_tensor m α β
end OpLidarReindex
namespace OpLidarTwinProbability
open OpLidarCircuitBridge
def retainedRow (m : ℕ) (φ : Fin m → ℝ × ℝ) (x : Fin m → Bool × Bool) : ℂ :=
  tensorOp (fun i : Fin (m + m) => Sum.elim
    (fun j => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (φ j).1)
    (fun j => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (φ j).2) (finSumFinEquiv.symm i))
    (fun _ => 0) (fun i => if Sum.elim (fun j => (x j).1) (fun j => (x j).2) (finSumFinEquiv.symm i) then 1 else 0)
private lemma retained_row_prod (m : ℕ) (φ : Fin m → ℝ × ℝ) (x : Fin m → Bool × Bool) : retainedRow m φ x =
    ∏ i, (hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (φ i).1) 0 (if (x i).1 then 1 else 0) *
      (hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (φ i).2) 0 (if (x i).2 then 1 else 0) := by
  simp only [retainedRow, tensorOp, Matrix.of_apply]
  rw [← finSumFinEquiv.prod_comp]
  simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type]
  rw [← Finset.prod_mul_distrib]; rfl
end OpLidarTwinProbability
namespace OpLidarReindex
open OpLidarReduced OpLidarMeasurement OpLidarAveraging OpLidarTwinProbability
def retainedEffect (m : ℕ) (φ : Fin m → ℝ × ℝ) (x x' : Fin m → Bool × Bool) : ℂ :=
  Matrix.vecMulVec (retainedRow m φ) (star (retainedRow m φ)) x x'
private lemma retained_effect_prod (m : ℕ) (φ : Fin m → ℝ × ℝ) (x x' : Fin m → Bool × Bool) : retainedEffect m φ x x' =
    ∏ i, effect (φ i).1 (x' i).1 (x i).1 * effect (φ i).2 (x' i).2 (x i).2 := by
  simp only [retainedEffect, Matrix.vecMulVec_apply, Pi.star_apply, retained_row_prod, star_prod,
    star_mul, effect, Matrix.vecMulVec_apply, Pi.star_apply, star_star]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _; ring
def twinDensityProbability (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) (α : Fin (4*m) → ℝ) : ℂ := densityProbability (4*m) (Matrix.vecMulVec (reindexedTwinAmplitude m qC) (star (reindexedTwinAmplitude m qC))) (retainedEffect m φ) α
private lemma twin_probability_conditional_mean (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) : (∫ α, twinDensityProbability m qC φ α ∂MeasureTheory.Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = (1 / 2 : ℂ) ^ (4*m) * ∏ i, (((1 + Real.cos (φ i).1 * Real.cos (φ i).2) / 4 : ℝ) : ℂ) := by
  classical
  unfold twinDensityProbability
  rw [complement_average]
  simp_rw [reindexed_twin_marginal]
  simp_rw [retained_effect_prod]
  simp_rw [← Finset.prod_mul_distrib, ← mul_assoc]
  rw [measurement_tensor_transpose]
def normalizedTwinDensity (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) (α : Fin (4*m) → ℝ) : ℝ := (2 : ℝ) ^ (6*m) * (twinDensityProbability m qC φ α).re
lemma normalized_twin_conditional_mean (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) : (∫ α, normalizedTwinDensity m qC φ α ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = ∏ i, (1 + Real.cos (φ i).1 * Real.cos (φ i).2) := by
  have hi : Integrable (twinDensityProbability m qC φ) (Measure.pi fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) := densityProbability_integrable _ _ _
  unfold normalizedTwinDensity
  rw [integral_const_mul]
  have hre : (∫ α, (twinDensityProbability m qC φ α).re ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) = (∫ α, twinDensityProbability m qC φ α ∂Measure.pi (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))).re := integral_re hi
  rw [hre, twin_probability_conditional_mean]
  have hr : ((1 / 2 : ℂ) ^ (4*m) * ∏ i, (((1 + Real.cos (φ i).1 * Real.cos (φ i).2) / 4 : ℝ) : ℂ)).re = (1 / 2 : ℝ) ^ (4*m) * ∏ i, ((1 + Real.cos (φ i).1 * Real.cos (φ i).2) / 4) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, ← Complex.ofReal_prod, ← Complex.ofReal_mul]
    rfl
  rw [hr, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : (2 : ℝ) ^ (6*m) * (1 / 2 : ℝ) ^ (4*m) / (4 : ℝ) ^ m = 1 := by
    rw [pow_mul, pow_mul, ← mul_pow, ← div_pow]
    norm_num
  calc
    _ = ((2 : ℝ) ^ (6*m) * (1 / 2 : ℝ) ^ (4*m) / (4 : ℝ) ^ m) * ∏ i, (1 + Real.cos (φ i).1 * Real.cos (φ i).2) := by ring
    _ = _ := by rw [hc,one_mul]
end OpLidarReindex
namespace OpLidarTwinProbability
open OpLidar OpLidarStateBridge OpLidarReindex OpLidarMeasurement
def twinProbability (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) (α : Fin (4*m) → ℝ) : ℝ := Complex.normSq (∑ x : Fin m → Bool × Bool, ∑ z : Fin (4*m) → Bool, reindexedTwinAmplitude m qC (x,z) * retainedRow m φ x * (tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) (fun _ => 0) (fun i => if z i then 1 else 0)))
lemma normSq_finite_sum {I : Type*} [Fintype I] (f : I → ℂ) : (Complex.normSq (∑ i, f i) : ℂ) = ∑ i, ∑ j, f i * star (f j) := by
  rw [Complex.normSq_eq_conj_mul_self]
  change star (∑ i, f i) * _ = _
  rw [star_sum, Finset.sum_mul, Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring
private lemma retainedRow_effect (m : ℕ) (φ : Fin m → ℝ × ℝ) (x x' : Fin m → Bool × Bool) : retainedRow m φ x * star (retainedRow m φ x') = retainedEffect m φ x x' := by
  rfl
private lemma tensor_zero_row_effect (k : ℕ) (α : Fin k → ℝ) (z z' : Fin k → Bool) : (tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) (fun _ => 0) (fun i => if z i then 1 else 0)) * star ((tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) (fun _ => 0) (fun i => if z' i then 1 else 0))) = ∏ i, effect (α i) (z' i) (z i) := by
  simp only [tensorOp, Matrix.of_apply]
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  simp only [effect, Matrix.vecMulVec_apply, Pi.star_apply, star_star]
  ring
lemma twin_probability_density (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) (α : Fin (4*m) → ℝ) : (twinProbability m qC φ α : ℂ) = twinDensityProbability m qC φ α := by
  classical
  unfold twinProbability
  rw [← Fintype.sum_prod_type' (fun x z => reindexedTwinAmplitude m qC (x,z) * retainedRow m φ x * (tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) (fun _ => 0) (fun i => if z i then 1 else 0))), normSq_finite_sum]
  simp only [Fintype.sum_prod_type]
  unfold twinDensityProbability
  simp_rw [OpLidarAveraging.density_probability_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x' _
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro z' _
  simp only [star_mul, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [← retainedRow_effect, ← tensor_zero_row_effect]
  ring
lemma normalized_density_nonneg (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) (α : Fin (4*m) → ℝ) : 0 ≤ normalizedTwinDensity m qC φ α := by
  unfold normalizedTwinDensity
  rw [← twin_probability_density]
  simp only [Complex.ofReal_re]
  exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
end OpLidarTwinProbability
namespace OpLidarAngleSplit
open MeasureTheory OpLidar OpLidarAnalysis
def retainedSplit (m : ℕ) : ((Fin m ⊕ Fin m) → ℝ) ≃ᵐ (Fin m → ℝ × ℝ) := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => ℝ)).trans (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm
def angleSplit (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) : ((Fin (6 * m)) → ℝ) ≃ᵐ ((Fin m → ℝ × ℝ) × (Fin (4*m) → ℝ)) := (MeasurableEquiv.piCongrLeft (fun _ : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) => ℝ) e.symm).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) => ℝ)).trans ((retainedSplit m).prodCongr (MeasurableEquiv.refl _)))
private lemma retainedSplit_preserves (m : ℕ) : MeasurePreserving (retainedSplit m) (Measure.pi fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) (Measure.pi fun _ => pairAngle) := by
  have hp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m) (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) (fun _ => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))
  have hs := measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))
  exact hp.symm.comp hs
private lemma angleSplit_preserves (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) : MeasurePreserving (angleSplit m e) (uniformAngles m) ((Measure.pi fun _ : Fin m => pairAngle).prod (Measure.pi fun _ : Fin (4*m) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) := by
  have he := measurePreserving_piCongrLeft (fun _ : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) e.symm
  have hs := measurePreserving_sumPiEquivProdPi (fun _ : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))
  have hr := (retainedSplit_preserves m).prod (MeasurePreserving.id (Measure.pi fun _ : Fin (4*m) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))))
  exact hr.comp (hs.comp he)
lemma split_integral (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) (f : ((Fin m → ℝ × ℝ) × (Fin (4*m) → ℝ)) → ℝ) : (∫ θ, f (angleSplit m e θ) ∂uniformAngles m) = ∫ w, f w ∂((Measure.pi fun _ : Fin m => pairAngle).prod (Measure.pi fun _ : Fin (4*m) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))))) := (angleSplit_preserves m e).integral_comp' f
end OpLidarAngleSplit
namespace OpLidarTwinMoment
open OpLidar OpLidarStateBridge OpLidarReindex OpLidarMeasurement OpLidarTwinProbability MeasureTheory OpLidarAnalysis
lemma gate_entry_norm_le_one (α : ℝ) (b : Bool) : ‖((hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 α) 0 (if b then 1 else 0))‖ ≤ 1 := by
  have hw : ‖(hadamard (if false then 1 else 0) (if false then 1 else 0))‖ ^ 2 = (1 / 2 : ℝ) := by
    have h := congrArg norm W_false_squared
    simpa only [norm_pow, norm_div, norm_one, Complex.norm_ofNat] using h
  have hW : ‖(hadamard (if false then 1 else 0) (if b then 1 else 0))‖ ≤ 1 := by
    have he : (hadamard (if false then 1 else 0) (if b then 1 else 0)) = (hadamard (if false then 1 else 0) (if false then 1 else 0)) := by cases b <;> norm_num [hadamard, s2, pauliMatrix, qubitX, qubitZ]
    rw [he]
    nlinarith [norm_nonneg ((hadamard (if false then 1 else 0) (if false then 1 else 0)))]
  have heq := congrArg norm (OpLidarCircuitBridge.zero_gate_entry_exp α b)
  rw [norm_mul] at heq
  have hphase : -Complex.I * ((α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign b / 2 : ℝ) : ℂ) = ((-α * D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign b / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hphase, Complex.norm_exp_ofReal_mul_I, mul_one] at heq
  exact heq.trans_le hW
private lemma retainedRow_norm_le_one (m : ℕ) (φ : Fin m → ℝ × ℝ) (x : Fin m → Bool × Bool) : ‖retainedRow m φ x‖ ≤ 1 := by
  simp_rw [retained_row_prod]
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_mul]
  exact (mul_le_mul (gate_entry_norm_le_one _ _) (gate_entry_norm_le_one _ _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
private lemma tensor_zero_row_norm_le_one (k : ℕ) (α : Fin k → ℝ) (z : Fin k → Bool) : ‖(tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) (fun _ => 0) (fun i => if z i then 1 else 0))‖ ≤ 1 := by
  simp only [tensorOp, Matrix.of_apply]
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => gate_entry_norm_le_one _ _)
private def amplitudeBudget (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) : ℝ := ∑ x : Fin m → Bool × Bool, ∑ z : Fin (4*m) → Bool, ‖reindexedTwinAmplitude m qC (x,z)‖
private lemma twinProbability_bound (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) (α : Fin (4*m) → ℝ) : twinProbability m qC φ α ≤ amplitudeBudget m qC ^ 2 := by
  have hnorm : ‖∑ x : Fin m → Bool × Bool, ∑ z : Fin (4*m) → Bool, reindexedTwinAmplitude m qC (x,z) * retainedRow m φ x * (tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 (α i)) (fun _ => 0) (fun i => if z i then 1 else 0))‖ ≤ amplitudeBudget m qC := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro x _
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro z _
    rw [norm_mul,norm_mul]
    calc
      _ ≤ ‖reindexedTwinAmplitude m qC (x,z)‖ * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (retainedRow_norm_le_one m φ x) (norm_nonneg _)
        · exact tensor_zero_row_norm_le_one _ α z
        · exact norm_nonneg _
        · exact mul_nonneg (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  unfold twinProbability
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
private lemma twinProbability_continuous (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) : Continuous (fun w : (Fin m → ℝ × ℝ) × (Fin (4*m) → ℝ) => twinProbability m qC w.1 w.2) := by
  unfold twinProbability
  simp_rw [retained_row_prod]
  simp only [tensorOp, Matrix.of_apply]
  simp_rw [OpLidarCircuitBridge.zero_gate_entry_exp]
  apply Complex.continuous_normSq.comp
  fun_prop
lemma normalizedDensity_eq (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (φ : Fin m → ℝ × ℝ) (α : Fin (4*m) → ℝ) : normalizedTwinDensity m qC φ α = (2 : ℝ) ^ (6*m) * twinProbability m qC φ α := by
  unfold normalizedTwinDensity
  rw [← twin_probability_density]
  rfl
private lemma normalizedDensity_integrable {A : Type*} [MeasurableSpace A] [TopologicalSpace A] [OpensMeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) (f : A → (Fin m → ℝ × ℝ) × (Fin (4*m) → ℝ)) (hf : Continuous f) : Integrable (fun w => normalizedTwinDensity m qC (f w).1 (f w).2) μ ∧ Integrable (fun w => Real.sqrt (normalizedTwinDensity m qC (f w).1 (f w).2)) μ := by
  have hc : Continuous (fun w => normalizedTwinDensity m qC (f w).1 (f w).2) := by
    simp_rw [normalizedDensity_eq]
    exact continuous_const.mul ((twinProbability_continuous m qC).comp hf)
  have hb : ∀ w, normalizedTwinDensity m qC (f w).1 (f w).2 ≤ (2 : ℝ) ^ (6*m) * amplitudeBudget m qC ^ 2 := by
    intro w
    rw [normalizedDensity_eq]
    exact mul_le_mul_of_nonneg_left (twinProbability_bound m qC _ _) (by positivity)
  constructor
  · refine (integrable_const ((2 : ℝ) ^ (6*m) * amplitudeBudget m qC ^ 2)).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro w
    rw [Real.norm_of_nonneg (normalized_density_nonneg _ _ _ _)]
    exact hb w
  · refine (integrable_const (Real.sqrt ((2 : ℝ) ^ (6*m) * amplitudeBudget m qC ^ 2))).mono' (Real.continuous_sqrt.comp hc).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro w
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hb w)
lemma twin_fractional_moment (m : ℕ) (qC : (Fin m → Fin 4 → Bool) → Bool) : (∫ w, Real.sqrt (normalizedTwinDensity m qC w.1 w.2) ∂((Measure.pi fun _ : Fin m => pairAngle).prod (Measure.pi fun _ : Fin (4*m) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))))) ≤ (47 / 48 : ℝ) ^ m := by
  apply conditional_fractional_moment (Measure.pi fun _ : Fin (4*m) => (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) m (fun w => normalizedTwinDensity m qC w.1 w.2)
  · intro w; exact normalized_density_nonneg _ _ _ _
  · intro φ
    exact normalizedDensity_integrable _ m qC (fun α => (φ,α)) (continuous_const.prodMk continuous_id)
  · exact (normalizedDensity_integrable _ m qC id continuous_id).2
  · intro φ; exact normalized_twin_conditional_mean m qC φ
end OpLidarTwinMoment
namespace OpLidarGraphAnalysis
open OpLidar OpLidarStateBridge OpLidarTwinProbability OpLidarTwinMoment OpLidarMeasurement OpLidarProductShift
set_option maxHeartbeats 2000000
def graphProbability {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) : ℝ := Complex.normSq (∑ z : (Fin (6 * m) → Bool),graphAmplitude G z * measurementRow (fun _ => false) θ z)
private def graphBudget {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) : ℝ := ∑ z : (Fin (6 * m) → Bool), ‖graphAmplitude G z‖
private lemma graphProbability_continuous {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) : Continuous (graphProbability G) := by
  unfold graphProbability
  simp_rw [measurement_row_exp]
  fun_prop
private lemma graphProbability_bound {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) : graphProbability G θ ≤ graphBudget G ^ 2 := by
  have hr : ∀ z : (Fin (6 * m) → Bool), ‖measurementRow (fun _ => false) θ z‖ ≤ 1 := by
    intro z
    simp only [measurementRow, tensorOp, Matrix.of_apply, Function.comp_apply]
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => gate_entry_norm_le_one (θ i) (z i))
  have hs : ‖∑ z : (Fin (6 * m) → Bool),graphAmplitude G z * measurementRow (fun _ => false) θ z‖ ≤ graphBudget G := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro z _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _)).trans_eq (mul_one _)
  unfold graphProbability
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hs 2
private lemma effect_periodic (α : ℝ) (r r' : Bool) : effect (α+2*Real.pi) r r' = effect α r r' := by
  simp [effect_entry, Real.cos_add_two_pi, Real.sin_add_two_pi]
private lemma graphProbability_coordinate_periodic {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) (i : (Fin (6 * m))) : Function.Periodic (fun t => graphProbability G (Function.update θ i t)) (2*Real.pi) := by
  classical
  intro t
  apply Complex.ofReal_injective
  unfold graphProbability
  rw [graph_probability_effect_zero,graph_probability_effect_zero]
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro z' _
  congr 1
  apply Finset.prod_congr rfl; intro j _
  by_cases h : j=i
  · subst j
    simp only [Function.update_self]
    exact effect_periodic _ _ _
  · simp [Function.update_of_ne h]
lemma graph_sqrt_shift {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (d : (Fin (6 * m)) → ℝ) : (∫ θ, Real.sqrt ((2:ℝ)^(6*m) * graphProbability G (fun i => θ i+d i)) ∂uniformAngles m) = ∫ θ, Real.sqrt ((2:ℝ)^(6*m) * graphProbability G θ) ∂uniformAngles m := by
  apply pi_periodic_shift (6*m) (fun θ => Real.sqrt ((2:ℝ)^(6*m) * graphProbability G θ)) (Real.continuous_sqrt.comp (continuous_const.mul (graphProbability_continuous G))) (Real.sqrt ((2:ℝ)^(6*m) * graphBudget G ^ 2))
  · intro θ
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (graphProbability_bound G θ) (by positivity))
  · intro θ i t
    exact congrArg (fun x : ℝ => Real.sqrt ((2:ℝ)^(6*m)*x)) (graphProbability_coordinate_periodic G θ i t)
end OpLidarGraphAnalysis
open D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation
namespace OpLidarFactorAverage
open MeasureTheory OpLidar OpLidarAnalysis
private lemma uniformFactors_probability (m : ℕ) (hne : (F4 m).Nonempty) : IsProbabilityMeasure (ProbabilityTheory.uniformOn (↑(F4 m) : Set (Finset (Fin (6 * m) × Fin (6 * m))))) := by
  exact ProbabilityTheory.isProbabilityMeasure_uniformOn (F4 m).finite_toSet (by simpa using hne)
private lemma factor_integral (m : ℕ) (f : Finset ((Fin (6 * m) × Fin (6 * m))) → ℝ) : (∫ G, f G ∂(ProbabilityTheory.uniformOn (↑(F4 m)))) = ((F4 m).card : ℝ)⁻¹ * ∑ G ∈ F4 m, f G := by
  unfold ProbabilityTheory.uniformOn ProbabilityTheory.cond
  rw [integral_smul_measure, Measure.count_apply_finset, ENNReal.toReal_inv]
  have hi : IntegrableOn f (↑(F4 m)) Measure.count := by
    exact (Integrable.of_finite (f := f) (μ := Measure.count)).integrableOn
  rw [setIntegral_finset _ hi]
  simp [measureReal_def, smul_eq_mul]
private lemma factor_average_bound (m : ℕ) (hne : (F4 m).Nonempty) (f : Finset ((Fin (6 * m) × Fin (6 * m))) → ℝ) (C : ℝ) (hbound : ∀ G ∈ F4 m, f G ≤ C) : (∫ G, f G ∂(ProbabilityTheory.uniformOn (↑(F4 m)))) ≤ C := by
  have hp : (0 : ℝ) < (F4 m).card := by exact_mod_cast Finset.card_pos.2 hne
  rw [factor_integral]
  calc _ ≤ ((F4 m).card : ℝ)⁻¹ * ∑ _G ∈ F4 m, C := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound) (by positivity)
    _ = C := by simp [Finset.sum_const, nsmul_eq_mul]; field_simp
lemma joint_fractional_bound (m : ℕ) (hne : (F4 m).Nonempty) (Z : Finset ((Fin (6 * m) × Fin (6 * m))) × ((Fin (6 * m)) → ℝ) → ℝ) (hs : Integrable (fun w => Real.sqrt (Z w)) (joint m)) (hb : ∀ G ∈ F4 m, (∫ θ, Real.sqrt (Z (G,θ)) ∂uniformAngles m) ≤ (47 / 48 : ℝ) ^ m) : (∫ w, Real.sqrt (Z w) ∂joint m) ≤ (47 / 48 : ℝ) ^ m := by
  unfold joint at hs ⊢
  rw [integral_prod _ hs]
  exact factor_average_bound m hne _ _ hb
end OpLidarFactorAverage
namespace OpLidarNonempty
open OpLidar OpLidarHardware OpLidarCombinatorics OpLidarFactorBridge OpLidarLocalBridge OpLidarTwins OpLidarFactorAverage
private def connectorFreeFactor (m : ℕ) : Finset ((Fin (6 * m) × Fin (6 * m))) := (hardwareEdges m).filter fun e => ((e.1.cast (Nat.mul_comm 6 m)).divNat).val = ((e.2.cast (Nat.mul_comm 6 m)).divNat).val ∧ ¬ ((((e.1.cast (Nat.mul_comm 6 m)).modNat).val = 0 ∧ ((e.2.cast (Nat.mul_comm 6 m)).modNat).val = 1) ∨ (((e.1.cast (Nat.mul_comm 6 m)).modNat).val = 2 ∧ ((e.2.cast (Nat.mul_comm 6 m)).modNat).val = 3))
private lemma localEdges_order (e : Fin 14) : (localEdges e).1.val < (localEdges e).2.val := by
  fin_cases e <;> decide
private lemma localEdges_first (e : Fin 14) : (localEdges e).1.val < 4 := by
  fin_cases e <;> decide
private lemma local_factor_flags {m : ℕ} [NeZero m] (hm : 1 < m) (i : Fin m) : localMatchingFlags (connectorFreeFactor m) i = ![false,true,true,true,true,true,true,true,true,false,true,true,true,true] := by
  funext e
  have hbr := block_encode m i (localEdges e).1
  have hbt := block_encode m i (localEdges e).2
  have hlt : (blockEquiv m (i,(localEdges e).1)).val < (blockEquiv m (i,(localEdges e).2)).val := by
    rw [blockEquiv_val,blockEquiv_val]
    have h := localEdges_order e
    omega
  have ha : hardwareAdj (blockEquiv m (i,(localEdges e).1)) (blockEquiv m (i,(localEdges e).2)) := by
    rw [hardware_internal_vertex hm _ _ _ _ (localEdges_first e)]
    refine ⟨rfl,?_⟩
    intro h
    have hval := congrArg Fin.val h
    have hlt := localEdges_order e
    omega
  unfold localMatchingFlags
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  unfold edgeAdj connectorFreeFactor
  rw [show (Sym2.sortEquiv s(blockEquiv m (i,(localEdges e).1), blockEquiv m (i,(localEdges e).2))).val = (blockEquiv m (i,(localEdges e).1), blockEquiv m (i,(localEdges e).2)) by change (min _ _, max _ _) = _; rw [min_eq_left (Fin.le_iff_val_le_val.mpr hlt.le), max_eq_right (Fin.le_iff_val_le_val.mpr hlt.le)]]
  simp only [hardwareEdges,Finset.mem_filter,Finset.mem_univ,true_and,hlt,ha, hbr.1,hbr.2,hbt.1,hbt.2,true_and,and_self]
  fin_cases e <;> decide
private lemma fin_ne_next {m : ℕ} [NeZero m] (hm : 1 < m) (i : Fin m) : i ≠ i+1 := by
  intro h
  have hi : i + 0 = i + 1 := (add_zero i).trans h
  have h01 : (0 : Fin m) = 1 := add_left_cancel hi
  have hv := congrArg Fin.val h01
  simp [Fin.val_one',Nat.mod_eq_of_lt hm] at hv
private lemma connector_free_flags {m : ℕ} [NeZero m] (hm : 1 < m) (i : Fin m) : connectorFlag (connectorFreeFactor m) i = false := by
  have hbr := block_encode m i 5
  have hbt := block_encode m (i+1) 4
  simp only [connectorFlag, decide_eq_false_iff_not]
  unfold edgeAdj connectorFreeFactor
  change (min _ _, max _ _) ∈ _ → False
  rcases le_total (blockEquiv m (i,5)) (blockEquiv m (i+1,4)) with hle | hle <;> simp only [min_eq_left hle, max_eq_right hle, min_eq_right hle, max_eq_left hle] <;> intro h
  · have heq := (Finset.mem_filter.mp h).2.1
    simp only [hbr.1,hbt.1] at heq
    exact fin_ne_next hm i (Fin.ext heq)
  · have heq := (Finset.mem_filter.mp h).2.1
    simp only [hbr.1,hbt.1] at heq
    exact fin_ne_next hm i (Fin.ext heq.symm)
lemma factor_nonempty {m : ℕ} [NeZero m] (hm : 1 < m) : (F4 m).Nonempty := by
  refine ⟨connectorFreeFactor m,?_⟩
  simp only [F4,Finset.mem_filter,Finset.mem_powerset]
  refine ⟨Finset.filter_subset _ _,?_⟩
  intro v
  obtain ⟨⟨i,r⟩,rfl⟩ := (blockEquiv m).surjective v
  have hsub : connectorFreeFactor m ⊆ hardwareEdges m := Finset.filter_subset _ _
  rw [subset_degree_local hm (connectorFreeFactor m) hsub i r, local_factor_flags hm i,connector_free_flags hm (i-1),connector_free_flags hm i]
  fin_cases r <;> decide
lemma literal_joint_probability {m : ℕ} [NeZero m] (hm : 1 < m) : MeasureTheory.IsProbabilityMeasure (joint m) := by
  letI := uniformFactors_probability m (factor_nonempty hm)
  unfold joint
  infer_instance
end OpLidarNonempty end D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation
open D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation D5.S3.Quantum.Measurements.IQP.HardwareCircuitFactors.OpLidar
namespace D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation
def claim : Prop := ¬ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ m : ℕ, 3 ≤ m → ∀ s : (Fin (6 * m) → Bool), b ≤ tailProbability m a s
namespace OpLidarCoordinates
open OpLidar OpLidarHardware OpLidarTwins OpLidarAngleSplit
private def retainedIndex (m : ℕ) : (Fin m ⊕ Fin m) ≃ Fin m × Fin 2 := (Equiv.sumCongr (Equiv.prodUnique (Fin m) (Fin 1)).symm (Equiv.prodUnique (Fin m) (Fin 1)).symm).trans ((Equiv.prodSumDistrib (Fin m) (Fin 1) (Fin 1)).symm.trans (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv))
private def complementIndex (m : ℕ) : Fin (4*m) ≃ Fin m × Fin 4 := (finCongr (Nat.mul_comm 4 m)).trans finProdFinEquiv.symm
private def baseIndex (m : ℕ) : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ Fin m × Fin 6 := (Equiv.sumCongr (retainedIndex m) (complementIndex m)).trans ((Equiv.prodSumDistrib (Fin m) (Fin 2) (Fin 4)).symm.trans (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv))
private def pairPermutation (r t : Fin 6) : Equiv.Perm (Fin 6) := (Equiv.swap 1 ((Equiv.swap 0 r).symm t)).trans (Equiv.swap 0 r)
private lemma pairPermutation_maps (r t : Fin 6) (hne : r ≠ t) : pairPermutation r t 0 = r ∧ pairPermutation r t 1 = t := by
  fin_cases r <;> fin_cases t <;>
    first | exact False.elim (hne rfl) | norm_num [pairPermutation,Equiv.swap_apply_def]
private def selectedIndex (m : ℕ) (p : Fin m → Equiv.Perm (Fin 6)) : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m)) := (baseIndex m).trans ((Equiv.prodCongrRight p).trans (blockEquiv m))
private lemma baseIndex_left (m : ℕ) (i : Fin m) : baseIndex m (.inl (.inl i)) = (i,0) := by rfl
private lemma baseIndex_right (m : ℕ) (i : Fin m) : baseIndex m (.inl (.inr i)) = (i,1) := by rfl
private lemma baseIndex_complement (m : ℕ) (j : Fin (4*m)) : baseIndex m (.inr j) = ((complementIndex m j).1, ⟨(complementIndex m j).2.val + 2, by have h := (complementIndex m j).2.isLt; omega⟩) := by
  simp only [baseIndex,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.prodSumDistrib, Equiv.prodCongr_apply,Equiv.sumProdDistrib,Equiv.prodComm_apply,finSumFinEquiv]
  apply Prod.ext
  · rfl
  · apply Fin.ext; simp [Nat.add_comm]
private lemma selectedIndex_left (m : ℕ) (p : Fin m → Equiv.Perm (Fin 6)) (i : Fin m) : selectedIndex m p (.inl (.inl i)) = blockEquiv m (i,p i 0) := by
  change blockEquiv m (Equiv.prodCongrRight p (baseIndex m (.inl (.inl i)))) = _
  rw [baseIndex_left]
  rfl
private lemma selectedIndex_right (m : ℕ) (p : Fin m → Equiv.Perm (Fin 6)) (i : Fin m) : selectedIndex m p (.inl (.inr i)) = blockEquiv m (i,p i 1) := by
  change blockEquiv m (Equiv.prodCongrRight p (baseIndex m (.inl (.inr i)))) = _
  rw [baseIndex_right]
  rfl
private lemma factor_permutations {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) : ∃ p : Fin m → Equiv.Perm (Fin 6), (∀ i j w, OpLidarFactorBridge.edgeAdj G (blockEquiv m (i,p i 0)) (blockEquiv m (j,p j w)) ↔ i = j ∧ w ≠ 0 ∧ w ≠ 1) ∧ (∀ i j w, OpLidarFactorBridge.edgeAdj G (blockEquiv m (i,p i 1)) (blockEquiv m (j,p j w)) ↔ i = j ∧ w ≠ 0 ∧ w ≠ 1) := by
  classical
  choose r t ht using (fun i : Fin m => factor_block_twins hm G hG i)
  let p : Fin m → Equiv.Perm (Fin 6) := fun i => pairPermutation (r i) (t i)
  have hp : ∀ i, p i 0 = r i ∧ p i 1 = t i := fun i => pairPermutation_maps _ _ (ht i).1
  refine ⟨p,?_,?_⟩
  · intro i j w
    rw [(hp i).1,(ht i).2.1]
    by_cases heq : i = j
    · subst j
      rw [← (hp i).1, ← (hp i).2]
      simp only [(p i).injective.ne_iff, true_and]
    · simp [heq]
  · intro i j w
    rw [(hp i).2,(ht i).2.2]
    by_cases heq : i = j
    · subst j
      rw [← (hp i).1, ← (hp i).2]
      simp only [(p i).injective.ne_iff, true_and]
    · simp [heq]
private lemma other_four_product (f : Fin 6 → ℂ) : (∏ w : Fin 6, if w ≠ 0 ∧ w ≠ 1 then f w else 1) = ∏ k : Fin 4, f (k.natAdd 2) := by
  simp only [Fin.prod_univ_succ]
  dsimp [Fin.natAdd]
  norm_num
private def retainedValues (m : ℕ) (A : Type*) : ((Fin m ⊕ Fin m) → A) ≃ (Fin m → A × A) := (Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => A)).trans (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => A) (fun _ => A)).symm
private def valuesSplit (m : ℕ) (A : Type*) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) : ((Fin (6 * m)) → A) ≃ ((Fin m → A × A) × (Fin (4*m) → A)) := (e.symm.arrowCongr (Equiv.refl A)).trans ((Equiv.sumPiEquivProdPi (fun _ : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) => A)).trans (Equiv.prodCongr (retainedValues m A) (Equiv.refl _)))
private lemma joinBits_left (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) (x : Fin m → Bool × Bool) (z : Fin (4*m) → Bool) (i : Fin m) : ((valuesSplit m Bool e).symm (x,z)) (e (.inl (.inl i))) = (x i).1 := by
  simp [valuesSplit,retainedValues,Equiv.arrowCongr,Equiv.sumPiEquivProdPi, Equiv.arrowProdEquivProdArrow]
private lemma joinBits_right (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) (x : Fin m → Bool × Bool) (z : Fin (4*m) → Bool) (i : Fin m) : ((valuesSplit m Bool e).symm (x,z)) (e (.inl (.inr i))) = (x i).2 := by
  simp [valuesSplit,retainedValues,Equiv.arrowCongr,Equiv.sumPiEquivProdPi, Equiv.arrowProdEquivProdArrow]
private lemma joinBits_complement (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) (x : Fin m → Bool × Bool) (z : Fin (4*m) → Bool) (j : Fin (4*m)) : ((valuesSplit m Bool e).symm (x,z)) (e (.inr j)) = z j := by
  simp [valuesSplit,retainedValues,Equiv.arrowCongr,Equiv.sumPiEquivProdPi, Equiv.arrowProdEquivProdArrow]
end OpLidarCoordinates
namespace OpLidarGraphPhase
open OpLidar OpLidarHardware OpLidarFactorBridge OpLidarCoordinates OpLidarStateBridge OpLidarReduced
set_option maxHeartbeats 2000000
private lemma incident_phase_product {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (hE : E ⊆ hardwareEdges m) (v : (Fin (6 * m))) (z : (Fin (6 * m) → Bool)) : (∏ e ∈ E.filter (fun e => v ∈ s(e.1, e.2)), (-1 : ℂ) ^ ((z e.1).toNat * (z e.2).toNat)) = ∏ w ∈ Finset.univ.filter (fun w => edgeAdj E v w), (-1 : ℂ) ^ ((z v).toNat * (z w).toNat) := by
  classical
  refine Finset.prod_bij (M := ℂ) (s := E.filter fun e => v ∈ s(e.1, e.2)) (t := Finset.univ.filter fun w => edgeAdj E v w) (fun e _ => if e.1 = v then e.2 else e.1) ?_ ?_ ?_ ?_
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
  · intro e he
    have heinc := (Finset.mem_filter.mp he).2
    have heinc : e.1 = v ∨ e.2 = v := (Sym2.mem_iff.mp heinc).imp Eq.symm Eq.symm
    have hlt := (Finset.mem_filter.mp (hE (Finset.mem_filter.mp he).1)).2.1
    rcases heinc with hleft | hright
    · simp [hleft]
    · have hne : e.1 ≠ v := by intro h; rw [h,hright] at hlt; omega
      simp [hne,hright,Nat.mul_comm]

private lemma independent_phase_split {m : ℕ} (E : Finset ((Fin (6 * m) × Fin (6 * m)))) (hE : E ⊆ hardwareEdges m) (S : Finset ((Fin (6 * m)))) (hS : ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)) (z : (Fin (6 * m) → Bool)) : graphPhase E z = graphPhase E (fun v => if v ∈ S then false else z v) * ∏ u ∈ S, ∏ w ∈ Finset.univ.filter (fun w => edgeAdj E u w), (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z u) else (z w))) := by
  classical
  have hi : ∀ u, (∏ w ∈ Finset.univ.filter (fun w => edgeAdj E u w), (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z u) else (z w)))) = ∏ e ∈ E, if u ∈ s(e.1, e.2) then (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z e.1) else (z e.2))) else 1 := by
    intro u
    simp only [D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase, Sym2.lift_mk, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [← incident_phase_product E hE u z]
    exact Finset.prod_filter _ _
  simp_rw [hi]
  unfold graphPhase
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  symm
  apply Finset.prod_congr rfl; intro e he
  have hn : e.1 ≠ e.2 := (Finset.mem_filter.mp (hE he)).2.2.1
  have hfilter : (S.filter fun u => u ∈ s(e.1, e.2)) = (if e.1 ∈ S then {e.1} else ∅) ∪ (if e.2 ∈ S then {e.2} else ∅) := by
    ext u
    rw [Finset.mem_filter]
    simp only [Sym2.mem_iff, eq_comm]
    split_ifs <;> simp_all only [Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty, or_false,false_or] <;> aesop
  rw [← Finset.prod_filter, hfilter]
  by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S
  · exact False.elim (hS e he ⟨h1,h2⟩)
  · simp [h1,h2,D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase]
  · simp [h1,h2,D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase]
  · simp [h1,h2]
private lemma four_star_pair : ∀ (r t : Bool) (y : Fin 4 → Bool), (∏ j, (-1 : ℤ) ^ (r.toNat * (y j).toNat)) * (∏ j, (-1 : ℤ) ^ (t.toNat * (y j).toNat)) = (Int.negOnePow (((r ^^ t) && (List.foldl Bool.xor (y 0) [y 1, y 2, y 3])).toNat : ℤ) : ℤ) := by decide
end OpLidarGraphPhase
namespace OpLidarLiteralPhase
open OpLidar OpLidarHardware OpLidarFactorBridge OpLidarCoordinates OpLidarGraphPhase OpLidarReduced OpLidarReindex OpLidarStateBridge
private def selectedSet (m : ℕ) (p : Fin m → Equiv.Perm (Fin 6)) : Finset ((Fin (6 * m))) := Finset.univ.filter fun v => ∃ i, v = blockEquiv m (i,p i 0) ∨ v = blockEquiv m (i,p i 1)
private lemma selectedSet_independent {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (p : Fin m → Equiv.Perm (Fin 6)) (h0 : ∀ i j w, edgeAdj G (blockEquiv m (i,p i 0)) (blockEquiv m (j,p j w)) ↔ i = j ∧ w ≠ 0 ∧ w ≠ 1) (h1 : ∀ i j w, edgeAdj G (blockEquiv m (i,p i 1)) (blockEquiv m (j,p j w)) ↔ i = j ∧ w ≠ 0 ∧ w ≠ 1) (hE : G ⊆ hardwareEdges m) : ∀ e ∈ G, ¬ (e.1 ∈ selectedSet m p ∧ e.2 ∈ selectedSet m p) := by
  classical
  intro e he ⟨ha,hb⟩
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hb).2
  have hlt := (Finset.mem_filter.mp (hE he)).2.1
  have hadj : edgeAdj G e.1 e.2 := by simpa [edgeAdj, Sym2.sortEquiv, Fin.le_iff_val_le_val.mpr hlt.le] using he
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    rw [hi,hj] at hadj
  · exact (h0 i j 0).mp hadj |>.2.1 rfl
  · exact (h0 i j 1).mp hadj |>.2.2 rfl
  · exact (h1 i j 0).mp hadj |>.2.1 rfl
  · exact (h1 i j 1).mp hadj |>.2.2 rfl
private lemma selected_product (m : ℕ) (p : Fin m → Equiv.Perm (Fin 6)) (f : (Fin (6 * m)) → ℂ) : (∏ u ∈ selectedSet m p, f u) = ∏ i, f (blockEquiv m (i,p i 0)) * f (blockEquiv m (i,p i 1)) := by
  classical
  unfold selectedSet
  rw [Finset.prod_filter]
  have he := Fintype.prod_equiv ((Equiv.prodCongrRight p).trans (blockEquiv m)) (fun w => if ∃ i, blockEquiv m (w.1,p w.1 w.2) = blockEquiv m (i,p i 0) ∨ blockEquiv m (w.1,p w.1 w.2) = blockEquiv m (i,p i 1)
      then f (blockEquiv m (w.1,p w.1 w.2)) else 1) (fun u => if ∃ i, u = blockEquiv m (i,p i 0) ∨ u = blockEquiv m (i,p i 1) then f u else 1) (by intro w; rfl)
  change (∏ u, if ∃ i, u = blockEquiv m (i,p i 0) ∨ u = blockEquiv m (i,p i 1) then f u else 1) = _
  rw [← he, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro i _
  have hmem : ∀ w : Fin 6, (∃ j, blockEquiv m (i,p i w) = blockEquiv m (j,p j 0) ∨ blockEquiv m (i,p i w) = blockEquiv m (j,p j 1)) ↔ w = 0 ∨ w = 1 := by
    intro w
    constructor
    · rintro ⟨j,h | h⟩
      · have hp := (blockEquiv m).injective h
        have hij : i = j := congrArg Prod.fst hp
        subst j
        exact Or.inl ((p i).injective (congrArg Prod.snd hp))
      · have hp := (blockEquiv m).injective h
        have hij : i = j := congrArg Prod.fst hp
        subst j
        exact Or.inr ((p i).injective (congrArg Prod.snd hp))
    · intro h; exact ⟨i,by rcases h with h|h <;> simp [h]⟩
  simp_rw [hmem]
  simp only [Fin.prod_univ_succ]
  norm_num [Fin.ext_iff,Fin.val_succ]
private lemma neighbor_product {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (p : Fin m → Equiv.Perm (Fin 6)) (i : Fin m) (a : Fin 6) (hn : ∀ j w, edgeAdj G (blockEquiv m (i,p i a)) (blockEquiv m (j,p j w)) ↔ i = j ∧ w ≠ 0 ∧ w ≠ 1) (z : (Fin (6 * m) → Bool)) : (∏ w ∈ Finset.univ.filter (edgeAdj G (blockEquiv m (i,p i a))), (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z (blockEquiv m (i,p i a))) else (z w)))) = ∏ k : Fin 4, (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z (blockEquiv m (i,p i a))) else (z (blockEquiv m (i,p i (k.natAdd 2)))))) := by
  classical
  rw [Finset.prod_filter]
  rw [← Equiv.prod_comp ((Equiv.prodCongrRight p).trans (blockEquiv m))]
  change (∏ w : Fin m × Fin 6, if edgeAdj G (blockEquiv m (i,p i a)) (blockEquiv m (w.1,p w.1 w.2)) then (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z (blockEquiv m (i,p i a))) else (z (blockEquiv m (w.1,p w.1 w.2))))) else 1) = _
  simp_rw [hn]
  rw [Fintype.prod_prod_type]
  have hsplit : ∀ j : Fin m, (∏ w : Fin 6, if i = j ∧ w ≠ 0 ∧ w ≠ 1 then (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z (blockEquiv m (i,p i a))) else (z (blockEquiv m (j,p j w))))) else 1) = if j = i then (∏ w : Fin 6, if w ≠ 0 ∧ w ≠ 1 then (D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase s((0 : Fin 2), 1) (fun czIndex => if czIndex = 0 then (z (blockEquiv m (i,p i a))) else (z (blockEquiv m (i,p i w))))) else 1) else 1 := by
    intro j
    by_cases h : j = i
    · simp [h]
    · simp [h,Ne.symm h]
  simp_rw [hsplit]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,if_true]
  exact other_four_product _
private lemma complement_evaluation (m : ℕ) (p : Fin m → Equiv.Perm (Fin 6)) (x : Fin m → Bool × Bool) (z : Fin (4*m) → Bool) (i : Fin m) (k : Fin 4) : ((valuesSplit m Bool (selectedIndex m p)).symm (x,z)) (blockEquiv m (i,p i (k.natAdd 2))) = complementEquiv m z i k := by
  have h := joinBits_complement m (selectedIndex m p) x z ((complementIndex m).symm (i,k))
  have he : selectedIndex m p (.inr ((complementIndex m).symm (i,k))) = blockEquiv m (i,p i (k.natAdd 2)) := by
    change blockEquiv m (Equiv.prodCongrRight p (baseIndex m (.inr _))) = _
    rw [baseIndex_complement]
    simp only [Equiv.apply_symm_apply]
    change blockEquiv m (i,p i ⟨k.val+2, _⟩) = blockEquiv m (i,p i (k.natAdd 2))
    congr 3
    apply Fin.ext
    simp [Fin.natAdd,Nat.add_comm]
  rw [he] at h
  exact h
private lemma masked_bits (m : ℕ) (p : Fin m → Equiv.Perm (Fin 6)) (x : Fin m → Bool × Bool) (z : Fin (4*m) → Bool) : (fun v => if v ∈ selectedSet m p then false else ((valuesSplit m Bool (selectedIndex m p)).symm (x,z)) v) = ((valuesSplit m Bool (selectedIndex m p)).symm ((fun _ => (false,false)),z)) := by
  classical
  funext v
  obtain ⟨⟨i,w⟩,rfl⟩ := ((Equiv.prodCongrRight p).trans (blockEquiv m)).surjective v
  change (if blockEquiv m (i,p i w) ∈ selectedSet m p then false else ((valuesSplit m Bool (selectedIndex m p)).symm (x,z)) (blockEquiv m (i,p i w))) = ((valuesSplit m Bool (selectedIndex m p)).symm ((fun _ => (false,false)),z)) (blockEquiv m (i,p i w))
  by_cases h0 : w = 0
  · subst w
    have hm : blockEquiv m (i,p i 0) ∈ selectedSet m p := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,i,Or.inl rfl⟩
    rw [if_pos hm, ← selectedIndex_left,joinBits_left]
  by_cases h1 : w = 1
  · subst w
    have hm : blockEquiv m (i,p i 1) ∈ selectedSet m p := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,i,Or.inr rfl⟩
    rw [if_pos hm, ← selectedIndex_right,joinBits_right]
  · have hm : blockEquiv m (i,p i w) ∉ selectedSet m p := by
      intro h
      obtain ⟨j,hj|hj⟩ := (Finset.mem_filter.mp h).2
      all_goals
        have hp := (blockEquiv m).injective hj
        have hij : i = j := congrArg Prod.fst hp
        subst j
      · exact h0 ((p i).injective (congrArg Prod.snd hp))
      · exact h1 ((p i).injective (congrArg Prod.snd hp))
    rw [if_neg hm]
    let k : Fin 4 := ⟨w.val - 2, by have hw := w.isLt; omega⟩
    have hk : k.natAdd 2 = w := by
      have hw0 : w.val ≠ 0 := by intro h; exact h0 (Fin.ext h)
      have hw1 : w.val ≠ 1 := by intro h; exact h1 (Fin.ext h)
      apply Fin.ext
      dsimp [k,Fin.natAdd]
      omega
    rw [← hk,complement_evaluation,complement_evaluation]
private lemma graphPhase_sign {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (z : (Fin (6 * m) → Bool)) : ∃ b : Bool, graphPhase G z = ((Int.negOnePow (b.toNat : ℤ) : ℤ): ℂ) := by
  classical
  induction G using Finset.induction_on with
  | empty => exact ⟨false,by simp [graphPhase]⟩
  | @insert e E he ih =>
    obtain ⟨b,hb⟩ := ih
    refine ⟨(z e.1 && z e.2) ^^ b, ?_⟩
    simp only [graphPhase,Finset.prod_insert he] at ⊢ hb
    rw [hb, ← sign_product]
    push_cast
    congr 1
    cases z e.1 <;> cases z e.2 <;> norm_num [D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase]
private lemma literal_phase_twin {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hE : G ⊆ hardwareEdges m) (p : Fin m → Equiv.Perm (Fin 6)) (h0 : ∀ i j w, edgeAdj G (blockEquiv m (i,p i 0)) (blockEquiv m (j,p j w)) ↔ i = j ∧ w ≠ 0 ∧ w ≠ 1) (h1 : ∀ i j w, edgeAdj G (blockEquiv m (i,p i 1)) (blockEquiv m (j,p j w)) ↔ i = j ∧ w ≠ 0 ∧ w ≠ 1) : ∃ qC : (Fin m → Fin 4 → Bool) → Bool, ∀ x z, graphPhase G (((valuesSplit m Bool (selectedIndex m p)).symm (x,z))) = (twinPhase m qC x (complementEquiv m z) : ℂ) := by
  classical
  choose qC hq using (fun y : Fin m → Fin 4 → Bool => graphPhase_sign G (((valuesSplit m Bool (selectedIndex m p)).symm ((fun _ => (false,false)),((complementEquiv m).symm y)))))
  refine ⟨qC,?_⟩
  intro x z
  rw [independent_phase_split G hE (selectedSet m p) (selectedSet_independent G p h0 h1 hE), masked_bits,selected_product]
  have hc := hq (complementEquiv m z)
  simp only [Equiv.symm_apply_apply] at hc
  rw [hc]
  unfold twinPhase
  push_cast
  congr 1
  apply Finset.prod_congr rfl; intro i _
  rw [neighbor_product G p i 0 (h0 i),neighbor_product G p i 1 (h1 i)]
  simp_rw [← selectedIndex_left,joinBits_left,← selectedIndex_right,joinBits_right,complement_evaluation]
  have hp := congrArg (fun a : ℤ => (a : ℂ)) (four_star_pair (x i).1 (x i).2 (complementEquiv m z i))
  push_cast at hp
  exact hp
end OpLidarLiteralPhase
namespace OpLidarLiteralProbability
open OpLidar OpLidarHardware OpLidarFactorBridge OpLidarCoordinates OpLidarAngleSplit OpLidarGraphPhase OpLidarLiteralPhase OpLidarReduced OpLidarReindex OpLidarStateBridge OpLidarTwinProbability OpLidarTwinMoment
private lemma hadamard_initial (m : ℕ) (z : (Fin (6 * m) → Bool)) : (tensorOp (fun _ : Fin (6 * m) => hadamard) (fun i => if z i then 1 else 0) (fun i => if (fun _ => false) i then 1 else 0)) = (((2 : ℝ)⁻¹ ^ (3*m) : ℝ) : ℂ) := by
  have he (b : Bool) : hadamard (if b then 1 else 0) 0 = s2 := by
    cases b <;> norm_num [hadamard, pauliMatrix, qubitX, qubitZ]
  have hs : s2 ^ 2 = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa [hadamard, pauliMatrix, qubitX, qubitZ] using W_false_squared
  simp only [tensorOp, Matrix.of_apply, Bool.false_eq_true, if_false, he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show 6*m=2*(3*m) by omega,pow_mul,hs,← Complex.ofReal_pow]
private lemma graph_amplitude_twin {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (p : Fin m → Equiv.Perm (Fin 6)) (qC : (Fin m → Fin 4 → Bool) → Bool) (hp : ∀ x z, graphPhase G (((valuesSplit m Bool (selectedIndex m p)).symm (x,z))) = (twinPhase m qC x (complementEquiv m z) : ℂ)) (x z) : graphAmplitude G (((valuesSplit m Bool (selectedIndex m p)).symm (x,z))) = reindexedTwinAmplitude m qC (x,z) := by
  unfold graphAmplitude
  rw [hadamard_initial]
  change (((2 : ℝ)⁻¹ ^ (3*m) : ℝ) : ℂ) * graphPhase G (((valuesSplit m Bool (selectedIndex m p)).symm (x,z))) = _
  rw [hp]
  rfl
private lemma angle_values (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) (θ : (Fin (6 * m)) → ℝ) : angleSplit m e θ = valuesSplit m ℝ e θ := by
  simp [angleSplit,retainedSplit,valuesSplit,retainedValues,MeasurableEquiv.piCongrLeft, Equiv.arrowCongr,Equiv.piCongrLeft,Equiv.sumPiEquivProdPi,Equiv.arrowProdEquivProdArrow, MeasurableEquiv.sumPiEquivProdPi,MeasurableEquiv.arrowProdEquivProdArrow,MeasurableEquiv.prodCongr]
private lemma measurement_row_split (m : ℕ) (e : ((Fin m ⊕ Fin m) ⊕ Fin (4*m)) ≃ (Fin (6 * m))) (θ : (Fin (6 * m)) → ℝ) (x : Fin m → Bool × Bool) (z : Fin (4*m) → Bool) : measurementRow (fun _ => false) θ (((valuesSplit m Bool e).symm (x,z))) = retainedRow m (angleSplit m e θ).1 x * (tensorOp (fun i => hadamard * D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation 1 ((angleSplit m e θ).2 i)) (fun _ => 0) (fun i => if z i then 1 else 0)) := by
  simp_rw [measurement_row_exp]
  rw [← e.prod_comp]
  simp only [Fintype.prod_sum_type]
  simp_rw [joinBits_left,joinBits_right,joinBits_complement]
  rw [← Finset.prod_mul_distrib,angle_values]
  simp only [tensorOp, Matrix.of_apply]
  simp_rw [retained_row_prod, OpLidarCircuitBridge.zero_gate_entry_exp]
  simp [valuesSplit,retainedValues,Equiv.arrowCongr, Equiv.sumPiEquivProdPi,Equiv.arrowProdEquivProdArrow]
private lemma probability_split {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (p : Fin m → Equiv.Perm (Fin 6)) (qC : (Fin m → Fin 4 → Bool) → Bool) (hp : ∀ x z, graphPhase G (((valuesSplit m Bool (selectedIndex m p)).symm (x,z))) = (twinPhase m qC x (complementEquiv m z) : ℂ)) (θ : (Fin (6 * m)) → ℝ) : Complex.normSq (∑ z : (Fin (6 * m) → Bool),graphAmplitude G z * measurementRow (fun _ => false) θ z) = twinProbability m qC (angleSplit m (selectedIndex m p) θ).1 (angleSplit m (selectedIndex m p) θ).2 := by
  unfold twinProbability
  congr 1
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (valuesSplit m Bool (selectedIndex m p))
  intro z
  obtain ⟨⟨x,y⟩,rfl⟩ := (valuesSplit m Bool (selectedIndex m p)).symm.surjective z
  simp only [Equiv.apply_symm_apply]
  change graphAmplitude G (((valuesSplit m Bool (selectedIndex m p)).symm (x,y))) * measurementRow (fun _ => false) θ (((valuesSplit m Bool (selectedIndex m p)).symm (x,y))) = _
  rw [graph_amplitude_twin G p qC hp,measurement_row_split]
  ring
private lemma literal_factor_twin_state {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) : ∃ p : Fin m → Equiv.Perm (Fin 6), ∃ qC : (Fin m → Fin 4 → Bool) → Bool, (∀ x z, graphAmplitude G (((valuesSplit m Bool (selectedIndex m p)).symm (x,z))) = reindexedTwinAmplitude m qC (x,z)) ∧ (∀ θ : (Fin (6 * m)) → ℝ, Complex.normSq (∑ z : (Fin (6 * m) → Bool),graphAmplitude G z * measurementRow (fun _ => false) θ z) = twinProbability m qC (angleSplit m (selectedIndex m p) θ).1 (angleSplit m (selectedIndex m p) θ).2) := by
  obtain ⟨p,h0,h1⟩ := factor_permutations hm G hG
  have hE : G ⊆ hardwareEdges m := Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1
  obtain ⟨qC,hq⟩ := literal_phase_twin G hE p h0 h1
  exact ⟨p,qC,graph_amplitude_twin G p qC hq,probability_split G p qC hq⟩
end OpLidarLiteralProbability
namespace OpLidarOutputShift
open OpLidar OpLidarStateBridge OpLidarTwinProbability OpLidarMeasurement OpLidarReduced
private lemma W_sign (s r : Bool) : (hadamard (if s then 1 else 0) (if r then 1 else 0)) = ((Int.negOnePow ((s && r).toNat : ℤ) : ℤ) : ℂ) * (hadamard (if false then 1 else 0) (if r then 1 else 0)) := by
  cases s <;> cases r <;> simp [hadamard, s2, pauliMatrix, qubitX, qubitZ] <;> ring
private lemma one_qubit_effect_output (α : ℝ) (s r r' : Bool) : ((hadamard (if s then 1 else 0) (if r then 1 else 0)) * Complex.exp (-Complex.I * ((α*D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r/2 : ℝ) : ℂ))) * star ((hadamard (if s then 1 else 0) (if r' then 1 else 0)) * Complex.exp (-Complex.I * ((α*D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r'/2 : ℝ) : ℂ))) = effect (α + if s then Real.pi else 0) r' r := by
  rw [W_sign s r,W_sign s r']
  calc
    _ = ((Int.negOnePow ((s && r).toNat : ℤ) : ℤ) : ℂ) * ((Int.negOnePow ((s && r').toNat : ℤ) : ℤ) : ℂ) * (((hadamard (if false then 1 else 0) (if r then 1 else 0)) * Complex.exp (-Complex.I * ((α*D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r/2 : ℝ) : ℂ))) * star ((hadamard (if false then 1 else 0) (if r' then 1 else 0)) * Complex.exp (-Complex.I * ((α*D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign r'/2 : ℝ) : ℂ)))) := by
      simp only [star_mul,star_intCast]
      ring
    _ = _ := by
      rw [one_qubit_effect_zero]
      cases s <;> cases r <;> cases r' <;>
        simp [effect_entry, Real.cos_add_pi, Real.sin_add_pi] <;> ring
private lemma measurement_row_effect_output {m : ℕ} (φ : (Fin (6 * m)) → ℝ) (s z z' : (Fin (6 * m) → Bool)) : measurementRow s φ z * star (measurementRow s φ z') = ∏ i, effect (φ i + if s i then Real.pi else 0) (z' i) (z i) := by
  simp_rw [measurement_row_exp]
  rw [star_prod,← Finset.prod_mul_distrib]
  simp_rw [one_qubit_effect_output]
private lemma output_probability_shift {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (φ : (Fin (6 * m)) → ℝ) (s : (Fin (6 * m) → Bool)) : Complex.normSq (∑ z : (Fin (6 * m) → Bool),graphAmplitude G z * measurementRow s φ z) = Complex.normSq (∑ z : (Fin (6 * m) → Bool),graphAmplitude G z * measurementRow (fun _ => false) (fun i => φ i + if s i then Real.pi else 0) z) := by
  apply Complex.ofReal_injective
  rw [normSq_finite_sum,graph_probability_effect_zero]
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro z' _
  simp only [star_mul]
  rw [← measurement_row_effect_output]
  ring
end OpLidarOutputShift
namespace OpLidarCircuitRegularity
open OpLidar OpLidarCircuitBridge OpLidarTwinProbability OpLidarTwinMoment OpLidarNonempty MeasureTheory
set_option maxHeartbeats 2000000
private lemma W_norm_le_one (s z : Bool) : ‖(hadamard (if s then 1 else 0) (if z then 1 else 0))‖ ≤ 1 := by
  have hf : ‖(hadamard (if false then 1 else 0) (if false then 1 else 0))‖ ≤ 1 := by simpa [Matrix.mul_apply, Fin.sum_univ_two, D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation, Matrix.diagonal_apply] using gate_entry_norm_le_one 0 false
  cases s <;> cases z <;> simpa [hadamard, s2, pauliMatrix, qubitX, qubitZ] using hf
private lemma hadamard_norm_le_one (m : ℕ) (s z : (Fin (6 * m) → Bool)) : ‖(tensorOp (fun _ : Fin (6 * m) => hadamard) (fun i => if s i then 1 else 0) (fun i => if z i then 1 else 0))‖ ≤ 1 := by
  unfold tensorOp
  simp only [Matrix.of_apply]
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => W_norm_le_one _ _)
private lemma phase_norm (x : ℝ) : ‖Complex.exp (-Complex.I * (x : ℂ))‖ = 1 := by
  have he : -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he,Complex.norm_exp_ofReal_mul_I]
private lemma literal_probability_bound {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (θ : (Fin (6 * m)) → ℝ) (s : (Fin (6 * m) → Bool)) : outputProbability G θ s ≤ (Fintype.card ((Fin (6 * m) → Bool)) : ℝ)^2 := by
  have hb : ‖circuit G θ s (fun _ => false)‖ ≤ (Fintype.card ((Fin (6 * m) → Bool)) : ℝ) := by
    rw [circuit_amplitude_literal]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _z : (Fin (6 * m) → Bool), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro z _
        rw [norm_mul,norm_mul,phase_norm,mul_one]
        exact (mul_le_mul (hadamard_norm_le_one _ _ _) (hadamard_norm_le_one _ _ _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      _ = _ := by simp
  unfold outputProbability
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2
private lemma literal_probability_continuous {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (s : (Fin (6 * m) → Bool)) : Continuous (fun θ => outputProbability G θ s) := by
  unfold outputProbability
  simp_rw [circuit_amplitude_literal]
  fun_prop
private def normalizedOutput (m : ℕ) (s : (Fin (6 * m) → Bool)) (w : Finset ((Fin (6 * m) × Fin (6 * m))) × ((Fin (6 * m)) → ℝ)) : ℝ := (2:ℝ)^(6*m) * outputProbability w.1 w.2 s
private lemma normalizedOutput_nonneg (m : ℕ) (s : (Fin (6 * m) → Bool)) (w) : 0 ≤ normalizedOutput m s w := by
  exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
private lemma normalizedOutput_measurable (m : ℕ) (s : (Fin (6 * m) → Bool)) : Measurable (normalizedOutput m s) := by
  apply measurable_from_prod_countable_right
  intro G
  exact (continuous_const.mul (literal_probability_continuous G s)).measurable
private lemma normalizedOutput_integrable {m : ℕ} [NeZero m] (hm : 1 < m) (s : (Fin (6 * m) → Bool)) : Integrable (normalizedOutput m s) (joint m) ∧ Integrable (fun w => Real.sqrt (normalizedOutput m s w)) (joint m) := by
  letI := literal_joint_probability hm
  have hb : ∀ w, normalizedOutput m s w ≤ (2:ℝ)^(6*m) * (Fintype.card ((Fin (6 * m) → Bool)) : ℝ)^2 := by
    intro w
    exact mul_le_mul_of_nonneg_left (literal_probability_bound w.1 w.2 s) (by positivity)
  constructor
  · refine (integrable_const ((2:ℝ)^(6*m) * (Fintype.card ((Fin (6 * m) → Bool)) : ℝ)^2)).mono' (normalizedOutput_measurable m s).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro w
    rw [Real.norm_of_nonneg (normalizedOutput_nonneg m s w)]
    exact hb w
  · refine (integrable_const (Real.sqrt ((2:ℝ)^(6*m) * (Fintype.card ((Fin (6 * m) → Bool)) : ℝ)^2))).mono' (Real.continuous_sqrt.measurable.comp (normalizedOutput_measurable m s)).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro w
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hb w)
private lemma tail_normalized (m : ℕ) (a : ℝ) (s : (Fin (6 * m) → Bool)) : tailProbability m a s = (joint m).real {w | a ≤ normalizedOutput m s w} := by
  unfold tailProbability normalizedOutput
  congr 1
  ext w
  change a * ((2:ℝ)^(6*m))⁻¹ ≤ outputProbability w.1 w.2 s ↔ a ≤ (2:ℝ)^(6*m) * outputProbability w.1 w.2 s
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity : (0:ℝ) < 2^(6*m))]
  simp only [mul_comm]
end OpLidarCircuitRegularity
namespace OpLidarSettlement
open OpLidar OpLidarHardware OpLidarCoordinates OpLidarAngleSplit OpLidarLiteralProbability OpLidarStateBridge OpLidarReindex OpLidarTwinMoment OpLidarTwinProbability OpLidarGraphAnalysis OpLidarOutputShift OpLidarCircuitRegularity OpLidarAnalysis OpLidarFactorAverage OpLidarNonempty MeasureTheory
private lemma factor_graph_fractional_moment {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) : (∫ θ, Real.sqrt ((2:ℝ)^(6*m)*graphProbability G θ) ∂uniformAngles m) ≤ (47/48:ℝ)^m := by
  obtain ⟨p,qC,hamp,hprob⟩ := literal_factor_twin_state hm G hG
  unfold graphProbability
  simp_rw [hprob,← normalizedDensity_eq]
  rw [split_integral m (selectedIndex m p) (fun w => Real.sqrt (normalizedTwinDensity m qC w.1 w.2))]
  exact twin_fractional_moment m qC
private lemma factor_probability_graph_zero {m : ℕ} (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (θ : (Fin (6 * m)) → ℝ) (s : (Fin (6 * m) → Bool)) : outputProbability G θ s = graphProbability G (fun i => θ i + (2*(Real.pi/7) + if s i then Real.pi else 0)) := by
  rw [factor_output_graph_probability G hG,output_probability_shift]
  unfold graphProbability
  simp only [add_assoc]
private lemma factor_literal_fractional_moment {m : ℕ} [NeZero m] (hm : 1 < m) (G : Finset ((Fin (6 * m) × Fin (6 * m)))) (hG : G ∈ F4 m) (s : (Fin (6 * m) → Bool)) : (∫ θ, Real.sqrt (normalizedOutput m s (G,θ)) ∂uniformAngles m) ≤ (47/48:ℝ)^m := by
  unfold normalizedOutput
  simp_rw [factor_probability_graph_zero G hG]
  rw [graph_sqrt_shift]
  exact factor_graph_fractional_moment hm G hG
private lemma literal_joint_fractional_moment {m : ℕ} [NeZero m] (hm : 1 < m) (s : (Fin (6 * m) → Bool)) : (∫ w, Real.sqrt (normalizedOutput m s w) ∂joint m) ≤ (47/48:ℝ)^m := by
  exact joint_fractional_bound m (factor_nonempty hm) _ (normalizedOutput_integrable hm s).2 (fun G hG => factor_literal_fractional_moment hm G hG s)
private lemma literal_tail_bound (m : ℕ) (hm : 3 ≤ m) (s : (Fin (6 * m) → Bool)) (a : ℝ) (ha : 0 < a) : tailProbability m a s ≤ (Real.sqrt a)⁻¹ * (47/48:ℝ)^m := by
  letI : NeZero m := ⟨by omega⟩
  have hm' : 1 < m := by omega
  letI := literal_joint_probability hm'
  rw [tail_normalized]
  exact fractional_markov (joint m) (normalizedOutput m s) (normalizedOutput_nonneg m s) (normalizedOutput_integrable hm' s).2 m (literal_joint_fractional_moment hm' s) a ha
theorem result : claim := by
  rintro ⟨a,b,ha,hb,hanti⟩
  obtain ⟨m,hm,hlt⟩ := eventual_tail_bound a b ha hb
  have hbound := literal_tail_bound m hm (fun _ => false) a ha
  exact (not_lt_of_ge ((hanti m hm (fun _ => false)).trans hbound)) hlt
end OpLidarSettlement end D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation

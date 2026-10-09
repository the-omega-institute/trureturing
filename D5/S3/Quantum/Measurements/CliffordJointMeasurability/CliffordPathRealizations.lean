/- GID: D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every path realization extends to exact Majorana bonds by qubit ancillas. -/
/-
proof_shape: arbitrary_path_majorana_extension: content
escape_witness: arbitrary_path_majorana_extension
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Quantum/FiniteDimensional.qubit_weyl_star; declaration statement_id=sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d; D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef (Lean name: RHLinalg.trace_mul_nonneg_of_posSemidef); declaration statement_id=sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3.
Direct frozen dependencies: D5/S3/QuantumBounds/MerminMeasurementDependence/Model.boolSign
  statement_id: sha256:460364e69c4d4ffdf8453b33aa340a45608100763a0cd87da8282661f430ea21
D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.phi
  statement_id: sha256:478d10f4d2630256660ee5625f24c556783d91db591c700b1e3b12dffa485453
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: signed_product: bind-only; consumer: pathMajorana_generator_relation
proof_shape: signed_smul: bind-only; consumer: pathMajorana_generator_relation
proof_shape: prefixSign_step: bind-only; consumer: pathMajorana_generator_relation
proof_shape: prefixSign_zero: bind-only; consumer: liftSeed_relation
proof_shape: pathMajorana_generator_relation: content; consumer: arbitrary_path_majorana_extension
proof_shape: anticommuting_product_square: bind-only; consumers: pathMajorana_square, CliffordBondParents.majorana_pair_square
proof_shape: pathMajorana_square: content; consumer: arbitrary_path_majorana_extension
proof_shape: pathMajorana_bond: bind-only; consumer: arbitrary_path_majorana_extension
proof_shape: pathMajorana_pairwise: content; consumer: arbitrary_path_majorana_extension
proof_shape: pathMajorana_hermitian: content; consumer: arbitrary_path_majorana_extension
proof_shape: anticommuting_trace_zero: bind-only; consumer: realization_trace_zero_of_neighbors
proof_shape: noisy_eq_of_trace_zero: bind-only; consumer: parent_signed_marginal
proof_shape: parent_signed_marginal: bind-only; consumer: weighted_trace_identity
proof_shape: weighted_trace_identity: bind-only; consumer: weighted_trace_bound
proof_shape: psd_eq_gram: bind-only; consumer: quadratic_psd
proof_shape: weighted_trace_bound: bind-only; consumer: path_feasible_upper
proof_shape: realization_trace_zero_of_neighbors: bind-only; consumer: path_realization_trace_zero
proof_shape: path_realization_trace_zero: bind-only; consumer: path_feasible_upper
proof_shape: cycle_realization_trace_zero: bind-only; consumer: cycle_feasible_upper
proof_shape: liftPath_square: bind-only; consumer: arbitrary_path_majorana_extension
proof_shape: liftSeed_square: bind-only; consumer: arbitrary_path_majorana_extension
proof_shape: liftPath_hermitian: bind-only; consumer: arbitrary_path_majorana_extension
proof_shape: liftSeed_hermitian: bind-only; consumer: arbitrary_path_majorana_extension
proof_shape: liftPath_relation: bind-only; consumer: arbitrary_path_majorana_extension
proof_shape: liftSeed_relation: bind-only; consumer: arbitrary_path_majorana_extension
proof_shape: realization_generator_relation: bind-only; consumer: realization_majoranas
proof_shape: realization_majoranas: bind-only; consumer: path_dual_operator_certificate
proof_shape: signed_parent_suffices: bind-only; consumer: labeled_parent_suffices
proof_shape: pushforward_signed_parent: bind-only; consumers: labeled_parent_suffices, CliffordBondParents.uniform_majorana_parent
proof_shape: labeled_parent_suffices: bind-only; consumer: central_relabel_parent
proof_shape: qubitV_isometry: bind-only; consumer: padCompression_isometry
proof_shape: qubitV_compress: bind-only; consumer: padCompression_compress
proof_shape: compress_psd: bind-only; consumer: compressed_parent
proof_shape: compressed_parent: bind-only; consumer: odd_path_JM_threshold
proof_shape: paddedMajoranas_relations: bind-only; consumer: path_dual_operator_certificate
proof_shape: paddedMajoranas_bond: bind-only; consumer: path_dual_operator_certificate
proof_shape: majorana_quadratic_symmetrization: bind-only; consumers: quadratic_transpose_balance, FourierCliffordVacuum.cliffordLinear_anticommutator
proof_shape: majorana_gram_expansion: bind-only; consumer: quadratic_psd
proof_shape: quadratic_sub: bind-only; consumer: quadratic_bound_of_positive_split
proof_shape: quadratic_psd: bind-only; consumer: quadratic_bound_of_positive_split
proof_shape: quadratic_transpose_balance: bind-only; consumer: quadratic_bound_of_positive_split
proof_shape: quadratic_bound_of_positive_split: bind-only; consumer: all_length_majorana_certificate
proof_shape: sum_fin_next: bind-only; consumer: tridiagonal_mul_apply
proof_shape: sum_fin_prev: bind-only; consumer: tridiagonal_mul_apply
proof_shape: tridiagonal_symmetric: bind-only; consumer: mul_tridiagonal_apply
proof_shape: tridiagonal_mul_apply: bind-only; consumer: mul_tridiagonal_apply
proof_shape: mul_tridiagonal_apply: bind-only; consumer: shiftedFourier_intertwines
proof_shape: weightedLap_psd: bind-only; consumer: upperT_positive_split
proof_shape: weightedLap_apply: bind-only; consumer: upperT_is_signed_laplacian
-/
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.QuantumBounds.MerminMeasurementDependence.Model
namespace D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
noncomputable section
open scoped ComplexOrder
structure Realization {m d : ℕ} (G : SimpleGraph (Fin m))
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) : Prop where
  dimension_pos : 1 ≤ d
  hermitian : ∀ v, (A v).IsHermitian
  square : ∀ v, A v * A v = 1
  adjacent : ∀ u v, u ≠ v → G.Adj u v → A u * A v = -(A v * A u)
  nonadjacent : ∀ u v, u ≠ v → ¬ G.Adj u v → A u * A v = A v * A u
noncomputable def noisyObservable {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ))
    (η : ℝ) (v : Fin m) : (Matrix (Fin d) (Fin d) ℂ) :=
  D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.phi d (1 - η) 0 (A v)
noncomputable def effect {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ))
    (η : ℝ) (v : Fin m) (s : Bool) : (Matrix (Fin d) (Fin d) ℂ) :=
  (1 / 2 : ℂ) • (1 + (if s then (1 : ℂ) else -1) • noisyObservable A η v)
noncomputable def JM {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (η : ℝ) : Prop :=
  ∃ E : (Fin m → Bool) → (Matrix (Fin d) (Fin d) ℂ),
    (∀ a, (E a).PosSemidef) ∧
    (∑ a, E a = 1) ∧
    ∀ v s, (∑ a ∈ Finset.univ.filter (fun a => a v = s), E a) = effect A η v s
noncomputable def visibility (n : ℕ) : ℝ :=
  (2 / (2 * (n : ℝ) + 2)) * (Real.sin (Real.pi / (2 * (n : ℝ) + 2)))⁻¹
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
lemma signed_product (a b x : R) (s t : ℂ)
    (ha : a * x = s • (x * a)) (hb : b * x = t • (x * b)) :
    (a * b) * x = (s * t) • (x * (a * b)) := by
  calc
    (a * b) * x = a * (b * x) := mul_assoc _ _ _
    _ = t • ((a * x) * b) := by rw [hb, mul_smul_comm, ← mul_assoc]
    _ = (t * s) • (x * (a * b)) := by
      rw [ha, smul_mul_assoc, smul_smul, mul_assoc]
    _ = (s * t) • (x * (a * b)) := by rw [mul_comm t s]
private lemma signed_smul (a x : R) (c s : ℂ) (h : a * x = s • (x * a)) :
    (c • a) * x = s • (x * (c • a)) := by
  simp only [smul_mul_assoc, h, smul_smul, mul_smul_comm]
  rw [mul_comm c s]
def generatorSign (k j : ℕ) : ℂ := if k + 1 = j ∨ j + 1 = k then -1 else 1
def prefixSign (k j : ℕ) : ℂ := if j + 1 = k ∨ j = k then -1 else 1
private lemma prefixSign_step (k j : ℕ) :
    prefixSign (k + 1) j = prefixSign k j * generatorSign k j := by
  unfold prefixSign generatorSign
  split_ifs <;> norm_num <;> omega
lemma prefixSign_zero (j : ℕ) : prefixSign 0 j = if j = 0 then -1 else 1 := by
  simp [prefixSign]
def pathMajorana (A : ℕ → R) (q : R) : ℕ → R
  | 0 => q
  | k + 1 => -Complex.I • (pathMajorana A q k * A k)
private lemma pathMajorana_generator_relation (m : ℕ) (A : ℕ → R) (q : R)
    (hA : ∀ k j, k < m → j < m → A k * A j = generatorSign k j • (A j * A k))
    (hq : ∀ j, j < m → q * A j = prefixSign 0 j • (A j * q)) :
    ∀ k, k ≤ m → ∀ j, j < m →
      pathMajorana A q k * A j = prefixSign k j • (A j * pathMajorana A q k) := by
  intro k
  induction k with
  | zero => intro hk j hj; exact hq j hj
  | succ k ih =>
    intro hk j hj
    have hprod := signed_product (pathMajorana A q k) (A k) (A j)
      (prefixSign k j) (generatorSign k j) (ih (by omega) j hj) (hA k j (by omega) hj)
    simpa only [pathMajorana, prefixSign_step] using
      signed_smul (pathMajorana A q k * A k) (A j) (-Complex.I)
        (prefixSign k j * generatorSign k j) hprod
lemma anticommuting_product_square (g a : R)
    (hg : g * g = 1) (ha : a * a = 1) (hga : g * a = -(a * g)) :
    (g * a) * (g * a) = -1 := by
  calc
    (g * a) * (g * a) = (g * a * g) * a := by noncomm_ring
    _ = -(a * (g * g)) * a := by rw [hga]; noncomm_ring
    _ = -1 := by rw [hg]; simp [ha]
private lemma pathMajorana_square (m : ℕ) (A : ℕ → R) (q : R)
    (hsq : ∀ k, k < m → A k * A k = 1) (hq2 : q * q = 1)
    (hrel : ∀ k, k ≤ m → ∀ j, j < m →
      pathMajorana A q k * A j = prefixSign k j • (A j * pathMajorana A q k)) :
    ∀ k, k ≤ m → pathMajorana A q k * pathMajorana A q k = 1 := by
  intro k
  induction k with
  | zero => intro _; exact hq2
  | succ k ih =>
    intro hk
    have hanti : pathMajorana A q k * A k = -(A k * pathMajorana A q k) := by
      simpa [prefixSign] using hrel k (by omega) k (by omega)
    rw [pathMajorana, smul_mul_smul,
      anticommuting_product_square _ _ (ih (by omega)) (hsq k (by omega)) hanti]
    simp
private lemma pathMajorana_bond (m : ℕ) (A : ℕ → R) (q : R)
    (hsq : ∀ k, k ≤ m → pathMajorana A q k * pathMajorana A q k = 1)
    (k : ℕ) (hk : k < m) :
    Complex.I • (pathMajorana A q k * pathMajorana A q (k + 1)) = A k := by
  rw [pathMajorana, mul_smul_comm, smul_smul, ← mul_assoc, hsq k (by omega)]
  simp
private lemma pathMajorana_pairwise (m : ℕ) (A : ℕ → R) (q : R)
    (hsq : ∀ k, k ≤ m → pathMajorana A q k * pathMajorana A q k = 1)
    (hrel : ∀ k, k ≤ m → ∀ j, j < m →
      pathMajorana A q k * A j = prefixSign k j • (A j * pathMajorana A q k)) :
    ∀ j, j ≤ m → ∀ i, i < j →
      pathMajorana A q i * pathMajorana A q j =
        -(pathMajorana A q j * pathMajorana A q i) := by
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi
    by_cases hij : i = j
    · subst i
      have hanti : pathMajorana A q j * A j = -(A j * pathMajorana A q j) := by
        simpa [prefixSign] using hrel j (by omega) j (by omega)
      simp only [pathMajorana, mul_smul_comm, smul_mul_assoc]
      rw [← smul_neg]
      congr 1
      calc
        pathMajorana A q j * (pathMajorana A q j * A j) = A j := by
          rw [← mul_assoc, hsq j (by omega), one_mul]
        _ = -(pathMajorana A q j * A j * pathMajorana A q j) := by
          rw [hanti, neg_mul, mul_assoc, hsq j (by omega), mul_one, neg_neg]
    · have hijlt : i < j := by omega
      have hcom : A j * pathMajorana A q i = pathMajorana A q i * A j := by
        have h := hrel i (by omega) j (by omega)
        simpa [prefixSign, show j + 1 ≠ i by omega, show j ≠ i by omega] using h.symm
      simp only [pathMajorana, mul_smul_comm, smul_mul_assoc]
      calc
        -Complex.I • (pathMajorana A q i * (pathMajorana A q j * A j)) =
          -Complex.I • (-(pathMajorana A q j * (pathMajorana A q i * A j))) := by
            rw [← mul_assoc, ih (by omega) i hijlt, neg_mul, mul_assoc]
        _ = -(-Complex.I • (pathMajorana A q j * A j * pathMajorana A q i)) := by
          rw [← hcom, ← mul_assoc, smul_neg]
section Star
variable [StarRing R] [StarModule ℂ R]
private lemma pathMajorana_hermitian (m : ℕ) (A : ℕ → R) (q : R)
    (hA : ∀ k, k < m → star (A k) = A k) (hq : star q = q)
    (hrel : ∀ k, k ≤ m → ∀ j, j < m →
      pathMajorana A q k * A j = prefixSign k j • (A j * pathMajorana A q k)) :
    ∀ k, k ≤ m → star (pathMajorana A q k) = pathMajorana A q k := by
  intro k
  induction k with
  | zero => intro _; exact hq
  | succ k ih =>
    intro hk
    have hanti : A k * pathMajorana A q k = -(pathMajorana A q k * A k) := by
      have h := hrel k (by omega) k (by omega)
      simpa [prefixSign] using congrArg Neg.neg h.symm
    simp only [pathMajorana, star_smul, star_mul, ih (by omega), hA k (by omega)]
    rw [hanti]
    simp
end Star
end
open scoped ComplexOrder
lemma anticommuting_trace_zero {d : ℕ} (A B : (Matrix (Fin d) (Fin d) ℂ))
    (hB : B * B = 1) (hAB : A * B = -(B * A)) : A.trace = 0 := by
  have hconj : B * A * B = -A := by
    calc
      B * A * B = -(A * B) * B := by rw [hAB]; simp
      _ = -A := by rw [neg_mul, Matrix.mul_assoc, hB, Matrix.mul_one]
  have htrace : (B * A * B).trace = A.trace := by
    rw [Matrix.trace_mul_cycle, hB, Matrix.one_mul]
  rw [hconj, Matrix.trace_neg] at htrace
  linear_combination -(1 / 2 : ℂ) * htrace
lemma noisy_eq_of_trace_zero {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ))
    (htr : ∀ v, (A v).trace = 0) (t : ℝ) (v : Fin m) :
    noisyObservable A t v = (t : ℂ) • A v := by
  simp [noisyObservable, D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.phi, htr]
def outcomeSign (b : Bool) : ℂ := (D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (!b) : ℂ)
lemma parent_signed_marginal {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ))
    (t : ℝ) (htr : ∀ v, (A v).trace = 0)
    (E : (Fin m → Bool) → (Matrix (Fin d) (Fin d) ℂ))
    (hmarg : ∀ v s, (∑ a ∈ Finset.univ.filter (fun a => a v = s), E a) =
      effect A t v s) (v : Fin m) :
    (∑ a, outcomeSign (a v) • E a) = (t : ℂ) • A v := by
  classical
  have hsum : (∑ a, outcomeSign (a v) • E a) =
      (∑ a ∈ Finset.univ.filter (fun a => a v = true), E a) -
      (∑ a ∈ Finset.univ.filter (fun a => a v = false), E a) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    cases hv : a v <;> simp [outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, hv]
  rw [hsum, hmarg v true, hmarg v false]
  simp only [effect, noisy_eq_of_trace_zero A htr, one_smul, Bool.false_eq_true,
    ↓reduceIte, neg_one_smul]
  module
noncomputable def weightedHamiltonian {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ))
    (w : Fin m → ℝ) (a : Fin m → Bool) : (Matrix (Fin d) (Fin d) ℂ) :=
  ∑ v, (outcomeSign (a v) * (w v : ℂ)) • A v
private lemma weighted_trace_identity {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ))
    (w : Fin m → ℝ) (t : ℝ) (htr : ∀ v, (A v).trace = 0)
    (hsq : ∀ v, A v * A v = 1)
    (E : (Fin m → Bool) → (Matrix (Fin d) (Fin d) ℂ))
    (hmarg : ∀ v s, (∑ a ∈ Finset.univ.filter (fun a => a v = s), E a) =
      effect A t v s) :
    (∑ a, (E a * weightedHamiltonian A w a).trace) =
      (t : ℂ) * (d : ℂ) * ∑ v, (w v : ℂ) := by
  classical
  simp only [weightedHamiltonian, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ v, (∑ a, (outcomeSign (a v) * (w v : ℂ)) *
      (E a * A v).trace) = (t : ℂ) * (d : ℂ) * (w v : ℂ) := by
    intro v
    calc
      (∑ a, (outcomeSign (a v) * (w v : ℂ)) * (E a * A v).trace) =
          (w v : ℂ) * ((∑ a, outcomeSign (a v) • E a) * A v).trace := by
        simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
          Matrix.trace_smul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = (t : ℂ) * (d : ℂ) * (w v : ℂ) := by
        rw [parent_signed_marginal A t htr E hmarg v, Matrix.smul_mul, hsq v,
          Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
        simp only [smul_eq_mul]
        ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
section MatrixOrder
open scoped MatrixOrder
private lemma psd_eq_gram {d : ℕ} (S : (Matrix (Fin d) (Fin d) ℂ)) (hS : S.PosSemidef) :
    ∃ Z : (Matrix (Fin d) (Fin d) ℂ), S = Z * Z.conjTranspose := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.nonneg
  refine ⟨B.conjTranspose, ?_⟩
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hB
lemma weighted_trace_bound {m d : ℕ} (hd : 0 < d)
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (w : Fin m → ℝ) (t c : ℝ)
    (htr : ∀ v, (A v).trace = 0) (hsq : ∀ v, A v * A v = 1)
    (hJM : JM A t)
    (hPSD : ∀ a, ((c : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ)) - weightedHamiltonian A w a).PosSemidef) :
    t * (∑ v, w v) ≤ c := by
  classical
  obtain ⟨E, hE, hsum, hmarg⟩ := hJM
  have hn : 0 ≤ ∑ a, (E a * ((c : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ)) -
      weightedHamiltonian A w a)).trace.re := by
    exact Finset.sum_nonneg fun a _ =>
      RHLinalg.trace_mul_nonneg_of_posSemidef (hE a) (hPSD a)
  have hlin : (∑ a, (E a * ((c : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ)) -
      weightedHamiltonian A w a)).trace) =
      (c : ℂ) * (d : ℂ) - (t : ℂ) * (d : ℂ) * ∑ v, (w v : ℂ) := by
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Matrix.trace_sum, hsum, Matrix.trace_one,
      Fintype.card_fin, weighted_trace_identity A w t htr hsq E hmarg]
  have he := congrArg Complex.re hlin
  simp at he hn
  rw [he] at hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith
end MatrixOrder
private lemma realization_trace_zero_of_neighbors {m d : ℕ} (G : SimpleGraph (Fin m))
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization G A)
    (hneighbors : ∀ v, ∃ u, u ≠ v ∧ G.Adj v u) : ∀ v, (A v).trace = 0 := by
  intro v
  obtain ⟨u, huv, hadj⟩ := hneighbors v
  exact anticommuting_trace_zero (A v) (A u) (hR.square u)
    (hR.adjacent v u huv.symm hadj)
lemma path_realization_trace_zero {m d : ℕ} (hm : 2 ≤ m)
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph m) A) :
    ∀ v, (A v).trace = 0 := by
  apply realization_trace_zero_of_neighbors _ A hR
  intro v
  by_cases hv : v.val = 0
  · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · intro he; have := congrArg Fin.val he; simp at this; omega
    · rw [SimpleGraph.pathGraph_adj]
      left
      simp [hv]
  · refine ⟨⟨v.val - 1, by omega⟩, ?_, ?_⟩
    · intro he; have := congrArg Fin.val he; simp at this; omega
    · rw [SimpleGraph.pathGraph_adj]
      right
      simp; omega
lemma cycle_realization_trace_zero {m d : ℕ} (hm : 2 ≤ m)
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.cycleGraph m) A) :
    ∀ v, (A v).trace = 0 := by
  apply realization_trace_zero_of_neighbors _ A hR
  intro v
  by_cases hv : v.val = 0
  · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · intro he; have := congrArg Fin.val he; simp at this; omega
    · apply SimpleGraph.pathGraph_le_cycleGraph
      rw [SimpleGraph.pathGraph_adj]; left; simp [hv]
  · refine ⟨⟨v.val - 1, by omega⟩, ?_, ?_⟩
    · intro he; have := congrArg Fin.val he; simp at this; omega
    · apply SimpleGraph.pathGraph_le_cycleGraph
      rw [SimpleGraph.pathGraph_adj]; right; simp; omega
open  D5.S3.Quantum.FiniteDimensional
open scoped Kronecker
noncomputable section
def liftPath {d : ℕ} (A : ℕ → (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) : (Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :=
  A k ⊗ₖ (if k = 0 then qubitZ else 1)
def liftSeed (d : ℕ) : (Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) := (1 : (Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ qubitX
private lemma liftPath_square {d : ℕ} (A : ℕ → (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ)
    (hA : A k * A k = 1) : liftPath A k * liftPath A k = 1 := by
  rcases qubit_weyl_star with ⟨_, _, _, _, hZ2⟩
  unfold liftPath
  rw [← Matrix.mul_kronecker_mul, hA]
  split_ifs <;> simp [← pow_two, hZ2, Matrix.one_kronecker_one]
lemma liftSeed_square (d : ℕ) : liftSeed d * liftSeed d = 1 := by
  rcases qubit_weyl_star with ⟨_, _, _, hX2, _⟩
  unfold liftSeed
  rw [← Matrix.mul_kronecker_mul]
  simp [← pow_two, hX2]
private lemma liftPath_hermitian {d : ℕ} (A : ℕ → (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ)
    (hA : (A k).IsHermitian) : star (liftPath A k) = liftPath A k := by
  rcases qubit_weyl_star with ⟨_, _, hZ, _, _⟩
  simp only [Matrix.star_eq_conjTranspose, liftPath, Matrix.conjTranspose_kronecker, hA.eq]
  split_ifs <;> simp_all [← Matrix.star_eq_conjTranspose]
private lemma liftSeed_hermitian (d : ℕ) : star (liftSeed d) = liftSeed d := by
  rcases qubit_weyl_star with ⟨_, hX, _, _, _⟩
  simp only [Matrix.star_eq_conjTranspose, liftSeed, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.star_eq_conjTranspose, hX]
private lemma liftPath_relation {d m : ℕ} (A : ℕ → (Matrix (Fin d) (Fin d) ℂ))
    (hA : ∀ k j, k < m → j < m → A k * A j = generatorSign k j • (A j * A k))
    (k j : ℕ) (hk : k < m) (hj : j < m) :
    liftPath A k * liftPath A j = generatorSign k j • (liftPath A j * liftPath A k) := by
  unfold liftPath
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hA k j hk hj,
    Matrix.smul_kronecker]
  congr 1
  by_cases hk0 : k = 0 <;> by_cases hj0 : j = 0 <;> simp [hk0, hj0]
lemma liftSeed_relation {d : ℕ} (A : ℕ → (Matrix (Fin d) (Fin d) ℂ)) (j : ℕ) :
    liftSeed d * liftPath A j = prefixSign 0 j • (liftPath A j * liftSeed d) := by
  rcases qubit_weyl_star with ⟨hZX, _, _, _, _⟩
  have hXZ : qubitX * qubitZ = -(qubitZ * qubitX) := by rw [hZX]; simp
  unfold liftSeed liftPath
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte, Matrix.one_mul, Matrix.mul_one, prefixSign_zero,
      neg_one_smul, hXZ]
    ext u v
    simp [Matrix.kronecker, Matrix.kroneckerMap]
  · simp [hj, prefixSign_zero]
lemma arbitrary_path_majorana_extension {d m : ℕ} (A : ℕ → (Matrix (Fin d) (Fin d) ℂ))
    (hsq : ∀ k, k < m → A k * A k = 1)
    (hherm : ∀ k, k < m → (A k).IsHermitian)
    (hcomm : ∀ k j, k < m → j < m → A k * A j = generatorSign k j • (A j * A k)) :
    let g := pathMajorana (liftPath A) (liftSeed d)
    (∀ k, k ≤ m → g k * g k = 1) ∧
    (∀ k, k ≤ m → star (g k) = g k) ∧
    (∀ j, j ≤ m → ∀ i, i < j → g i * g j = -(g j * g i)) ∧
    ∀ k, k < m → Complex.I • (g k * g (k + 1)) = liftPath A k := by
  dsimp only
  have hrel := pathMajorana_generator_relation m (liftPath A) (liftSeed d)
    (fun k j hk hj => liftPath_relation A hcomm k j hk hj)
    (fun j _ => liftSeed_relation A j)
  have hsq' := pathMajorana_square m (liftPath A) (liftSeed d)
    (fun k hk => liftPath_square A k (hsq k hk)) (liftSeed_square d) hrel
  refine ⟨hsq', ?_, pathMajorana_pairwise m _ _ hsq' hrel, ?_⟩
  · exact pathMajorana_hermitian m _ _ (fun k hk => liftPath_hermitian A k (hherm k hk))
      (liftSeed_hermitian d) hrel
  · intro k hk
    exact pathMajorana_bond m _ _ hsq' k hk
end
noncomputable section
private lemma realization_generator_relation {d m : ℕ}
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph m) A)
    (k j : Fin m) : A k * A j = generatorSign k j • (A j * A k) := by
  by_cases hkj : k = j
  · subst j
    simp [generatorSign]
  · by_cases hAdj : (SimpleGraph.pathGraph m).Adj k j
    · rw [SimpleGraph.pathGraph_adj] at hAdj
      simpa [generatorSign, hAdj] using hR.adjacent k j hkj
        (SimpleGraph.pathGraph_adj.mpr hAdj)
    · have hn := hAdj
      rw [SimpleGraph.pathGraph_adj] at hn
      simpa [generatorSign, hn] using hR.nonadjacent k j hkj hAdj
def totalPath {d m : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) : (Matrix (Fin d) (Fin d) ℂ) :=
  if hk : k < m then A ⟨k,hk⟩ else 1
lemma realization_majoranas {d m : ℕ}
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph m) A) :
    let g := pathMajorana (liftPath (totalPath A)) (liftSeed d)
    (∀ k, k ≤ m → g k * g k = 1) ∧
    (∀ k, k ≤ m → star (g k) = g k) ∧
    (∀ j, j ≤ m → ∀ i, i < j → g i * g j = -(g j * g i)) ∧
    ∀ k, k < m → Complex.I • (g k * g (k + 1)) = liftPath (totalPath A) k := by
  apply arbitrary_path_majorana_extension
  · intro k hk
    simpa [totalPath, hk] using hR.square ⟨k,hk⟩
  · intro k hk
    simpa [totalPath, hk] using hR.hermitian ⟨k,hk⟩
  · intro k j hk hj
    simpa [totalPath, hk, hj] using realization_generator_relation A hR ⟨k,hk⟩ ⟨j,hj⟩
end
open scoped ComplexOrder MatrixOrder
noncomputable section
private lemma signed_parent_suffices {m d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ)
    (E : (Fin m → Bool) → (Matrix (Fin d) (Fin d) ℂ))
    (hE : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a = 1)
    (hsigned : ∀ v, ∑ a, outcomeSign (a v) • E a = noisyObservable A t v) : JM A t := by
  classical
  refine ⟨E, hE, hsum, ?_⟩
  intro v s
  have htwo : (2 : ℂ) • (∑ a ∈ Finset.univ.filter (fun a => a v = s), E a) =
      (∑ a, E a) + outcomeSign s • (∑ a, outcomeSign (a v) • E a) := by
    rw [Finset.sum_filter, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    cases hv : a v <;> cases s <;> simp [outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, hv, smul_smul, two_smul]
  have hhalf := congrArg (fun M : (Matrix (Fin d) (Fin d) ℂ) => (1 / 2 : ℂ) • M) htwo
  rw [smul_smul] at hhalf
  norm_num at hhalf
  rw [hsum, hsigned] at hhalf
  cases s <;> simpa [effect, outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, smul_add] using hhalf
lemma pushforward_signed_parent {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] {q : ℕ} (B : Fin q → Matrix ι ι ℂ) (t : ℝ)
    (label : Ω → Fin q → Bool) (P : Ω → Matrix ι ι ℂ)
    (hP : ∀ ω, (P ω).PosSemidef) (hsum : ∑ ω, P ω=1)
    (hsigned : ∀ v, ∑ ω, outcomeSign (label ω v) • P ω=(t:ℂ) • B v) :
    ∃ E : (Fin q → Bool) → Matrix ι ι ℂ,
      (∀ a, (E a).PosSemidef) ∧ (∑ a, E a=1) ∧
      ∀ v, ∑ a, outcomeSign (a v) • E a=(t:ℂ) • B v := by
  classical
  let E : (Fin q → Bool) → Matrix ι ι ℂ := fun a => ∑ ω, if label ω=a then P ω else 0
  refine ⟨E,?_,?_,?_⟩
  · intro a
    apply Matrix.posSemidef_sum
    intro ω hω
    by_cases he : label ω=a
    · simpa [he] using hP ω
    · simp only [he,↓reduceIte];exact Matrix.PosSemidef.zero
  · dsimp only [E]
    rw [Finset.sum_comm]
    simpa using hsum
  · intro v
    dsimp only [E]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ ω, (∑ a : Fin q → Bool, outcomeSign (a v) • (if label ω=a then P ω else 0))=
        outcomeSign (label ω v) • P ω := by
      intro ω
      simp only [smul_ite,smul_zero]
      simp
    simp_rw [hterm]
    exact hsigned v
lemma labeled_parent_suffices {m d : ℕ} {Ω : Type*} [Fintype Ω]
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ) (label : Ω → Fin m → Bool)
    (P : Ω → (Matrix (Fin d) (Fin d) ℂ)) (hP : ∀ ω, (P ω).PosSemidef) (hsum : ∑ ω, P ω = 1)
    (hsigned : ∀ v, ∑ ω, outcomeSign (label ω v) • P ω = noisyObservable A t v) : JM A t := by
  obtain ⟨E, hE, hsumE, hsignedE⟩ := pushforward_signed_parent (fun v => noisyObservable A t v) 1 label P hP hsum
    (fun v => by simpa using hsigned v)
  exact signed_parent_suffices A t E hE hsumE (fun v => by simpa using hsignedE v)

end
open  D5.S3.Quantum.FiniteDimensional
open scoped Kronecker
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def qubitV : Matrix (ι × Fin 2) ι ℂ := (1 : Matrix (ι × Fin 2) (ι × Fin 2) ℂ).submatrix id (fun v => (v, 0))
lemma qubitV_isometry : (qubitV (ι:=ι)).conjTranspose*(qubitV (ι:=ι))=(1:Matrix ι ι ℂ) := by
  classical
  ext u v
  simp [qubitV, Matrix.submatrix_apply, Matrix.one_apply, Prod.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.one_apply, eq_comm]
lemma qubitV_compress (A : Matrix ι ι ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    (qubitV (ι:=ι)).conjTranspose*(A ⊗ₖ D)*(qubitV (ι:=ι))=D 0 0 • A := by
  classical
  ext u v
  simp [qubitV, Matrix.submatrix_apply, Matrix.one_apply, Prod.ext_iff, Matrix.mul_apply, Matrix.kroneckerMap, Fintype.sum_prod_type,
    Fin.sum_univ_two, eq_comm]
  ring
end
noncomputable section
private lemma compress_psd {d : ℕ} {ι : Type*} [Fintype ι] (E : Matrix ι ι ℂ)
    (hE : E.PosSemidef) (V : Matrix ι (Fin d) ℂ) : (V.conjTranspose * E * V).PosSemidef :=
  hE.conjTranspose_mul_mul_same V
lemma compressed_parent {m d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (B : Fin m → Matrix ι ι ℂ) (t : ℝ)
    (V : Matrix ι (Fin d) ℂ) (hV : V.conjTranspose * V = 1)
    (htr : ∀ v, (A v).trace = 0)
    (hcomp : ∀ v, V.conjTranspose * B v * V = A v)
    (E : (Fin m → Bool) → Matrix ι ι ℂ) (hE : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1)
    (hsigned : ∀ v, ∑ a, outcomeSign (a v) • E a = (t : ℂ) • B v) : JM A t := by
  classical
  apply signed_parent_suffices A t (fun a => V.conjTranspose * E a * V)
  · intro a
    exact compress_psd (E a) (hE a) V
  · rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsum, Matrix.mul_one, hV]
  · intro v
    have hterm : ∀ a, outcomeSign (a v) • (V.conjTranspose * E a * V) =
        V.conjTranspose * (outcomeSign (a v) • E a) * V := by
      intro a
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    simp_rw [hterm]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsigned v, Matrix.mul_smul,
      Matrix.smul_mul, hcomp v, noisy_eq_of_trace_zero A htr]
end
open  D5.S3.Quantum.FiniteDimensional
open scoped Kronecker
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def paddedMajoranas {m : ℕ} (g : ℕ → Matrix ι ι ℂ) (j : Fin (m+2)) :
    Matrix (ι × Fin 2) (ι × Fin 2) ℂ :=
  if j.val=0 then (1:Matrix ι ι ℂ) ⊗ₖ qubitX else g (j.val-1) ⊗ₖ qubitZ
lemma paddedMajoranas_relations {m : ℕ} (g : ℕ → Matrix ι ι ℂ)
    (hsq : ∀ k, k ≤ m → g k*g k=1) (hg : ∀ k, k ≤ m → star (g k)=g k)
    (hanti : ∀ k l, k ≤ m → l ≤ m → k ≠ l → g k*g l=-(g l*g k)) :
    (∀ j, paddedMajoranas (m:=m) g j*paddedMajoranas g j=1) ∧
    (∀ j, star (paddedMajoranas (m:=m) g j)=paddedMajoranas g j) ∧
    ∀ j k, j ≠ k → paddedMajoranas (m:=m) g j*paddedMajoranas g k=
      -(paddedMajoranas g k*paddedMajoranas g j) := by
  rcases qubit_weyl_star with ⟨hZX,hX,hZ,hX2,hZ2⟩
  have hXsq : qubitX*qubitX=1 := by simpa [pow_two] using hX2
  have hZsq : qubitZ*qubitZ=1 := by simpa [pow_two] using hZ2
  have hXZ : qubitX*qubitZ=-(qubitZ*qubitX) := by rw [hZX]; simp
  refine ⟨?_,?_,?_⟩
  · intro j
    unfold paddedMajoranas
    split_ifs
    · rw [← Matrix.mul_kronecker_mul,hXsq,Matrix.one_mul,Matrix.one_kronecker_one]
    · rw [← Matrix.mul_kronecker_mul,hZsq,hsq _ (by have := j.isLt; omega),Matrix.one_kronecker_one]
  · intro j
    unfold paddedMajoranas
    split_ifs
    · simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
      rw [← Matrix.star_eq_conjTranspose,hX]
    · simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_kronecker]
      rw [← Matrix.star_eq_conjTranspose,← Matrix.star_eq_conjTranspose,hZ,hg _ (by have := j.isLt; omega)]
  · intro j k hjk
    unfold paddedMajoranas
    by_cases hj : j.val=0 <;> by_cases hk : k.val=0
    · have he : j=k := by apply Fin.ext; omega
      exact (hjk he).elim
    · simp only [hj,hk,↓reduceIte,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one,hXZ]
      ext u v
      simp [Matrix.kronecker,Matrix.kroneckerMap]
    · simp only [hj,hk,↓reduceIte,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one,hZX]
      ext u v
      simp [Matrix.kronecker,Matrix.kroneckerMap]
    · simp only [hj,hk,↓reduceIte,← Matrix.mul_kronecker_mul,hZsq]
      rw [hanti _ _ (by have := j.isLt; omega) (by have := k.isLt; omega)
        (by intro he; apply hjk; apply Fin.ext; omega)]
      ext u v
      simp [Matrix.kronecker,Matrix.kroneckerMap]
lemma paddedMajoranas_bond {m : ℕ} (g : ℕ → Matrix ι ι ℂ)
    (j : Fin (m+2)) (hpos : 0 < j.val) (hnext : j.val+1 < m+2) :
    Complex.I • (paddedMajoranas g j*paddedMajoranas g ⟨j.val+1,hnext⟩)=
      (Complex.I • (g (j.val-1)*g j.val)) ⊗ₖ (1:Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases qubit_weyl_star with ⟨_,_,_,_,hZ2⟩
  unfold paddedMajoranas
  simp only [show j.val≠0 by omega, show j.val+1≠0 by omega, ↓reduceIte,
    Fin.val_mk, Nat.add_sub_cancel, ← Matrix.mul_kronecker_mul]
  rw [show qubitZ*qubitZ=1 by simpa [pow_two] using hZ2, Matrix.smul_kronecker]
end
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [Ring R] [Algebra ℂ R]
lemma majorana_quadratic_symmetrization (g : ι → R)
    (hsq : ∀ j, g j * g j = 1)
    (hanti : ∀ j k, j ≠ k → g j * g k = -(g k * g j)) (C : ι → ι → ℂ) :
    (∑ j, ∑ k, C j k • (g j * g k)) =
      (∑ j, C j j) • (1 : R) +
        (1 / 2 : ℂ) • (∑ j, ∑ k, (C j k - C k j) • (g j * g k)) := by
  classical
  let Q := ∑ j, ∑ k, C j k • (g j * g k)
  have hpair : ∀ j k, C j k • (g j * g k) + C k j • (g k * g j) =
      (if j = k then (2 * C j j) • (1 : R) else 0) +
        (C j k - C k j) • (g j * g k) := by
    intro j k
    by_cases h : j = k
    · subst k
      simp only [hsq, ↓reduceIte, sub_self, zero_smul, add_zero]
      module
    · rw [hanti k j (Ne.symm h)]
      simp only [h, ↓reduceIte, zero_add, smul_neg]
      module
  have htwo : Q + Q = (2 : ℂ) • ((∑ j, C j j) • (1 : R)) +
      ∑ j, ∑ k, (C j k - C k j) • (g j * g k) := by
    dsimp only [Q]
    calc
      (∑ j, ∑ k, C j k • (g j * g k)) + (∑ j, ∑ k, C j k • (g j * g k)) =
          ∑ j, ∑ k, (C j k • (g j * g k) + C k j • (g k * g j)) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
      _ = _ := by
        simp_rw [hpair]
        simp only [Finset.sum_add_distrib]
        simp
        rw [← Finset.sum_smul, ← Finset.mul_sum, smul_smul]
  change Q = _
  calc
    Q = (1 / 2 : ℂ) • (Q + Q) := by module
    _ = _ := by rw [htwo]; module
section Star
variable [StarRing R] [StarModule ℂ R]
variable {κ : Type*} [Fintype κ]
private lemma majorana_gram_expansion (g : ι → R) (hstar : ∀ j, star (g j) = g j)
    (b : κ → ℂ) (z : κ → ι → ℂ) :
    (∑ r, b r • ((∑ j, z r j • g j) * star (∑ j, z r j • g j))) =
      ∑ j, ∑ k, (∑ r, b r * z r j * star (z r k)) • (g j * g k) := by
  classical
  simp only [star_sum, star_smul, hstar, Finset.sum_mul_sum,
    smul_mul_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  ring
end Star
end
open scoped ComplexOrder MatrixOrder
noncomputable section
variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
def Quadratic (g : Fin M → Matrix ι ι ℂ) (C : Matrix (Fin M) (Fin M) ℂ) : Matrix ι ι ℂ :=
  ∑ j, ∑ k, C j k • (g j*g k)
private lemma quadratic_sub (g : Fin M → Matrix ι ι ℂ) (P Q : Matrix (Fin M) (Fin M) ℂ) :
    Quadratic g (P-Q)=Quadratic g P-Quadratic g Q := by
  classical
  simp [Quadratic, sub_smul, Finset.sum_sub_distrib]
private lemma quadratic_psd (g : Fin M → Matrix ι ι ℂ) (hg : ∀ j, star (g j)=g j)
    (P : Matrix (Fin M) (Fin M) ℂ) (hP : P.PosSemidef) : (Quadratic g P).PosSemidef := by
  classical
  obtain ⟨Z,hZ⟩ := psd_eq_gram P hP
  have he : Quadratic g P=∑ r : Fin M,
      (∑ j, Z j r • g j)*star (∑ j, Z j r • g j) := by
    rw [hZ]
    change Quadratic g (Z*Z.conjTranspose)=_
    simpa only [Quadratic, Matrix.mul_apply, Matrix.conjTranspose_apply,
      one_mul, one_smul] using
      (majorana_gram_expansion g hg (fun _ : Fin M => (1:ℂ)) (fun r j => Z j r)).symm
  rw [he]
  apply Matrix.posSemidef_sum
  intro r hr
  simpa only [Matrix.star_eq_conjTranspose] using
    Matrix.posSemidef_self_mul_conjTranspose (∑ j, Z j r • g j)
private lemma quadratic_transpose_balance (g : Fin M → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (P : Matrix (Fin M) (Fin M) ℂ) :
    Quadratic g P+Quadratic g P.transpose=(2*P.trace) • (1:Matrix ι ι ℂ) := by
  classical
  have hp := majorana_quadratic_symmetrization g hsq hanti P
  have hpt := majorana_quadratic_symmetrization g hsq hanti P.transpose
  have hn : (∑ j, ∑ k, (P.transpose j k-P.transpose k j) • (g j*g k)) =
      -(∑ j, ∑ k, (P j k-P k j) • (g j*g k)) := by
    have he : ∀ j k : Fin M, P.transpose j k-P.transpose k j=-(P j k-P k j) := by
      intro j k; simp only [Matrix.transpose_apply]; ring
    simp_rw [he, neg_smul]
    simp only [Finset.sum_neg_distrib]
  change Quadratic g P=_ at hp
  change Quadratic g P.transpose=_ at hpt
  rw [hp, hpt, hn]
  simp only [Matrix.transpose_apply]
  change P.trace • (1:Matrix ι ι ℂ) + _ + (P.trace • (1:Matrix ι ι ℂ) + _) = _
  module
lemma quadratic_bound_of_positive_split (g : Fin M → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j))
    (P Q K : Matrix (Fin M) (Fin M) ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hsplit : K=P-Q) :
    (P.trace • (1:Matrix ι ι ℂ)-(1/2:ℂ) • Quadratic g K).PosSemidef := by
  have hPt : P.transpose.PosSemidef := by
    simpa using hP.transpose
  have hp := quadratic_psd g hg P.transpose hPt
  have hq := quadratic_psd g hg Q hQ
  have he : P.trace • (1:Matrix ι ι ℂ)-(1/2:ℂ) • Quadratic g K =
      (1/2:ℂ) • (Quadratic g P.transpose+Quadratic g Q) := by
    rw [hsplit, quadratic_sub]
    have hb := quadratic_transpose_balance g hsq hanti P
    calc
      _ = (1/2:ℂ) • ((2*P.trace) • (1:Matrix ι ι ℂ)-Quadratic g P+Quadratic g Q) := by module
      _ = _ := by rw [← hb]; module
  rw [he]
  exact (hp.add hq).smul (by norm_num [Complex.le_def] : (0:ℂ)≤1/2)
end
noncomputable section
lemma sum_fin_next {M : ℕ} {S : Type*} [AddCommMonoid S]
    (j : Fin M) (f : Fin M → S) :
    (∑ k, if j.val+1=k.val then f k else 0) =
      if h : j.val+1<M then f ⟨j.val+1,h⟩ else 0 := by
  classical
  by_cases h : j.val+1 < M
  · rw [dif_pos h]
    have he : ∀ k : Fin M, j.val+1=k.val ↔ k=⟨j.val+1,h⟩ := by
      intro k; constructor
      · intro hk; apply Fin.ext; simpa using hk.symm
      · intro hk; subst k; rfl
    simp_rw [he]
    simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    have hn : ¬j.val+1=k.val := by have := k.isLt; omega
    simp [hn]
private lemma sum_fin_prev {M : ℕ} {S : Type*} [AddCommMonoid S]
    (j : Fin M) (f : Fin M → S) :
    (∑ k, if k.val+1=j.val then f k else 0) =
      if h : 0<j.val then f ⟨j.val-1,by omega⟩ else 0 := by
  classical
  by_cases h : 0 < j.val
  · rw [dif_pos h]
    have he : ∀ k : Fin M, k.val+1=j.val ↔ k=⟨j.val-1,by omega⟩ := by
      intro k; constructor
      · intro hk; apply Fin.ext; simp; omega
      · intro hk; subst k; simp; omega
    simp_rw [he]
    simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    have hn : ¬k.val+1=j.val := by omega
    simp [hn]
def tridiagonal (M : ℕ) (d w : Fin M → ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal d + Matrix.of (fun j k : Fin M => if j.val+1=k.val then w j else 0) +
    Matrix.transpose (Matrix.of (fun j k : Fin M => if j.val+1=k.val then w j else 0))
private lemma tridiagonal_symmetric {M : ℕ} (d w : Fin M → ℂ) :
    (tridiagonal M d w).transpose = tridiagonal M d w := by
  ext j k
  simp only [tridiagonal, Matrix.transpose_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.of_apply]
  by_cases hjk : j=k
  · subst k; simp
  · simp [hjk, Ne.symm hjk]; ring
lemma tridiagonal_mul_apply {M N : ℕ} (d w : Fin M → ℂ)
    (F : Matrix (Fin M) (Fin N) ℂ) (j : Fin M) (r : Fin N) :
    (tridiagonal M d w * F) j r = d j * F j r +
      (if h : j.val+1<M then w j * F ⟨j.val+1,h⟩ r else 0) +
      (if h : 0<j.val then w ⟨j.val-1,by omega⟩ * F ⟨j.val-1,by omega⟩ r else 0) := by
  classical
  simp only [Matrix.mul_apply, tridiagonal, Matrix.add_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Matrix.of_apply, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib]
  rw [sum_fin_next, sum_fin_prev]
  simp
lemma mul_tridiagonal_apply {M N : ℕ} (d w : Fin M → ℂ)
    (F : Matrix (Fin N) (Fin M) ℂ) (j : Fin N) (r : Fin M) :
    (F * tridiagonal M d w) j r = F j r * d r +
      (if h : r.val+1<M then F j ⟨r.val+1,h⟩ * w r else 0) +
      (if h : 0<r.val then F j ⟨r.val-1,by omega⟩ * w ⟨r.val-1,by omega⟩ else 0) := by
  have h := tridiagonal_mul_apply d w F.transpose r j
  rw [← tridiagonal_symmetric d w, ← Matrix.transpose_mul] at h
  simpa [Matrix.transpose_apply, mul_comm] using h
end
open scoped ComplexOrder MatrixOrder
noncomputable section
def edgeVector (M : ℕ) (r j : Fin M) : ℂ :=
  (Pi.single r (1:ℂ) : Fin M → ℂ) j - (if r.val+1=j.val then 1 else 0)
def weightedLap (M : ℕ) (b : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℂ :=
  ∑ r, (b r:ℂ) • Matrix.vecMulVec (edgeVector M r) (star (edgeVector M r))
lemma weightedLap_psd {M : ℕ} (b : Fin M → ℝ) (hb : ∀ r, 0≤b r) :
    (weightedLap M b).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro r hr
  exact (Matrix.posSemidef_vecMulVec_self_star (edgeVector M r)).smul
    (Complex.zero_le_real.mpr (hb r))
lemma weightedLap_apply {M : ℕ} (b : Fin M → ℝ) (j k : Fin M) :
    weightedLap M b j k =
      (if j=k then ((b j:ℂ)+(if h : 0<j.val then (b ⟨j.val-1,by omega⟩:ℂ) else 0)) else 0) -
      (if j.val+1=k.val then (b j:ℂ) else 0) -
      (if k.val+1=j.val then (b k:ℂ) else 0) := by
  classical
  have h00 : (∑ r : Fin M, (b r:ℂ)*(if j=r then 1 else 0)*(if k=r then 1 else 0)) =
      if j=k then (b j:ℂ) else 0 := by
    by_cases h : j=k
    · subst k; simp [mul_ite, ite_mul]
    · simp [mul_ite, ite_mul, h]
  have h01 : (∑ r : Fin M, (b r:ℂ)*(if j=r then 1 else 0)*(if r.val+1=k.val then 1 else 0)) =
      if j.val+1=k.val then (b j:ℂ) else 0 := by
    have he : ∀ r : Fin M,
        (b r:ℂ)*(if j=r then 1 else 0)*(if r.val+1=k.val then 1 else 0) =
          if j=r then (if r.val+1=k.val then (b r:ℂ) else 0) else 0 := by
      intro r; split_ifs <;> simp_all
    simp_rw [he]
    simp
  have h10 : (∑ r : Fin M, (b r:ℂ)*(if r.val+1=j.val then 1 else 0)*(if k=r then 1 else 0)) =
      if k.val+1=j.val then (b k:ℂ) else 0 := by
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp
  have h11 : (∑ r : Fin M, (b r:ℂ)*(if r.val+1=j.val then 1 else 0)*(if r.val+1=k.val then 1 else 0)) =
      if j=k then (if h : 0<j.val then (b ⟨j.val-1,by omega⟩:ℂ) else 0) else 0 := by
    by_cases h : j=k
    · subst k
      simp only [↓reduceIte]
      have he : ∀ r : Fin M, (b r:ℂ)*(if r.val+1=j.val then 1 else 0)*(if r.val+1=j.val then 1 else 0) =
          if r.val+1=j.val then (b r:ℂ) else 0 := by intro r; split_ifs <;> simp
      simp_rw [he]
      exact sum_fin_prev j (fun r => (b r:ℂ))
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro r hr
      have he : ¬(r.val+1=j.val ∧ r.val+1=k.val) := by
        intro hh; apply h; apply Fin.ext; omega
      split_ifs <;> simp_all
  have hs : ∀ r k : Fin M, star (edgeVector M r k)=edgeVector M r k := by
    intro r k; unfold edgeVector; simp only [Pi.single_apply]; split_ifs <;> norm_num
  unfold weightedLap
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Pi.star_apply]
  simp only [hs]
  simp only [edgeVector, Pi.single_apply]
  have he : ∀ r : Fin M,
      (b r:ℂ)*(((if j=r then 1 else 0)-(if r.val+1=j.val then 1 else 0))*
        ((if k=r then 1 else 0)-(if r.val+1=k.val then 1 else 0))) =
      (b r:ℂ)*(if j=r then 1 else 0)*(if k=r then 1 else 0) -
      (b r:ℂ)*(if j=r then 1 else 0)*(if r.val+1=k.val then 1 else 0) -
      (b r:ℂ)*(if r.val+1=j.val then 1 else 0)*(if k=r then 1 else 0) +
      (b r:ℂ)*(if r.val+1=j.val then 1 else 0)*(if r.val+1=k.val then 1 else 0) := by
    intro r; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h00, h01, h10, h11]
  split_ifs <;> ring
end
end D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations

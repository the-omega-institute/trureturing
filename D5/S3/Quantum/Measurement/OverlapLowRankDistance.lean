/- GID: D5/S3/Quantum/Measurement/OverlapLowRankDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OverlapLowRankDistance
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: OverlapLowRankDistance supports the overlap bound. -/

/-
proof_shape: frob_distance_eigenvalues: bind-only; consumer: low_rank_distance_lower
escape_witness: frob_distance_eigenvalues: none
Direct frozen dependencies: frob_distance_eigenvalues: F7, F8, F9, F11, F12
proof_shape: cSq_nonneg: bind-only; consumer: quantitative_spectral_condition
escape_witness: cSq_nonneg: none
Direct frozen dependencies: cSq_nonneg: none
proof_shape: delta_budget: bind-only; consumer: delta_overlap_budget, quantitative_spectral_condition
escape_witness: delta_budget: none
Direct frozen dependencies: delta_budget: none
proof_shape: frobSq_add_le_twice: bind-only; consumer: quantitative_spectral_condition
escape_witness: frobSq_add_le_twice: none
Direct frozen dependencies: frobSq_add_le_twice: F2, F3, F7
proof_shape: delta_pos: bind-only; consumer: delta_overlap_budget, not_tight_of_quantitative, quantitative_spectral_condition
escape_witness: delta_pos: none
Direct frozen dependencies: delta_pos: none
proof_shape: cSq_lt_half: bind-only; consumer: quantitative_rank_contradiction, quantitative_spectral_condition
escape_witness: cSq_lt_half: none
Direct frozen dependencies: cSq_lt_half: none
proof_shape: one_sided_l1_bound: bind-only; consumer: one_sided_l2_bound
escape_witness: one_sided_l1_bound: none
Direct frozen dependencies: one_sided_l1_bound: none
proof_shape: offDiag_card: bind-only; consumer: overlap_excess_identity, overlap_target_distance_bound, quantitative_spectral_condition
escape_witness: offDiag_card: none
Direct frozen dependencies: offDiag_card: none
proof_shape: sum_diag_offDiag: bind-only; consumer: overlap_frobSq_target, overlap_trace_identity
escape_witness: sum_diag_offDiag: none
Direct frozen dependencies: sum_diag_offDiag: none
proof_shape: eigenvalue_lower_of_psd_sub_scalar: bind-only; consumer: equalOverlap_eigenvalue_lower
escape_witness: eigenvalue_lower_of_psd_sub_scalar: none
Direct frozen dependencies: eigenvalue_lower_of_psd_sub_scalar: none
proof_shape: equalOverlap: bind-only; consumer: equalOverlap_eigenvalue_lower, equalOverlap_low_rank_distance, overlap_frobSq_target, overlap_target_distance_bound, quantitative_spectral_condition
escape_witness: equalOverlap: none
Direct frozen dependencies: equalOverlap: none
proof_shape: ones_posSemidef: bind-only; consumer: equalOverlap_eigenvalue_lower, equalOverlap_posSemidef
escape_witness: ones_posSemidef: none
Direct frozen dependencies: ones_posSemidef: none
proof_shape: low_rank_distance_lower: content; consumer: equalOverlap_low_rank_distance
escape_witness: low_rank_distance_lower: low_rank_distance_lower
Direct frozen dependencies: low_rank_distance_lower: F4, F5, F6, F7, F8, F9, F11, F12
proof_shape: delta_overlap_budget: bind-only; consumer: quantitative_spectral_condition
escape_witness: delta_overlap_budget: none
Direct frozen dependencies: delta_overlap_budget: none
proof_shape: quantitative_rank_contradiction: bind-only; consumer: quantitative_spectral_condition
escape_witness: quantitative_rank_contradiction: none
Direct frozen dependencies: quantitative_rank_contradiction: none
proof_shape: one_sided_l2_bound: bind-only; consumer: overlap_target_distance_bound
escape_witness: one_sided_l2_bound: none
Direct frozen dependencies: one_sided_l2_bound: none
proof_shape: overlap_trace_identity: bind-only; consumer: overlap_excess_identity
escape_witness: overlap_trace_identity: none
Direct frozen dependencies: overlap_trace_identity: F1, F7
proof_shape: overlap_frobSq_target: bind-only; consumer: overlap_target_distance_bound
escape_witness: overlap_frobSq_target: none
Direct frozen dependencies: overlap_frobSq_target: F1, F7, F10
proof_shape: equalOverlap_posSemidef: bind-only; consumer: equalOverlap_eigenvalue_lower, equalOverlap_low_rank_distance
escape_witness: equalOverlap_posSemidef: none
Direct frozen dependencies: equalOverlap_posSemidef: none
proof_shape: equalOverlap_eigenvalue_lower: bind-only; consumer: equalOverlap_low_rank_distance
escape_witness: equalOverlap_eigenvalue_lower: none
Direct frozen dependencies: equalOverlap_eigenvalue_lower: none
proof_shape: overlap_excess_identity: bind-only; consumer: overlap_target_distance_bound, quantitative_spectral_condition
escape_witness: overlap_excess_identity: none
Direct frozen dependencies: overlap_excess_identity: F1, F7
proof_shape: equalOverlap_low_rank_distance: content; consumer: quantitative_spectral_condition
escape_witness: equalOverlap_low_rank_distance: equalOverlap_low_rank_distance
Direct frozen dependencies: equalOverlap_low_rank_distance: F4, F5, F6, F7, F8, F9, F11, F12
proof_shape: overlap_target_distance_bound: bind-only; consumer: quantitative_spectral_condition
escape_witness: overlap_target_distance_bound: none
Direct frozen dependencies: overlap_target_distance_bound: F1, F7, F10
admission_basis: escape-witness
Frozen declaration identities:
F1: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum
  declaration statement_id: sha256:41486c053d8cde79073cf7fd478d3eec15c60ab40b220c770f2f8b9d2ae6c459
F2: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.vectorize
  declaration statement_id: sha256:965518d7298ad8acdfeb6d0b33fc04a6e526724592513da04e49a30b340e8ddb
F3: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.vectorize_norm_sq
  declaration statement_id: sha256:6c5f3c08cd68a8eaf88971cbe045c165f849a18949357cf6c63724d4581b30e5
F4: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.card_eigenvalues_reindex
  declaration statement_id: sha256:587f80758b75110c6e73f0a75200f7e8fa58b12f878eb09edb2705914a3be32b
F5: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigEquiv
  declaration statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
F6: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigenvalues_eigEquiv
  declaration statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
F7: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.frobSq
  declaration statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
F8: owner GID: D5/S3/Weil/ZetaLinear/RankTrace; declaration: RHLinalg.frobSq_add_hermitian
  declaration statement_id: sha256:2455ef94b9a3b384dead727978c5badae8178b7c4419a88c4ecd0cef405a3e0c
F9: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues
  declaration statement_id: sha256:8517f9a9ec34b3ab0b7f30f5025ab007ce87f585c396c39fa4b953498c3fd325
F10: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.normSqMatrix
  declaration statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea
F11: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.sum_eigenvalues_reindex
  declaration statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
F12: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.vonNeumann_trace_ineq
  declaration statement_id: sha256:62c803a8caa4f496d67cb6aab1077ed04427bd78c6be62d5430e5aa1486bdc8e
Definition rows classify unfolding; they assert no proposition and supply no escape witness.
Utility: none; finite-dimensional symbolic mathematics for arbitrary parameters.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15730.
DTR reading: DTR-Unregistered for the public theorem targets in this module.
Registration gap: exact dependent source-family reconstruction, lawful template readout,
selection coordinates, whole-family variation, slot sensitivity and observational dependence
are not all established by the retained registration evidence.
-/

import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Weil.ZetaLinear.RankTrace

open Matrix Finset Filter Unitary
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace

namespace D5.S3.Quantum.Measurement.OverlapLowRankDistance
noncomputable section
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem frob_distance_eigenvalues {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ k, (hA.eigenvalues₀ k - hB.eigenvalues₀ k) ^ 2) ≤
      RHLinalg.frobSq (A - B) := by
  have hneg : RHLinalg.frobSq (-B) = RHLinalg.frobSq B := by
    simp [RHLinalg.frobSq]
  have hexp : RHLinalg.frobSq (A - B) =
      RHLinalg.frobSq A - 2 * (A * B).trace.re + RHLinalg.frobSq B := by
    rw [sub_eq_add_neg, RHLinalg.frobSq_add_hermitian hA hB.neg, hneg]
    simp [Matrix.mul_neg, Matrix.trace_neg]
    ring
  have ha : RHLinalg.frobSq A = ∑ k, (hA.eigenvalues₀ k) ^ 2 := by
    rw [RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hA]
    exact RHLinalg.sum_eigenvalues_reindex hA (· ^ 2)
  have hb : RHLinalg.frobSq B = ∑ k, (hB.eigenvalues₀ k) ^ 2 := by
    rw [RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hB]
    exact RHLinalg.sum_eigenvalues_reindex hB (· ^ 2)
  have hv := RHLinalg.vonNeumann_trace_ineq hA hB
  change (A * B).trace.re ≤ _ at hv
  have hs : (∑ k, (hA.eigenvalues₀ k - hB.eigenvalues₀ k) ^ 2) =
      (∑ k, (hA.eigenvalues₀ k) ^ 2) -
      2 * (∑ k, hA.eigenvalues₀ k * hB.eigenvalues₀ k) +
      (∑ k, (hB.eigenvalues₀ k) ^ 2) := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_sum, mul_assoc]
  rw [hs, hexp, ha, hb]
  linarith

end

section


theorem cSq_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ cSq n := by
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold cSq
  exact div_nonneg (by linarith) (by linarith)

end

section


theorem delta_budget (n : ℕ) (hn : 10 ≤ n) :
    ((n : ℝ)-3) * ((n : ℝ)*((n : ℝ)-1)) * delta n = ((n : ℝ)-9)/16 := by
  have h : (10 : ℝ) ≤ n := by exact_mod_cast hn
  unfold delta
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  have hn3 : (n : ℝ)-3 ≠ 0 := by linarith
  field_simp <;> ring

end

section


theorem frobSq_add_le_twice (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    RHLinalg.frobSq (A+B) ≤ 2*RHLinalg.frobSq A + 2*RHLinalg.frobSq B := by
  have ha := D5.S3.Quantum.Matrix.CartesianVariance.vectorize_norm_sq A
  have hb := D5.S3.Quantum.Matrix.CartesianVariance.vectorize_norm_sq B
  have hs := D5.S3.Quantum.Matrix.CartesianVariance.vectorize_norm_sq (A+B)
  have htri : ‖D5.S3.Quantum.Matrix.CartesianVariance.vectorize n (A+B)‖ ≤
      ‖D5.S3.Quantum.Matrix.CartesianVariance.vectorize n A‖ +
      ‖D5.S3.Quantum.Matrix.CartesianVariance.vectorize n B‖ := by
    rw [map_add]
    exact norm_add_le _ _
  have hsa := norm_nonneg (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n A)
  have hsb := norm_nonneg (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n B)
  have hss := norm_nonneg (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n (A+B))
  nlinarith [sq_nonneg (‖D5.S3.Quantum.Matrix.CartesianVariance.vectorize n A‖ -
    ‖D5.S3.Quantum.Matrix.CartesianVariance.vectorize n B‖)]

end

section


theorem delta_pos (n : ℕ) (hn : 10 ≤ n) : 0 < delta n := by
  have h : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) - 9 := by linarith
  have hb : 0 < (n : ℝ) - 1 := by linarith
  have hc : 0 < (n : ℝ) - 3 := by linarith
  unfold delta
  exact div_pos ha (by positivity)

end

section


theorem cSq_lt_half (n : ℕ) (hn : 2 ≤ n) : cSq n < 1 / 2 := by
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold cSq
  have hd : 0 < 2 * ((n : ℝ) - 1) := by linarith
  rw [div_lt_iff₀ hd]
  linarith

end

section
variable {ι : Type*} [DecidableEq ι]

private theorem one_sided_l1_bound (s : Finset ι) (x : ι → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hx : ∀ i ∈ s, x i ≤ e) (hs : 0 ≤ ∑ i ∈ s, x i) :
    (∑ i ∈ s, |x i|) ≤ 2 * s.card * e := by
  have hp : ∀ i ∈ s, |x i| ≤ 2*e-x i := by
    intro i hi
    rw [abs_le]
    constructor <;> linarith [hx i hi]
  have hb := sum_le_sum hp
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hb
  nlinarith

end

section
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

theorem offDiag_card (n : ℕ) : (((univ : Finset (Fin n)).offDiag)).card = n*(n-1) := by
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.mul_sub_left_distrib, Nat.mul_one] using (Finset.offDiag_card (univ : Finset (Fin n)))

end

section
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

private theorem sum_diag_offDiag (x : Fin n × Fin n → ℝ) :
    (∑ p, x p) = (∑ i, x (i,i)) + ∑ p ∈ ((univ : Finset (Fin n)).offDiag), x p := by
  have hd : (∑ p ∈ (univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2), x p) =
      ∑ i, x (i,i) := by
    symm
    apply sum_bij (fun i _ => (i,i))
    · intro i _; simp
    · intro i _ j _ hij; exact congrArg Prod.fst hij
    · intro p hp; simp only [mem_filter, mem_univ, true_and] at hp
      exact ⟨p.1, mem_univ _, by cases p; simp_all⟩
    · intro i _; rfl
  rw [← hd]
  have hoff : (univ : Finset (Fin n)).offDiag =
      (univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp [Finset.mem_offDiag]
  rw [hoff]
  exact (sum_filter_add_sum_filter_not univ (fun p => p.1 = p.2) x).symm

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eigenvalue_lower_of_psd_sub_scalar {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (a : ℝ) (hsub : (A - a • (1 : Matrix ι ι ℂ)).PosSemidef)
    (i : ι) : a ≤ hA.eigenvalues i := by
  let x : EuclideanSpace ℂ ι := hA.eigenvectorBasis i
  have hp := hsub.re_dotProduct_nonneg (x : ι → ℂ)
  have hx : star (x : ι → ℂ) ⬝ᵥ (x : ι → ℂ) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [inner_self_eq_norm_sq_to_K, x, hA.eigenvectorBasis.orthonormal.1 i]
  have he : hA.eigenvalues i = (star (x : ι → ℂ) ⬝ᵥ (A *ᵥ (x : ι → ℂ))).re :=
    hA.eigenvalues_eq i
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, map_sub, RCLike.smul_re, hx, RCLike.one_re,
    mul_one] at hp
  change 0 ≤ (star (x : ι → ℂ) ⬝ᵥ (A *ᵥ (x : ι → ℂ))).re - a at hp
  linarith

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def equalOverlap (n : ℕ) (c : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (1-c) • (1 : Matrix (Fin n) (Fin n) ℂ) + c • Matrix.of (Function.const (Fin n) (Function.const (Fin n) (1 : ℂ)))

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem ones_posSemidef (n : ℕ) :
    Matrix.PosSemidef ((fun _ _ => (1 : ℂ)) : Matrix (Fin n) (Fin n) ℂ) := by
  let V : Matrix (Fin n) (Fin 1) ℂ := fun _ _ => 1
  have hp := Matrix.posSemidef_self_mul_conjTranspose V
  have he : V * Vᴴ = (fun _ _ => 1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    change (∑ k : Fin 1, V i k * star (V j k)) = 1
    simp [V]
  rwa [he] at hp

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem low_rank_distance_lower {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (hmin : ∀ i, a ≤ hA.eigenvalues i)
    (r : ℕ) (hr : B.rank ≤ r) :
    ((Fintype.card ι : ℝ) - r) * a ^ 2 ≤ RHLinalg.frobSq (A - B) := by
  classical
  let z : Finset (Fin (Fintype.card ι)) := {k | hB.eigenvalues₀ k = 0}
  have hmin0 : ∀ k, a ≤ hA.eigenvalues₀ k := by
    intro k
    rw [← RHLinalg.eigenvalues_eigEquiv hA k]
    exact hmin _
  have hrank : #{k | hB.eigenvalues₀ k ≠ 0} ≤ r := by
    have heq : #{i | hB.eigenvalues i ≠ 0} = B.rank := by
      rw [hB.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    rw [← RHLinalg.card_eigenvalues_reindex hB (· ≠ 0), heq]
    exact hr
  have hcard : Fintype.card ι ≤ z.card + r := by
    have hpartition : z.card + #{k | hB.eigenvalues₀ k ≠ 0} = Fintype.card ι := by
      simpa [z] using Finset.card_filter_add_card_filter_not
        (s := univ) (fun k : Fin (Fintype.card ι) => hB.eigenvalues₀ k = 0)
    omega
  have hcardR : (Fintype.card ι : ℝ) - r ≤ z.card := by
    have hc : (Fintype.card ι : ℝ) ≤ (z.card : ℝ) + (r : ℝ) := by exact_mod_cast hcard
    linarith
  have hzeros : z.card * a ^ 2 ≤ ∑ k ∈ z, (hA.eigenvalues₀ k - hB.eigenvalues₀ k) ^ 2 := by
    calc
      z.card * a ^ 2 = ∑ _k ∈ z, a ^ 2 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro k hk
        have hk0 : hB.eigenvalues₀ k = 0 := by simpa [z] using hk
        rw [hk0, sub_zero]
        exact pow_le_pow_left₀ ha (hmin0 k) 2
  calc
    ((Fintype.card ι : ℝ) - r) * a ^ 2 ≤ z.card * a ^ 2 :=
      mul_le_mul_of_nonneg_right hcardR (sq_nonneg a)
    _ ≤ ∑ k ∈ z, (hA.eigenvalues₀ k - hB.eigenvalues₀ k) ^ 2 := hzeros
    _ ≤ ∑ k, (hA.eigenvalues₀ k - hB.eigenvalues₀ k) ^ 2 := by
      exact sum_le_sum_of_subset_of_nonneg (subset_univ z) (fun _ _ _ => sq_nonneg _)
    _ ≤ RHLinalg.frobSq (A - B) := frob_distance_eigenvalues hA hB

end

section


theorem delta_overlap_budget (n : ℕ) (hn : 10 ≤ n) :
    (2 * ((n : ℝ)*((n : ℝ)-1)) * delta n) ^ 2 ≤ ((n : ℝ)-9)/64 := by
  have h : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hd := delta_budget n hn
  have hn3 : 0 < (n : ℝ)-3 := by linarith
  have hx : 0 ≤ 2 * ((n : ℝ)*((n : ℝ)-1)) * delta n := by
    have := delta_pos n hn
    have hn0 : 0 ≤ (n : ℝ) := by linarith
    have hn1 : 0 ≤ (n : ℝ)-1 := by linarith
    positivity
  have hb : 2 * ((n : ℝ)*((n : ℝ)-1)) * delta n ≤ 1/8 := by
    nlinarith
  have hsq : (2 * ((n : ℝ)*((n : ℝ)-1)) * delta n) ^ 2 ≤ (1/8 : ℝ)^2 :=
    pow_le_pow_left₀ hx hb 2
  nlinarith

end

section


theorem quantitative_rank_contradiction (n : ℕ) (hn : 10 ≤ n) (dist2 : ℝ)
    (hupper : dist2 ≤ 2 * (((n : ℝ)-9)/16) + 2 * (((n : ℝ)-9)/64))
    (hlower : ((n : ℝ)-9)*(1-cSq n)^2 ≤ dist2) : False := by
  have h : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := cSq_lt_half n (by omega)
  have ha : 1/2 < 1-cSq n := by linarith
  have hb : (1/2 : ℝ)^2 < (1-cSq n)^2 := by nlinarith
  have hp := mul_lt_mul_of_pos_left hb (show 0 < (n : ℝ)-9 by linarith)
  nlinarith

end

section
variable {ι : Type*} [DecidableEq ι]

private theorem one_sided_l2_bound (s : Finset ι) (x : ι → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hx : ∀ i ∈ s, x i ≤ e) (hs : 0 ≤ ∑ i ∈ s, x i) :
    (∑ i ∈ s, x i ^ 2) ≤ (2 * s.card * e) ^ 2 := by
  have h := one_sided_l1_bound s x e he hx hs
  have hsq := sum_sq_le_sq_sum_of_nonneg (fun i (_ : i ∈ s) => abs_nonneg (x i))
  simp only [sq_abs] at hsq
  exact hsq.trans (pow_le_pow_left₀ (sum_nonneg fun i _ => abs_nonneg (x i)) h 2)

variable {n : ℕ}

end

section
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

private theorem overlap_trace_identity (G : Matrix (Fin n) (Fin n) ℂ)
    (hdiag : ∀ i, G i i = 1) (c : ℝ) :
    (∑ p ∈ ((univ : Finset (Fin n)).offDiag), (‖G p.1 p.2‖ ^ 2 - c)) =
      RHLinalg.frobSq G - n - (((univ : Finset (Fin n)).offDiag)).card*c := by
  have hf : RHLinalg.frobSq G = ∑ p : Fin n × Fin n, ‖G p.1 p.2‖ ^ 2 := by
    rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum, Fintype.sum_prod_type,
      Finset.sum_comm]
    simp only [Complex.normSq_eq_norm_sq]
  rw [hf, sum_diag_offDiag]
  simp only [hdiag, norm_one, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sum_sub_distrib]
  ring

end

section
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

private theorem overlap_frobSq_target (G : Matrix (Fin n) (Fin n) ℂ)
    (hdiag : ∀ i, G i i = 1) (c : ℝ) :
    RHLinalg.frobSq ((RHLinalg.normSqMatrix G).map (algebraMap ℝ ℂ) - equalOverlap n c) =
      ∑ p ∈ ((univ : Finset (Fin n)).offDiag), (‖G p.1 p.2‖ ^ 2 - c) ^ 2 := by
  rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum, Finset.sum_comm]
  simp only [Complex.normSq_eq_norm_sq]
  rw [← Fintype.sum_prod_type (fun p : Fin n × Fin n =>
    ‖((RHLinalg.normSqMatrix G).map (algebraMap ℝ ℂ) - equalOverlap n c) p.1 p.2‖ ^ 2)]
  rw [sum_diag_offDiag]
  have hentry : ∀ i j, ((RHLinalg.normSqMatrix G).map (algebraMap ℝ ℂ) - equalOverlap n c) i j =
      if i=j then 0 else ((‖G i j‖ ^ 2-c : ℝ) : ℂ) := by
    intro i j
    change ((‖G i j‖ ^ 2 : ℝ) : ℂ) -
      ((1-c) • (if i=j then (1 : ℂ) else 0) + c • (1 : ℂ)) = _
    by_cases hij : i=j
    · subst j
      simp [hdiag, Complex.real_smul]
    · simp [hij, Complex.real_smul]
  simp only [hentry, ite_true, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    sum_const_zero, zero_add]
  apply sum_congr rfl
  intro p hp
  have hne : p.1 ≠ p.2 := by simpa only [Finset.mem_offDiag, mem_univ, true_and] using hp
  rw [if_neg hne, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem equalOverlap_posSemidef (n : ℕ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (equalOverlap n c).PosSemidef := by
  exact (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hc1)).add
    ((ones_posSemidef n).smul hc)

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem equalOverlap_eigenvalue_lower (n : ℕ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (i : Fin n) :
    1-c ≤ (equalOverlap_posSemidef n c hc hc1).isHermitian.eigenvalues i := by
  apply eigenvalue_lower_of_psd_sub_scalar
  simp only [equalOverlap, add_sub_cancel_left]
  exact (ones_posSemidef n).smul hc

end

section
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

theorem overlap_excess_identity (n : ℕ) (hn : 2 ≤ n)
    (G : Matrix (Fin n) (Fin n) ℂ) (hdiag : ∀ i, G i i = 1) :
    (∑ p ∈ ((univ : Finset (Fin n)).offDiag), (‖G p.1 p.2‖ ^ 2 - cSq n)) =
      RHLinalg.frobSq G - (n : ℝ) ^ 2 / 2 := by
  rw [overlap_trace_identity G hdiag, offDiag_card]
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  rw [Nat.cast_mul, Nat.cast_sub (by omega)]
  norm_num only [Nat.cast_one]
  unfold cSq
  field_simp
  ring

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem equalOverlap_low_rank_distance (n r : ℕ) (c : ℝ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) (hr : B.rank ≤ r) :
    ((n : ℝ)-r) * (1-c)^2 ≤ RHLinalg.frobSq (equalOverlap n c - B) := by
  simpa using low_rank_distance_lower (equalOverlap_posSemidef n c hc hc1).isHermitian
    hB (1-c) (sub_nonneg.mpr hc1)
    (equalOverlap_eigenvalue_lower n c hc hc1) r hr

end

section
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

theorem overlap_target_distance_bound (n : ℕ) (hn : 2 ≤ n)
    (G : Matrix (Fin n) (Fin n) ℂ) (hdiag : ∀ i, G i i = 1)
    (e : ℝ) (he : 0 ≤ e)
    (hcap : ∀ i j, i ≠ j → ‖G i j‖ ^ 2 ≤ cSq n + e)
    (hexcess : 0 ≤ RHLinalg.frobSq G - (n : ℝ) ^ 2 / 2) :
    RHLinalg.frobSq ((RHLinalg.normSqMatrix G).map (algebraMap ℝ ℂ) - equalOverlap n (cSq n)) ≤
      (2*((n : ℝ)*((n : ℝ)-1))*e)^2 := by
  rw [overlap_frobSq_target G hdiag]
  have hx : ∀ p ∈ ((univ : Finset (Fin n)).offDiag), ‖G p.1 p.2‖ ^ 2-cSq n ≤ e := by
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa only [Finset.mem_offDiag, mem_univ, true_and] using hp
    linarith [hcap p.1 p.2 hne]
  have hs : 0 ≤ ∑ p ∈ ((univ : Finset (Fin n)).offDiag), (‖G p.1 p.2‖ ^ 2-cSq n) := by
    rw [overlap_excess_identity n hn G hdiag]
    exact hexcess
  have h := one_sided_l2_bound (((univ : Finset (Fin n)).offDiag)) (fun p => ‖G p.1 p.2‖ ^ 2-cSq n) e he hx hs
  rw [offDiag_card, Nat.cast_mul, Nat.cast_sub (by omega)] at h
  norm_num only [Nat.cast_one] at h
  exact h

end

end
end D5.S3.Quantum.Measurement.OverlapLowRankDistance

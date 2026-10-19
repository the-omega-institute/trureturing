/- GID: D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every boundary projection state locally distinguishes adjacent blockpositive sets. -/

/-
result proof_shape: content
escape_witness: none
admission_basis: open-problem-resolution (#17787; Proved)
Direct frozen dependencies: D1, D2, D5, D6, D4, D8, D9, D7, D10, D3.
Frozen declaration identities:
D1: D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.schmidtRank
  statement_id: sha256:9dfca1352888b59471f75e25bab5db0601d4059ee230fa472dd1ad5aa5ba3170
D2: D5/S3/Quantum/Foundation/FiniteTraceDistance.re_trace_eq_trace
  statement_id: sha256:f4d69c781be41732b5575afe6452a880aaaf7c959e52dbb9ed6c2738ad7788f2
D3: D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake
  statement_id: sha256:3f3685dfb0637d23f5f799f8ec2e875fbc8fee9823e2940f31ba7983a7b83b1e
D4: D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
  statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
D5: D5/S3/Weil/ZetaLinear/Sylvester.hermForm
  statement_id: sha256:73fe60400b35034994e7c69515b0b2e4349284066d1b1d60c2cbc066f776f399
D6: D5/S3/Weil/ZetaLinear/Sylvester.hermForm_add
  statement_id: sha256:82f2e514123bb212e131f3c26e8835a9db590e7bcc35bd5ead882f4ded811129
D7: D5/S3/Weil/ZetaLinear/Sylvester.hermForm_one
  statement_id: sha256:0bee6888fa3690daa127e5b383b3b8d256de079f6eee0cf979026543af837ef4
D8: D5/S3/Weil/ZetaLinear/Sylvester.hermForm_sub
  statement_id: sha256:6948d79f8bb85d326207469b5bfeb44953cc7d9bdb58c87fb967a4276fac4221
D9: D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.BlockSpectral.rankOneQuadratic
  statement_id: deferred (not in cached report; a fresh report is required).
D10: D5/S3/Quantum/Reduction/IsometricCompression.compress
  statement_id: sha256:ece129ea3121d41eb72b96831bf50f675e9fccf3bae2b5d39dc556c28adb9beb
Declaration classifications (all escape_witness values are none):
ambient: proof_shape: bind-only; consumer(s): BP, OnBoundary, boundary_kernel, kernel_state_in_closure, negative_unit_of_not_mem_BP, result;
  Direct frozen dependencies: none.
BP: proof_shape: bind-only; consumer(s): OnBoundary, boundary_kernel, claim, closure_of_low_rank_kernel, kernel_state_in_closure, negative_unit_of_not_mem_BP, result;
  Direct frozen dependencies: D1.
rhoPerp: proof_shape: bind-only; consumer(s): boundary_subspace_vector, claim, result, rhoPerp_kernel, rhoPerp_psd;
  Direct frozen dependencies: none.
OnBoundary: proof_shape: bind-only; consumer(s): boundary_kernel, boundary_subspace_vector, claim, result;
  Direct frozen dependencies: D1.
LocallyDistinguishable: proof_shape: bind-only; consumer(s): claim, closure_locallyDistinguishable, result;
  Direct frozen dependencies: none.
claim: proof_shape: bind-only; consumer(s): result;
  Direct frozen dependencies: D1.
compact_cone_overlap: proof_shape: content; consumer(s): overlap_schmidtRank;
  Direct frozen dependencies: none.
closed_rank_le: proof_shape: bind-only; consumer(s): closed_schmidtRank_le;
  Direct frozen dependencies: none.
closed_schmidtRank_le: proof_shape: bind-only; consumer(s): compact_rank_sphere, overlap_schmidtRank;
  Direct frozen dependencies: none.
schmidtRank_smul: proof_shape: bind-only; consumer(s): negative_unit_of_not_mem_BP, overlap_schmidtRank, unit_schmidtRank_density;
  Direct frozen dependencies: D1.
overlap_schmidtRank: proof_shape: content; consumer(s): overlap_witness;
  Direct frozen dependencies: D1.
compact_rank_sphere: proof_shape: bind-only; consumer(s): boundary_kernel;
  Direct frozen dependencies: D1.
isClosed_exists_compact_nonpos: proof_shape: bind-only; consumer(s): boundary_kernel;
  Direct frozen dependencies: none.
compress: proof_shape: bind-only; consumer(s): closure_of_low_rank_kernel, compress_at_kernel, compress_kernel, compress_psd, compress_trace, continuous_compress;
  Direct frozen dependencies: D10, D4.
qf_smul_real: proof_shape: bind-only; consumer(s): kernel_state_in_closure, qf_witnessQ;
  Direct frozen dependencies: D5.
qf_smul_vec: proof_shape: bind-only; consumer(s): negative_unit_of_not_mem_BP;
  Direct frozen dependencies: D5.
qf_one: proof_shape: bind-only; consumer(s): qf_witnessQ;
  Direct frozen dependencies: D5, D7.
proj_hermitian: proof_shape: bind-only; consumer(s): compress_at_kernel, compress_trace, witnessQ_hermitian;
  Direct frozen dependencies: none.
qf_proj: proof_shape: bind-only; consumer(s): qf_proj_inner;
  Direct frozen dependencies: D5, D4, D9.
qf_proj_inner: proof_shape: bind-only; consumer(s): qf_witnessQ;
  Direct frozen dependencies: D5, D4, D9.
proj_mulVec_self: proof_shape: bind-only; consumer(s): compress_kernel;
  Direct frozen dependencies: D4.
compress_psd: proof_shape: bind-only; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: D4.
compress_kernel: proof_shape: bind-only; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: D4, D10.
compress_at_kernel: proof_shape: bind-only; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: D4, D10.
compress_trace: proof_shape: bind-only; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: D4, D3, D10.
continuous_compress: proof_shape: bind-only; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: D10, D4.
unit_dot: proof_shape: bind-only; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: none.
witnessQ: proof_shape: bind-only; consumer(s): kernel_state_in_closure, overlap_witness, qf_witnessQ, witnessQ_hermitian;
  Direct frozen dependencies: D4.
witnessQ_hermitian: proof_shape: bind-only; consumer(s): overlap_witness;
  Direct frozen dependencies: D4.
qf_witnessQ: proof_shape: bind-only; consumer(s): overlap_witness;
  Direct frozen dependencies: D5, D4, D8, D9, D7.
overlap_witness: proof_shape: content; consumer(s): kernel_state_in_closure;
  Direct frozen dependencies: D1, D5, D4, D8, D9, D7.
projection_matrix_psd: proof_shape: bind-only; consumer(s): rhoPerp_psd;
  Direct frozen dependencies: none.
rhoPerp_psd: proof_shape: bind-only; consumer(s): boundary_subspace_vector, result;
  Direct frozen dependencies: none.
rhoPerp_kernel: proof_shape: bind-only; consumer(s): boundary_subspace_vector, result;
  Direct frozen dependencies: none.
negative_unit_of_not_mem_BP: proof_shape: bind-only; consumer(s): boundary_kernel;
  Direct frozen dependencies: D1, D5.
boundary_kernel: proof_shape: content; consumer(s): boundary_subspace_vector;
  Direct frozen dependencies: D1, D5.
rank_one_raise: proof_shape: content; consumer(s): matrix_rank_raise;
  Direct frozen dependencies: none.
matrix_rank_raise: proof_shape: content; consumer(s): mem_closure_next_rank;
  Direct frozen dependencies: none.
mem_closure_next_rank: proof_shape: content; consumer(s): mem_closure_exact_rank;
  Direct frozen dependencies: none.
mem_closure_exact_rank: proof_shape: content; consumer(s): schmidtRank_density;
  Direct frozen dependencies: none.
schmidtRank_density: proof_shape: content; consumer(s): unit_schmidtRank_density;
  Direct frozen dependencies: D1.
normalize_continuousAt: proof_shape: bind-only; consumer(s): unit_schmidtRank_density;
  Direct frozen dependencies: none.
unit_schmidtRank_density: proof_shape: content; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: D1.
kernel_state_in_closure: proof_shape: content; consumer(s): closure_of_low_rank_kernel;
  Direct frozen dependencies: D1, D5, D2, D6, D4, D8, D9, D7.
boundary_subspace_vector: proof_shape: content; consumer(s): result;
  Direct frozen dependencies: D1, D5.
closure_of_low_rank_kernel: proof_shape: content; consumer(s): result;
  Direct frozen dependencies: D1, D2, D5, D6, D4, D8, D9, D7, D10, D3.
closure_locallyDistinguishable: proof_shape: bind-only; consumer(s): result;
  Direct frozen dependencies: none.
result: proof_shape: content; consumer(s): settling result;
  Direct frozen dependencies: D1, D2, D5, D6, D4, D8, D9, D7, D10, D3.
The matrix type is written directly; vector normalization uses NormedSpace.normalize,
coefficient reshaping uses Function.curry, rank-one matrices use rankOneDensity,
compression uses IsometricCompression.compress, and real quadratic forms use
RHLinalg.hermForm and its existing laws.
The source definitions retain the expressions specified in #17787.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18546
-/
import D5.S3.Quantum.Reduction.IsometricCompression
import D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation
import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction


set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

open _root_.Matrix Topology
open RHLinalg (hermForm hermForm_add hermForm_sub)
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)


/-- The affine space `H` of trace-one Hermitian matrices (arXiv:2608.14199v1, Section 3). -/
def ambient (m n : ℕ) : Set ((Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) := {W | W.IsHermitian ∧ W.trace = 1}

/-- `BP_k`: the trace-one Hermitian matrices that are `k`-blockpositive, i.e. whose quadratic form
is nonnegative on every vector of Schmidt rank at most `k` (frozen `schmidtRank`, the rank of the
coefficient matrix). -/
def BP (m n k : ℕ) : Set ((Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) :=
  {W | W ∈ ambient m n ∧ ∀ x : Fin m × Fin n → ℂ, schmidtRank x ≤ k → 0 ≤ (star x ⬝ᵥ (W *ᵥ x)).re}

/-- The projection state `ϱ_{E⊥}` onto the orthogonal complement of `E`, normalized to trace one. -/
def rhoPerp {m n : ℕ} (E : Submodule ℂ (EuclideanSpace ℂ (Fin m × Fin n))) : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  ((Module.finrank ℂ Eᗮ : ℂ)⁻¹) • Matrix.toEuclideanLin.symm Eᗮ.starProjection.toLinearMap

/-- `ρ` is a boundary point of `BP_k` in the affine space `H` (`BP_k` is closed in `H`). -/
def OnBoundary (m n k : ℕ) (ρ : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) : Prop :=
  ρ ∈ BP m n k ∧ ρ ∈ closure (ambient m n \ BP m n k)

/-- Section 2: for `C ⊃ D` sharing the boundary point `x₀`, the inclusion is locally
distinguishable around `x₀` if every neighborhood of `x₀` meets `C \ D`. -/
def LocallyDistinguishable {m n : ℕ} (C D : Set ((Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ))) (x₀ : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) : Prop :=
  ∀ N ∈ 𝓝 x₀, (N ∩ (C \ D)).Nonempty

/-- Kiem–Kye, arXiv:2608.14199v1, Section 5: whenever `ϱ_{E⊥}` is on the boundary of `BP_k`, the
inclusion `BP_ℓ ⊋ BP_{ℓ+1}` is locally distinguishable around `ϱ_{E⊥}` for every `ℓ ≥ k` (with
`ℓ < min m n`, the length of the chain `BP_1 ⊋ ⋯ ⊋ BP_{min m n}`). -/
def claim : Prop :=
  ∀ (m n : ℕ) (E : Submodule ℂ (EuclideanSpace ℂ (Fin m × Fin n))), E ≠ ⊥ → E ≠ ⊤ →
    ∀ k ℓ : ℕ, 1 ≤ k → k ≤ ℓ → ℓ < min m n → OnBoundary m n k (rhoPerp E) →
      LocallyDistinguishable (BP m n ℓ) (BP m n (ℓ + 1)) (rhoPerp E)

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Topology
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability
open scoped InnerProductSpace

private theorem compact_cone_overlap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (S : Set H) (hS : IsClosed S) (h0 : (0 : H) ∈ S)
    (hsm : ∀ (c : ℂ) (x : H), x ∈ S → c • x ∈ S)
    (v : H) (hv : ‖v‖ = 1) (hvn : v ∉ S) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧ ∀ x ∈ S, ‖inner ℂ v x‖ ^ 2 ≤ α * ‖x‖ ^ 2 := by
  let K : Set H := Metric.closedBall 0 1 ∩ S
  have hK : IsCompact K := (isCompact_closedBall (0 : H) 1).inter_right hS
  have hK0 : (0 : H) ∈ K := ⟨Metric.mem_closedBall_self zero_le_one, h0⟩
  have hc : Continuous (fun x : H => ‖inner ℂ v x‖ ^ 2) := by fun_prop
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨0, hK0⟩ hc.continuousOn
  have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy.1
  have hv0 : v ≠ 0 := Ne.symm (ne_of_mem_of_not_mem h0 hvn)
  have hn : ‖inner ℂ v y‖ ≤ ‖y‖ := by simpa [hv] using norm_inner_le_norm v y
  have hle : ‖inner ℂ v y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (inner ℂ v y), norm_nonneg y]
  have hlt : ‖inner ℂ v y‖ ^ 2 < 1 := by
    by_contra hh
    have hnorm : ‖inner ℂ v y‖ = 1 := by nlinarith [norm_nonneg (inner ℂ v y)]
    have hyunit : ‖y‖ = 1 := le_antisymm hy1 (by exact le_of_eq_of_le (id (Eq.symm hnorm)) hn)
    have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_zero_of_eq_one hyunit)
    have heq : ‖inner ℂ v y‖ = ‖v‖ * ‖y‖ := by rw [hnorm, hv, hyunit, one_mul]
    obtain ⟨c, hc0, hcy⟩ := (norm_inner_eq_norm_iff hv0 hy0).mp heq
    apply hvn
    have hh := hsm c⁻¹ y hy.2
    simpa [hcy, smul_smul, hc0] using hh
  refine ⟨‖inner ℂ v y‖ ^ 2, sq_nonneg _, hlt, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hn0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  let z : H := ((‖x‖ : ℂ)⁻¹) • x
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    exact norm_smul_inv_norm (𝕜 := ℂ) hx0
  have hzK : z ∈ K := ⟨by simpa [hz], hsm _ x hx⟩
  have hh : ‖inner ℂ v z‖ ^ 2 ≤ ‖inner ℂ v y‖ ^ 2 := hmax hzK
  have heq : ‖inner ℂ v z‖ = ‖inner ℂ v x‖ / ‖x‖ := by
    simp [z, inner_smul_right, norm_mul, div_eq_inv_mul]
  rw [heq, div_pow] at hh
  exact (div_le_iff₀ (sq_pos_of_ne_zero hn0)).mp hh

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology
open RHLinalg (hermForm hermForm_add hermForm_sub)
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

private theorem closed_rank_le {m n : ℕ} (j : ℕ) :
    IsClosed {A : Matrix (Fin m) (Fin n) ℂ | A.rank ≤ j} := by
  let f : Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ((Fin n → ℂ) →L[ℂ] (Fin m → ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toLin'.toLinearMap
  have hc : Continuous f := f.continuous_of_finiteDimensional
  have ho := (isOpen_setOfPred_nat_le_rank (𝕜 := ℂ) (E := Fin n → ℂ)
    (F := Fin m → ℂ) (j+1)).preimage hc
  have he : f ⁻¹' {g | ((j+1 : ℕ) : Cardinal) ≤ (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)).rank} =
      {A : Matrix (Fin m) (Fin n) ℂ | ¬ A.rank ≤ j} := by
    ext A
    change ((j+1 : ℕ) : Cardinal) ≤ Module.rank ℂ (LinearMap.range A.mulVecLin) ↔ ¬ A.rank ≤ j
    rw [← Module.finrank_eq_rank]
    change ((j+1 : ℕ) : Cardinal) ≤ ((A.rank : ℕ) : Cardinal) ↔ ¬ A.rank ≤ j
    norm_cast
    omega
  rw [he] at ho
  exact isOpen_compl_iff.mp ho

private theorem closed_schmidtRank_le {m n : ℕ} (j : ℕ) :
    IsClosed {x : EuclideanSpace ℂ (Fin m × Fin n) | schmidtRank (WithLp.ofLp x) ≤ j} := by
  exact (closed_rank_le j).preimage (by fun_prop)

private theorem schmidtRank_smul {m n : ℕ} (c : ℂ) (hc : c ≠ 0) (x : Fin m × Fin n → ℂ) :
    schmidtRank (c • x) = schmidtRank x := by
  unfold schmidtRank
  change (c • (Matrix.of fun i j => x (i,j))).rank = _
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)

private theorem overlap_schmidtRank {m n : ℕ} (j : ℕ)
    (v : EuclideanSpace ℂ (Fin m × Fin n)) (hv : ‖v‖ = 1)
    (hr : j < schmidtRank (WithLp.ofLp v)) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ x : EuclideanSpace ℂ (Fin m × Fin n), schmidtRank (WithLp.ofLp x) ≤ j →
        ‖inner ℂ v x‖ ^ 2 ≤ α * ‖x‖ ^ 2 := by
  let S : Set (EuclideanSpace ℂ (Fin m × Fin n)) :=
    {x | schmidtRank (WithLp.ofLp x) ≤ j}
  have h0 : (0 : EuclideanSpace ℂ (Fin m × Fin n)) ∈ S := by
    change (0 : Matrix (Fin m) (Fin n) ℂ).rank ≤ j
    simp
  have hsm : ∀ (c : ℂ) (x : EuclideanSpace ℂ (Fin m × Fin n)), x ∈ S → c • x ∈ S := by
    intro c x hx
    by_cases hc : c = 0
    · simpa [hc] using h0
    · change schmidtRank (c • WithLp.ofLp x) ≤ j
      rwa [schmidtRank_smul c hc]
  exact compact_cone_overlap S (closed_schmidtRank_le j) h0 hsm v hv (not_le.mpr hr)

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Topology _root_.Matrix
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability
private theorem compact_rank_sphere {m n : ℕ} (j : ℕ) :
    IsCompact {x : EuclideanSpace ℂ (Fin m × Fin n) |
      ‖x‖ = 1 ∧ schmidtRank (WithLp.ofLp x) ≤ j} := by
  have he : {x : EuclideanSpace ℂ (Fin m × Fin n) |
      ‖x‖ = 1 ∧ schmidtRank (WithLp.ofLp x) ≤ j} =
      Metric.sphere 0 1 ∩ {x | schmidtRank (WithLp.ofLp x) ≤ j} := by
    ext x
    simp [Metric.mem_sphere, dist_zero_right]
  rw [he]
  exact (isCompact_sphere (0 : EuclideanSpace ℂ (Fin m × Fin n)) 1).inter_right
    (closed_schmidtRank_le j)
end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Topology Filter
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability
private theorem isClosed_exists_compact_nonpos {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (K : Set Y) (hK : IsCompact K) (f : X → Y → ℝ)
    (hc : Continuous (fun p : X × Y => f p.1 p.2)) :
    IsClosed {x : X | ∃ y ∈ K, f x y ≤ 0} := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hh : IsClosed {p : X × K | f p.1 p.2 ≤ 0} :=
    isClosed_le (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) continuous_const
  have hp := isClosedMap_fst_of_compactSpace _ hh
  have he : Prod.fst '' {p : X × K | f p.1 p.2 ≤ 0} = {x : X | ∃ y ∈ K, f x y ≤ 0} := by
    ext x
    constructor
    · rintro ⟨⟨a, y⟩, hy, rfl⟩
      exact ⟨y, y.2, hy⟩
    · rintro ⟨y, hyK, hy⟩
      exact ⟨(x, ⟨y, hyK⟩), hy, rfl⟩
  rwa [he] at hp

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology
open RHLinalg (hermForm hermForm_add hermForm_sub)
open scoped ComplexOrder
open D5.S3.Quantum.PureState.PureStateHandshake
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


private def compress (A : Matrix ι ι ℂ) (u : ι → ℂ) : Matrix ι ι ℂ :=
  D5.S3.Quantum.Reduction.IsometricCompression.compress (1 - rankOneDensity u) A

omit [DecidableEq ι] in
private theorem qf_smul_real (r : ℝ) (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    hermForm ((r : ℂ) • A) x = r * hermForm A x := by
  simp [hermForm, smul_mulVec, dotProduct_smul, Complex.mul_re]

omit [DecidableEq ι] in
private theorem qf_smul_vec (c : ℂ) (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    hermForm A (c • x) = Complex.normSq c * hermForm A x := by
  simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, ← mul_assoc]
  have hh : c * star c = (Complex.normSq c : ℂ) := by
    simpa only [Complex.star_def, mul_comm] using (Complex.normSq_eq_conj_mul_self (z := c)).symm
  rw [hh]
  simp

private theorem qf_one (x : ι → ℂ) :
    hermForm (1 : Matrix ι ι ℂ) x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [RHLinalg.hermForm_one, EuclideanSpace.norm_sq_eq]

omit [DecidableEq ι] in
private theorem proj_hermitian (u : ι → ℂ) : (rankOneDensity u).IsHermitian :=
  (Matrix.posSemidef_vecMulVec_self_star u).isHermitian

omit [DecidableEq ι] in
private theorem qf_proj (u x : ι → ℂ) :
    hermForm (rankOneDensity u) x = Complex.normSq (star u ⬝ᵥ x) := by
  unfold hermForm
  rw [D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector]
  simp only [star_dotProduct x u, Complex.star_def, Complex.normSq_conj]
  rfl

omit [DecidableEq ι] in
private theorem qf_proj_inner (u x : EuclideanSpace ℂ ι) :
    hermForm (rankOneDensity (WithLp.ofLp u)) (WithLp.ofLp x) = ‖inner ℂ u x‖ ^ 2 := by
  rw [qf_proj, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, Complex.normSq_eq_norm_sq]

omit [DecidableEq ι] in
private theorem proj_mulVec_self (u : ι → ℂ) (hu : star u ⬝ᵥ u = 1) :
    rankOneDensity u *ᵥ u = u := by
  simp [rankOneDensity, vecMulVec_mulVec, hu]

private theorem compress_psd (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (u : ι → ℂ) :
    (compress A u).PosSemidef := by
  exact hA.conjTranspose_mul_mul_same (1 - rankOneDensity u)

private theorem compress_kernel (A : Matrix ι ι ℂ) (u : ι → ℂ) (hu : star u ⬝ᵥ u = 1) :
    compress A u *ᵥ u = 0 := by
  simp only [compress, D5.S3.Quantum.Reduction.IsometricCompression.compress, ← mulVec_mulVec, sub_mulVec, one_mulVec, proj_mulVec_self u hu,
    sub_self, mulVec_zero]

private theorem compress_at_kernel (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (u : ι → ℂ) (hu : A *ᵥ u = 0) : compress A u = A := by
  have hright : A * rankOneDensity u = 0 := by
    simp [rankOneDensity, mul_vecMulVec, hu]
  have hleft : rankOneDensity u * A = 0 := by
    have hh := congrArg Matrix.conjTranspose hright
    simpa [conjTranspose_mul, hA.eq, (proj_hermitian u).eq] using hh
  simp [compress, D5.S3.Quantum.Reduction.IsometricCompression.compress,
    (isHermitian_one.sub (proj_hermitian u)).eq, mul_sub, sub_mul, hright, hleft]

private theorem compress_trace (A : Matrix ι ι ℂ) (u : ι → ℂ) (hu : star u ⬝ᵥ u = 1) :
    (compress A u).trace = A.trace - (star u ⬝ᵥ (A *ᵥ u)) := by
  have hid : rankOneDensity u * rankOneDensity u = rankOneDensity u := (pure_state_handshake u hu A).1
  have htr : (A * rankOneDensity u).trace = star u ⬝ᵥ (A *ᵥ u) := (pure_state_handshake u hu A).2.2.symm
  calc
    (compress A u).trace = (A * ((1 - rankOneDensity u) * (1 - rankOneDensity u))).trace := by
      rw [compress, D5.S3.Quantum.Reduction.IsometricCompression.compress,
        (isHermitian_one.sub (proj_hermitian u)).eq, trace_mul_cycle, trace_mul_comm]
    _ = (A * (1 - rankOneDensity u)).trace := by
      congr 2
      noncomm_ring [hid]
    _ = A.trace - (star u ⬝ᵥ (A *ᵥ u)) := by
      rw [mul_sub, mul_one, trace_sub, htr]

private theorem continuous_compress (A : Matrix ι ι ℂ) : Continuous (compress A) := by
  unfold compress D5.S3.Quantum.Reduction.IsometricCompression.compress rankOneDensity
  fun_prop

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology
open RHLinalg (hermForm hermForm_add hermForm_sub)
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem unit_dot (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    star (WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  exact inner_self_eq_one_of_norm_eq_one hu

private def witnessQ (u : ι → ℂ) (α : ℝ) : Matrix ι ι ℂ :=
  (α : ℂ) • (1 : Matrix ι ι ℂ) - rankOneDensity u

private theorem witnessQ_hermitian (u : ι → ℂ) (α : ℝ) : (witnessQ u α).IsHermitian := by
  have hh : IsSelfAdjoint (α : ℂ) :=
    (Complex.im_eq_zero_iff_isSelfAdjoint (α : ℂ)).mp rfl
  exact (isHermitian_one.smul hh).sub (proj_hermitian u)

private theorem qf_witnessQ (u x : EuclideanSpace ℂ ι) (α : ℝ) :
    hermForm (witnessQ (WithLp.ofLp u) α) (WithLp.ofLp x) =
      α * ‖x‖ ^ 2 - ‖inner ℂ u x‖ ^ 2 := by
  rw [witnessQ, hermForm_sub, qf_smul_real, qf_one, qf_proj_inner]

private theorem overlap_witness {m n : ℕ} (j : ℕ)
    (u : EuclideanSpace ℂ (Fin m × Fin n)) (hu : ‖u‖ = 1)
    (hr : j < schmidtRank (WithLp.ofLp u)) :
    ∃ (α : ℝ) (Q : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
      0 ≤ α ∧ α < 1 ∧ Q = witnessQ (WithLp.ofLp u) α ∧ Q.IsHermitian ∧
      (∀ x : Fin m × Fin n → ℂ, schmidtRank x ≤ j → 0 ≤ hermForm Q x) ∧
      hermForm Q (WithLp.ofLp u) = α - 1 := by
  obtain ⟨α, hα0, hα1, hα⟩ := overlap_schmidtRank j u hu hr
  refine ⟨α, witnessQ (WithLp.ofLp u) α, hα0, hα1, rfl, witnessQ_hermitian _ _, ?_, ?_⟩
  · intro x hx
    have hh := hα (WithLp.toLp 2 x) hx
    have he := qf_witnessQ u (WithLp.toLp 2 x) α
    dsimp only [WithLp.ofLp_toLp] at he
    rw [he]
    linarith
  · rw [qf_witnessQ, hu, inner_self_eq_norm_sq_to_K, hu]
    simp

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology
open RHLinalg (hermForm hermForm_add hermForm_sub)
open scoped ComplexOrder
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability
variable {m n : ℕ}

private theorem projection_matrix_psd (E : Submodule ℂ (EuclideanSpace ℂ (Fin m × Fin n))) :
    (Matrix.toEuclideanLin.symm E.starProjection.toLinearMap).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearEquiv.apply_symm_apply]
  exact LinearMap.IsSymmetricProjection.isPositive
    ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap E.isIdempotentElem_starProjection, E.starProjection_isSymmetric⟩

private theorem rhoPerp_psd (E : Submodule ℂ (EuclideanSpace ℂ (Fin m × Fin n))) :
    (rhoPerp E).PosSemidef := by
  unfold rhoPerp
  apply (projection_matrix_psd Eᗮ).smul
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem rhoPerp_kernel (E : Submodule ℂ (EuclideanSpace ℂ (Fin m × Fin n)))
    (hE : E ≠ ⊤) (u : EuclideanSpace ℂ (Fin m × Fin n)) :
    rhoPerp E *ᵥ WithLp.ofLp u = 0 ↔ u ∈ E := by
  have hdim : Module.finrank ℂ Eᗮ ≠ 0 := by
    intro h
    have he : Eᗮ = ⊥ := Submodule.finrank_eq_zero.mp h
    exact hE (Submodule.orthogonal_eq_bot_iff.mp he)
  have hd : ((Module.finrank ℂ Eᗮ : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hdim)
  have he : (Matrix.toEuclideanLin.symm Eᗮ.starProjection.toLinearMap) *ᵥ WithLp.ofLp u =
      WithLp.ofLp (Eᗮ.starProjection u) := by
    have h := congrArg (fun f : Module.End ℂ (EuclideanSpace ℂ (Fin m × Fin n)) => WithLp.ofLp (f u))
      (Matrix.toEuclideanLin.apply_symm_apply Eᗮ.starProjection.toLinearMap)
    exact h
  rw [rhoPerp, smul_mulVec, smul_eq_zero_iff_right hd, he]
  have hh : WithLp.ofLp (Eᗮ.starProjection u) = 0 ↔ Eᗮ.starProjection u = 0 :=
    by exact WithLp.ofLp_eq_zero 2
  rw [hh, Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology
open RHLinalg (hermForm hermForm_add hermForm_sub)
open scoped ComplexOrder
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability
private theorem negative_unit_of_not_mem_BP {m n j : ℕ} (W : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ))
    (hW : W ∈ ambient m n) (hnot : W ∉ BP m n j) :
    ∃ u : EuclideanSpace ℂ (Fin m × Fin n), ‖u‖ = 1 ∧
      schmidtRank (WithLp.ofLp u) ≤ j ∧ hermForm W (WithLp.ofLp u) < 0 := by
  classical
  have htest : ¬ ∀ x : Fin m × Fin n → ℂ, schmidtRank x ≤ j → 0 ≤ hermForm W x := by
    intro hh
    exact hnot ⟨hW, hh⟩
  push Not at htest
  obtain ⟨x, hxr, hxq⟩ := htest
  have hx0 : x ≠ 0 := by intro h; simp [hermForm, h] at hxq
  let y : EuclideanSpace ℂ (Fin m × Fin n) := WithLp.toLp 2 x
  have hy0 : y ≠ 0 := (WithLp.toLp_eq_zero 2).ne.2 hx0
  let c : ℂ := (‖y‖⁻¹ : ℝ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hy0))
  refine ⟨c • y, ?_, ?_, ?_⟩
  · dsimp only [c]
    rw [Complex.ofReal_inv]
    exact norm_smul_inv_norm (𝕜 := ℂ) hy0
  · change schmidtRank (c • x) ≤ j
    rwa [schmidtRank_smul c hc]
  · change hermForm W (c • x) < 0
    rw [qf_smul_vec]
    exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc) hxq

private theorem boundary_kernel {m n j : ℕ} (ρ : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) (hρ : ρ.PosSemidef)
    (hb : OnBoundary m n j ρ) :
    ∃ u : EuclideanSpace ℂ (Fin m × Fin n), ‖u‖ = 1 ∧
      schmidtRank (WithLp.ofLp u) ≤ j ∧ ρ *ᵥ WithLp.ofLp u = 0 := by
  let K : Set (EuclideanSpace ℂ (Fin m × Fin n)) :=
    {u | ‖u‖ = 1 ∧ schmidtRank (WithLp.ofLp u) ≤ j}
  have hK : IsCompact K := compact_rank_sphere j
  have hc : Continuous (fun p : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) × EuclideanSpace ℂ (Fin m × Fin n) =>
      hermForm p.1 (WithLp.ofLp p.2)) := by
    unfold hermForm
    fun_prop
  have hclosed := isClosed_exists_compact_nonpos K hK
    (fun (W : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) u => hermForm W (WithLp.ofLp u)) hc
  have hinc : ambient m n \ BP m n j ⊆
      {W : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) | ∃ u ∈ K, hermForm W (WithLp.ofLp u) ≤ 0} := by
    intro W hW
    obtain ⟨u, hu, hr, hq⟩ := negative_unit_of_not_mem_BP W hW.1 hW.2
    exact ⟨u, ⟨hu, hr⟩, hq.le⟩
  have hh := closure_minimal hinc hclosed hb.2
  obtain ⟨u, ⟨hu, hr⟩, hq⟩ := hh
  have hz : star (WithLp.ofLp u) ⬝ᵥ (ρ *ᵥ WithLp.ofLp u) = 0 := by
    apply Complex.ext
    · exact le_antisymm hq (hρ.re_dotProduct_nonneg _)
    · exact hρ.isHermitian.im_star_dotProduct_mulVec_self _
  exact ⟨u, hu, hr, hρ.dotProduct_mulVec_zero_iff.mp hz⟩

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology Filter
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

private theorem rank_one_raise {m n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hm : Module.finrank ℂ (LinearMap.range f) < m)
    (hn : Module.finrank ℂ (LinearMap.range f) < n) :
    ∃ g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ t : ℂ, t ≠ 0 →
      Module.finrank ℂ (LinearMap.range (f + t • g)) =
        Module.finrank ℂ (LinearMap.range f) + 1 := by
  classical
  have hnull := f.finrank_range_add_finrank_ker
  have hdimn : Module.finrank ℂ (Fin n → ℂ) = n := Module.finrank_fin_fun ℂ
  have hkdim : Module.finrank ℂ (LinearMap.ker f) ≠ 0 := by omega
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro hh
    apply hkdim
    rw [hh]
    simp
  obtain ⟨u, hu, hu0⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  obtain ⟨φ, hφu⟩ := Module.Projective.exists_dual_eq_one ℂ hu0
  have hφ : φ ≠ 0 := by intro h; simp [h] at hφu
  have hdimm : Module.finrank ℂ (Fin m → ℂ) = m := Module.finrank_fin_fun ℂ
  obtain ⟨w, hw⟩ := (LinearMap.range f).exists_of_finrank_lt (by exact Nat.lt_of_lt_of_eq hm (id (Eq.symm hdimm)))
  refine ⟨φ.smulRight w, ?_⟩
  intro t ht
  have hk : LinearMap.ker (f + t • φ.smulRight w) = LinearMap.ker f ⊓ LinearMap.ker φ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_inf, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul]
    constructor
    · intro hx
      have hc : t * φ x = 0 := by
        by_contra hc
        have hh : (t * φ x) • w ∈ LinearMap.range f := by
          have he : (t * φ x) • w = -f x := by exact Eq.symm (neg_eq_of_add_eq_zero_right hx)
          rw [he]
          exact Submodule.neg_mem _ ⟨x, rfl⟩
        exact hw _ hc hh
      have hpx : φ x = 0 := (mul_eq_zero.mp hc).resolve_left ht
      exact ⟨by simpa [hpx] using hx, hpx⟩
    · rintro ⟨hx, hp⟩
      simp [hx, hp]
  have hs : LinearMap.ker f ⊔ LinearMap.ker φ = ⊤ := by
    apply top_unique
    rw [← φ.span_singleton_sup_ker_eq_top (by exact ne_zero_of_eq_one hφu)]
    exact sup_le_sup ((Submodule.span_singleton_le_iff_mem u _).mpr hu) le_rfl
  have hdim := (LinearMap.ker f).finrank_sup_add_finrank_inf_eq (LinearMap.ker φ)
  rw [hs, finrank_top] at hdim
  have hdφ := φ.finrank_ker_add_one_of_ne_zero hφ
  have hnew := (f + t • φ.smulRight w).finrank_range_add_finrank_ker
  rw [hk] at hnew
  omega

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology Filter
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

private theorem matrix_rank_raise {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (hm : A.rank < m) (hn : A.rank < n) :
    ∃ B : Matrix (Fin m) (Fin n) ℂ, ∀ t : ℂ, t ≠ 0 → (A + t • B).rank = A.rank + 1 := by
  obtain ⟨g, hg⟩ := rank_one_raise (Matrix.toLin' A) hm hn
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  intro t ht
  have he : (A + t • LinearMap.toMatrix' g).mulVecLin = Matrix.toLin' A + t • g := by
    change Matrix.toLin' (A + t • LinearMap.toMatrix' g) = _
    rw [map_add, map_smul, Matrix.toLin'_toMatrix']
  change Module.finrank ℂ (LinearMap.range _) = _
  rw [he]
  exact hg t ht

private theorem mem_closure_next_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (hm : A.rank < m) (hn : A.rank < n) :
    A ∈ closure {B : Matrix (Fin m) (Fin n) ℂ | B.rank = A.rank+1} := by
  obtain ⟨B, hB⟩ := matrix_rank_raise A hm hn
  have hc : Continuous (fun t : ℝ => A + (t : ℂ) • B) := by fun_prop
  have ht : Tendsto (fun t : ℝ => A + (t : ℂ) • B) (𝓝[>] 0) (𝓝 A) := by
    have h0 : Tendsto (fun t : ℝ => A + (t : ℂ) • B) (𝓝 (0 : ℝ)) (𝓝 A) := by
      simpa using hc.tendsto 0
    exact h0.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hB (t : ℂ) (Complex.ne_zero_of_re_pos ht)

private theorem mem_closure_exact_rank {m n j : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (hr : A.rank ≤ j) (hm : j ≤ m) (hn : j ≤ n) :
    A ∈ closure {B : Matrix (Fin m) (Fin n) ℂ | B.rank = j} := by
  induction j generalizing A with
  | zero => exact subset_closure (by simpa using hr)
  | succ j ih =>
    by_cases he : A.rank = j+1
    · exact subset_closure he
    have hlow : A.rank ≤ j := by omega
    have hprev := ih A hlow (Nat.le_of_succ_le hm) (Nat.le_of_succ_le hn)
    apply closure_minimal (t := closure {B : Matrix (Fin m) (Fin n) ℂ | B.rank = j+1})
      (fun B hB => ?_) isClosed_closure hprev
    have hb : B.rank = j := hB
    have hh := mem_closure_next_rank B (by omega) (by omega)
    simpa only [hb] using hh

private theorem schmidtRank_density {m n j : ℕ} (x : EuclideanSpace ℂ (Fin m × Fin n))
    (hr : schmidtRank (WithLp.ofLp x) ≤ j) (hm : j ≤ m) (hn : j ≤ n) :
    x ∈ closure {y : EuclideanSpace ℂ (Fin m × Fin n) | schmidtRank (WithLp.ofLp y) = j} := by
  let f : Matrix (Fin m) (Fin n) ℂ → EuclideanSpace ℂ (Fin m × Fin n) :=
    fun A => WithLp.toLp 2 (fun p => A p.1 p.2)
  have hc : Continuous f := by unfold f; fun_prop
  have hi : Set.MapsTo f {A : Matrix (Fin m) (Fin n) ℂ | A.rank = j}
      {y : EuclideanSpace ℂ (Fin m × Fin n) | schmidtRank (WithLp.ofLp y) = j} := by
    intro A hA
    exact hA
  have hh := hi.closure hc (mem_closure_exact_rank (Matrix.of (Function.curry (WithLp.ofLp x))) hr hm hn)
  exact hh

private theorem normalize_continuousAt {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) (hx : x ≠ 0) :
    ContinuousAt NormedSpace.normalize x := by
  unfold NormedSpace.normalize
  exact (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

private theorem unit_schmidtRank_density {m n j : ℕ} (x : EuclideanSpace ℂ (Fin m × Fin n))
    (hu : ‖x‖ = 1) (hr : schmidtRank (WithLp.ofLp x) ≤ j)
    (hj : 0 < j) (hm : j ≤ m) (hn : j ≤ n) :
    x ∈ closure {y : EuclideanSpace ℂ (Fin m × Fin n) |
      ‖y‖ = 1 ∧ schmidtRank (WithLp.ofLp y) = j} := by
  have hx : x ≠ 0 := norm_ne_zero_iff.mp (ne_zero_of_eq_one hu)
  have he : NormedSpace.normalize x = x := by
    exact NormedSpace.normalize_eq_self_of_norm_eq_one hu
  rw [← he]
  apply closure_mono (s := NormedSpace.normalize ''
    {y : EuclideanSpace ℂ (Fin m × Fin n) | schmidtRank (WithLp.ofLp y) = j}) ?_
      (mem_closure_image (normalize_continuousAt x hx) (schmidtRank_density x hr hm hn))
  rintro _ ⟨y, hyr, rfl⟩
  have hy : y ≠ 0 := by
    intro hy
    have hz : schmidtRank (WithLp.ofLp y) = 0 := by
      subst y
      change (0 : Matrix (Fin m) (Fin n) ℂ).rank = 0
      simp
    have hyr' : schmidtRank (WithLp.ofLp y) = j := hyr
    omega
  have hnorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  refine ⟨?_, ?_⟩
  · exact NormedSpace.norm_normalize hy
  · change schmidtRank (((‖y‖⁻¹ : ℝ) : ℂ) • WithLp.ofLp y) = j
    rw [schmidtRank_smul _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hnorm))]
    exact hyr

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology Filter
open scoped ComplexOrder
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

private theorem kernel_state_in_closure {m n j : ℕ} (A : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) (hA : A.PosSemidef)
    (htr : A.trace = 1) (u : EuclideanSpace ℂ (Fin m × Fin n))
    (hu : ‖u‖ = 1) (hr : schmidtRank (WithLp.ofLp u) = j+1)
    (hAu : A *ᵥ WithLp.ofLp u = 0) :
    A ∈ closure (BP m n j \ BP m n (j+1)) := by
  obtain ⟨α, Q, hα0, hα1, hQeq, hQ, hpos, hneg⟩ :=
    overlap_witness j u hu (by omega)
  let d : ℝ → ℝ := fun t => 1 + t * Q.trace.re
  let W : ℝ → (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) := fun t => (((d t)⁻¹ : ℝ) : ℂ) • (A + (t : ℂ) • Q)
  have hd0 : d 0 = 1 := by simp [d]
  have hd : Continuous d := by unfold d; fun_prop
  have hdpos : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), 0 < d t :=
    (hd.continuousAt.eventually (Ioi_mem_nhds (by rw [hd0]; norm_num)))
  have hwlim : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    have hwc : ContinuousAt W 0 := by
      have hsum : Continuous (fun t : ℝ => A + (t : ℂ) • Q) := by fun_prop
      unfold W
      exact ((Complex.continuous_ofReal.continuousAt.comp
        (hd.continuousAt.inv₀ (by exact ne_zero_of_eq_one hd0)))).smul
          hsum.continuousAt
    have hw0 : W 0 = A := by simp [W, hd0]
    rw [← hw0]
    exact hwc.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hwlim
  have hdp : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < d t := hdpos.filter_mono nhdsWithin_le_nhds
  filter_upwards [hdp, self_mem_nhdsWithin] with t hdt ht
  have ht0 : 0 < t := ht
  have hdh : IsSelfAdjoint (((d t)⁻¹ : ℝ) : ℂ) :=
    (Complex.im_eq_zero_iff_isSelfAdjoint (((d t)⁻¹ : ℝ) : ℂ)).mp rfl
  have hth : IsSelfAdjoint (t : ℂ) :=
    (Complex.im_eq_zero_iff_isSelfAdjoint (t : ℂ)).mp rfl
  have hWherm : (W t).IsHermitian := (hA.isHermitian.add (hQ.smul hth)).smul hdh
  have hWtr : (W t).trace = 1 := by
    have he : A.trace + (t : ℂ) * Q.trace = (d t : ℂ) := by
      rw [htr, ← D5.S3.Quantum.Foundation.FiniteTraceDistance.re_trace_eq_trace hQ]
      simp [d]
    simp only [W, trace_smul, trace_add, smul_eq_mul]
    rw [he]
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ne_zero_of_re_pos hdt)
  refine ⟨⟨⟨hWherm, hWtr⟩, ?_⟩, ?_⟩
  · intro x hx
    change 0 ≤ hermForm (W t) x
    dsimp only [W]
    rw [qf_smul_real, hermForm_add, qf_smul_real]
    exact mul_nonneg (inv_nonneg.mpr hdt.le)
      (add_nonneg (hA.re_dotProduct_nonneg x) (mul_nonneg ht0.le (hpos x hx)))
  · intro hb
    have hp := hb.2 (WithLp.ofLp u) (by exact Nat.le_of_eq hr)
    change 0 ≤ hermForm (W t) (WithLp.ofLp u) at hp
    have hzero : hermForm A (WithLp.ofLp u) = 0 := by simp [hermForm, hAu]
    dsimp only [W] at hp
    rw [qf_smul_real, hermForm_add, qf_smul_real, hzero, hneg, zero_add] at hp
    have hn : (d t)⁻¹ * (t * (α - 1)) < 0 :=
      mul_neg_of_pos_of_neg (inv_pos.mpr hdt) (mul_neg_of_pos_of_neg ht0 (sub_neg.mpr hα1))
    linarith

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.Matrix Topology Filter
open scoped ComplexOrder
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
namespace D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

private theorem boundary_subspace_vector {m n k : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin m × Fin n))) (hE : E ≠ ⊤)
    (hb : OnBoundary m n k (rhoPerp E)) :
    ∃ v : EuclideanSpace ℂ (Fin m × Fin n), ‖v‖ = 1 ∧
      schmidtRank (WithLp.ofLp v) ≤ k ∧ v ∈ E := by
  obtain ⟨v, hv, hr, hker⟩ := boundary_kernel (rhoPerp E) (rhoPerp_psd E) hb
  exact ⟨v, hv, hr, (rhoPerp_kernel E hE v).mp hker⟩

private theorem closure_of_low_rank_kernel {m n j : ℕ} (A : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) (hA : A.PosSemidef)
    (htr : A.trace = 1) (v : EuclideanSpace ℂ (Fin m × Fin n))
    (hv : ‖v‖ = 1) (hr : schmidtRank (WithLp.ofLp v) ≤ j + 1)
    (hm : j < m) (hn : j < n) (hAv : A *ᵥ WithLp.ofLp v = 0) :
    A ∈ closure (BP m n j \ BP m n (j+1)) := by
  let d : EuclideanSpace ℂ (Fin m × Fin n) → ℝ :=
    fun u => (compress A (WithLp.ofLp u)).trace.re
  let F : EuclideanSpace ℂ (Fin m × Fin n) → (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
    fun u => (((d u)⁻¹ : ℝ) : ℂ) • compress A (WithLp.ofLp u)
  have hcomp : compress A (WithLp.ofLp v) = A := compress_at_kernel A hA.isHermitian _ hAv
  have hdv : d v = 1 := by
    dsimp only [d]
    rw [compress_trace A _ (unit_dot v hv), hAv]
    simp [htr]
  have hcc : Continuous (fun u : EuclideanSpace ℂ (Fin m × Fin n) =>
      compress A (WithLp.ofLp u)) :=
    (continuous_compress A).comp (PiLp.continuous_ofLp 2 (fun _ => ℂ))
  have hdc : Continuous d := by
    have ht : Continuous (fun B : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) => B.trace.re) := by
      unfold Matrix.trace
      fun_prop
    exact ht.comp hcc
  have hFv : F v = A := by simp [F, hdv, hcomp]
  have hFc : ContinuousAt F v := by
    unfold F
    exact (Complex.continuous_ofReal.continuousAt.comp
      (hdc.continuousAt.inv₀ (ne_zero_of_eq_one hdv))).smul
        hcc.continuousAt
  have hdpos : ∀ᶠ u in 𝓝 v, 0 < d u :=
    hdc.continuousAt.eventually (Ioi_mem_nhds (by rw [hdv]; norm_num))
  have hcl := unit_schmidtRank_density v hv (j := j+1) hr (Nat.zero_lt_succ j)
    (Order.add_one_le_iff.mpr hm) (Order.add_one_le_iff.mpr hn)
  have hfreq := (mem_closure_iff_frequently.mp hcl).and_eventually hdpos
  have htarget : ∃ᶠ u in 𝓝 v, F u ∈ closure (BP m n j \ BP m n (j+1)) := by
    apply hfreq.mono
    rintro u ⟨⟨hu, hur⟩, hdu⟩
    have hp := compress_psd A hA (WithLp.ofLp u)
    have hpsd : (F u).PosSemidef := by
      apply hp.smul
      exact_mod_cast inv_nonneg.mpr hdu.le
    have htrace : (F u).trace = 1 := by
      have he : (compress A (WithLp.ofLp u)).trace = (d u : ℂ) :=
        (D5.S3.Quantum.Foundation.FiniteTraceDistance.re_trace_eq_trace hp.isHermitian).symm
      simp only [F, trace_smul, smul_eq_mul, he]
      rw [Complex.ofReal_inv]
      exact inv_mul_cancel₀ (Complex.ne_zero_of_re_pos hdu)
    have hker : F u *ᵥ WithLp.ofLp u = 0 := by
      simp only [F, smul_mulVec, compress_kernel A _ (unit_dot u hu), smul_zero]
    exact kernel_state_in_closure (F u) hpsd htrace u hu hur hker
  rw [← hFv]
  exact isClosed_closure.mem_of_frequently_of_tendsto htarget hFc.tendsto

private theorem closure_locallyDistinguishable {m n : ℕ} (C D : Set ((Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ))) (x : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ))
    (hx : x ∈ closure (C \ D)) : LocallyDistinguishable C D x := by
  exact mem_closure_iff_nhds.mp hx

theorem result : claim := by
  intro m n E hE0 hEtop k j hk hkj hj hb
  have hp := rhoPerp_psd E
  obtain ⟨v, hv, hr, hmem⟩ := boundary_subspace_vector E hEtop hb
  have hker := (rhoPerp_kernel E hEtop v).mpr hmem
  apply closure_locallyDistinguishable
  exact closure_of_low_rank_kernel (rhoPerp E) hp hb.1.1.2 v hv (by omega)
    (lt_of_lt_of_le hj (min_le_left _ _)) (lt_of_lt_of_le hj (min_le_right _ _)) hker

end D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability

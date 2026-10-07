/- GID: D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate
   generality: G
   mirror-B: D5/B/S3/Quantum/BlockNorm/SpikeEdgeEstimate
   mirror-E: none(waiver:analytic-matrix-inequality)
   anchors: []
   utility: none
   digest: Quantitative two-sided spectral edges of a rank-one block spike. -/
/-
upper_shift_iff: proof_shape: bind-only; escape_witness: none; consumer: SpikeEdgeEstimate.rayleigh_le_max, EssentiallyHermitian.edge_symmetry
outer_action: proof_shape: bind-only; escape_witness: none; consumer: SpikeEdgeEstimate.A0_matrix, EssentiallyHermitian.projected_action, EssentiallyHermitian.trace_square_defect
outer_hermitian: proof_shape: bind-only; escape_witness: none; consumer: SpikeEdgeEstimate.spectral_spike_enclosure, SpikeEdgeEstimate.negative_bound, EssentiallyHermitian.edge_symmetry_forces_defect_zero, EssentiallyHermitian.zero_pairing_outer_equal, EssentiallyHermitian.trace_square_defect, EssentiallyHermitian.edge_symmetry_forces_pairing_zero, EssentiallyHermitian.completion_bound_projected_outer
positive_spike_enclosure: proof_shape: content; escape_witness: positive_spike_enclosure
edge_sum_bound: proof_shape: content; escape_witness: positive_spike_enclosure
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy.residual_driven_projective_energy
statement_id: sha256:14cb3ca6d58df854c287ff53463d4a6751e335edf7bc835267edc39f3a320419.
rank_spike_enclosure constructs r₁ = R e h (E e), r₂ = R e h (E r₁) and f = e + ε • r₁ + ε² • r₂.
The live constructed candidate has g = ε³ • E r₂, ⟪e,f⟫ = 1, ‖f - e‖ ≤ 2x and ‖g‖ ≤ x³,
where x = ε(3L), and (A0 + εE)f = f + ε² a2 • e + g.
These coupled estimates give |lam - (1 + ε² a2 + ε³ a3)| ≤ 891 L⁴ ε⁴.
Private declarations (name: shape [live consumer]; content witness follows =):
test_inner: bind-only [test_norm_ge]; test_norm_ge: bind-only [large_spike_enclosure]; test_dist: bind-only [rank_spike_enclosure].
test_equation: bind-only [rank_spike_enclosure]; normalize_norm: bind-only [rayleigh_control]; normalize_dist: bind-only [rayleigh_control].
normalize_rayleigh: bind-only [rayleigh_control]; polynomial_bounds: bind-only [rayleigh_error_tail]; rayleigh_error_tail: bind-only [rayleigh_control].
enclosure_scalar: bind-only [eigenvalue_enclosure]; eigenvalue_residual_upper: bind-only [eigenvalue_enclosure]; abs_inner_re_bound: bind-only [rayleigh_control].
rayleigh_control: bind-only [eigenvalue_enclosure]; escape_witness: none; complement_gap: bind-only [eigenvalue_enclosure]; eigenvalue_enclosure: bind-only [rank_spike_enclosure]; escape_witness: none.
R_apply: bind-only [R_orth]; A0_apply: bind-only [A0_e]; R_norm: bind-only [rank_spike_enclosure].
R_orth: bind-only [reduced_equation]; A0_e: bind-only [rank_spike_enclosure]; reduced_equation: bind-only [rank_spike_enclosure].
A0_quadratic: bind-only [A0_upper]; A0_upper: bind-only [rank_spike_enclosure]; R_symmetric: bind-only [coefficient2_real].
A0_symmetric: bind-only [rank_spike_enclosure]; coefficient2_real: bind-only [rank_spike_enclosure]; coefficient3_identity: bind-only [block_coefficient3].
rank_spike_enclosure: content [large_spike_enclosure]; escape_witness: constructed two-correction candidate f and residual g; coefficient2_formula: bind-only [block_coefficient2]; large_spike_enclosure: content=rank_spike_enclosure [spectral_spike_enclosure].
max_has_eigenvector: bind-only [spectral_spike_enclosure]; rayleigh_le_max: bind-only [spectral_spike_enclosure]; max_neg: bind-only [reflected_edge].
block_inner: bind-only [block_norm_sq]; block_norm_sq: bind-only [block_zero_norm]; block_zero_norm: bind-only [spectral_spike_enclosure].
block_orth: bind-only [spectral_spike_enclosure]; block_action: bind-only [A0_matrix]; A0_matrix: bind-only [decomposition].
decomposition: bind-only [spectral_spike_enclosure]; E_e: bind-only [mean_zero]; mean_zero: bind-only [spectral_spike_enclosure].
K_symmetric: bind-only [block_coefficient3]; r1_block: bind-only [block_coefficient3]; block_coefficient3: bind-only [positive_spike_enclosure].
reflected_edge: bind-only [star_reflected_edge]; star_reflected_edge: bind-only [negative_bound]; star_block_norm: bind-only [negative_bound].
adjoint_pairing: bind-only [paired_norm]; paired_norm: bind-only [positive_spike_enclosure]; spectral_spike_enclosure: content=rank_spike_enclosure [positive_spike_enclosure].
block_coefficient2: bind-only [positive_spike_enclosure]; negative_bound: content=positive_spike_enclosure [edge_sum_bound].
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Normalize
import D5.S3.Weil.GroundMode.ResidualDrivenProjectiveEnergy
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate
open Matrix InnerProductSpace
noncomputable def edgeMax {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) : ℝ := sSup (spectrum ℝ K)
noncomputable def edgeMin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) : ℝ := sInf (spectrum ℝ K)
def K {ι : Type*} [Fintype ι] [DecidableEq ι] (X D : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks D X Xᴴ (-D)
section
theorem upper_shift_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (c : ℝ) :
    (c • 1 - K).PosSemidef ↔ ∀ x ∈ spectrum ℝ K, x ≤ c := by
  have h := le_algebraMap_iff_spectrum_le (r := c)
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hK)
  rwa [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
end
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
private def test (e r₁ r₂ : H) (ε : ℝ) : H :=
  e + (ε : ℂ) • r₁ + ((ε^2 : ℝ) : ℂ) • r₂
private theorem test_inner (e r₁ r₂ : H) (ε : ℝ) (he : ‖e‖ = 1)
    (h₁ : ⟪e,r₁⟫_ℂ = 0) (h₂ : ⟪e,r₂⟫_ℂ = 0) :
    ⟪e,test e r₁ r₂ ε⟫_ℂ = 1 := by
  simp only [test, inner_add_right, inner_smul_right, h₁, h₂,
    inner_self_eq_norm_sq_to_K, he, Complex.ofReal_one, one_pow, mul_zero, add_zero]
  norm_num
private theorem test_norm_ge (e r₁ r₂ : H) (ε : ℝ) (he : ‖e‖ = 1)
    (h₁ : ⟪e,r₁⟫_ℂ = 0) (h₂ : ⟪e,r₂⟫_ℂ = 0) :
    1 ≤ ‖test e r₁ r₂ ε‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) e (test e r₁ r₂ ε)
  rw [test_inner e r₁ r₂ ε he h₁ h₂, norm_one, he, one_mul] at h
  exact h
private theorem test_dist (e r₁ r₂ : H) (ε L : ℝ) (hε : 0 ≤ ε)
    (hL : 0 ≤ L) (h₁ : ‖r₁‖ ≤ L) (h₂ : ‖r₂‖ ≤ L^2) :
    ‖test e r₁ r₂ ε-e‖ ≤ ε*L+(ε*L)^2 := by
  have heq : test e r₁ r₂ ε-e =
      (ε : ℂ) • r₁ + ((ε^2 : ℝ) : ℂ) • r₂ := by dsimp [test]; module
  rw [heq]
  calc
    _ ≤ ‖(ε : ℂ) • r₁‖ + ‖((ε^2 : ℝ) : ℂ) • r₂‖ := norm_add_le _ _
    _ = ε*‖r₁‖+ε^2*‖r₂‖ := by
      simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε,
        abs_of_nonneg (sq_nonneg ε)]
    _ ≤ ε*L+ε^2*L^2 := by gcongr
    _ = _ := by ring
private theorem test_equation (A E : H →ₗ[ℂ] H) (e r₁ r₂ : H) (ε a₂ : ℝ)
    (he : A e=e) (h₁ : A r₁+E e=r₁)
    (h₂ : A r₂+E r₁=r₂+(a₂ : ℂ) • e) :
    (A+(ε : ℂ) • E) (test e r₁ r₂ ε)=
      test e r₁ r₂ ε+((ε^2*a₂ : ℝ) : ℂ) • e+
        ((ε^3 : ℝ) : ℂ) • E r₂ := by
  simp only [test, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul]
  have h₁' : A r₁=r₁-E e := by exact eq_sub_iff_add_eq.mpr h₁
  have h₂' : A r₂=r₂+(a₂ : ℂ) • e-E r₁ := by exact eq_sub_iff_add_eq.mpr h₂
  rw [he,h₁',h₂']
  push_cast
  module
private theorem normalize_norm (f : H) (hf : 1 ≤ ‖f‖) : ‖NormedSpace.normalize f‖=1 := by
  have hn : ‖f‖ ≠ 0 := by linarith
  simp [NormedSpace.normalize,RCLike.real_smul_eq_coe_smul (K := ℂ), norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg f)), hn]
private theorem normalize_dist (f e : H) (he : ‖e‖=1) (hf : 1 ≤ ‖f‖) :
    ‖NormedSpace.normalize f-e‖ ≤ 2*‖f-e‖ := by
  have hn : 0 < ‖f‖ := by linarith
  have hi : ‖f‖⁻¹ ≤ 1 := (inv_le_one₀ hn).mpr hf
  have hid : NormedSpace.normalize f-f = (((‖f‖⁻¹-1 : ℝ) : ℂ)) • f := by
    dsimp [NormedSpace.normalize,RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    module
  have hd : ‖NormedSpace.normalize f-f‖=‖f‖-1 := by
    rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : ‖f‖⁻¹-1 ≤ 0)]
    field_simp
    ring
  have hb := norm_sub_norm_le f e
  rw [he] at hb
  calc
    ‖NormedSpace.normalize f-e‖ ≤ ‖NormedSpace.normalize f-f‖+‖f-e‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*‖f-e‖ := by rw [hd]; linarith
private theorem normalize_rayleigh (T : H →ₗ[ℂ] H) (f : H) :
    (⟪NormedSpace.normalize f,T (NormedSpace.normalize f)⟫_ℂ).re = (⟪f,T f⟫_ℂ).re/‖f‖^2 := by
  change (⟪((‖f‖⁻¹ : ℝ) : ℂ) • f,T (((‖f‖⁻¹ : ℝ) : ℂ) • f)⟫_ℂ).re = _
  simp only [map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, neg_zero, zero_mul, mul_zero, sub_zero]
  field_simp
end
section
private theorem polynomial_bounds (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1/32) :
    x^3 ≤ x^2 ∧ x^5 ≤ x^4 ∧ (x+x^2)^2 ≤ 4*x^2 ∧
    x^3+10*x^4 ≤ x^2 ∧ 16*x^2+x ≤ 1/4 ∧
    128*x^6 ≤ x^4 := by
  have hxx : x^2 ≤ x/32 := by nlinarith
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have hx3 : 0 ≤ x^3 := by positivity
  have hx4 : 0 ≤ x^4 := by positivity
  have hb : x^2 ≤ (1/32:ℝ)^2 := by gcongr
  have h3 : x^3 ≤ x^2/32 := by nlinarith [mul_le_mul_of_nonneg_left hx1 hx2]
  have h4 : x^4 ≤ x^2/1024 := by nlinarith [mul_le_mul_of_nonneg_left hb hx2]
  have h5 : x^5 ≤ x^4/32 := by nlinarith [mul_le_mul_of_nonneg_left hx1 hx4]
  have h6 : x^6 ≤ x^4/1024 := by nlinarith [mul_le_mul_of_nonneg_left hb hx4]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · nlinarith
  · nlinarith
private theorem rayleigh_error_tail (x N q b₂ b₃ c : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1/32) (hN : 1 ≤ N) (hN1 : N-1 ≤ 4*x^2)
    (hb₂ : |b₂| ≤ x^2) (hb₃ : |b₃| ≤ x^3)
    (hc : |c| ≤ 2*x^4) (hq : q=(N+b₂+b₃+c)/N) :
    |q-(1+b₂+b₃)| ≤ 10*x^4 := by
  have hN0 : N ≠ 0 := by linarith
  have hid : (q-(1+b₂+b₃))*N=c-(b₂+b₃)*(N-1) := by rw [hq]; field_simp; ring
  have hp := polynomial_bounds x hx hx1
  have hab : |b₂+b₃| ≤ 2*x^2 := (abs_add_le _ _).trans (by linarith)
  have hNb : |N-1| ≤ 4*x^2 := by rw [abs_of_nonneg (by linarith)]; exact hN1
  have hprod : |(b₂+b₃)*(N-1)| ≤ 8*x^4 := by
    rw [abs_mul]
    calc
      _ ≤ (2*x^2)*(4*x^2) := mul_le_mul hab hNb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hh : |(q-(1+b₂+b₃))*N| ≤ 10*x^4 := by
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ N)] at hh
  have hm := mul_le_mul_of_nonneg_left hN (abs_nonneg (q-(1+b₂+b₃)))
  nlinarith
private theorem enclosure_scalar (x q d lam app rho : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1/32)
    (hq : 1-2*x^2 ≤ q) (hd : d ≤ 16*x^2+x)
    (herr : |q-app| ≤ 10*x^4) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 8*x^3)
    (hlower : q ≤ lam) (hupper : lam ≤ q+rho^2/(q-d)) :
    |lam-app| ≤ 11*x^4 := by
  have hp := polynomial_bounds x hx hx1
  have hx2 : x^2 ≤ (1/32:ℝ)^2 := by gcongr
  have hg : 1/2 ≤ q-d := by nlinarith
  have hquot : rho^2/(q-d) ≤ x^4 := by
    apply (div_le_iff₀ (by linarith : 0 < q-d)).mpr
    have hr2 : rho^2 ≤ 64*x^6 := by nlinarith [sq_nonneg (8*x^3-rho)]
    have hm := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ x^4)
    nlinarith
  have he := abs_le.mp herr
  apply abs_le.mpr
  constructor <;> linarith
end
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
private theorem eigenvalue_residual_upper (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (k u : H) (q d lam : ℝ) (hk : ‖k‖ = 1) (hu : u ≠ 0)
    (hq : (⟪k,T k⟫_ℂ).re = q) (hTu : T u = (lam : ℂ) • u)
    (hlam : q ≤ lam) (hgap : d < q)
    (hcomp : ∀ f : H, ⟪k,f⟫_ℂ = 0 → (⟪f,T f⟫_ℂ).re ≤ d*‖f‖^2) :
    lam ≤ q + ‖T k-(q : ℂ) • k‖^2/(q-d) := by
  let M : H →ₗ[ℂ] H := (q : ℂ) • LinearMap.id - T
  let g : ℝ := q-d
  let r : H := T k-(q : ℂ) • k
  let E : ℝ := ‖r‖^2/g
  have hg : 0 < g := sub_pos.mpr hgap
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hM : M.IsSymmetric :=
    (LinearMap.IsSymmetric.id.smul (by simp : star (q : ℂ) = (q : ℂ))).sub hT
  have hMapply (v : H) : M v = (q : ℂ) • v-T v := rfl
  have he : M u = ((q-lam : ℝ) : ℂ) • u := by
    rw [hMapply,hTu]
    push_cast
    module
  have hMk : (⟪k,M k⟫_ℂ).re = 0 := by
    rw [hMapply,inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hk]
    norm_num [hq]
  have hMkvec : M k = -r := by rw [hMapply]; dsimp [r]; module
  have hco : ∀ f : H, ⟪k,f⟫_ℂ = 0 → g*‖f‖^2 ≤ (⟪f,M f⟫_ℂ).re := by
    intro f hf
    have hc := hcomp f hf
    rw [hMapply,inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re, ← Complex.ofReal_pow]
    dsimp [g]
    linarith
  have hres : ∀ f : H, ⟪k,f⟫_ℂ = 0 →
      ‖⟪f,M k - ((⟪k,M k⟫_ℂ).re : ℂ) • k⟫_ℂ‖^2 ≤ E*(⟪f,M f⟫_ℂ).re := by
    intro f hf
    rw [hMk, Complex.ofReal_zero, zero_smul, sub_zero, hMkvec, inner_neg_right, norm_neg]
    have hi := norm_inner_le_norm (𝕜 := ℂ) f r
    have hisq : ‖⟪f,r⟫_ℂ‖^2 ≤ ‖f‖^2*‖r‖^2 := by
      nlinarith [norm_nonneg f,norm_nonneg r,norm_nonneg ⟪f,r⟫_ℂ]
    have hc := hco f hf
    have hm := mul_le_mul_of_nonneg_left hc hE
    have heq : E*(g*‖f‖^2) = ‖f‖^2*‖r‖^2 := by dsimp [E]; field_simp
    rw [heq] at hm
    exact hisq.trans hm
  have hb := D5.S3.Weil.GroundMode.ResidualDrivenProjectiveEnergy.residual_driven_projective_energy
    LinearMap.id M k u (q-lam) g E hk hu he (by linarith) hg hE hco hres
  let alpha : ℂ := ⟪k,u⟫_ℂ
  let w : H := alpha⁻¹ • u-k
  change alpha ≠ 0 ∧ ⟪k,w⟫_ℂ=0 ∧ _ at hb
  obtain ⟨ha,ho,hwn,hwE,hwNorm⟩ := hb
  have hkw : ⟪k,k+w⟫_ℂ = 1 := by
    rw [inner_add_right,ho,inner_self_eq_norm_sq_to_K,hk]
    norm_num
  have hact : M (k+w) = ((q-lam : ℝ) : ℂ) • (k+w) := by
    have hw : k+w = alpha⁻¹ • u := by dsimp [w]; module
    rw [hw,map_smul,he]
    module
  have hpair : (⟪k,M w⟫_ℂ).re = q-lam := by
    have hi := congrArg (fun v => (⟪k,v⟫_ℂ).re) hact
    rw [map_add,inner_add_right,inner_smul_right,hkw] at hi
    simp only [Complex.add_re, mul_one, Complex.ofReal_re,hMk] at hi
    linarith
  have hinner : (⟪w,r⟫_ℂ).re = lam-q := by
    have hi := hM k w
    rw [hMkvec,inner_neg_left] at hi
    have hr := congrArg Complex.re hi
    simp only [Complex.neg_re] at hr
    have hsym : (⟪r,w⟫_ℂ).re = (⟪w,r⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) r w
    linarith [hpair,hsym]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) w r
  have hre := Complex.abs_re_le_norm ⟪w,r⟫_ℂ
  rw [hinner] at hre
  rw [abs_of_nonneg (by linarith : 0 ≤ lam-q)] at hre
  have hsq : (lam-q)^2 ≤ ‖w‖^2*‖r‖^2 := by
    nlinarith [norm_nonneg w,norm_nonneg r,norm_nonneg ⟪w,r⟫_ℂ]
  change ‖w‖^2 ≤ E/g at hwNorm
  have hmul := mul_le_mul_of_nonneg_right hwNorm (sq_nonneg ‖r‖)
  have heq : (E/g)*‖r‖^2 = E^2 := by dsimp [E]; field_simp
  rw [heq] at hmul
  have hle : lam-q ≤ E := by nlinarith
  change lam ≤ q+E
  linarith
end
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
private theorem abs_inner_re_bound (z w : H) : |(⟪z,w⟫_ℂ).re| ≤ ‖z‖*‖w‖ :=
  (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
private theorem rayleigh_control (T : H →ₗ[ℂ] H) (e f g : H) (x b₂ b₃ : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1/32) (he : ‖e‖=1)
    (hef : ⟪e,f⟫_ℂ=1) (hdist : ‖f-e‖ ≤ 2*x) (hg : ‖g‖ ≤ x^3)
    (hb₂ : |b₂| ≤ x^2) (hb₃ : |b₃| ≤ x^3)
    (hact : T f=f+(b₂ : ℂ) • e+g) (heg : (⟪e,g⟫_ℂ).re=b₃) :
    let k := NormedSpace.normalize f
    let q := (⟪k,T k⟫_ℂ).re
    ‖k‖=1 ∧ ‖k-e‖ ≤ 4*x ∧
      |q-(1+b₂+b₃)| ≤ 10*x^4 ∧ 1-2*x^2 ≤ q ∧
      ‖T k-(q : ℂ) • k‖ ≤ 8*x^3 := by
  dsimp only
  let k := NormedSpace.normalize f
  let q := (⟪k,T k⟫_ℂ).re
  have hfn : 1 ≤ ‖f‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℂ) e f
    simpa [hef,he] using hh
  have hk : ‖k‖=1 := normalize_norm f hfn
  have hke : ‖k-e‖ ≤ 4*x := (normalize_dist f e he hfn).trans (by linarith)
  have hfe : ⟪f,e⟫_ℂ=1 := by rw [← inner_conj_symm,hef]; simp
  have horth : ⟪e,f-e⟫_ℂ=0 := by
    rw [inner_sub_right,hef,inner_self_eq_norm_sq_to_K,he]
    norm_num
  have hN : ‖f‖^2=1+‖f-e‖^2 := by
    have hh := norm_add_sq (𝕜 := ℂ) e (f-e)
    rw [horth,he] at hh
    norm_num at hh
    exact hh
  have hN1 : ‖f‖^2-1 ≤ 4*x^2 := by nlinarith [norm_nonneg (f-e)]
  have hfg : (⟪f,g⟫_ℂ).re=b₃+(⟪f-e,g⟫_ℂ).re := by
    have hh : f=e+(f-e) := by module
    conv_lhs => rw [hh]
    rw [inner_add_left,Complex.add_re,heg]
  have hnum : (⟪f,T f⟫_ℂ).re=‖f‖^2+b₂+b₃+(⟪f-e,g⟫_ℂ).re := by
    rw [hact,inner_add_right,inner_add_right,Complex.add_re,Complex.add_re,
      show (⟪f,f⟫_ℂ).re=‖f‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) f,
      inner_smul_right,hfe,mul_one,Complex.ofReal_re,hfg]
    ring
  have htail : |(⟪f-e,g⟫_ℂ).re| ≤ 2*x^4 := by
    calc
      _ ≤ ‖f-e‖*‖g‖ := abs_inner_re_bound _ _
      _ ≤ (2*x)*x^3 := mul_le_mul hdist hg (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hq : q=(‖f‖^2+b₂+b₃+(⟪f-e,g⟫_ℂ).re)/‖f‖^2 := by
    dsimp [q,k]
    rw [normalize_rayleigh,hnum]
  have herr := rayleigh_error_tail x (‖f‖^2) q b₂ b₃ (⟪f-e,g⟫_ℂ).re
    hx hx1 (by nlinarith) hN1 hb₂ hb₃ htail hq
  have hp := polynomial_bounds x hx hx1
  have hqlo : 1-2*x^2 ≤ q := by
    have ha := abs_le.mp hb₂
    have hb := abs_le.mp hb₃
    have hc := abs_le.mp herr
    linarith
  have hfn2 : ‖f‖ ≤ 2 := by
    have hh := norm_sub_norm_le f e
    rw [he] at hh
    linarith
  have hresf : ‖T f-((1+b₂+b₃ : ℝ) : ℂ) • f‖ ≤ 5*x^3 := by
    have hid : T f-((1+b₂+b₃ : ℝ) : ℂ) • f =
        (b₂ : ℂ) • (e-f)+g-(b₃ : ℂ) • f := by rw [hact]; push_cast; module
    rw [hid]
    calc
      _ ≤ ‖(b₂ : ℂ) • (e-f)+g‖+‖(b₃ : ℂ) • f‖ := norm_sub_le _ _
      _ ≤ ‖(b₂ : ℂ) • (e-f)‖+‖g‖+‖(b₃ : ℂ) • f‖ := by gcongr; exact norm_add_le _ _
      _ = |b₂| *‖f-e‖+‖g‖+|b₃| *‖f‖ := by
        simp [norm_smul,Complex.norm_real,Real.norm_eq_abs,norm_sub_rev]
      _ ≤ x^2*(2*x)+x^3+x^3*2 := by gcongr
      _ = _ := by ring
  have hresk : ‖T k-((1+b₂+b₃ : ℝ) : ℂ) • k‖ ≤ 5*x^3 := by
    have hid : T k-((1+b₂+b₃ : ℝ) : ℂ) • k =
        ((‖f‖⁻¹ : ℝ) : ℂ) • (T f-((1+b₂+b₃ : ℝ) : ℂ) • f) := by
      simp only [k,NormedSpace.normalize,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]
      module
    rw [hid,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_right ((inv_le_one₀ (by linarith)).mpr hfn)
      (norm_nonneg _)).trans (by simpa using hresf)
  have hr : ‖T k-(q : ℂ) • k‖ ≤ 8*x^3 := by
    have hid : T k-(q : ℂ) • k =
        T k-((1+b₂+b₃ : ℝ) : ℂ) • k+((1+b₂+b₃-q : ℝ) : ℂ) • k := by
      push_cast
      module
    rw [hid]
    calc
      _ ≤ ‖T k-((1+b₂+b₃ : ℝ) : ℂ) • k‖+‖((1+b₂+b₃-q : ℝ) : ℂ) • k‖ := norm_add_le _ _
      _ = ‖T k-((1+b₂+b₃ : ℝ) : ℂ) • k‖+|q-(1+b₂+b₃)| := by
        simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,hk,mul_one,abs_sub_comm]
      _ ≤ 5*x^3+10*x^4 := add_le_add hresk herr
      _ ≤ 8*x^3 := by
        have hh := mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ x^3)
        nlinarith
  exact ⟨hk,hke,herr,hqlo,hr⟩
private theorem complement_gap (A E : H →ₗ[ℂ] H) (e k : H) (ε L x : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hx : x=ε*L)
    (hclose : ‖k-e‖ ≤ 4*x)
    (hA : ∀ z : H, (⟪z,A z⟫_ℂ).re ≤ ‖⟪e,z⟫_ℂ‖^2)
    (hE : ∀ z : H, ‖E z‖ ≤ L*‖z‖) :
    ∀ z : H, ⟪k,z⟫_ℂ=0 →
      (⟪z,(A+(ε : ℂ) • E) z⟫_ℂ).re ≤ (16*x^2+x)*‖z‖^2 := by
  intro z hz
  have hi : ⟪e,z⟫_ℂ=⟪e-k,z⟫_ℂ := by rw [inner_sub_left,hz,sub_zero]
  have hn : ‖⟪e,z⟫_ℂ‖ ≤ 4*x*‖z‖ := by
    rw [hi]
    exact (norm_inner_le_norm _ _).trans (by
      rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  have hsq : ‖⟪e,z⟫_ℂ‖^2 ≤ 16*x^2*‖z‖^2 := by
    have hxn : 0 ≤ x := by rw [hx]; positivity
    nlinarith [norm_nonneg ⟪e,z⟫_ℂ,norm_nonneg z]
  have hEq : (⟪z,E z⟫_ℂ).re ≤ L*‖z‖^2 := by
    calc
      _ ≤ |(⟪z,E z⟫_ℂ).re| := le_abs_self _
      _ ≤ ‖z‖*‖E z‖ := abs_inner_re_bound _ _
      _ ≤ ‖z‖*(L*‖z‖) := mul_le_mul_of_nonneg_left (hE z) (norm_nonneg _)
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hEq hε
  simp only [LinearMap.add_apply, LinearMap.smul_apply,inner_add_right,inner_smul_right,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  rw [hx] at hsq ⊢
  nlinarith [hA z]
private theorem eigenvalue_enclosure (A E : H →ₗ[ℂ] H) (e f g u : H)
    (ε L x b₂ b₃ lam : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1/32) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hxε : x=ε*L) (he : ‖e‖=1) (hef : ⟪e,f⟫_ℂ=1)
    (hdist : ‖f-e‖ ≤ 2*x) (hg : ‖g‖ ≤ x^3)
    (hb₂ : |b₂| ≤ x^2) (hb₃ : |b₃| ≤ x^3)
    (hact : (A+(ε : ℂ) • E) f=f+(b₂ : ℂ) • e+g)
    (heg : (⟪e,g⟫_ℂ).re=b₃)
    (hA : ∀ z : H, (⟪z,A z⟫_ℂ).re ≤ ‖⟪e,z⟫_ℂ‖^2)
    (hE : ∀ z : H, ‖E z‖ ≤ L*‖z‖)
    (hT : (A+(ε : ℂ) • E).IsSymmetric) (hu : u ≠ 0)
    (heigen : (A+(ε : ℂ) • E) u=(lam : ℂ) • u)
    (hrayleigh : (⟪NormedSpace.normalize f,(A+(ε : ℂ) • E) (NormedSpace.normalize f)⟫_ℂ).re ≤ lam) :
    |lam-(1+b₂+b₃)| ≤ 11*x^4 := by
  let T := A+(ε : ℂ) • E
  let k := NormedSpace.normalize f
  let q := (⟪k,T k⟫_ℂ).re
  let d := 16*x^2+x
  obtain ⟨hk,hclose,herr,hqlo,hres⟩ := rayleigh_control T e f g x b₂ b₃
    hx hx1 he hef hdist hg hb₂ hb₃ hact heg
  have hcomp := complement_gap A E e k ε L x hε hL hxε hclose hA hE
  have hx2 : x^2 ≤ (1/32:ℝ)^2 := by gcongr
  have hd := (polynomial_bounds x hx hx1).2.2.2.2.1
  have hgap : d < q := by dsimp [d,q,T,k]; dsimp [T] at hqlo; nlinarith
  have hupp := eigenvalue_residual_upper T hT k u q d lam hk hu rfl
    heigen hrayleigh hgap hcomp
  exact enclosure_scalar x q d lam (1+b₂+b₃) ‖T k-(q : ℂ) • k‖ hx hx1 hqlo
    (le_refl _) herr (norm_nonneg _) hres hrayleigh hupp
end
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
private def A0 (e h : H) : H →L[ℂ] H := rankOne ℂ e e-rankOne ℂ h h
private def R (e h : H) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H-rankOne ℂ e e-(1/2 : ℂ) • rankOne ℂ h h
private theorem R_apply (e h z : H) :
    R e h z=z-⟪e,z⟫_ℂ • e-((1/2 : ℂ)*⟪h,z⟫_ℂ) • h := by
  simp only [R,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply,rankOne_apply,smul_smul]
private theorem A0_apply (e h z : H) : A0 e h z=⟪e,z⟫_ℂ • e-⟪h,z⟫_ℂ • h := by
  simp [A0]
private theorem R_norm (e h : H) (he : ‖e‖=1) (hh : ‖h‖=1) : ‖R e h‖ ≤ 3 := by
  calc
    _ ≤ ‖ContinuousLinearMap.id ℂ H-rankOne ℂ e e‖+‖(1/2 : ℂ) • rankOne ℂ h h‖ := norm_sub_le _ _
    _ ≤ (‖ContinuousLinearMap.id ℂ H‖+‖rankOne ℂ e e‖)+‖(1/2 : ℂ) • rankOne ℂ h h‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ 3 := by
      simp only [norm_smul,norm_rankOne,he,hh,one_mul,mul_one]
      norm_num
      have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := H)
      linarith
private theorem R_orth (e h z : H) (he : ‖e‖=1) (heh : ⟪e,h⟫_ℂ=0) : ⟪e,R e h z⟫_ℂ=0 := by
  rw [R_apply]
  simp only [inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,
    he,heh,mul_zero]
  norm_num
private theorem A0_e (e h : H) (he : ‖e‖=1) (heh : ⟪e,h⟫_ℂ=0) : A0 e h e=e := by
  have hhe : ⟪h,e⟫_ℂ=0 := by rw [← inner_conj_symm,heh]; simp
  rw [A0_apply]
  simp [hhe,inner_self_eq_norm_sq_to_K,he]
private theorem reduced_equation (e h z : H) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : ⟪e,h⟫_ℂ=0) :
    A0 e h (R e h z)+z=R e h z+⟪e,z⟫_ℂ • e := by
  have hhe : ⟪h,e⟫_ℂ=0 := by rw [← inner_conj_symm,heh]; simp
  rw [A0_apply,R_orth e h z he heh,R_apply]
  simp only [inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hh,hhe,
    mul_zero,sub_zero,zero_smul]
  norm_num
  module
private theorem A0_quadratic (e h z : H) :
    (⟪z,A0 e h z⟫_ℂ).re=‖⟪e,z⟫_ℂ‖^2-‖⟪h,z⟫_ℂ‖^2 := by
  rw [A0_apply,inner_sub_right,inner_smul_right,inner_smul_right]
  rw [← inner_conj_symm z e,← inner_conj_symm z h]
  simp only [Complex.mul_conj,Complex.sub_re,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
private theorem A0_upper (e h z : H) : (⟪z,A0 e h z⟫_ℂ).re ≤ ‖⟪e,z⟫_ℂ‖^2 := by
  rw [A0_quadratic]
  nlinarith
private theorem R_symmetric (e h : H) : (R e h : H →ₗ[ℂ] H).IsSymmetric :=
  (LinearMap.IsSymmetric.id.sub (isSymmetric_rankOne_self e)).sub
    ((isSymmetric_rankOne_self h).smul (by norm_num : star (1/2 : ℂ)=(1/2 : ℂ)))
private theorem A0_symmetric (e h : H) : (A0 e h : H →ₗ[ℂ] H).IsSymmetric :=
  (isSymmetric_rankOne_self e).sub (isSymmetric_rankOne_self h)
private def r1 (E : H →L[ℂ] H) (e h : H) : H := R e h (E e)
private def r2 (E : H →L[ℂ] H) (e h : H) : H := R e h (E (r1 E e h))
private def a2 (E : H →L[ℂ] H) (e h : H) : ℝ := (⟪e,E (r1 E e h)⟫_ℂ).re
private def a3 (E : H →L[ℂ] H) (e h : H) : ℝ := (⟪e,E (r2 E e h)⟫_ℂ).re
private theorem coefficient2_real (E : H →L[ℂ] H) (e h : H)
    (hE : (E : H →ₗ[ℂ] H).IsSymmetric) :
    ((a2 E e h : ℝ) : ℂ)=⟪e,E (r1 E e h)⟫_ℂ := by
  have hs : ((E : H →ₗ[ℂ] H).comp
      ((R e h : H →ₗ[ℂ] H).comp (E : H →ₗ[ℂ] H))).IsSymmetric := by
    intro z w
    simp only [LinearMap.comp_apply]
    rw [← hE,← R_symmetric e h, hE]
  exact hs.coe_re_inner_self_apply e
private theorem coefficient3_identity (E : H →L[ℂ] H) (e h : H)
    (hE : (E : H →ₗ[ℂ] H).IsSymmetric) :
    a3 E e h=(⟪r1 E e h,E (r1 E e h)⟫_ℂ).re := by
  dsimp only [a3,r2]
  have hs₁ := (hE e (R e h (E (r1 E e h)))).symm
  have hs₂ := ((R_symmetric e h) (E e) (E (r1 E e h))).symm
  exact congrArg Complex.re (hs₁.trans hs₂)
private theorem rank_spike_enclosure (E : H →L[ℂ] H) (e h u : H) (ε L lam : ℝ)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : ⟪e,h⟫_ℂ=0)
    (hE : (E : H →ₗ[ℂ] H).IsSymmetric) (hmean : ⟪e,E e⟫_ℂ=0)
    (hL : 1 ≤ L) (hEn : ‖E‖ ≤ L) (hε : 0 ≤ ε) (hsmall : ε*(3*L) ≤ 1/32)
    (hu : u ≠ 0) (heigen : (A0 e h+(ε : ℂ) • E) u=(lam : ℂ) • u)
    (hrayleigh : (⟪NormedSpace.normalize (test e (r1 E e h) (r2 E e h) ε),
      (A0 e h+(ε : ℂ) • E) (NormedSpace.normalize (test e (r1 E e h) (r2 E e h) ε))⟫_ℂ).re ≤ lam) :
    |lam-(1+ε^2*a2 E e h+ε^3*a3 E e h)| ≤ 891*L^4*ε^4 := by
  let r₁ := r1 E e h
  let r₂ := r2 E e h
  let M := 3*L
  let x := ε*M
  let f := test e r₁ r₂ ε
  let g := ((ε^3 : ℝ) : ℂ) • E r₂
  have hL0 : 0 ≤ L := by linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hEb (z : H) : ‖E z‖ ≤ L*‖z‖ := (E.le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hEn (norm_nonneg z))
  have hn1 : ‖r₁‖ ≤ M := by
    calc
      _ ≤ ‖R e h‖*‖E e‖ := (R e h).le_opNorm _
      _ ≤ 3*(L*1) := by
        gcongr
        · exact R_norm e h he hh
        · simpa [he] using hEb e
      _ = M := by dsimp [M]; ring
  have hEr1 : ‖E r₁‖ ≤ L*M := (hEb r₁).trans (mul_le_mul_of_nonneg_left hn1 hL0)
  have hn2 : ‖r₂‖ ≤ M^2 := by
    calc
      _ ≤ ‖R e h‖*‖E r₁‖ := (R e h).le_opNorm _
      _ ≤ 3*(L*M) := by
        gcongr
        · exact R_norm e h he hh
      _ ≤ M^2 := by dsimp [M]; nlinarith [sq_nonneg L]
  have hEr2 : ‖E r₂‖ ≤ L*M^2 := (hEb r₂).trans (mul_le_mul_of_nonneg_left hn2 hL0)
  have ho1 : ⟪e,r₁⟫_ℂ=0 := R_orth e h (E e) he heh
  have ho2 : ⟪e,r₂⟫_ℂ=0 := R_orth e h (E r₁) he heh
  have ha2 : |a2 E e h| ≤ M^2 := by
    calc
      _ ≤ ‖e‖*‖E r₁‖ := abs_inner_re_bound _ _
      _ ≤ 1*(L*M) := by simpa only [he,one_mul] using hEr1
      _ ≤ M^2 := by dsimp [M]; nlinarith [sq_nonneg L]
  have ha3 : |a3 E e h| ≤ M^3 := by
    calc
      _ ≤ ‖e‖*‖E r₂‖ := abs_inner_re_bound _ _
      _ ≤ 1*(L*M^2) := by simpa only [he,one_mul] using hEr2
      _ ≤ M^3 := by dsimp [M]; nlinarith [show 0 ≤ L^3 by positivity]
  have hdist : ‖f-e‖ ≤ 2*x := by
    have hd := test_dist e r₁ r₂ ε M hε hM hn1 hn2
    have hp := polynomial_bounds x hx0 hsmall
    change ‖f-e‖ ≤ x+x^2 at hd
    have hxx : x^2 ≤ x := by nlinarith
    linarith
  have hg : ‖g‖ ≤ x^3 := by
    dsimp only [g]
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ε^3)]
    calc
      _ ≤ ε^3*(L*M^2) := mul_le_mul_of_nonneg_left hEr2 (by positivity)
      _ ≤ x^3 := by dsimp [x,M]; nlinarith [show 0 ≤ ε^3*L^3 by positivity]
  have hb2 : |ε^2*a2 E e h| ≤ x^2 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg ε)]
    calc
      _ ≤ ε^2*M^2 := mul_le_mul_of_nonneg_left ha2 (sq_nonneg _)
      _ = x^2 := by dsimp [x]; ring
  have hb3 : |ε^3*a3 E e h| ≤ x^3 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ ε^3)]
    calc
      _ ≤ ε^3*M^3 := mul_le_mul_of_nonneg_left ha3 (by positivity)
      _ = x^3 := by dsimp [x]; ring
  have heq1 : A0 e h r₁+E e=r₁ := by
    have ht := reduced_equation e h (E e) he hh heh
    simpa [r₁,r1,hmean] using ht
  have heq2 : A0 e h r₂+E r₁=r₂+(a2 E e h : ℂ) • e := by
    have ht := reduced_equation e h (E r₁) he hh heh
    rw [← coefficient2_real E e h hE] at ht
    exact ht
  have hact : (A0 e h+(ε : ℂ) • E) f=f+((ε^2*a2 E e h : ℝ) : ℂ) • e+g :=
    test_equation (A0 e h) E e r₁ r₂ ε (a2 E e h) (A0_e e h he heh) heq1 heq2
  have hge : (⟪e,g⟫_ℂ).re=ε^3*a3 E e h := by
    dsimp only [g,a3]
    simp only [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  have hs : ((A0 e h+(ε : ℂ) • E : H →L[ℂ] H) : H →ₗ[ℂ] H).IsSymmetric :=
    (A0_symmetric e h).add (hE.smul (by simp : star (ε : ℂ)=(ε : ℂ)))
  have hb := eigenvalue_enclosure (A0 e h) E e f g u ε M x (ε^2*a2 E e h)
    (ε^3*a3 E e h) lam hx0 hsmall hε hM rfl he
    (test_inner e r₁ r₂ ε he ho1 ho2) hdist hg hb2 hb3 hact hge
    (A0_upper e h) (fun z => (E.le_opNorm z).trans (by dsimp [M]; nlinarith [norm_nonneg z]))
    hs hu heigen hrayleigh
  calc
    _ ≤ 11*x^4 := hb
    _ = 891*L^4*ε^4 := by dsimp [x,M]; ring
private theorem coefficient2_formula (E : H →L[ℂ] H) (e h : H)
    (hE : (E : H →ₗ[ℂ] H).IsSymmetric) (hmean : ⟪e,E e⟫_ℂ=0) :
    a2 E e h=‖E e‖^2-(1/2:ℝ)*‖⟪h,E e⟫_ℂ‖^2 := by
  have heq := (hE e (R e h (E e))).symm
  change ⟪e,E (R e h (E e))⟫_ℂ=⟪E e,R e h (E e)⟫_ℂ at heq
  change (⟪e,E (R e h (E e))⟫_ℂ).re = _
  rw [heq,R_apply,inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_right,
    hmean,zero_mul,sub_zero,← inner_conj_symm (E e) h]
  rw [mul_assoc,Complex.mul_conj]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.normSq_eq_norm_sq]
  rw [show (⟪E e,E e⟫_ℂ).re=‖E e‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) _]
  norm_num
private theorem large_spike_enclosure (E : H →L[ℂ] H) (e h u : H) (t L lam : ℝ)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : ⟪e,h⟫_ℂ=0)
    (hE : (E : H →ₗ[ℂ] H).IsSymmetric) (hmean : ⟪e,E e⟫_ℂ=0)
    (hL : 1 ≤ L) (hEn : ‖E‖ ≤ L) (ht : 96*L ≤ t)
    (hu : u ≠ 0) (heigen : ((t : ℂ) • A0 e h+E) u=(lam : ℂ) • u)
    (hrayleigh : ∀ z : H, (⟪z,((t : ℂ) • A0 e h+E) z⟫_ℂ).re ≤ lam*‖z‖^2) :
    |lam-(t+a2 E e h/t+a3 E e h/t^2)| ≤ 891*L^4/t^3 := by
  have ht0 : 0 < t := by linarith
  have htn : t ≠ 0 := ne_of_gt ht0
  let ε : ℝ := t⁻¹
  let T : H →L[ℂ] H := (t : ℂ) • A0 e h+E
  have hid (z : H) : (A0 e h+(ε : ℂ) • E) z=(ε : ℂ) • T z := by
    simp only [T,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      smul_add,smul_smul]
    have hc : (ε : ℂ)*(t : ℂ)=1 := by
      dsimp only [ε]
      exact_mod_cast inv_mul_cancel₀ htn
    rw [hc,one_smul]
  have hei : (A0 e h+(ε : ℂ) • E) u=((lam/t : ℝ) : ℂ) • u := by
    rw [hid,heigen,smul_smul]
    congr 1
    dsimp only [ε]
    change ((t⁻¹ : ℝ) : ℂ)*(lam : ℂ)=((lam/t : ℝ) : ℂ)
    norm_cast
    ring
  let f := test e (r1 E e h) (r2 E e h) ε
  let k := NormedSpace.normalize f
  have hkn : ‖k‖=1 := normalize_norm f (test_norm_ge e _ _ ε he
    (R_orth e h (E e) he heh) (R_orth e h (E (r1 E e h)) he heh))
  have hq : (⟪k,(A0 e h+(ε : ℂ) • E) k⟫_ℂ).re ≤ lam/t := by
    rw [hid,inner_smul_right]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hr := hrayleigh k
    rw [hkn,one_pow,mul_one] at hr
    have hm := mul_le_mul_of_nonneg_left hr (by dsimp [ε]; positivity : 0 ≤ ε)
    simpa only [ε,inv_mul_eq_div] using hm
  have hsmall : ε*(3*L) ≤ 1/32 := by
    dsimp [ε]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ ht0).mpr
    linarith
  have hb := rank_spike_enclosure E e h u ε L (lam/t) he hh heh hE hmean hL hEn
    (by dsimp [ε]; positivity) hsmall hu hei hq
  have hid2 : lam-(t+a2 E e h/t+a3 E e h/t^2)=
      t*(lam/t-(1+ε^2*a2 E e h+ε^3*a3 E e h)) := by
    dsimp [ε]
    field_simp
  rw [hid2,abs_mul,abs_of_pos ht0]
  calc
    _ ≤ t*(891*L^4*ε^4) := mul_le_mul_of_nonneg_left hb ht0.le
    _ = _ := by dsimp [ε]; field_simp
end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
private theorem max_has_eigenvector (K : Matrix ι ι ℂ) (hK : K.IsHermitian) :
    ∃ u : EuclideanSpace ℂ ι, u ≠ 0 ∧
      Matrix.toEuclideanCLM (𝕜 := ℂ) K u=(edgeMax K : ℂ) • u := by
  have hne := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) K
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hK)
  have hmax := (spectrum.isCompact (𝕜 := ℝ) K).isGreatest_sSup hne
  have hmem : edgeMax K ∈ Set.range hK.eigenvalues :=
    (Set.ext_iff.mp hK.spectrum_real_eq_range_eigenvalues (edgeMax K)).mp hmax.1
  obtain ⟨i,hi⟩ := hmem
  change hK.eigenvalues i=edgeMax K at hi
  refine ⟨hK.eigenvectorBasis i, ?_, ?_⟩
  · exact ne_of_apply_ne norm (by simp)
  · apply PiLp.ext
    intro j
    have hh := congrFun (hK.mulVec_eigenvectorBasis i) j
    simpa [Matrix.ofLp_toEuclideanCLM,hi] using hh
private theorem rayleigh_le_max (K : Matrix ι ι ℂ) (hK : K.IsHermitian)
    (v : EuclideanSpace ℂ ι) :
    (⟪v,Matrix.toEuclideanCLM (𝕜 := ℂ) K v⟫_ℂ).re ≤ edgeMax K*‖v‖^2 := by
  have hne := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) K
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hK)
  have hmax := (spectrum.isCompact (𝕜 := ℝ) K).isGreatest_sSup hne
  have hp := (upper_shift_iff K hK (edgeMax K)).mpr hmax.2
  have hh := hp.re_dotProduct_nonneg v.ofLp
  change 0 ≤ (star v.ofLp ⬝ᵥ ((edgeMax K • 1-K) *ᵥ v.ofLp)).re at hh
  have heq : (star v.ofLp ⬝ᵥ ((edgeMax K • 1-K) *ᵥ v.ofLp)).re =
      edgeMax K*‖v‖^2-(⟪v,Matrix.toEuclideanCLM (𝕜 := ℂ) K v⟫_ℂ).re := by
    have hip (M : Matrix ι ι ℂ) :
        ⟪v,Matrix.toEuclideanCLM (𝕜 := ℂ) M v⟫_ℂ = star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toEuclideanCLM]
      exact dotProduct_comm _ _
    rw [← hip]
    have hact : Matrix.toEuclideanCLM (𝕜 := ℂ) (edgeMax K • 1-K) v =
        (edgeMax K : ℂ) • v-Matrix.toEuclideanCLM (𝕜 := ℂ) K v := by
      apply PiLp.ext
      intro j
      simp [Matrix.ofLp_toEuclideanCLM,sub_mulVec,smul_mulVec,PiLp.smul_apply]
    change (⟪v,Matrix.toEuclideanCLM (𝕜 := ℂ) (edgeMax K • 1-K) v⟫_ℂ).re = _
    rw [hact,inner_sub_right,inner_smul_right]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [show (⟪v,v⟫_ℂ).re=‖v‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) v]
  rw [heq] at hh
  linarith
private theorem max_neg (K : Matrix ι ι ℂ) (hK : K.IsHermitian) : edgeMax (-K)=-edgeMin K := by
  have hne := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) K
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hK)
  have hnen := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (-K)
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hK.neg)
  have hmax := (spectrum.isCompact (𝕜 := ℝ) (-K)).isGreatest_sSup hnen
  have hmin := (spectrum.isCompact (𝕜 := ℝ) K).isLeast_sInf hne
  have hmn : -edgeMax (-K) ∈ spectrum ℝ K := by
    have hm : edgeMax (-K) ∈ spectrum ℝ (-K) := hmax.1
    simpa only [← spectrum.neg_eq,Set.mem_neg] using hm
  have hmm : -edgeMin K ∈ spectrum ℝ (-K) := by
    rw [← spectrum.neg_eq,Set.mem_neg,neg_neg]
    exact hmin.1
  have ha := hmin.2 hmn
  have hb := hmax.2 hmm
  change edgeMin K ≤ -edgeMax (-K) at ha
  change -edgeMin K ≤ edgeMax (-K) at hb
  linarith
end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem block_inner (a b c d : EuclideanSpace ℂ ι) :
    ⟪(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (a, b),(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (c, d)⟫_ℂ=⟪a,c⟫_ℂ+⟪b,d⟫_ℂ := by
  simp [EuclideanSpace.sumEquivProd,PiLp.inner_apply,Fintype.sum_sum_type]
private theorem block_norm_sq (a b : EuclideanSpace ℂ ι) :
    ‖(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (a, b)‖^2=‖a‖^2+‖b‖^2 := by
  have hh := congrArg Complex.re (block_inner a b a b)
  simp only [Complex.add_re] at hh
  simpa only [show ∀ z : EuclideanSpace ℂ ι, (⟪z,z⟫_ℂ).re=‖z‖^2 from
    fun z => inner_self_eq_norm_sq (𝕜 := ℂ) z,
    show (⟪(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (a, b),(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (a, b)⟫_ℂ).re=‖(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (a, b)‖^2 from
      inner_self_eq_norm_sq (𝕜 := ℂ) _] using hh
private theorem block_zero_norm (v : EuclideanSpace ℂ ι) (hv : ‖v‖=1) :
    ‖(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)‖=1 ∧ ‖(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v)‖=1 := by
  have ha := block_norm_sq v 0
  have hb := block_norm_sq 0 v
  simp only [hv,norm_zero,zero_pow (by decide : 2 ≠ 0),one_pow,add_zero,zero_add] at ha hb
  constructor <;> nlinarith [norm_nonneg ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)),norm_nonneg ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v))]
private theorem block_orth (v : EuclideanSpace ℂ ι) : ⟪(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0),(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v)⟫_ℂ=0 := by
  rw [block_inner]
  simp
private theorem block_action (A B C D : Matrix ι ι ℂ) (a b : EuclideanSpace ℂ ι) :
    toEuclideanCLM (𝕜 := ℂ) (fromBlocks A B C D) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (a, b))=
      (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm ((toEuclideanCLM (𝕜 := ℂ) A a+toEuclideanCLM (𝕜 := ℂ) B b), (toEuclideanCLM (𝕜 := ℂ) C a+toEuclideanCLM (𝕜 := ℂ) D b)) := by
  apply PiLp.ext
  intro j
  cases j <;> simp [EuclideanSpace.sumEquivProd,ofLp_toEuclideanCLM,mulVec,dotProduct,Fintype.sum_sum_type,
    fromBlocks,Finset.sum_add_distrib]
theorem outer_action (v z : EuclideanSpace ℂ ι) :
    toEuclideanCLM (𝕜 := ℂ) ((Matrix.vecMulVec (v).ofLp (star (v).ofLp))) z=⟪v,z⟫_ℂ • v := by
  apply PiLp.ext
  intro j
  simp only [ofLp_toEuclideanCLM,vecMulVec_mulVec,PiLp.smul_apply,
    Pi.smul_apply,op_smul_eq_smul,smul_eq_mul]
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]
theorem outer_hermitian (v : EuclideanSpace ℂ ι) : ((Matrix.vecMulVec (v).ofLp (star (v).ofLp))).IsHermitian := by
  exact (Matrix.posSemidef_vecMulVec_self_star v.ofLp).isHermitian
private theorem A0_matrix (v : EuclideanSpace ℂ ι) :
    toEuclideanCLM (𝕜 := ℂ) (fromBlocks ((Matrix.vecMulVec (v).ofLp (star (v).ofLp))) 0 0 (-(Matrix.vecMulVec (v).ofLp (star (v).ofLp))))=
      A0 ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v)) := by
  ext z j
  have hz : z=(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm ((WithLp.toLp 2 (fun i => z (Sum.inl i))), (WithLp.toLp 2 (fun i => z (Sum.inr i)))) := by apply PiLp.ext; intro i; cases i <;> rfl
  rw [hz,block_action,A0_apply]
  simp only [map_zero,zero_add,add_zero,map_neg,neg_apply,outer_action,block_inner,
    inner_zero_left,inner_zero_right,add_zero,zero_add]
  cases j <;> simp [EuclideanSpace.sumEquivProd,PiLp.smul_apply,PiLp.sub_apply,vecMulVec_mulVec,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]
private theorem decomposition (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (t : ℝ) :
    toEuclideanCLM (𝕜 := ℂ) (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))=
      (t : ℂ) • A0 ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v))+
        toEuclideanCLM (𝕜 := ℂ) (K X S) := by
  have hm : K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S)=
      (t : ℂ) • fromBlocks ((Matrix.vecMulVec (v).ofLp (star (v).ofLp))) 0 0 (-(Matrix.vecMulVec (v).ofLp (star (v).ofLp)))+K X S := by
    ext i j
    cases i <;> cases j <;> simp [K,fromBlocks,add_comm]
  rw [hm,map_add,map_smul,A0_matrix]
private theorem E_e (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) :
    toEuclideanCLM (𝕜 := ℂ) (K X S) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0))=
      (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)) := by
  rw [K,block_action,hSv]
  simp
private theorem mean_zero (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) :
    ⟪(EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0),toEuclideanCLM (𝕜 := ℂ) (K X S) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0))⟫_ℂ=0 := by
  rw [E_e X S v hSv,block_inner]
  simp
private theorem K_symmetric (X S : Matrix ι ι ℂ) (hS : S.IsHermitian) :
    ((toEuclideanCLM (𝕜 := ℂ) (K X S)) :
      EuclideanSpace ℂ (ι ⊕ ι) →ₗ[ℂ] EuclideanSpace ℂ (ι ⊕ ι)).IsSymmetric := by
  intro a b
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hS.fromBlocks rfl hS.neg)) a b
private theorem r1_block (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) :
    r1 (toEuclideanCLM (𝕜 := ℂ) (K X S)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v))=
      (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, (toEuclideanCLM (𝕜 := ℂ) Xᴴ v-
        ((1/2:ℂ)*⟪v,toEuclideanCLM (𝕜 := ℂ) Xᴴ v⟫_ℂ) • v)) := by
  dsimp only [r1]
  rw [R_apply,E_e X S v hSv,block_inner,block_inner]
  simp only [inner_zero_left,inner_zero_right,zero_add,add_zero,zero_smul,sub_zero]
  apply PiLp.ext
  intro j
  cases j <;> simp [EuclideanSpace.sumEquivProd,PiLp.smul_apply,PiLp.sub_apply]
private theorem block_coefficient3 (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) :
    a3 (toEuclideanCLM (𝕜 := ℂ) (K X S)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v))=
      -(⟪toEuclideanCLM (𝕜 := ℂ) Xᴴ v,
        toEuclideanCLM (𝕜 := ℂ) S (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)⟫_ℂ).re := by
  let z := toEuclideanCLM (𝕜 := ℂ) Xᴴ v
  let c := (1/2:ℂ)*⟪v,z⟫_ℂ
  let T := toEuclideanCLM (𝕜 := ℂ) S
  have hs : (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric := by
    simpa only [T,coe_toEuclideanCLM_eq_toEuclideanLin] using Matrix.isSymmetric_toEuclideanLin_iff.mpr hS
  have hz : ⟪v,T z⟫_ℂ=0 := by
    have heq := (hs v z).symm
    change ⟪v,T z⟫_ℂ=⟪T v,z⟫_ℂ at heq
    rw [heq,hSv,inner_zero_left]
  have hy : T (z-c • v)=T z := by
    simp only [map_sub,map_smul,T,hSv,smul_zero,sub_zero]
  rw [coefficient3_identity _ _ _
    (by intro a b; exact K_symmetric X S hS a b),r1_block X S v hSv]
  rw [K,block_action,block_inner]
  simp only [inner_zero_left,map_zero,zero_add,add_zero,map_neg,ContinuousLinearMap.neg_apply,inner_neg_right,Complex.neg_re]
  change -(⟪z-c • v,T (z-c • v)⟫_ℂ).re = -(⟪z,T z⟫_ℂ).re
  rw [hy,inner_sub_left,inner_smul_left,hz,mul_zero,sub_zero]
private theorem reflected_edge [Nonempty ι] (X D : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    edgeMax (K X (-D))=-edgeMin (K X D) := by
  have hj : ((Matrix.fromBlocks 1 0 0 (-1)) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)ᴴ=(Matrix.fromBlocks 1 0 0 (-1)) := by simp [fromBlocks_conjTranspose]
  have hu : (Matrix.fromBlocks 1 0 0 (-1)) ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change (Matrix.fromBlocks 1 0 0 (-1))*(Matrix.fromBlocks 1 0 0 (-1))ᴴ=1
    rw [hj]
    simp [fromBlocks_multiply,← fromBlocks_one]
  let U : unitary (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := ⟨(Matrix.fromBlocks 1 0 0 (-1)),hu⟩
  have hc : (Matrix.fromBlocks 1 0 0 (-1))*K X (-D)*(Matrix.fromBlocks 1 0 0 (-1))=-(K X D) := by
    simp [K,fromBlocks_multiply,fromBlocks_neg]
  have hs := Unitary.spectrum_star_left_conjugate (R := ℝ) (a := K X (-D)) (U := U)
  change spectrum ℝ ((Matrix.fromBlocks 1 0 0 (-1))ᴴ*K X (-D)*(Matrix.fromBlocks 1 0 0 (-1)))=spectrum ℝ (K X (-D)) at hs
  rw [hj,hc] at hs
  have hh : edgeMax (K X (-D))=edgeMax (-(K X D)) :=
    congrArg sSup hs.symm
  rw [hh]
  exact max_neg _ (hD.fromBlocks rfl hD.neg)
private theorem star_reflected_edge [Nonempty ι] (X D : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    edgeMax (K Xᴴ D)=-edgeMin (K X D) := by
  have hf : ((Matrix.fromBlocks 0 1 1 0) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)ᴴ=(Matrix.fromBlocks 0 1 1 0) := by simp [fromBlocks_conjTranspose]
  have hu : (Matrix.fromBlocks 0 1 1 0) ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change (Matrix.fromBlocks 0 1 1 0)*(Matrix.fromBlocks 0 1 1 0)ᴴ=1
    rw [hf]
    simp [fromBlocks_multiply,← fromBlocks_one]
  let U : unitary (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := ⟨(Matrix.fromBlocks 0 1 1 0),hu⟩
  have hc : (Matrix.fromBlocks 0 1 1 0)*K X (-D)*(Matrix.fromBlocks 0 1 1 0)=K Xᴴ D := by
    simp [K,fromBlocks_multiply]
  have hs := Unitary.spectrum_star_left_conjugate (R := ℝ) (a := K X (-D)) (U := U)
  change spectrum ℝ ((Matrix.fromBlocks 0 1 1 0)ᴴ*K X (-D)*(Matrix.fromBlocks 0 1 1 0))=spectrum ℝ (K X (-D)) at hs
  rw [hf,hc] at hs
  calc
    _ = edgeMax (K X (-D)) := congrArg sSup hs
    _ = _ := reflected_edge X D hD
private theorem star_block_norm (X S : Matrix ι ι ℂ) : ‖K Xᴴ S‖=‖K X S‖ := by
  have hu : (Matrix.fromBlocks 0 1 (-1) 0) ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change (Matrix.fromBlocks 0 1 (-1) 0)*(Matrix.fromBlocks 0 1 (-1) 0)ᴴ=1
    simp [fromBlocks_conjTranspose,fromBlocks_multiply,← fromBlocks_one]
  let U : unitary (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := ⟨(Matrix.fromBlocks 0 1 (-1) 0),hu⟩
  have hc : (Matrix.fromBlocks 0 1 (-1) 0)*K X S*(Matrix.fromBlocks 0 1 (-1) 0)ᴴ=-(K Xᴴ S) := by
    simp [K,fromBlocks_conjTranspose,fromBlocks_multiply,fromBlocks_neg]
  have hn : ‖(Matrix.fromBlocks 0 1 (-1) 0)*K X S*(Matrix.fromBlocks 0 1 (-1) 0)ᴴ‖=‖K X S‖ := by
    change ‖(U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*K X S*star (U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)‖=‖K X S‖
    change ‖(U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*K X S*(star U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)‖=‖K X S‖
    exact (CStarRing.norm_mul_coe_unitary
      ((U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*K X S) (star U)).trans
      (CStarRing.norm_coe_unitary_mul U (K X S))
  simpa only [hc,norm_neg] using hn
private theorem adjoint_pairing (X : Matrix ι ι ℂ) (v z : EuclideanSpace ℂ ι) :
    ⟪v,toEuclideanCLM (𝕜 := ℂ) Xᴴ z⟫_ℂ=⟪toEuclideanCLM (𝕜 := ℂ) X v,z⟫_ℂ := by
  have ht : toEuclideanCLM (𝕜 := ℂ) Xᴴ=(toEuclideanCLM (𝕜 := ℂ) X).adjoint := by
    have ht := map_star (toEuclideanCLM (n := ι) (𝕜 := ℂ)) X
    simpa only [Matrix.star_eq_conjTranspose,ContinuousLinearMap.star_eq_adjoint] using ht
  rw [ht,ContinuousLinearMap.adjoint_inner_right]
private theorem paired_norm (X : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    ‖⟪v,toEuclideanCLM (𝕜 := ℂ) Xᴴ v⟫_ℂ‖=‖⟪v,toEuclideanCLM (𝕜 := ℂ) X v⟫_ℂ‖ := by
  rw [adjoint_pairing]
  exact norm_inner_symm _ _
private theorem spectral_spike_enclosure [Nonempty ι] (X S : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) (t L : ℝ) (hv : ‖v‖=1)
    (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0)
    (hL : 1 ≤ L) (hEn : ‖K X S‖ ≤ L) (ht : 96*L ≤ t) :
    let E := toEuclideanCLM (𝕜 := ℂ) (K X S)
    let e := (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)
    let h := (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v)
    |edgeMax (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))-
      (t+a2 E e h/t+a3 E e h/t^2)| ≤ 891*L^4/t^3 := by
  dsimp only
  let E := toEuclideanCLM (𝕜 := ℂ) (K X S)
  let e := (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)
  let h := (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v)
  let D := t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S
  have hD : D.IsHermitian := ((outer_hermitian v).smul (isSelfAdjoint_iff.mpr rfl)).add hS
  have hK : (K X D).IsHermitian := hD.fromBlocks rfl hD.neg
  obtain ⟨u,hu,heigen⟩ := max_has_eigenvector (K X D) hK
  have hdec := decomposition X S v t
  rw [hdec] at heigen
  exact large_spike_enclosure E e h u t L (edgeMax (K X D))
    (block_zero_norm v hv).1 (block_zero_norm v hv).2 (block_orth v)
    (by intro a b; exact K_symmetric X S hS a b)
    (mean_zero X S v hSv) hL hEn ht hu heigen
    (fun z => by rw [← hdec]; exact rayleigh_le_max (K X D) hK z)
private theorem block_coefficient2 (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) :
    a2 (toEuclideanCLM (𝕜 := ℂ) (K X S)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (v, 0)) ((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := ι) (κ := ι)).symm (0, v))=
      ‖toEuclideanCLM (𝕜 := ℂ) Xᴴ v‖^2-
        (1/2:ℝ)*‖⟪v,toEuclideanCLM (𝕜 := ℂ) Xᴴ v⟫_ℂ‖^2 := by
  rw [coefficient2_formula _ _ _
    (by intro a b; exact K_symmetric X S hS a b)
    (mean_zero X S v hSv),E_e X S v hSv,block_norm_sq,block_inner]
  simp
end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
private def coeff2 (X : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : ℝ :=
  ‖toEuclideanCLM (𝕜 := ℂ) Xᴴ v‖^2-‖⟪v,toEuclideanCLM (𝕜 := ℂ) X v⟫_ℂ‖^2/2
def defect1 (X : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : ℝ :=
  ‖toEuclideanCLM (𝕜 := ℂ) Xᴴ v‖^2-‖toEuclideanCLM (𝕜 := ℂ) X v‖^2
def defect2 (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : ℝ :=
  (⟪toEuclideanCLM (𝕜 := ℂ) X v,toEuclideanCLM (𝕜 := ℂ) S (toEuclideanCLM (𝕜 := ℂ) X v)⟫_ℂ).re-
  (⟪toEuclideanCLM (𝕜 := ℂ) Xᴴ v,toEuclideanCLM (𝕜 := ℂ) S (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)⟫_ℂ).re
theorem positive_spike_enclosure (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (t L : ℝ)
    (hv : ‖v‖=1) (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0)
    (hL : 1 ≤ L) (hEn : ‖K X S‖ ≤ L) (ht : 96*L ≤ t) :
    |edgeMax (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))-
      (t+(‖toEuclideanCLM (𝕜 := ℂ) Xᴴ v‖^2-
        ‖⟪v,toEuclideanCLM (𝕜 := ℂ) X v⟫_ℂ‖^2/2)/t-
        (⟪toEuclideanCLM (𝕜 := ℂ) Xᴴ v,
          toEuclideanCLM (𝕜 := ℂ) S (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)⟫_ℂ).re/t^2)| ≤ 891*L^4/t^3 := by
  have hb := spectral_spike_enclosure X S v t L hv hS hSv hL hEn ht
  dsimp only at hb
  rw [block_coefficient2 X S v hS hSv,block_coefficient3 X S v hS hSv,paired_norm X v] at hb
  convert hb using 1 <;> dsimp [coeff2] <;> ring
private theorem negative_bound (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (t L : ℝ)
    (hv : ‖v‖=1) (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0)
    (hL : 1 ≤ L) (hEn : ‖K X S‖ ≤ L) (ht : 96*L ≤ t) :
    |edgeMin (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))-
      (-t-(‖toEuclideanCLM (𝕜 := ℂ) X v‖^2-
        ‖⟪v,toEuclideanCLM (𝕜 := ℂ) X v⟫_ℂ‖^2/2)/t+
        (⟪toEuclideanCLM (𝕜 := ℂ) X v,
          toEuclideanCLM (𝕜 := ℂ) S (toEuclideanCLM (𝕜 := ℂ) X v)⟫_ℂ).re/t^2)| ≤ 891*L^4/t^3 := by
  have hb := positive_spike_enclosure Xᴴ S v t L hv hS hSv hL (by rw [star_block_norm]; exact hEn) ht
  have hD : (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S).IsHermitian := ((outer_hermitian v).smul (isSelfAdjoint_iff.mpr rfl)).add hS
  rw [star_reflected_edge X _ hD] at hb
  simp only [coeff2,conjTranspose_conjTranspose,paired_norm X v] at hb
  convert hb using 1
  rw [← abs_neg]
  congr 1
  ring
theorem edge_sum_bound (X S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (t L : ℝ)
    (hv : ‖v‖=1) (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0)
    (hL : 1 ≤ L) (hEn : ‖K X S‖ ≤ L) (ht : 96*L ≤ t) :
    |edgeMax (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))+edgeMin (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))-
      (defect1 X v/t+defect2 X S v/t^2)| ≤ 1782*L^4/t^3 := by
  have hp := positive_spike_enclosure X S v t L hv hS hSv hL hEn ht
  have hn := negative_bound X S v t L hv hS hSv hL hEn ht
  let a := edgeMax (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))-
      (t+coeff2 X v/t-
        (⟪toEuclideanCLM (𝕜 := ℂ) Xᴴ v,
          toEuclideanCLM (𝕜 := ℂ) S (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)⟫_ℂ).re/t^2)
  let b := edgeMin (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))-
      (-t-(‖toEuclideanCLM (𝕜 := ℂ) X v‖^2-
        ‖⟪v,toEuclideanCLM (𝕜 := ℂ) X v⟫_ℂ‖^2/2)/t+
        (⟪toEuclideanCLM (𝕜 := ℂ) X v,
          toEuclideanCLM (𝕜 := ℂ) S (toEuclideanCLM (𝕜 := ℂ) X v)⟫_ℂ).re/t^2)
  have heq : edgeMax (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))+edgeMin (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))-
      (defect1 X v/t+defect2 X S v/t^2)=a+b := by dsimp [a,b,coeff2,defect1,defect2]; ring
  rw [heq]
  change |a| ≤ _ at hp
  change |b| ≤ _ at hn
  exact (abs_add_le a b).trans (by
    calc
      _ ≤ 891*L^4/t^3+891*L^4/t^3 := add_le_add hp hn
      _ = _ := by ring)
end
end D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate

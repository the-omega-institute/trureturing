/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BesselSchurBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BesselSchurBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.CuspKernel.BesselSchurBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/CuspKernel/BesselSchurBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bessel.UnipotentCoords
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of measure and integration (textbook or folklore).

Part of: Schur orthogonality; coefficients of integrable discrete series are cusp forms (known
result; see Lib.DiscreteSeries.CuspKernel.CircleMean).

This file: Definitions: convolution, Bessel functions, unitary action of U(κ).
Schur orthogonality: convolution with reproduced functions is an isometry up to the degree. -/

open Matrix MeasureTheory ContinuousLinearMap ENNReal InnerProductSpace

/-- The convolution F*x of a vector-valued function F and a complex function x on G: the
function y ↦ ∫ x(a⁻¹) F(ya) da. -/
noncomputable def convolve {G E} [Group G] [MeasureSpace G] [NormedAddCommGroup E] [NormedSpace ℂ E]
  (F : G → E) (x : G → ℂ) y := ∫ a, x a⁻¹ • F (y * a)

variable {𝔰 : Shape} {I} [Fintype I] (rep : U (1 : Matrix 𝔰.κ _ ℂ) →* unitaryGroup I ℂ)

/-- Bessel function: F : G₁ → ℂ^I bounded measurable, F(ny) = exp(σ(n) − conj σ(n))F(y) for n in
`besselU`, σ = `simpleRootSum`, and F(hy) = rep(h)F(y) for h in U(κ). -/
structure IsBesselFunction (F : 𝔰.G₁ → EuclideanSpace ℂ I) extends IsBoundedMeasurable F where
  map_U : ∀ n ∈ besselU, ∀ y, F (n * y) = wave (simpleRootSum n) • F y
  map_H h y : F (embedH h * y) = toEuclideanCLM (𝕜 := ℂ) (rep h) (F y)

/-- The unitary matrix representation rep of U(κ), read as a homomorphism to the continuous
linear operators on the Euclidean space ℂ^I. -/
noncomputable def besselValueRep :=
  (Unitary.map (.ofClass (toEuclideanCLM (𝕜 := ℂ)))).toMonoidHom.comp rep

attribute [local simp] Complex.mul_conj' integral_div integral_smul mul_smul convolve
  inner_smul_right mul_assoc mul_div norm_smul

variable {G E} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasureSpace G] {F : G → E}
  [BorelSpace G]
  [(@volume G _).IsHaarMeasure] {x z ψ c : G → ℂ} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ν} [SFinite ν] {S : Subgroup G} {ρ : Measure S} [SFinite ρ] [HasCutoff ρ G]
  [ρ.IsInvInvariant] (hν : orbitMeasure ρ volume = ν) (hc : ∀ s, ‖c s‖ = 1) (hF :
  IsBoundedMeasurable F) {d : ℝ} (hL : ∀ s ∈ S, ∀ y, F (s * y) = c s • F y) (h2 :
  Integrable F ν) (hx : Integrable x) (K : IsIdempotentKernel ψ)
  (hd : ψ 1 = d) (fx : convolve F ψ = F) (hb : IsBoundedMeasurable ψ) (ex : convolve ψ x = x)

include h2 in
omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [(@volume G _).IsHaarMeasure] [InnerProductSpace ℂ E] [CompleteSpace E] [SFinite ν] in
lemma lintegral_enorm_sq (t : MemLp F ∞ ν) : ∫⁻ y, ‖F y‖ₑ ^ 2 ∂ν = .ofReal (∫ y, ‖F y‖ ^ 2 ∂ν) := by
  simpa [sq] using (ofReal_integral_norm_eq_lintegral_enorm (h2.norm.mul_of_top_left t.norm)).symm

lemma IsIdempotentKernel.integral_inv_mul_translate [(@volume G _).IsMulRightInvariant]
    [LocallyCompactSpace G] [PolishSpace G] (K : IsIdempotentKernel ψ) g y : ∫ a, ψ a⁻¹ * ψ
  (g * (a * y)) = ψ g / ψ 1 * ψ y := by simpa using (integral_inv_eq_self ..).trans (K.5 g⁻¹ y)

lemma convolve_star (K : IsIdempotentKernel ψ) (ex : convolve ψ x = x) : convolve (⟪x ·⁻¹, 1⟫_ℂ) ψ =
  (⟪x ·⁻¹, 1⟫_ℂ) := by
  ext y; rw [convolve, ← integral_mul_left_eq_self _ y⁻¹]
  simp [← congrFun ex y⁻¹, ← K.3, ← integral_conj, mul_comm]

variable [(@volume G _).IsMulRightInvariant] [LocallyCompactSpace G] [PolishSpace G]

lemma integrable_convolve (hx : Integrable x) (j : Integrable z) : Integrable (convolve x z) :=
  (integral_skew_product (map_mul_right_eq_self _) (j.comp_inv.mul_prod hx)).1

namespace IsBoundedMeasurable

include hF hx

/-- On a second countable locally compact group G with two-sided Haar measure, for F : G → E
bounded and strongly measurable, E a Hilbert space, and x integrable, y ↦ ∫ x(a⁻¹) F(ya) da
is continuous. -/
lemma continuous_convolve : Continuous (convolve F x) := (by fun_prop : Continuous fun y ↦
    ((lsmul ℂ ℂ).lpPairing ..) (DomMulAct.mk y⁻¹ • hx.comp_inv.toL1) hF.memLp_top.toLp).congr
  fun y ↦ by erw [lpPairing_eq_integral, integral_congr_ae ((AEEqFun.coeFn_mk
  ..).smul hF.memLp_top.coeFn_toLp), ← integral_mul_left_eq_self _ y]; simp

lemma convolve_right : IsBoundedMeasurable (convolve F x) :=
  .of (hF.2.imp' _ fun C h _ ↦ norm_integral_le_of_norm_le
  (hx.comp_inv.norm.mul_const C) (by simp [*, mul_le_mul])) (hF.continuous_convolve hx)

omit [(@volume G _).IsMulRightInvariant] [LocallyCompactSpace G] [PolishSpace G]
  [(@volume G _).IsHaarMeasure] [CompleteSpace E] in
lemma integrable_smul y : Integrable fun a ↦ x a • F (y * a) :=
  hx.smul_of_top_left (hF.comp _).memLp_top

lemma convolve_assoc (j : Integrable z) : convolve (convolve F x) z = convolve F (convolve x
  z) := by ext; simpa using (_root_.integral_conv _ j.comp_inv hx.comp_inv (hF.comp _)).2

include hν hc hL h2 K hd fx hb ex

/-- Schur orthogonality: let ψ be bounded, integrable, hermitian, ∫ψ(a⁻¹)ψ(gay)da = ψ(g)ψ(y)/d,
F*ψ = F, ψ*x = x, x integrable, F bounded, ν-integrable, left S-equivariant by modulus-one
factors, ν the measure on S\G. Then ‖F*x‖²_ν = (‖x‖₂²/d)·‖F‖²_ν, with * = `convolve`. -/
lemma lintegral_sq_convolve :
    ∫⁻ y, ‖convolve F x y‖ₑ ^ 2 ∂ν = .ofReal ((∫ y, ‖x y‖ ^ 2) / d * ∫ y, ‖F y‖ ^ 2 ∂ν) := by
  obtain ⟨A, X, i⟩ := hF.convolve_right hx, ex ▸ hb.convolve_right hx,
    hx.comp_inv.inner_const (𝕜 := ℂ) 1
  let f a y := ⟪convolve F x (y * a), x a • F y⟫_ℂ
  have J {a} := hν ▸ identDistrib_orbitMeasure_mul_right a⁻¹ (by simp_all [f, smul_comm (x _),
            mul_left_comm (c _)]) (by fun_prop : StronglyMeasurable (f a)).measurable
  have k : Integrable f.uncurry _ := ((hx.smul_prod h2).norm.const_mul _).mono' ⟨_, by fun_prop,
    .rfl⟩ (.of_forall fun _ ↦ (norm_inner_le_norm ..).trans (by grw [A.2.choose_spec]))
  have g : Integrable (fun a y ↦ f a (y * a⁻¹)).uncurry (volume.prod ν) := (integrable_prod_iff
    ⟨_, by fun_prop, .rfl⟩).2 (by
    simp_all [J.integrable_iff, J.norm.integral_eq, integrable_prod_iff k.1])
  have D {w} (h : Integrable w) g : convolve (convolve ψ w) ψ g = convolve ψ w 1 / d * ψ g := by
    simpa [K.integral_inv_mul_translate, *, div_mul_comm (ψ g), ← mul_assoc (w _)] using
      (_root_.integral_conv (g * ·) K.2.comp_inv h.comp_inv hb).1
  obtain ⟨e, u, _⟩ := integral_integral_swap g, fun y ↦ (integral_inv_eq_self ..).trans
    (integral_inner (𝕜 := ℂ) (hF.integrable_smul hx.comp_inv y) (convolve F x y)), fun y ↦
    congr(starRingEnd ℂ $(integral_inner (A.integrable_smul i.comp_inv y) (F y))), convolve_star K
    ex ▸ X.convolve_assoc i K.2 ▸ ex ▸ hb.convolve_assoc hx i ▸ D (integrable_convolve hx i),
    hF.convolve_assoc hx i
  simp [← integral_conj, J.integral_eq, integral_integral_swap k, funext_iff] at *
  simp [f, *, inner_smul_left, ← integral_conj] at e
  rw_mod_cast [e, eq_comm]
  simpa [f, ← ofReal_norm, u] using ofReal_integral_norm_eq_lintegral_enorm g.integral_prod_right

/-- Under the hypotheses of `IsBoundedMeasurable.lintegral_sq_convolve`, for integrable φ the
function y ↦ ∫φ(a)(F*x)(ya)da has squared L²(ν) norm at most (‖x‖₂²/d)·(‖F‖²_ν/d)·‖φ‖₂². -/
lemma lintegral_sq_convolve_convolve_le (j :
  Integrable z) : ∫⁻ y, ‖convolve (convolve F x) (z ·⁻¹) y‖ₑ ^ 2 ∂ν ≤ .ofReal
  ((∫ y, ‖x y‖ ^ 2) / d) * (.ofReal d⁻¹ * ∫⁻ y, ‖F y‖ₑ ^ 2 ∂ν) * ∫⁻ y, ‖z y‖ₑ ^ 2 := by
  have i := j.comp_inv; obtain ⟨U, e⟩ := integrable_convolve hx i,
    ex ▸ (hb.convolve_assoc hx i).symm
  cases e ▸ hb.convolve_right U
  have v : IsBoundedMeasurable (⟪convolve x (z ·⁻¹) ·⁻¹, 1⟫_ℂ) := ⟨by fun_prop, by aesop⟩
  have s := sq_lintegral_le (j.1.enorm.pow_const 2)
    ((v.convolve_right hx).memLp_top.aestronglyMeasurable.enorm.pow_const 2) fun _ ↦ by rw
      [← mul_pow, ← enorm_mul]
  grw [v.lintegral_sq_convolve quotMeasure_bot (c := 1), ← enorm_integral_le_lintegral_enorm,
    ofReal_mul', ← mul_rotate',
    sq, ← ofReal_norm, show integral .. = _ by simpa [← Complex.ofReal_pow, integral_complex_ofReal]
    using (congrFun (v.convolve_assoc hx i) 1), ← Complex.re_le_norm] at s
  grw [hF.convolve_assoc, hF.lintegral_sq_convolve hν, ofReal_mul', ← lintegral_enorm_sq,
    ← integral_inv_eq_self, division_def, ofReal_mul, ← ENNReal.mul_div_cancel_right' id
    ofReal_ne_top.elim, div_le_of_le_mul' (by simpa using s), mul_assoc, mul_rotate]
  all_goals first | solve_by_elim [convolve_star, memLp_top,
    U.comp_inv.inner_const] | positivity | simp

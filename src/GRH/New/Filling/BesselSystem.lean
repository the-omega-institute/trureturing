import GRH.New.Filling.EichlerFlag
import GRH.Lib.DiscreteSeries.CuspKernel.BesselSchurBound
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Definition of Bessel systems: band limits, Schur bounds, tail bound; the
constants of the open-cell bound, which is proved in New.RealPlace.OpenCellBound. -/

noncomputable section


open MeasureTheory Matrix ComplexConjugate Real Fintype Set Norms.L2Operator
variable (𝔰 : Shape)

/-- The constant c_G = vol U(k)·(2π^k/(k−1)!)/vol U(k + 2ϱ + 1); for k ≥ 1 the middle factor is
vol U(k)/vol U(k−1). -/
def Shape.openCellConst := volU 𝔰.k / volU 𝔰.r * sphereDensity 𝔰.k 1

lemma Shape.openCellConst_pos : 0 < 𝔰.openCellConst := by simp [openCellConst]; positivity

/-- The constant Θ = π^((2ϱ+1)k)·vol U(k)/vol U(r), with k the rank of X₀ and r the rank of the
whole space. -/
def Shape.bandConst := volU 𝔰.k / volU 𝔰.r * π ^ ((2 * 𝔰.ϱ + 1) * 𝔰.k)

variable {𝔰} (y : 𝔰.G₁) {I : Type} [Fintype I] (b) (W : 𝔰.G₁ → EuclideanSpace ℂ I) (deg f)

/-- For y in G₁, the infimum of ‖sy‖ + 1 (operator norm) over s in the Bessel subgroup S. -/
def besselSize := ⨅ s : besselS, ‖(s.1 * y).1.1‖ + 1

/-- The size `besselSize` of y is at most b^(6ϱ+8); the cut Bessel function vanishes where this
fails. -/
abbrev InCut := besselSize y ≤ b ^ (6 * 𝔰.n + 2)

/-- For real ρ, the set of y in G₁ such that every vector y⁻¹f_a has Euclidean norm at most ρ. -/
def frameBox ρ := {y : 𝔰.G₁ | ∀ a, ‖frameVector y a‖ ≤ ρ}

/-- For a (ϱ+1)×(ϱ+1) complex matrix Z, the real number 𝗀(Z) = |det Z|² − |D_ϱ|², D_ϱ the
leading principal minor of order ϱ. -/
def gramDiscReal (Z : 𝔰.FrameMat) := (frameDisc 1 Z).re

/-- The number (ρ^(9n)/𝗀)^(10⁵n⁴)·d²/(deg·c_G·(𝗀/2)^(k−1)), with n = ϱ+1, k = |κ|, c_G =
`Shape.openCellConst` and 𝗀 = `gramDiscReal` of the frame matrix Z(y). -/
def cellMass ρ d := (ρ ^ (9 * 𝔰.n) / gramDiscReal (realFrameGram y)) ^ (10 ^ 5 * 𝔰.n ^ 4) *
  (d ^ 2 / (deg * 𝔰.openCellConst * (gramDiscReal (realFrameGram y) / 2) ^ (𝔰.k - 1)))

/-- The tensor J(γ) = ∫ W(y) ⊗ W(γ⁻¹y)^* dμ(y), with coordinates ∫ W_i(y) conj(W_j(γ⁻¹y)) dμ(y),
for a vector-valued function W on a group G. -/
def besselCorrelation {G I} [Group G] [MeasurableSpace G] (μ : Measure G) (W : G → EuclideanSpace ℂ
  I) (γ : G) : EuclideanSpace ℂ (I × I) := .toLp 2 fun x ↦ ∫ y, W y x.1 * conj (W (γ⁻¹ * y) x.2) ∂μ

/-- Schur's bound: for every integrable φ on G₁, the function γ ↦ ∫ φ(y)W(γy) dy has squared L²
norm on 𝖴∖G₁ at most D·∫|φ|². -/
def SchurLe D := ∀ φ : _ → ℂ, Integrable φ →
  ∫⁻ γ, ‖∫ y, φ y • W (γ * y)‖ₑ ^ 2 ∂besselQuotMeasure ≤ D * ∫⁻ y, ‖φ y‖ₑ ^ 2

/-- Bessel functions W_w, w words, with W_{(a,b)w} the right derivative of W_w along E_{ab}, and
‖∫ φ(y)W_w(·y) dy‖₂² ≤ B^{2|w|}D∫|φ|² on 𝖴∖G₁ for |w| ≤ 2(ϱ+1)², φ integrable. -/
def HasSchurBound rep B D := ∃ V : _ → C(_, _), W = V [] ∧ ∀ w, IsBesselFunction rep (V w) ∧
  (∀ (γ : ℝ →
  𝔰.G₁) X t, HasDerivAt (γ · |>.1.1) (γ t * X) t → HasDerivAt (V w ∘ γ) (∑ a, ∑ b, X a b • V ((a, b)
  :: w) (γ t)) t) ∧ (w.length ≤ 2 * 𝔰.n ^ 2 → SchurLe (V w) (.ofReal (B ^ (2 * w.length)) * D))

/-- The tensor J(w_p y) of `besselCorrelation` times √c_G·√(|p_ϱ|² −
1)^(k−1)·|I|⁻¹·∏_{a<ϱ}|p_a|^(k+1+2(ϱ−a−1)), where w_p is the Weyl element of length ϱ, k =
|κ|, c_G = `Shape.openCellConst`. -/
def normCorrelation p := (√𝔰.openCellConst * √(‖(p 𝔰.ϱ).1‖ ^ 2 - 1) ^ (𝔰.k - 1) / card I * ∏ a ∈
  .range 𝔰.ϱ, ‖(p a).1‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))) • besselCorrelation volume W
  (weylElem 𝔰.ϱ p * y)

/-- Band limits: the forms J are a `SieveSystem` on ℂ with bottom bound (1 + b⁻¹⁰)/deg and explicit
weights, and J_{ϱ+1}(p,q) = ⟨`normCorrelation` σ W p, `normCorrelation` σ W q⟩ whenever σ ∈ U(X₀ ⊕
ℂz), p_ϱ = q_ϱ = h(z, σz). -/
def HasBandLimits J := SieveSystem unitOrOne (·⁻¹.1) 𝔰.ϱ J wave ((1 + b⁻¹ ^ 10) / deg) (headWeight
  (𝔰.n ^ 6)) (fun ξ ↦ 𝔰.bandConst * b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) ‖ξ‖⁻¹) ∧
  ∀ σ ∈ GT 𝔰.ϱ, ∀ p q, realFrameGram σ 𝔰.top 𝔰.top = p 𝔰.ϱ →
  q 𝔰.ϱ = p 𝔰.ϱ → J 𝔰.n p q = inner ℂ (normCorrelation σ W p) (normCorrelation σ W q)

/-- The Bessel function, or its cut. -/
class inductive Side | full | cut

/-- Continuous Bessel functions, full and cut: squared L² norms |I| and ≤ |I|, the full one
integrable, the cut supported in `InCut`, L²-close, with a controlled 𝖴-invariant
majorant. -/
structure IsCutPair rep (W : Side → C(𝔰.G₁, EuclideanSpace ℂ I)) where
  isBesselFunction t : IsBesselFunction rep (W t)
  integrable : Integrable (W .full) besselQuotMeasure
  lintegral_sq_full_eq : ∫⁻ y, ‖W .full y‖ₑ ^ 2 ∂besselQuotMeasure = card I
  lintegral_sq_cut_le : ∫⁻ y, ‖W .cut y‖ₑ ^ 2 ∂besselQuotMeasure ≤ card I
  inCut_of_ne_zero y : W .cut y ≠ 0 → InCut y b
  lintegral_sq_sub_le : ∫⁻ y, ‖W .cut y - W .full y‖ₑ ^ 2 ∂besselQuotMeasure ≤
    .ofReal (b⁻¹ ^ (5 * 𝔰.r ^ 2)) ^ 2 * card I
  exists_majorant : ∃ A, ∃ m : Measure _, Measurable A ∧ besselU.FixesLeft A ∧ (∀ t y,
    ite (W .full y = W .cut y) 1
    (.ofReal (b ^ (3 * 𝔰.r ^ 3 * f))) * ‖W t y‖ₑ ≤ A y) ∧ (∀ y, A y ≤ m {g | InCut (y * g) b}) ∧
    IsFiniteMeasure m ∧ m univ * ∫⁻ y, A y ∂besselQuotMeasure ≤ .ofReal (b ^ (2 * 𝔰.r ^ 3)) * card I

variable (𝔰)

/-- A full and a cut Bessel function on G₁ for an irreducible rep, with `IsCutPair`, Schur
bounds |I|/deg for derivatives (`HasSchurBound`), 8·rank ≤ b, and band limits `HasBandLimits`. -/
structure BesselSystem where
  (I) [fintype : Fintype I] [nonempty : Nonempty I]
  W : _ → C(𝔰.G₁, EuclideanSpace ℂ I)
  (deg : ℝ) (deg_pos : 0 < deg) (rep) tail : IsCutPair b f rep W
  irreducible M : (∀ h, Commute M (rep h).1) → M ∈ range (scalar I)
  hasSchurBound : ∀ P ≥ b ^ 5, HasSchurBound (W .full) rep P (.ofReal deg⁻¹ * card I)
  eight_mul_rank_le : 8 * 𝔰.r ≤ b
  (bandLimit) band_limits : HasBandLimits b (W .cut) deg bandLimit

attribute [instance] Side.full BesselSystem.fintype BesselSystem.nonempty

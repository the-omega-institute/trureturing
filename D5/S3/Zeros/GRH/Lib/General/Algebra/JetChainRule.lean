/- GID: D5/S3/Zeros/GRH/Lib/General/Algebra/JetChainRule
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Algebra/JetChainRule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Algebra.JetChainRule. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Algebra/JetChainRule.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Algebra.ZerosCostDegree
import D5.S3.Zeros.GRH.Lib.CM.Sigma.PadicSeriesDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore).

Chain rule for power series substitution; jets under linear substitution. -/

open Finset MvPowerSeries WithPiTopology

open scoped PowerSeries

variable {p : ℕ} [Fact p.Prime] {σ R S} [CommRing R] [CommRing S] {ι} [Fintype ι]

lemma mem_range_seriesToCp {f : ℂ_[p]⟦X⟧} : f ∈ seriesToCp.range ↔ ∀ n, ‖f.coeff n‖ ≤ 1 :=
    ⟨fun ⟨g, e⟩ _ ↦ e ▸ (g _).2, (⟨fun d ↦ ⟨_, d.unique_single ▸ · _⟩, rfl⟩)⟩

lemma map_pderiv (Ψ : R →+* S) (i : σ) f : MvPowerSeries.map Ψ (pderiv i f) = pderiv i
    (MvPowerSeries.map Ψ f) := MvPowerSeries.ext (by simp [coeff_pderiv])

@[simp] lemma isUnit_integer_iff_norm_eq_one {c : valRingCp p} : IsUnit c ↔ ‖c.1‖ = 1 :=
  Valued.integer.isUnit_iff_norm_eq_one

@[simp] lemma constantCoeff_linearSeries [Fintype σ] (c : σ → R) :
  constantCoeff (linearSeries c) = 0 := by simp [linearSeries]

attribute [simp] jet_monomial hasSubst_of_constantCoeff_zero

@[simp] lemma pderiv_subst {a} (ha : @HasSubst ι σ R _ a) k (F : MvPowerSeries ι R) :
  pderiv k (subst a F) = ∑ i,
  (pderiv i F).subst a * pderiv k (a i) := let : UniformSpace R := ⊥
  have := continuous_subst
  denseRange_toMvPowerSeries.induction_on F (by apply isClosed_eq <;> simp [pderiv] <;> fun_prop
    [pderivFun]) (by simp_intro Q [pderiv_coe, subst_coe]; apply Q.induction_on <;> simp_all
    [add_mul, mul_sum, apply_ite, mul_assoc])

variable {ι : Type} {κ} {R : Type} [CommRing R] [Fintype ι]

/-- Chain rule for a linear substitution: for a matrix M, the jet along P of F(Mz) equals the
jet of F along the polynomial P(Mᵀx). -/
lemma jet_subst_linearSeries [Fintype κ] (M : Matrix ι κ R) P : ∀ F,
  jet R P (subst (linearSeries <| M ·) F) = jet R (linSubst M P) F := by apply
  P.induction_on <;> simp_all [linSubst, linearSeries, ↓jet_mul_X, mul_sum, jet_eq_sum,
  constantCoeff_subst, finsum_eq_single _ default, prod_pow_eq_pow_sum, Finsupp.ne_iff, pderiv_X]

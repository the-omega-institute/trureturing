import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.ZerosCostDegree
import OmegaMath.NumberTheory.GRH.Lib.CM.Sigma.PadicSeriesDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

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

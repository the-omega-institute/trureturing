import GRH.Lib.CM.KroneckerLimit.LogTheta
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Local heights and Tate's trick; integrality of CM theta functions and torsion
translates (known result; see Lib.CM.LocalHeight.IntegralParameter).

This file: Integral series in the formal parameter along linear forms; Euler's addition formula. -/

open MvPowerSeries Finset Fin

namespace CMLattice

variable {d} [PrimeSevenModEight d] {C : CMLattice d} {p} [Fact p.Prime] [PadicPlace p] {I X : Type}
  [Fintype I] [Fintype X] (μ : I → X → ℂ_[p])

attribute [scoped simp low] sum_univ_four PowerSeries.coe_substAlgHom

/-- The ring 𝔬[[φ(μ_i)]] of series over ℂ_p: integral power series in the series φ(∑_x μ_{i,x}
z_x), i ∈ I. -/
noncomputable def multiPhiRing := ((substAlgHom (a := (taylorVia ιₚ C.translatedWpDeriv).subst ∘
  linearSeries ∘ μ) (by simp)).1.comp (@seriesToCp p ..)).range

omit [PrimeSevenModEight d] in
lemma subst_mem_multiPhiRing {v} : v ∈ C.phiSeriesRing → ∀ i,
  v.subst (linearSeries (μ i)) ∈ C.multiPhiRing μ := fun ⟨g, e⟩ i ↦ e ▸ ⟨g.subst fun _ ↦ .X i, by
  simp (disch := simp) [map_subst, subst_comp_subst_apply, PowerSeries.subst_comp_subst_apply]; rfl⟩

/-- Euler's addition formula, integral form: read in ℂ_p, the series φ(u + w) lies in 𝔬[[φ(u),
φ(w)]]. -/
lemma translatedWpDeriv_add_mem_multiPhiRing :
  (taylorVia ιₚ C.translatedWpDeriv).subst (linearSeries 1) ∈ C.multiPhiRing !![1, 0; 0, 1] := by
  convert_to _ ∈ ?S
  let x i : ?S := ⟨_, subst_mem_multiPhiRing _ C.taylorVia_translatedWp_mem_phiSeriesRing i⟩
  let y i : ?S :=
    ⟨_, subst_mem_multiPhiRing _ C.isSeriesGenerator_translatedWpDeriv.generator_mem i⟩
  let a : ?S := ⟨_, .C ⟨_, C.norm_a₁_le_one⟩, rfl⟩
  have (i : Fin 2) := congr(($(C.taylorVia_curve_eq ιₚ)).toMvPowerSeries i)
  let m := univ.prod x
  have ⟨u, hu⟩ := (@IsLocalRing.isUnit_one_sub_self_of_mem_nonunits ?S _ (LocalSubring.range _).2
    m (by simpa [m, x, translatedWp] using ·.map (constantCoeff.domRestrict _))).exists_left_inv
  convert ((1 + m * u) ^ 2 * ((1 + m) * 1 ⬝ᵥ y - a * univ.prod y) + u ^ 3 * ((1 + 1 + 1 + m) *
    1 ⬝ᵥ x + a * a * m) * (x ⬝ᵥ y ∘ rev + a * m)).2
  apply_fun fun E ↦ (E.pderiv 0 - E.pderiv 1, E.rescale (↑)); ext1
  any_goals simp +zetaDelta [PowerSeries.subst, linearSeries, ← PowerSeries.derivative.eq_def,
    Derivation.leibniz_of_mul_eq_one _ congr(($hu).1), Subtype.ext_iff] at *
  simp_all [← PowerSeries.subst.eq_def, ← PowerSeries.toMvPowerSeries_eq_subst, map_ofNat]; grind
  simp [rescale_eq_subst, subst_comp_subst_apply, ← Pi.zero_def, translatedWp, subst_add]
  intro E F h; ext D; induction e : D 0 generalizing D
  simpa [*] using congr(($h).2.coeff D)
  simpa [coeff_pderiv, *, tsub_add_cancel_of_le, Nat.cast_add_one_ne_zero] using
    congr(($h).1.coeff (D - .single 0 1 :))

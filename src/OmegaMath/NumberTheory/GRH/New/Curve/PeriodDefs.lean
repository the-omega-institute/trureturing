import OmegaMath.NumberTheory.GRH.New.Data.WeilDataOfE
import OmegaMath.NumberTheory.GRH.Lib.ClassField.HeckeL.AutCharLFunction
import OmegaMath.NumberTheory.GRH.Lib.CM.FormalGroup.FormalHeight
import OmegaMath.NumberTheory.GRH.Lib.Weil.Construction.FockThetaFunctions
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: The number s₀, an f-th root of `chiFin`(α)⁻¹, and its absolute value. Names for the
curve, its period and the scale of derivatives. -/

/-- The principal f-th root of the complex number υ(α)⁻¹|α|^(1/2), where α = `Parameters.α` and f
is the number of infinite places of E. -/
noncomputable def Parameters.vacuumRoot P s := (chiFin (α P s))⁻¹ ^ (numInfPlaces (P.E s) : ℂ)⁻¹

open NumberField Real

/-- Every automorphism σ of ℂ over K preserves the absolute value of s₀ = `Parameters.vacuumRoot`:
|σ(s₀)|² = rootDiscr(E)/√d. -/
lemma Parameters.norm_gal_vacuumRoot P s (σ : Gal(ℂ/K P)) : ‖σ (vacuumRoot P s)‖ ^ 2 =
  rootDiscr (P.E s) / √P.d := by
  obtain ⟨k, h, ⟨⟩⟩ := WeilData.exists_chiFin_pow_eq_prod (P.α s)
  erw [rootDiscr, ← pow_left_inj₀, div_pow, ← prod_varpi_eq_rootDiscr_pow, pow_right_comm,
    ← norm_pow, ← map_pow]
  simp [vacuumRoot, by simpa [h.ne'] using congr(‖$(σ.commutes ⟨chiFin (P.α s) ^ k, by simp_all
    [prod_phi_eq_norm]⟩)‖)]
  simpa [ideleAbs_toAdele, Finset.prod_pow, infinitePlace_apply_varpi, chiFin, Circle.norm_coe,
    ← InfinitePlace.apply, Finset.prod_nonneg, NeZero.ne, chiAdelic, field] using
    (ideleAbs_eq_prod_of_v_eq_one (x := finIdeleIncl _ * star (finIdeleIncl _) * .map toAdele.1
    (.mk0 _ (P.relDifferentGen_ne_zero s))) (by simpa using v_alpha_mul_relDifferentGen) :)
  repeat positivity

/-- A chosen CM datum whose lattice is a complex multiple Ω₀𝓞_K of 𝓞_K: the curve 𝓔 = ℂ/Ω₀𝓞_K. -/
noncomputable def Parameters.cmCurve (P : Parameters) :=
  (@QuadField.exists_latticeModule_eq_scaledIdeal P.d _ 1).choose

/-- A chosen nonzero complex number with the lattice of 𝓔 equal to Ω₀𝓞_K. -/
noncomputable def Parameters.Ω₀ (P : Parameters) :=
  (@QuadField.exists_latticeModule_eq_scaledIdeal P.d _ 1).choose_spec.choose

/-- The number (2π/√d)^{1/2}, as a unit of ℂ. -/
noncomputable def Parameters.areaScale (P : Parameters) : ℂˣ :=
  .mk0 √(2 * π / √P.d) (by simp [pi_nonneg, NeZero.ne])

/-- The number s₁ = s₀/u₀, with s₀ = `Parameters.vacuumRoot` and u₀ the unit chosen from
`CMLattice.chowla_selberg` for the curve 𝓔 (`Parameters.cmCurve`). -/
noncomputable def Parameters.periodFactor (P : Parameters) s :=
  P.vacuumRoot s / P.cmCurve.chowla_selberg.choose

/-- The number per = s₁(2π/√d)^{1/2}/Ω₀, the scale at which Taylor series of theta functions are
taken. -/
noncomputable def Parameters.jetScale (P : Parameters) s := P.periodFactor s * P.areaScale / P.Ω₀

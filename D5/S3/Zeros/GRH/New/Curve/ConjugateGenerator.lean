/- GID: D5/S3/Zeros/GRH/New/Curve/ConjugateGenerator
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/ConjugateGenerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.ConjugateGenerator. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/ConjugateGenerator.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.ThetaProducts
import D5.S3.Zeros.GRH.New.Curve.FrameSections
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known results stated on this proof's data: Galois action on CM theta functions and on the finite
Weil representation (known result; see Lib.CM.Reciprocity.SemilinearWeilLaw).

This file: Galois action on translates of a theta product; integral bounded scaled vacuum values. -/

namespace Parameters

open Real NeZero Space CMLattice Finset Submodule MvPowerSeries Fintype Set Notation

/-- The real number Ω = `Parameters.bigOmega` attached to the parameters P and the exponent s is
positive. -/
lemma bigOmega_pos {P s} : 0 < bigOmega P s := by simp [bigOmega, rootDiscr_pos, pi_pos, exp_pos]

/-- The scale per of the derivatives is non-zero, for all parameters and every s. -/
@[simp] lemma jetScale_ne_zero {P s} :
  jetScale P s ≠ 0 := by simpa [jetScale, periodFactor, ne_of_gt, rootDiscr_pos, ne] using
  (congr($(P.norm_gal_vacuumRoot s 1) / $(P.cmCurve.chowla_selberg.choose_spec.2 1) ≠ 0)).mpr

/-- Some C and, for each s, adeles b_σ serve all standard V of rank n: some c ≠ 0 makes the
values of c·vac integral, with K-conjugates ≤ e^{CN₁²n}; translates of some F ∈ 𝒲_f, θF = 1,
span 𝒲_f; and σT_per ϱ(x)F = T_t ϱ(b_σx)F′ (places permuted), some F′ ∈ 𝒲_f, |t|² = 1/Ω.
Here T_a = `Space.jetSeries` a, per = `Parameters.jetScale`, 𝒲_f = `Space.finitePart`. -/
lemma exists_isJetConjugate_generator P : ∃ C : ℕ, ∀ s, ∃ B : _ → 𝔸f (P.E s), ∀ {n} [Fintype n] {ε}
  (V : Space _ n ε) [V.IsStd], (∃ c ≠ 0, (∀ p [Fact p.Prime] [PadicPlace p] x, ‖ιₚ (c * V.vacElem
  (finVec x))‖ ≤ 1) ∧ ∀ (σ : Gal(ℂ/K P)) x, ‖σ (c * V.vacElem (finVec x))‖ ≤ rexp (C * P.N₁ s ^ 2) ^
  card n) ∧ ∃ F ∈ V.finitePart, V.θ F = 1 ∧ V.finitePart ≤ span ℂ (.range fun x ↦ V.ϱ (finVec x)
  F) ∧ ∀ σ : Gal(ℂ/K P), ∃ t, ∃ F' ∈ V.finitePart, ‖t‖ ^ 2 = (P.bigOmega s)⁻¹ ∧ ∀ x, IsJetConjugate
  σ (placePerm s σ) (P.jetScale s) t (V.ϱ (finVec x) F) (V.ϱ (finVec (B σ • x)) F') := by
  choose Ω hA e he β a hb H using (complex_multiplication_theta _ · latticeModule_cmCurve)
  refine (isAlgebraic_of_padic fun _ ↦ @norm_a₁_le_one _ _ P.cmCurve _ _ ⟨_⟩).elim fun p hp ↦
    (isCompact_iUnion fun x : p.rootSet ℂ ↓∩ .range (@a₁ P.d) ↦
    IsAppellHumbert.isCompact_range_norm_thetaShift (x.2.choose.monomialSection_mem
    (1, 0))).bddAbove.imp' (⌈·⌉₊ + 4) fun M hm s ↦ ⟨finAdeleIncl .. ∘ β, fun V _ ↦ ?_⟩
  let N := P.N₁ s
  have fr (e : ℕ+) := exists_finitePart_of_isTightFrame V (N * e) (ne ((N * e) ^ 2)) (by simp [sq])
    (P.isTightFrame_zeta_pow s N).repeat_vectors (fun _ ↦ (1, 0)) (by simp)
  obtain ⟨F, W, hF, hI, K, x, m, -, hJ, hs⟩ := fr 1 omega₀_mem_cmCurve_lattice
    (by simp [QuadField.area_eq_of_eq_scaledIdeal latticeModule_cmCurve, field, N, ne])
  have h1 := by simpa [monomialSection] using (hF 0).1
  obtain ⟨j, hj⟩ := by simpa [h1] using
    (congr(V.dataInner V.vacElem $(hs V.θ)).symm.trans (map_sum ..)).trans ∘ sum_eq_zero
  have hc := (hs ((m⁻¹ : ℂ) • V.dataInner V.vacElem ∘L V.ϱ (finVec (-x j)))).symm
  set c : ℂ := _ * _
  simp [hj, ↓rho_finVec, congr($(V.heisRep_right_rho _) _) ▸ (V.dataInner_rho_of_vacElem _).trans
    ((adelicSum ..).vac_equiv _), realVac, stdLattice.finVac, ← sum_filter] at hc
  refine have c0 := by simp [c, hj]
    (forall_and.1 fun σ ↦ ?_).imp (⟨c, c0, ?_, ·⟩) (⟨F, W, h1, ?_, ·⟩)
  refine (fr (e σ) (he σ) (by simp [hA, field, N, ne])).elim fun _ ⟨W', h', _⟩ ↦ (fun J ↦ ⟨fun _ ↦
    ?_, σ (P.periodFactor s) / Ω σ * P.areaScale, _, W', ?_,
    J⟩) (denseRange_finiteImage.induction_on · ⟨(isLocallyConstant_rho_finVec
    W).comp₂ ((isLocallyConstant_rho_finVec W').comp_continuous (by fun_prop)) (IsJetConjugate _ _ _
    _) Not⟩ fun γ ↦ ?_)
  any_goals simp_rw [← V.smul_apply, hc, ← θ_ϱ, map_sum]
  · grw [norm_sum_le, sum_le_card_nsmul _ _ (M.exp ^ _), card_le_univ, hJ]; swap
    simp_intro .. [↓rho_finVec, by simpa [rho_finVec_mem_finitePart, W, W'] using
      (congrArg constantCoeff <| J ·)]
    rw [← θ_ϱ, ← (exists_finiteImage_approx W' _).choose_spec.2, (h' _).1, norm_prod,
      ← prod_const]; gcongr
    grw [← add_one_le_exp, ← hm
      ⟨_, ⟨⟨σ • ⟨_, p.mem_rootSet.2 hp⟩, exists_galConjugate ..⟩, rfl⟩, _, rfl⟩]; bound
    simp; grw [le_exp_log N, log_le_self, Nat.le_ceil M, ← numInfPlaces, card_infinitePlace_E,
      Nat.totient_le] <;> simp [← exp_add, ← exp_nat_mul]; clear * -; grind
  convert congr($(P.norm_gal_vacuumRoot s σ) * π / $(P.cmCurve.chowla_selberg.choose_spec.2
    σ)) <;> clear * - hA <;> simp [hA, periodFactor, areaScale, bigOmega, div_pow, mul_pow,
    pi_nonneg] <;> field [ne]
  let t i j := -Algebra.trace P.K _ (γ i * star (P.ζ s ^ @Fin.val N j)) / N
  choose T g h₂ using ((hb σ).frequently ((by fun_prop :
    ContinuousAt (finAdeleIncl _ (P.E s) · • finiteImage γ) _).eventually
    ((isLocallyConstant_rho_finVec W').eventually_eq _))).forall_exists_of_atTop (image₂ t ⊤ ⊤)
  erw [← h₂, adeleMap_algebraMap, algebraMap_smul, ← map_smul]
  simp [IsJetConjugate, hF, ↓h', map_subst, PowerSeries.subst, rename_eq_subst,
    subst_comp_subst_apply]
  congr! 3 with i
  · simp [← rename_eq_subst, linearSeries, ↓smul_eq_C_mul]
    apply Fintype.sum_equiv ((placePerm s σ).prodCongr 1); rintro ⟨⟩
    simp [jetScale, starRingEnd_apply, ← map_star_complex, placePerm_spec, apply_ite σ,
      ← smul_eq_C_mul]; field_simp
  convert! H σ T (t i.2 i.1.1) (g (by simp)) using 2 <;>
    simp [t, monomialSection, coe_trace_eq_sum, -star_ζ, mul_assoc, ← mul_sum] <;> field_simp
  iterate 2 simp [IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg, ↓rho_finVec, *, finitePart,
    span_le,
    (eq_inv_smul_iff₀ c0).2 hc, finHeisOp, smul_sum, smul_smul, sum_smul_mem, mem_span_of_mem]

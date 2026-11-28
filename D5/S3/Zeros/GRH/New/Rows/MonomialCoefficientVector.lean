/- GID: D5/S3/Zeros/GRH/New/Rows/MonomialCoefficientVector
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/MonomialCoefficientVector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.MonomialCoefficientVector. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/MonomialCoefficientVector.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.GluedFormTheta
import D5.S3.Zeros.GRH.New.Seesaw.BesselGeneric
import D5.S3.Zeros.GRH.New.Selmer.RankOneDenominator
import D5.S3.Zeros.GRH.New.Exchange.RowLadder
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

Set-up for this proof: size bookkeeping for the data of this proof.

Part of: Each ratio of Hecke values repays one direction (see New.Rows.HeckeValueHeight).

This file: Crude exponential bounds for conjugates of cleared L-values. Integrality and size bounds
pass through translation and projection to good types. Integral invariant vector that reads the
coefficient of a monomial in given rows. -/

open Nat Fint Fintype Function PolyRep Ideal LValueData Matrix MvPolynomial AuxPair LevelPlaces Real

/-- Let all c_τ = z and |n| = 2z ≥ 4 (`Data.Pair.IsFlat`). Then every conjugate under Aut ℂ of the
normalised value `Data.Pair.intAlgPart` at the trivial twist has modulus at most exp(x^34). -/
lemma Data.Pair.norm_conj_intAlgPart_le {P} {D} {p : @Pair P D} {n} [Fintype n] (H :
  p.IsFlat n) (σ : ℂ ≃+* ℂ) : ‖σ (intAlgPart H.2 .one)‖ ≤ exp (D.x ^ 34) := by
  let X := trivialLift H.2 .one
  have k σ : X.normSqAt σ ≤ _ :=
    classSum_le_card_mul_sq fun _ ↦ by grw (transparency := default) [trivialLift_apply,
    sqrt_weylNormSq_sum_le, (P.norm_jet_le_of_isAdmissibleComb (hb := b_hasWeight _)
    (P.isAdmissibleComb_vacuumDatum 1 (by grind -abstractProof [levelIndicator, norm_one, norm_zero])) ..).2 1
    (LValueData.isLiftWeight _), Fintype.card_fun, card_levelModulus_resRing, prod_q_chosenPlace,
    prod_eq_one _ nofun, (by aesop : AuxPair.κ _ = 0), (congrArg _ (by simp [_root_.funext_iff,
    weylEval, nablaBasis_eq_one])).trans (weylNormSq_weylEval_permArray (rowPos _))]
  have := X.norm_map_inner_le X
  simp [intAlgPart, twist_one_spec, diagramWeight, ← card_eq_fintype_card, Nat.card_pi] at *
  grw [this, k, k, mul_self_sqrt (by bound),
    D.card_stdClasses_le_exp (D.principalLevel_le_chosenLevel ⟨_, rfl⟩), prod_eq_one _ nofun,
    D.card_stdClasses_le_exp (principalLevel_le_levelOf (·.rec (mul_mem_right _ _ ·.2.2.1) nofun))
    (H.2.1 ▸ D.nat_le_of_hasLogBound), ← le_exp_of_log_le]
  simpa [denomBound, H, log_mul, NeZero.ne] using D.le_of_hasLogBound

lemma Data.iota_goodProjTranslate_apply {P} {D : Data P} ϑ s z g : (ι ϑ (D.goodProjTranslate s
  z).1).1 g = ∑ t, (Nat.card D.G * D.e₀.coeff t) • (ι ϑ z).1 (g * groupLift ϑ (t * s)) := by
  simp [asAlgebraHom_eq_sum, ← Module.End.mul_apply, ← map_mul, iota_principalRep, Finset.smul_sum,
    mul_smul]

/-- Passage to the good part keeps integrality: for j : ℂ → ℂ_l, a twist ϑ, a in ℂ, s in 𝖦 =
`Data.G` and z in `Data.principalForms` on Y₀, if a·ι(z) is integral at j (ι = `iotaAtLevel` ϑ),
so is a·ι(|𝖦|e₀sz), with e₀ =
`Data.e₀`. -/
lemma Data.goodProjTranslate_mem_integralForms {P} {D : Data P} {l} [Fact l.Prime] (j :
  PadicPlace l) {ϑ} {a : ℂ} {z} (h : a • iotaAtLevel ϑ z ∈ LevelForm.integralForms j) s :
  a • iotaAtLevel ϑ (D.goodProjTranslate s z).1 ∈ LevelForm.integralForms j := fun _ ↦ by
  erw [weylGauge_smul, iota_goodProjTranslate_apply, ← weylGauge_smul,
    Finset.smul_sum]; apply weylGauge_sum_le <;> intros; simp
  grw [smul_comm, weylGauge_smul, norm_le_one_of_isIntegral, one_mul, ← weylGauge_mul]
  exacts [h _, Kf_le_localLevel (groupLift ..).2, norm_nonneg _,
    D.isCentralProj_e₀.isChar.isIntegral _]

/-- For the trivial twist, σ in Aut ℂ and s in 𝖦: if all values of σι_μ(z) have squared norm at
most e^B, then σι_μ(|𝖦|e₀sz) has squared class-sum norm at most exp(x^99 + B). -/
lemma Data.normSqAt_goodProjTranslate_le {P} {D : Data P} {σ : ℂ ≃+* ℂ} {z s B} (h : ∀ g,
  weylNormSq (σ ∘ (D.ι .one z).1 g)
  ≤ exp B) : (D.iotaAtLevel .one (D.goodProjTranslate s z).1).normSqAt σ ≤ exp (D.x ^ 99 + B) := by
  have k s := by simpa [apply_ite, inv_mul_eq_one] using (Finset.single_le_sum (by simp)
    (Finset.mem_univ s)).trans ((D.isCentralProj_e₀.map σ).sum_norm_conv_le (.id _)
    (Pi.single 1 (1 : ℂ)))
  grw [LevelForm.normSqAt, classSum_le_card_mul_sq fun g ↦ by
    erw [iota_goodProjTranslate_apply]; grw [sqrt_weylNormSq_sum_le]; simp [-Fintype.card_pi]; grw
      [h, k], D.card_stdClasses_le_exp
    (principalLevel_le_levelOf (·.rec (mul_mem_right _ _ ·.2.2.1) nofun)) (D.card_Y_le .refl)]
  simp [exp_add, ← card_eq_fintype_card, field, exp_nonneg]
  grw [Nat.le_of_dvd Fin.pos' (D.card_GL_dvd_chosenGroupOrder D.nat_le_of_hasLogBound),
    le_exp_log D.chosenGroupOrder]; use D.le_of_hasLogBound D.lt_of_hasLogBound

attribute [-simp] map_nablaBasis

attribute [local simp↓] Finsupp.prod_mapDomain_index_inj Injective.eq_1 coeff_map rename_monomial
  fockPairing_monomial fockPairing_rowSubst diagramWeight mem_nabla mul_pow pow_add borelMul

/-- For a monomial α in rows e of degree dg_τ at each τ, some integral vector has Fock
polynomial (∏_τ dg_τ!/α!) times that monomial and is fixed, over any characteristic 0 field,
by all g whose columns e are those of 1. -/
lemma exists_int_vector_harmonicPoly_eq {P} {D : Data P} {n} [Fintype n] (X :
  LValueData D.E n) {r} (e : Fin r ↪ n) {α : _ →₀ ℕ} (hα : ∀ τ, ∑ i, α (τ, i, ()) = X.jetDeg τ) :
  ∃ v : _ → ℤ, X.auxPair.harmonicPoly (star ((↑) ∘ v)) = ((∏ τ, (X.jetDeg τ)!) / α.prod fun _ k ↦
  (k ! : ℂ)) • renameRowsCols e id (monomial α 1) ∧ ∀ {R} [Field R] [CharZero R]
  {g : _ → GL n R} {w}, w = (↑) ∘ v → (∀ i a b, (g i).1 b (e a) = ite (b = e a) 1 0) →
  weylRep _ X.auxPair.detExp g *ᵥ w = w := ⟨fun k ↦ (nablaBasis ℤ _ _ k).coeff ?δ,
  rename_injective _ (by simp) ((X.toPoly_eq_rename_harmonicPoly _).symm.trans ((range_toPoly.ge
  (by simp [aeval_monomial, X.one_lt_card, mixedWeight, ← hα, ← Finsupp.prod_finsetSum_index,
  prod_prod_type, ← Finset.prod_pow_eq_pow_sum]; intros; ring)).elim fun ξ m ↦ .trans (congrArg _
  (funext (by simpa [m, field, ← map_nablaBasis (algebraMap ℤ ℂ), X.hookNumber_eq_prod_factorial,
  Finset.prod_eq_zero_iff] using fockPairing_toPoly_nablaBasis ξ))) m)), fun {R _ _ g w} k h ↦ by
  simpa [k, funext_iff, ↓← sum_schur_smul_nablaBasis, weylRep, coeff_sum, mulVec_eq_sum,
    ← map_nablaBasis (algebraMap ℤ R)]
    using congr(fockPairing R $(show IsFixedPt (rowSubst (g · |>.1.transpose)) (monomial ?δ 1) by
    simp [IsFixedPt, rowSubst, h, monomial_eq]) ∘ nablaBasis R _ _)⟩

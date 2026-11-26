import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdelicModulus
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hecke L-functions: Euler product, continuation to s = 1, non-vanishing, prime densities
(known result; see Lib.ClassField.HeckeL.HeckeContinuation).

This file: Adelic theta sum of a tent; Riemann-sum estimate replacing Poisson summation. -/

noncomputable section

open NumberField MeasureTheory Measure Metric mixedEmbedding Set ENNReal Module Algebra AddSubgroup
  ContinuousLinearMap Units Continuous Real


/-- The subgroup of principal ideles: the image of K^× in the idele group. -/
def principalIdeles K [Field K] [NumberField K] :=
  ((map (mixedEmbedding K).1).prod principalIdele).range

variable {K} [Field K] [NumberField K] (r : ℝ) (d : (𝔸f K)ˣ) (a : (mixedSpace K)ˣ × (𝔸f K)ˣ)

/-- The module of an idele: the absolute value of the norm to ℝ of its infinite part times the
module of its finite part. -/
def ideleModule :=
  (normHom.toMonoidHom.comp ((norm ℝ).comp (coeHom (mixedSpace K)))).coprod (@finIdeleAbs K _ _)

/-- The function on adeles x = (x_∞, x_f) equal to the tent max(r − dist(x_∞, 1), 0) if x_f lies
in 1 + d⁻¹Ô, and 0 otherwise. -/
@[simp] def adelicTent (x : mixedSpace K × _) :=
  ite (d.1 * (x.2 - 1) ∈ Ô K) (max (r - dist x.1 1) 0) 0

deriving instance PolishSpace for mixedSpace K

@[simp] lemma ideleModule_pos : 0 < ideleModule a :=
  mul_pos (a.1.map (norm ℝ)).norm_pos ideleAbs_pos

@[fun_prop] lemma continuous_ideleModule : Continuous (@ideleModule K _ _) :=
  (continuous_det.comp ((mul ℝ (mixedSpace K)).2.comp continuous_val)).abs.fst'.mul
  (continuous_ideleAbs.comp (units_map _ (prodMk_right _))).snd'

@[fun_prop] lemma continuous_adelicTent : Continuous (adelicTent r d) := (IsClopen.preimage
  ⟨isCompact_Ô.isClosed, isOpen_Ô⟩ (by fun_prop)).continuous_indicator (by fun_prop)

lemma measurePreserving_idele_mul :
  MeasurePreserving (a.map val val * ·) volume (ENNReal.ofReal (ideleModule a)⁻¹ • volume) := by
  simpa [ideleModule, prod_smul_left, prod_smul_right, mul_smul, ofReal_mul',
    genIndex_eq_inv_distribHaarChar, genIndex_eq_inv_finIdeleAbs] using!
    MeasurePreserving.prod ⟨(LinearMap.continuous_of_finiteDimensional _).measurable,
    map_linearMap_addHaar_eq_smul_addHaar _ (a.1.map (norm
    ℝ)).ne_zero⟩ ⟨by fun_prop, map_smul_eq_inv_distribHaarChar_smul (ν := @volume (𝔸f K) _) a.2⟩

@[simp] lemma ideleModule_principal_eq_one : ∀ γ : principalIdeles K,
  ideleModule γ.1 = 1 := by simp [principalIdeles, ideleModule, field]; simp [← map_mul,
  norm_eq_matrix_det (latticeBasis K), Matrix.det_apply', norm_eq_matrix_det (integralBasis K),
  leftMulMatrix_eq_repr_mul, latticeBasis_repr_apply]

lemma hasCompactSupport_adelicTent_mul : HasCompactSupport (adelicTent r d <| a.map val val * ·) :=
  .intro (.prod ((isCompact_closedBall 1 r).preimage_smul a.1) (((isCompact_Ô.preimage_smul
  d).image_auto (· + 1)).preimage_smul a.2)) (by simp [Units.smul_def, sub_eq_add_neg]; grind)

/-- For 0 < r < 1 the principal ideles are discrete and, with Θ_r(b) = ∑_γ `adelicTent` r d (γb)
over them, some δ > 0, C satisfy: each l > 0 has an i with |i − Θ_{r/3}(b)| ≤ C l^δ |Θ_r(b)| for all
ideles b of module l. -/
lemma exists_abs_sub_thetaSum_le (h : 0 < r) (hr :
  r < 1) : let Θ r b := ∑' γ : principalIdeles K, adelicTent r d ((↑γ * b).map val val)
  DiscreteTopology (principalIdeles K) ∧ ∃ δ > (0 : ℝ), ∃ C, ∀ l > 0, ∃ i, ∀ b, ideleModule b = l →
    |i - Θ (r / 3) b| ≤ C * l ^ δ * |Θ r b| := let j := ((mixedEmbedding K).prod _).toAddMonoidHom
  have := prod.instIsAddHaarMeasure (@volume (mixedSpace K) _) (@volume (𝔸f K) _)
  have ⟨R, p, H@⟨_, F, hR, mF, v, uF⟩⟩ :=
    exists_hasFundDomain (mixedEmbedding K) ⟨1, .id _, by simp⟩
  have := H.isCovolOneLattice.1
  have hD := IsAddFundamentalDomain.mk' (μ := volume) mF.nullMeasurableSet
    ((j.ofInjective (RingHom.injective _)).existsUnique_congr_right.1 <| uF ·)
  let g : _ → j.range := .map _ (by simp [principalIdeles]; tauto)
  have gi : g.Injective := Subtype.map_injective _ (val_injective.prodMap val_injective)
  have gs : ∀ x ≠ 0, x ∈ range g | ⟨_, y, rfl⟩, _ => ⟨⟨_, .mk0 y (by bound), rfl⟩, rfl⟩
  have o ρ := (@isOpen_ball _ _ (j 0).1 ρ).prod (isOpen_Ô.preimage_of_continuous (f := (d.1 * ·)))
  (exists_nat_pos_mul_gt ((o (r / 6)).measure_ne_zero volume ⟨0, by simpa⟩) one_ne_top).elim fun n
    _ ↦ ⟨.of_continuous_injective (by fun_prop) gi, (finrank ℚ K)⁻¹,
    by simp [finrank_pos], R * _, fun l h ↦ let t := (n * l) ^ (finrank ℚ K : ℝ)⁻¹
    ⟨integral (ENNReal.ofReal l⁻¹ • volume) (adelicTent ((r - t * r * R) / 3) d), fun b e ↦ by
  have : 0 < t := by bound
  obtain ⟨x, X, _, Y, γ, z, rfl⟩ := hD.exists_ne_zero_vadd_eq
    ((measurePreserving_idele_mul b).1 (o (t * (r / 6))).measurableSet).nullMeasurableSet
    (by simp_all [↓(measurePreserving_idele_mul _).measure_preimage, ↓v, t, volume,
    IsOpen.nullMeasurableSet, addHaar_ball_mul_of_pos, ↓mixedEmbedding.finrank, finrank_pos.ne',
    Real.rpow_inv_natCast_pow, h.le, mul_assoc, mul_left_comm, ENNReal.mul_inv_cancel_left])
  obtain ⟨γ, rfl⟩ := gs γ z; grw [mul_assoc R, ← mul_rpow n.cast_nonneg h.le, ← le_abs_self,
    show l⁻¹ = (ideleModule (b * ↑γ))⁻¹ by simp [e],
    ← (measurePreserving_idele_mul _).hasLaw.integral_comp (by fun_prop)]
  have c := by simpa [g, vadd_def, mul_add, *] using Y.imp (sub_mem_sub · X.1) ((Ô K).sub_mem · X.2)
  have J {ρ a} := (hasCompactSupport_adelicTent_mul ρ d a).integrable (ν := volume)
  have H ρ (h : ρ ≤ 1 := by bound) := (summable_of_hasFiniteSupport
    (tendsto_coe_cofinite_of_isDiscrete _ ⟨‹_›⟩ (Filter.mem_cocompact'.2 ⟨_,
    hasCompactSupport_adelicTent_mul ρ d (b * γ),
    subset_closure⟩))).hasSum_iff.2 ((gi.tsum_eq (gs · ∘ mt (by simp [·, h]))).symm.trans (.trans
    (by simp [g]; ac_nf) ((Equiv.mulLeft γ).tsum_eq (adelicTent ρ d <| .map val val <| · * b))))
  use (hD.sum_restrict ▸ (hasSum_integral_measure (hD.sum_restrict ▸ J)).sub (H _)
    ).norm_le_of_bounded ((H _).mul_left _) fun y ↦ @Convex.integral_mem _ _ _ _ _ _ _ _ _
    ⟨by simpa⟩ (convex_closedBall ..) isClosed_closedBall (ae_restrict_of_forall_mem
    (mF.const_vadd _) (forall_mem_image.2 fun z u ↦ ?_)) J.restrict
  have := (abs_dist_sub_le _ ((b * γ).1 * y.1.1) 1).trans ((dist_self_add_left
    ..).trans_le (norm_mul_le_of_le c.1.le (by simpa using (hR u).1)))
  simp [vadd_def, add_sub_right_comm, mul_add, abs_le, max_def, dist_eq, add_mem_cancel_right
    (mul_assoc d.1 .. ▸ mul_mem c.2 (hR u).2)] at this ⊢; split_ifs <;> and_intros <;> nlinarith⟩⟩

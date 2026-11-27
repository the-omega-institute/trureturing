/- GID: D5/S3/Zeros/GRH/New/Filling/FillingAdmissible
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/FillingAdmissible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.FillingAdmissible. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/FillingAdmissible.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.GlobalToLocal
import D5.S3.Zeros.GRH.New.Filling.DegreeBounds
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Index and class counts of columns; the filling data are admissible. -/

namespace Data

open Finset Real Filling Subgroup MulAction Fintype Shape NeZero NumberField
variable {P} (D : Data P)

/-- The elements of the stabiliser of the standard lattice of X₀ that preserve the lattice of Y₀
have
index (N^k − 1)^f. -/
lemma relIndex_latStabilizer : (comap D.filling.inclHFin D.filling.latStabilizer).relIndex (Kf ..) =
  (D.N ^ D.k - 1 : ℝ) ^ D.f := by
  rw [(?_ : comap .. = levelOf (↑) (pi ⊤ fun w : D.piPlaces ↦
    (stabilizer _ (Pi.single D.shape.k₀ 1 : _ → ResField w.1)).comap invTransposeGL.toMonoidHom)),
    relIndex_levelOf (h := ⟨by simp, by simp [D.isSplitLevel_piPlaces.star_notMem]⟩)]
  simp [index_pi_univ, index_comap, index_stabilizer_GL_vector, card_ResField,
    D.isSplitLevel_piPlaces.q_eq, ↓card_X₀, card_piPlaces, Fin.pos']
  ext; erw [inclHFin_mem_latStabilizer, mem_levelOf]
  refine exists_prop.symm.trans (exists_congr fun h ↦
    (?_ : _ ↔ ∀ w _, (transposeGL _)⁻¹ ∈ stabilizer ..))
  simpa [funext_iff, Units.smul_def, ↓dvd_def, ← mem_piPlaces, Subtype.ext_iff, -reduceAt_eq_zero]
    using! (forall₂_congr fun (_ : Unit) j ↦ dvd_iff_reduceAt_eq_zero D.intValuation_pi (⟨_,
    h.isIntMatrix (.inr ()) j⟩ - ite (j = D.shape.k₀) 1 0)).trans forall₂_comm

lemma card_classes_filling : card D.filling.Classes =
  Nat.card (D.filling.reducedImage besselH) * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k := by
  erw [card_eq_nat_card, card_classes_eq_classSum D.classAut_columnLevel_eq_bot,
    classSum_one_of_le IsLevel.le, columnLevel_zero_eq_comap, ← relIndex_mul_relIndex _ _ _
    (comap_mono (map_subtype_le _)) fun _ ↦ ((inclHFin_mem_latStabilizer _).1 · |>.1),
    relIndex_comap, map_comap_eq, ← subgroupOf_map_subtype, relIndex_map_map_of_injective _ _ (by
    simp), relIndex_ker, range_inclHFin, classSum_stdRatPoints_eq_mass,
    card_X₀]; simp [D.relIndex_latStabilizer, reducedImage]

/-- The filling data of D satisfies `Filling.IsAdmissible`. -/
instance : D.filling.IsAdmissible := by
  obtain ⟨m, f, p, _⟩ := @mass_pos D.E, @nsmul_le_nsmul_right ℝ, sub_pos.2 (one_lt_pow₀
    (D.lt_of_hasLogBound (G := D.N)) D.k_pos.ne'), pos D.gProd, D.filling.besselDegree_pos,
    rootDiscr_pos D.E, D.filling.frameScaleProd_pos, @Nat.card_pos (D.filling.reducedImage besselH)
    _ _, @card_pos D.filling.BesselCoord _ _, D.N_prime.two_le, Nat.le_self_pow D.k_pos.ne'
    D.N, D.log_N_mem_Icc, D.k_le_r, D.k_pos, log_natCast_nonneg (card D.filling.BesselCoord),
    congr(D.k * D.m * $(mul_div_cancel₀ (∑ v, log (D.nominalWeight v)) (ne ↑D.f)))
  obtain _ := D.card_besselCoord_mul_factorial_le, m D.k, m D.r,
    f (log_natCast_nonneg (D.k - 1).factorial) D.f, f (log_le_log (by positivity)
    (D.le_of_hasLogBound : D.b ^ 19 ≤ D.gProd)) (D.f * D.k), f (log_le_log p (sub_one_lt
    _).le) D.f, (nsmul_right_mono D.f).mapsTo_Icc ⟨(log_le_sub_one_of_pos (div_pos (p.trans
    (sub_one_lt _)) p)).trans (by field_simp; norm_cast; lia),
    (D.le_of_hasLogBound : 2 / D.N ≤ D.logB)⟩, D.log_filling_besselDegree_mem_Icc,
    congr(D.f * ∑ i ∈ $(D.k.Ico_pred_singleton ‹_›), log i.factorial), (nsmul_right_mono (D.f *
    D.k)).mapsTo_Icc D.log_N_mem_window, ((abs_sum_le_sum_abs _ (Ico D.k D.r)).trans (sum_le_sum
    fun i _ ↦ abs_log_mass_ratio_sub_le D.E i D.ϱ D.nat_le_of_hasLogBound (by grind))).trans (by
    grw [le_sub_iff_add_le, ← le_log_one_add_of_nonneg (by positivity)]; simp [*]; use
      D.le_of_hasLogBound : _ ≤ log (1 + D.b⁻¹ ^ 9) - D.f * (2 / D.N)),
    le_sub_iff_add_le.2 (D.le_of_hasLogBound : |D.f * (D.m - 1) * (D.ϱ *
    log (D.gProd * D.rootDisc / 2 / π) + log (√D.rootDisc / 2 / π)) - D.m * ∑ v,
    log (D.nominalWeight v)| + (log 2 + log (1 + D.b⁻¹ ^ 9) + D.m * (D.m * ∑ v, log (D.nominalWeight
    v) + D.f * D.r * D.x⁻¹) + D.f * D.k * √D.logB) ≤ D.f * D.k * D.logB / 4), (D.le_of_hasLogBound :
    D.f * ((D.m - 1) * (D.ϱ * log (2 / D.rootDisc / D.gProd) - log √D.rootDisc) - (D.ϱ + 1) ^ 7 *
    ((D.m - 1) * log (D.gProd * D.rootDisc / 2 / π) - log (D.gProd * D.N))) ≤ D.f * D.k * D.logB)
  apply (by simpa only [← and_imp] using IsAdmissible.mk D.columnLevel_zero_eq_comap (⟨_,
    D.filling_fits.reduction_finiteEquiv_iff _ · |>.2 ⟨_, reduceFamily_liftResidue
    (w := D.chosen) _⟩ |>.2⟩) : _ → _)
  rify [card_X₀, @id (D.filling.g = D.gProd) rfl, abs_kappa_eq, ← InfinitePlace.apply, mk_Φ,
    besselEnergy, codimFactor, columnDim, tailScale, packetConst, card_reducedImage_besselS,
    card_classes_filling, D.relIndex_latStabilizer, siegelConst, Filling.unipCovolume,
    openCellConst, bandConst, ↓card_rowIndex, volU, Shape.k, mainEnergy, volÔ_eq,
    abs_discr_eq_rootDiscr_pow, prod_mul_distrib, prod_div_distrib, prod_pow, prod_pow_eq_pow_sum]
  simp only [filling, P.prod_varpi_eq_rootDiscr_pow, eq_tsub_of_add_eq D.r_add] at *
  iterate 3 use fun _ ↦ D.le_of_hasLogBound
  simp (disch := intros; first | positivity | omega) only [← log_le_log_iff, log_div, log_mul,
    log_pow, log_sqrt, log_rpow, log_exp, log_inv, log_prod, log_one, sum_add_distrib, sum_const,
    card_range, nsmul_eq_mul, sum_range_id, ← Nat.choose_two_right, card_univ, logLevelTarget,
    abs_le, ↓sum_Ico_eq_sub, Set.mem_Icc, sum_sub_distrib, ← mul_sum, sum_singleton, ← sum_mul, ←
    Nat.cast_sum _ (·), ↓sum_range_sub (log <| mass D.E ·)] at *
  push_cast (disch := apply D.nat_le_of_hasLogBound) [Nat.cast_choose_two, ← add_assoc,
    m_eq_two_mul_varrho_add_two] at *
  and_intros <;> linarith [log_two_gt_d9]

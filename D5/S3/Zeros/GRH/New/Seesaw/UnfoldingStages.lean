/- GID: D5/S3/Zeros/GRH/New/Seesaw/UnfoldingStages
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/UnfoldingStages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.UnfoldingStages. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/UnfoldingStages.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Columns.TwistedHeckeType
import D5.S3.Zeros.GRH.New.Seesaw.StandardLatticeLevel
import D5.S3.Zeros.GRH.New.Trace.LabelRigidity
import D5.S3.Zeros.GRH.New.Filling.FillingAdmissible
import D5.S3.Zeros.GRH.New.Seesaw.LinesStep
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Function left after k unfoldings: coefficient of the definite chain; its support. -/

namespace Data

open MeasureTheory Function UniqueFactorizationMonoid Multiset IsDedekindDomain.HeightOneSpectrum
  Space Grading stdLattice Prod Modulus
variable {P} {D : Data P} (ϑ : D.TameChar) (φ : D.Column) (ξ : ∀ k, GInf D.E (D.signsY k))
  (y : ∀ k, Gf D.E (D.Y k))

/-- The function P_k on U(Y_k)(𝔸): P₀ = 𝖶_φ is the Poincaré series of φ over the rational points
of the Bessel subgroup, and P_{k+1} comes from P_k by the unfolding step
`Grading.unfoldStep` at the point (ξ_k, y_k). -/
noncomputable def unfoldStage : ∀ k ≤ 2 * D.ϱ + 2, ∀ {X s} [Fintype X], Grading (D.spaceY k) D.N X s
  → _root_.G D.E (D.signsY k) → ℂ | 0, _ => (D.filling_fits.poincare
  (D.columnCoords φ) ·.ratBessel) | k + 1, l => ((D.gradingY k).unfoldStep · (rankTwist
  (D.chainChar ϑ (k + 1))) (datumY ϑ k) (unfoldStage k (by lia) (D.gradingY k)) (ξ k, y k))

lemma unfoldStage_update {l} s t k hk (h : k ≤ l) : @unfoldStage _ D ϑ φ (update ξ l s) (update y l
  t) k hk = @unfoldStage _ D ϑ φ ξ y k hk := by induction k <;> simp (disch := lia) [unfoldStage, *]

lemma isGeneric_unfoldStage : ∀ k l,
  (D.gradingY k l).IsGeneric (unfoldStage ϑ φ ξ y k l.step (D.gradingY k))
  | 0, _ => D.filling_fits.isGeneric_poincare _ (by simp [gradingY, filling, gProd, field])
  | _ + 1, _ => isGeneric_unfoldStep (isGeneric_unfoldStage ..) rfl

/-- Let i ≤ ϱ, R a pair of steps with evaluation `Data.pairEvalY` i, and ξ, x real points. Some
linear form t gives, for all ϑ, columns φ, y with y₀ in K(g) and g in U(X): `Data.unfoldStage`
2i + 2 at g·(x, y_{2i+2}) is the matrix coefficient at t, at the point R.embX g, of i + 1 paired
lifts of φ with data `Data.evaluatedDatum`. -/
lemma unfoldStage_even i (h : 2 * i < 2 * D.ϱ + 1) {X q s} [Fintype X] [Fintype q]
    {Y : Grading _ _ X s} (R : ArrowPair _ q (D.gradingY _ h.le) (D.gradingY _ h) Y) (e :
  D.pairEvalY i = R.finEval) x : ∃ t, ∀ ϑ φ y, y 0 ∈ D.chosenLevel → ∀ g,
  unfoldStage ϑ φ ξ y (2 * i + 2) (by lia) Y (Y.inclX g * (x, y
  _)) = algFormCoeff 1 t (chain₂ (D.liftKernel ϑ) (evaluatedDatum ϑ y) (i + 1) φ) (R.embX g) := by
  induction' i using Nat.strongRec with i H generalizing X q s
  obtain ⟨t, a⟩ : ∃ t, ∀ ϑ φ y b g, _ = _
  swap
  choose u _ using (zeroTermFin_spec R.splitting).2
  choose _ _ using R.integral_constTermAtT_mul
  have L {i} : IsThetaLift _ _ _ _ (D.liftKernel · i |>.lift) := isThetaLift_thetaKernel (by simp)
  refine .imp (fun _ H o φ y b g ↦
    .trans ?_ (H o ..)) (integral_theta_eq_lift₂ (@L (2 * i)) L ((?z : ℂ) • ?v) t)
  simp_rw [evaluatedDatum, e, R.arrowTensor_finEval]
  simp +instances [unfoldStage, Grading.unfoldStep, *, isGeneric_unfoldStage, constTermAtT,
    ← integral_mul_const, ← mk_mul_mk, arrowProduct,
    pairWeil_integrated_all (ξ _), Std.map_integrated, boxProd_integrated]
  refine .trans congr(∫ g, $(a o φ y b g) * _ ∂_) (by rfl)
  cases i; exacts [⟨(dotProductBilin ℂ ℂ).flip _ ∘ₗ D.filling_fits.weylBesselEquiv.1.1,
    fun ϑ φ y a g ↦ by simpa [simpleRootSum_eq_zero_of_mem_besselH] using!
    (D.filling_fits.poincare_bessel_normal_form (D.centralRep (D.latticeScale 0) φ) (one_mem _) g
    (x := (_, _)) a).trans congr(_ * D.filling_fits.weylBesselEquiv.1 (conjWeylRep _ _ _
    (φ.1.1 $(inv_mul_cancel_right ..))) ⬝ᵥ _)⟩, H _ .refl _ _ (dite_eq_left (by omega)) _]

lemma evaluatedDatum_out : evaluatedDatum ϑ (fun k ↦ (y k : _ ⧸ levelY ϑ k).out) =
  evaluatedDatum ϑ y := by
  choose u e using (QuotientGroup.mk_out_eq_mul (levelY ϑ _) <| y ·)
  simp [funext_iff, evaluatedDatum, translatedUpsilon, e, ← mk_mul_mk]
  congr! <;> simp [thetaKernelY_omega_upsilonY ϑ _ (mem_levelOf.1 (u _).2).2
    (mem_levelOf.1 (u _).2).2 fun _ ↦ (@Matrix.mul_one _ _ _ _ _ (_) _).symm]

/-- Let φ be a ramified column and y₀ of principal level above g. If the stage-k function is
non-zero at a point of U(Y_k), the lines of its lattice move at most k steps above Q and not
elsewhere (`Grading.HasNearLines`). -/
lemma hasNearLines_of_unfoldStage_ne_zero (φ : D.ramifiedColumns) (y₀ :
  y 0 ∈ chosenLevel) k hk g (e : unfoldStage ϑ φ ξ y k hk.step (gradingY k hk) g ≠ 0) :
  (D.gradingY k).HasNearLines D.ideleA ϑ.Q ((D.m - k + 1) / 2) k g.2 := by
  induction' k with k ih
  · exact hasNearLines_zero _ (D.spansLattice_gradingY ..) levelOf_le_Kf
      (D.filling_fits.exists_besselFin_mul_mem_of_ne_zero _ e)
  let 𝔪 := D.𝔪 ϑ 1
  refine (exists_ne_zero_of_integral_ne_zero e).rec fun r l ↦ (ih _ _ (left_ne_zero_of_mul l)).step
    (by clear * - hk; grind) (by omega) D.valuation_shift_const_eq_ideleA_norm
    (right_ne_zero_of_mul l) 𝔪.generator (fun w ↦ ?_)
    (fun x o ↦ ?_) (·.ideleLogVal_add_rev_nonpos D.piIdele_spec fun o n m w H ↦ e ?_)
  · erw [ideleLogVal, ideleLogVal, 𝔪.valued_generator,
      multiplicity_mul w.prime (.of_prime_left w.prime 𝔪.2), ← span_piGBar,
      ← count_normalizedFactors_eq_multiplicity (right_ne_zero_of_mul 𝔪.2), ϑ.Q.prod_coe_sort,
      Finset.prod, normalizedFactors_prod_of_prime] <;> simp [ideleA, chosenIdele, valued_generator,
      prime, count_map_eq_count', asIdeal_injective, count_eq_of_nodup ϑ.Q.2]
  · obtain ⟨z, a, d⟩ : IsAdmissibleComb _ _ 1 _ _ 0 (upsilonY ϑ k).1 :=
      isAdmissibleComb_name _ _ (g := 0) (by simp) (by simp
      [ite_mem]) id (projOn_vacElem _) ⟨⟨_, 𝔪.generator_spec.1⟩, by simp [𝔪, generator_spec]⟩
    rw [d, map_finsuppSum, Finsupp.sum_congr fun t e ↦ ?_]
    simp [finHeisOp_comm, finHeisOp_vacElem
      (smul_mem_stdLattice 𝔪.generator_spec.1 o), by simpa using (mem_stdLattice_iff_psi₀.1
      o (star 𝔪.generator.1 • t) fun i ↦ mem_Ô.2 (a.1 t e i · (mod_cast Ideal.one_notMem _)))]
  obtain ⟨⟨j, rfl⟩ : Odd k, ⟨u, hu, a, d⟩, ψ, f⟩ := ⟨k / 2, o.elim (by omega)⟩,
    exists_unipotent_mul_inclX _ (inv_mem (x := (1, n)) m), D.exists_eq_sub_centralGen w φ.2
  choose t ht using unfoldStage_even (update ξ _ g.1) j _ _ (dite_eq_left (by omega)) g.1
  replace ht := by simpa only [unfoldStage_update, update_self, le_rfl,
    ← evaluatedDatum_out _ (update _ _ _),
    (apply_update fun _ ↦ QuotientGroup.mk)] using fun ψ x ↦ ht ϑ ψ (update y (2 * j + 2) x) y₀
  have := by simpa [twoKernelAction, liftKernel_ω, pairWeilFinite_scalarFin,
    (D.charUnramifiedAt_rankTwist_of_N_mem _ _ _ _ (D.isSplitLevel_piPlaces.natCast_mem _
    w.2)).det_maxCompactAt_eq_one (D.isSplitLevel_piPlaces.star_notMem
    _ w.2 <| ·.symm ▸ w.2) (D.scalarFin_centralGen_mem ..)] using
    chain₂_equivariant (liftKernel ϑ) fun _ ↦ scalarFin _ (D.centralGen w)
  rw [← inv_mul_cancel_left _ g, d, mul_assoc,
    (isGeneric_unfoldStage ..).unipotent_mul _ u hu (hasDegreeGe_two_of_odd _ o hu)]
  simpa [middlePair, algFormCoeff_apply, inclX_inr, mul_assoc, mul_def _ g, *, ← QuotientGroup.eq.2
    (maxCompactAt_le_levelOf (by simp [levelPlaces, range_chosen]; clear * - w; grind
    [not_isChosen_of_N_mem, D.isSplitLevel_piPlaces.natCast_mem_iff, →
    levelNorm_mem_and_notMem_of_mem_Q]) (H _ (D.scalarFin_centralGen_mem ..)) : _ ∈ levelY ϑ _)]
    using! (ht ψ (n * g.2) (a * (1, scalarFin _ (D.centralGen w))) :)

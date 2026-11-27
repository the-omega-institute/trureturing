/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineEtale
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineEtale
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Crystalline.CrystallineEtale. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Crystalline/CrystallineEtale.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.ChartedSchemes
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore).

Part of: Crystalline comparison: p-adic étale cohomology with good reduction is crystalline (known
result; see Lib.PadicComparison.Crystalline.CrystallineClasses).

This file: A_max as Frobenius-twisted A_inf-algebra; map from O_C to A_max modulo divided powers.
Étale algebras lift along surjections; étale over perfect is perfect. Crystalline comparison is
bijective on algebras etale over a perfectoid torus. -/

noncomputable section

section

open CategoryTheory Ideal Quotient Amax WittVector Algebra Lift
variable {p} [ThePrime p]

instance : Module.Flat Amax Bcris := by apply_rules +allowSynthFailures [Localization.flat]

/-- The coefficient functor on p-torsion-free p-complete A_max-algebras sending D to B_max
⊗_{A_max} D. -/
abbrev crysPeriodCoeff : AbFunctor (CrysTest Amax) :=
  moduleCoeff (asModules (ObjectProperty.ι _) ⋙ tensorWith Bcris Bcris)

/-- An A_inf-algebra structure on A_max satisfying `IsPeriodRingPair` for (A_max, B_max), with the
image of μ divisible by p³ in A_max and a unit in B_max. -/
class CrysPeriodAlgebra extends Algebra Ainf Amax, IsPeriodRingPair p Amax Bcris where
  p_cube_dvd_mu : p.cast ^ 3 ∣ algebraMap mu
  isUnit_mu : IsUnit (ofId _ Bcris (algebraMap mu))

/-- The ring map O_C → A_max/𝔡(A_max) obtained by factoring A_inf → A_max/𝔡(A_max) through
Fontaine's surjection θ: A_inf → O_C. -/
def ocToAmaxModPd [h : CrysPeriodAlgebra] : OC →+* _ ⧸ pdIdeal Amax :=
  .liftOfSurjective _ theta_surjective ⟨algebraMap .., fun _ a ↦ eq_zero_iff_mem.2
  (mem_of_dvd _ (by grw [h.dvd_xi, theta_eq_zero_iff_xi_dvd.1 a]) h.p_mem_pdIdeal)⟩

lemma ocToAmaxModPd_untilt [h : CrysPeriodAlgebra] t : ocToAmaxModPd t.untilt =
  h.algebraMap (teichmuller p t) := theta_teichmuller t ▸ theta.liftOfSurjective_comp_apply ..

/-- If y in O_C has p dividing y^N, there is an A_inf-algebra structure on A_max as in
`CrysPeriodAlgebra`, compatible with ℤ_p and commuting with Frobenius and G_p, for which the
map O_C → A_max/𝔡(A_max) (`ocToAmaxModPd`) kills y. -/
lemma exists_crysPeriodAlgebra {N} {y : OC} (hy : ↑p ∣ y ^ N) : ∃ h : CrysPeriodAlgebra,
  IsScalarTower ℤ_[p] Ainf
  Amax ∧ (∀ (m : FrobGal) a, m • h.algebraMap a = h.algebraMap (m • a)) ∧ ocToAmaxModPd y = 0 := by
  obtain ⟨⟨t, rfl⟩, mem⟩ := untilt_surjective_of_isAIC (p := p) y, @p_pow_dvd_of_mem_pow p _ 1
  simp at mem
  let := compHom Amax (MulSemiringAction.toRingHom FrobGal Ainf (.ofAdd (N ⊔ 3), 1))
  let h : CrysPeriodAlgebra := ⟨⟨⟨.of_ne_zero NeZero.out, {}⟩, mem (smul_xi_mem_span _),
    isUnit_smul_of_dvd_mu _ (by simp [← xi_mul_tau])⟩,
    p_pow_dvd_of_mem_pow (pow_le_pow_right le_sup_right (by simpa [mu, FrobGal.smul_def]
    using (pow_p_pow_sub_mem_of_xi_dvd ⟨_, xi_mul_tau.symm⟩ _))), isUnit_smul_of_dvd_mu _ dvd_rfl⟩
  use h, .of_algebraMap_eq (by rw [compHom_algebraMap_eq]; aesop), by simp [compHom_algebraMap_eq,
    smul_smul, mul_comm],
    ocToAmaxModPd_untilt t ▸ eq_zero_iff_mem.2 (mem_of_dvd _ (mem ?_) h.p_mem_pdIdeal)
  grw [Witt.mem_span_pair_iff, ← untilt_dvd_iff, untilt_constantCoeff_xi_dvd_p, hy]
  simp [untilt_frobGal_smul, smul_teichmuller, pow_dvd_pow, (Nat.lt_pow_self Fact.out).le.trans']

end

open Function Algebra RingHom NeZero TensorProduct FormallyUnramified Etale IsLocalization Away
variable {p} [ThePrime p] (C D) [CommRing.{0} C] [CommRing.{0} D] [Algebra C D]

/-- Étale algebras lift along surjections: if C → D is onto with kernel I and B is étale over D,
there are an étale C-algebra T and a surjective C-algebra map T → B with kernel contained in
IT. -/
lemma exists_etale_lift B [CommRing B] [Algebra D B] [e : Etale D B] (s : Surjective
    (algebraMap C D)) : ∃ T : CommAlg C, Etale C T ∧ Nonempty (D ⊗[C] T ≃ₐ[D] B) := by
  algebraize [(algebraMap D B).comp (algebraMap C D)]
  simp [iff_isStandardSmoothOfRelativeDimension_zero] at *
  let ⟨_, _, _, _, P, d⟩ := e
  have : P.HasCoeffs C := ⟨by tauto⟩
  let Q := P.1.ofHasCoeffs C
  let e := P.tensorModelOfHasCoeffsEquiv C
  exact ⟨.of _ (Localization.Away Q.jacobian), ⟨_, _,
    _, .instSum, ⟨.comp (.localizationAway _ Q.jacobian) Q, by
      simp [algebraMap_isUnit, smul_def, -isUnit_map_iff]⟩,
    by simp_all +arith [Presentation.dimension]⟩, ⟨(tensorProductEquivTMulRight _ _ Q.jacobian
    _).trans (((atUnit _ _ _ (.of_map e (1 ⊗ₜ Q.jacobian) (@Q.jacobian_eq_jacobiMatrix_det .. ▸
    .mul (by simp) (P.aeval_jacobianOfHasCoeffs C ▸ P.2)))).symm.restrictScalars _).trans e)⟩⟩

/-- If C is a perfect ring with p = 0 and D is an étale C-algebra, then x ↦ x^p is bijective on
D. -/
lemma perfectRing_of_etale [Etale C D] [k : PerfectRing C p] (h : (p : C) = 0) : PerfectRing D p :=
  (k.pow ..).rec fun k ↦ pow_one p ▸ let := (frobPow (natCast_eq_zero_of_algebra h D) 1).toAlgebra
  let := @of_restrictScalars C D D _ _ _ _ (_) _ (by use by simp [smul_toAlgebra, smul_def, mul_pow,
    mul_assoc]) _ ((of_bijective k).stableUnderComposition (frobPow h 1) _ (etale_algebraMap.2 ‹_›))
  have := @Module.FaithfullyFlat.of_comap_surjective D D _ _ _ _ fun x ↦ ⟨x, by
    ext; exact x.2.pow_mem_iff_mem _ (pos _)⟩
  ⟨FaithfulSMul.algebraMap_injective .., fun _ ↦ (IsEffective.of_faithfullyFlat ..).1 (sub_eq_zero.2
    ((IsUnit.of_pow_eq_one (.trans congr($(show frobPow (natCast_eq_zero_of_algebra h _) 1 =
    (algebraMap D _).comp (lmul' D).1 by
    ext <;> simp <;> erw [← pow_one p, tmul_one_eq_one_tmul]; rfl) _)
    (by simp [lmul_elem, map_one])) out).mul_right_cancel (one_tmul_mul_elem _).symm))⟩

open CategoryTheory ConcreteCategory Ideal ObjectProperty CommAlgCat ULift PadicTest

open WittVector hiding map_surjective
variable {p : _} [ThePrime p] [h : CrysPeriodAlgebra]

/-- The functor sending a p-adic test S to the p-adic completion of A_max ⊗_{A_inf} W(S^♭), a
p-torsion-free p-complete A_max-algebra. -/
def crysThickening : PadicTest ⥤ CrysTest Amax :=
  ObjectProperty.lift _ (_ ⋙ periodAlg ..) (isCompleteTorsionFree_completion <|
  isSMulRegular_tensor_witt h.regular ·.isPerfectTorsionFree_tilt)

/-- The quotient map E → E/𝔡(E), natural in the A_max-algebra E, as a map of A_inf-algebras;
A_inf acts on E/𝔡(E) through θ and `ocToAmaxModPd`. -/
def toPdReduction : ι _ ⋙ restrictAlg Ainf _ ⟶ pdReduction ocToAmaxModPd ⋙ restrictAlg _ _ :=
  .mk fun E ↦ CommAlg.homOfRingHom (pdQuotientMk _)
  fun _ ↦ by erw [eq_comm, RingHom.comp_apply, RingHom.comp_apply, liftOfSurjective_comp_apply]; rfl

/-- The natural O_C-algebra map S → D/𝔡(D), D the completion of A_max ⊗ W(S^♭), sending y to the
class of 1 ⊗ [x] whenever x in S^♭ has zeroth component y mod p. -/
@[irreducible] def testToThickening : algFunctor ⟶ crysThickening ⋙ pdReduction ocToAmaxModPd :=
  thetaIso.2 ≫ (baseChangeTranspose ..).2 (tilt.whiskerLeft (baseChangeTranspose _
  (periodAlg ..) (wittFunctor.whiskerLeft ((algBaseChange _).whiskerLeft
  (algCompletion.of ..)))) ≫ by exact crysThickening.whiskerLeft toPdReduction)

/-- Assume `CrysPeriodAlgebra`. For a p-adic test c with ring S and x in W(S^♭), `testToThickening`
sends θ(x), θ Fontaine's map, to the class of 1 ⊗ x in D/𝔡(D), D the p-adic completion of
A_max ⊗ W(S^♭) over A_inf. -/
lemma testToThickening_theta c x : testToThickening c (fontaineTheta c.ProdRing p x) =
  Quot.mk _ (.of _ _ (1 ⊗ₜ x)) := .trans (by erw [← thetaIso_hom_one_tmul, testToThickening,
  ← NatTrans.comp_app_apply, Iso.hom_inv_id_assoc]; rfl) (one_smul OC _)

/-- For a functor P on O_C-algebras: restriction along `crysThickening` and `testToThickening`,
from the cohomology of D ↦ P(D/𝔡(D)) with coefficients B_max ⊗ D to that of S ↦ P(S) on
p-adic tests, is bijective in every degree. -/
def HasCrysComparison :=
  (Comparison.restrict crysThickening crysPeriodCoeff).IsBijectiveOn testToThickening

/-- Let b be a perfect π-torsion-free O^♭-algebra (π = `pFlat`) and k: T → W(b) an
A_inf-algebra map that is bijective on p-adic completions. Then the crystalline comparison
`HasCrysComparison` is bijective for the functor Hom_{A_inf}(T, −) on O_C-algebras. -/
lemma hasCrysComparison_of_witt (b : FullSubcategory IsPerfectTorsionFree) {T} (k :
  T ⟶ wittFunctor.obj b.1) (hk : IsBijOnCompletion p k.hom.toLinearMap) :
  HasCrysComparison (restrictAlg Ainf _ ⋙ reprBy T) := have := b.2.1
  Iff.mpr (Comparison.isBijective_congr (p := pointMap ⟨k ≫ algBaseChangeAdj.homEquiv _ _
    ((algCompletion.of ..).1 _) ≫ toPdReduction.1 ⟨_, isCompleteTorsionFree_completion
    (isSMulRegular_tensor_witt h.regular b.2)⟩⟩) (p' := homTiltIso.1 ≫ algFunctor.whiskerLeft
    (pointMap ⟨k ≫ algBaseChangeAdj.1.1 _⟩)) (v := tilt.whiskerLeft (pointMap (Y := periodAlg .. ⋙
    reprBy _) ⟨𝟙 _⟩) ≫ .mk fun _ ↦ by exact ↾(⟨⟨·.1⟩⟩)) (by ext; exact up_inj.2 (ext_apply fun _ ↦
    (congrArg _ (thetaIso_hom_one_tmul ..)).trans ((testToThickening_theta ..).trans
    (congrArg _ (.symm (adicMap_algebraMap ..)))))) (.of_bijective fun E ↦ ULift.map_bijective.2
    ((hk.comp_bijective _ (by erw [E.p_eq_zero_mod_pdIdeal, span_zero]; tauto)).comp
    ((Bijective.of_existsUnique (· ≫ toPdReduction E) (by
    rintro ⟨f, c⟩
    obtain ⟨F, ⟨⟩⟩ := (constantCoeff.liftOfRightInverse (teichmuller p) .refl).symm.surjective
      ⟨f, by simpa [witt_reduction_spec OFlat] using!
      (map_natCast ..).trans E.p_eq_zero_mod_pdIdeal⟩
    let ⟨w, a, H⟩ := E.2.existsUnique_witt_lift p_eq_zero_of_algebra_oFlat F
    use! w, (w.comp _).congr_fun ((E.2.existsUnique_witt_lift p_eq_zero_of_algebra_oFlat
      (F.comp _)).unique (a <| ·.map _) ((toPdReduction _).1.2 · |>.trans (c _).symm)), ext_apply a,
      fun g k ↦ ext_apply (RingHom.congr_fun (H _ (congr($k.1 ·)))))).comp
    ((algBaseChangeAdj.homEquiv ..).bijective.comp ((isBijOnCompletion_completion.comp_bijective
    ((algCompletion.of ..).1 _) E.2.2).comp InducedCategory.homEquiv.bijective)))))
    (.of_bijective fun c ↦ ((ULift.map_bijective.2 (hk.comp_bijective _
    c.isAdicComplete_prodRing)).comp (pointMap_algBaseChange_unit_bijective ..)).comp
    (homTiltIso.app _).toEquiv.bijective)) (.transfer (CoeffCompBij.periodAlg_of_almostCoeff
    (β := 𝟙 (ObjectProperty.lift _ _ isPerfectTorsionFree_tilt ⋙ ι _)) (α :=
    freeAbMap (.mk fun _ ↦ by exact ↾(⟨⟨·.1⟩⟩))) (hasFlatBaseChange_reprFunctor _) h.2 (fun _ _ ↦
    hasFlatBaseChange_of_iso_reprBy homTiltIso.symm ..) (·.2) isPerfectTorsionFree_tilt
    ((isAcyclicAt_almostCoeff h.pFlat_smul_eq_zero _).transfer bijective_id)) bijective_id)

open AddMonoidAlgebra Algebra TensorProduct AlgebraMonoidAlgebra in
/-- If G is a commutative monoid that is a module over ℚ≥0 and B is étale over the monoid
algebra O_C[G], then the crystalline comparison is bijective (`HasCrysComparison`) for the
functor Hom(B, −) on O_C-algebras. -/
lemma hasCrysComparison_of_etale G [AddCommMonoid.{0} G] [Module ℚ≥0 G] (B : CommAlg _) [Algebra
  OC[G] B] [IsScalarTower OC OC[G] B] [Etale OC[G] B] : HasCrysComparison (reprBy B) := by
  let W := Ainf[G]
  have ⟨T, _, ⟨E⟩⟩ := exists_etale_lift W OC[G] B (map_surjective _ theta_surjective)
  algebraize [T.3.2.comp (algebraMap Ainf _)]
  let a S [CommRing S] [Algebra Ainf S] := IsPushout.cancelBaseChangeAlg Ainf S W S[G] T
  let b := CommAlgCat.of OFlat (OFlat[G] ⊗[W] T)
  have := perfectRing_of_etale _ b (k := perfectRing_monoidAlgebra G) p_eq_zero_of_algebra_oFlat
  have ⟨c, w, z, _⟩ := witt_reduction_spec OFlat b
  let := (liftNCRingHom (WittVector.map b.3.2) ((teichmuller p).comp
    (includeLeftRingHom.1.comp (of ..))) fun _ _ ↦ .all ..).toAlgebra
  let e := quotientKerAlgEquivOfSurjective (f := ⟨constantCoeff, (constantCoeff.comp (algebraMap W
    _)).congr_fun (by ext <;> simp [*, b, W, algebraMap_toAlgebra, map_one])⟩) c.1
  obtain ⟨κ, hκ⟩ := @FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete _ _ _ _ _ _ _ _ _ _
    (z ▸ w.2 :) (e.symm.toAlgHom.comp includeRight)
  exact ((Comparison.isClosedClass (.restrict ..) testToThickening).iff_of_isIso (freeAb.map
    (reprFunctor.mapIso (isoMk ((a _).symm.trans (E.restrictScalars _))).op ≪≫ isoOfAppBijective _
    (pointMap_algBaseChange_unit_bijective _)).1)).2 (hasCrysComparison_of_witt (T := .of _ T) ⟨b,
    ‹_›, (Module.Flat.trans _ OFlat[G] _).isTorsionFree.1 (.of_ne_zero pFlat_ne_zero)⟩
    (CommAlg.homOfRingHom κ.1 fun _ ↦ by erw [κ.2, liftNC_single, map_one, mul_one]; rfl)
    (.of_dvd_sub_of_pow_dvd _ (fun y ↦ (mk_surjective W T OFlat[G]
    (map_surjective _ (constantCoeff_surjective p)) (y.1 0)).imp fun t u ↦ mem_span_singleton.1 (z ▸
    (sub_mem_ker_iff _).2 ((e.eq_symm_apply.1 congr($hκ t)).trans u).symm)) fun _ _ ↦ pow_dvd_of_map
    (by simp) (by simpa [mem_nonZeroDivisors_iff_left] using! @w.1.right_eq_zero_of_smul) fun t u ↦
    ((((witt_reduction_spec OFlat _).1.lTensor (Algebra.linearMap Ainf OFlat)).2 (t ⊗ₜ 1)).1
    ((TensorProduct.comm
    ..).injective ((a _).symm.injective (by simpa [a] using!
    (e.eq_symm_apply.1 congr($hκ t)).symm.trans (z.ge (mem_span_singleton.2 u)))))).elim fun y h ↦
    ⟨_, by simpa [← nsmul_eq_mul] using congr(TensorProduct.rid _ _ $h).symm⟩))

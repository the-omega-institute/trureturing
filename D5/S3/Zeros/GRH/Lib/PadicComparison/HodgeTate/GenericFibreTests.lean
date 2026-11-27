/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GenericFibreTests
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GenericFibreTests
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.HodgeTate.GenericFibreTests. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/HodgeTate/GenericFibreTests.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline.TestGenericFibre
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology (known result; see
Lib.PadicComparison.HodgeTate.HodgeTateVectors).

This file: Relative ring B_dR+/ξ² on p-adic tests as square-zero extension of the generic fibre. -/

noncomputable section

attribute [local instance 2000] Algebra.toSMul Algebra.toModule Algebra.FormallyEtale.of_isSeparable
attribute [-simp] mul_eq_zero isUnit_map_iff


open CategoryTheory Function Ideal WittVector Algebra IsLocalization RingHom PadicTest Functor
  CommAlgCat Quot FormallySmooth FormallyUnramified

/-- The field k has characteristic zero and comes with an embedding in Q̄_p, the algebraic
closure of ℚ_p, for the fixed prime p. -/
class EmbeddedInQpBar (p : outParam ℕ) (k : outParam Type) [Field k] extends
  ThePrime p, Algebra k (PadicAlgCl p), CharZero k

section

variable {p} [ThePrime p] (c : PadicTest)

namespace PadicTest

/-- The structure map ℂ_p → R[1/p], defined through a choice. -/
instance algebraGenericRing : ∀ c : PadicTest, Algebra ℂ_[p] c.GenericRing :=
  (@exists_eq _ (map _ ·.structureMap (powers_le_comap_powers p _) |>.toAlgebra)).choose

/-- For a p-adic test c with ring R, the structure map ℂ_p → K = R[1/p]. -/
def structMap := algebraMap ℂ_[p] c.GenericRing

lemma structMap_coe x : c.structMap x.1 = algebraMap _ _
  (c.structureMap x) := by simpa +instances [structMap, algebraGenericRing] using! map_eq ..

instance : IsScalarTower OC ℂ_[p] c.GenericRing := .of_algebraMap_eq (c.structMap_coe · |>.symm)

/-- For a p-adic test with ring R, the map W(R^♭)[1/p] → R[1/p] obtained from Fontaine's map θ:
W(R^♭) → R by inverting p. -/
def thetaGeneric : Localization.Away (p : WittVector p c.TiltRing) →+* c.GenericRing :=
  map _ (fontaineTheta c.ProdRing p) (powers_le_comap_powers p _)

lemma thetaGeneric_algebraMap_ainf a : c.thetaGeneric (algebraMap _ _ a) =
  c.structMap (theta a) := by erw [map_eq, fontaineTheta_map_tiltMap, structMap_coe]

lemma thetaGeneric_mu :
  c.thetaGeneric (algebraMap _ _ mu) = 0 := by simp [thetaGeneric_algebraMap_ainf, mu]

/-- For a p-adic test with ring R, the quotient W(R^♭)[1/p]/(ker θ)², where θ: W(R^♭)[1/p] →
R[1/p]. -/
abbrev Thickening := _ ⧸ ker c.thetaGeneric ^ 2

/-- For a p-adic test with ring R, the ring map W(R^♭)[1/p]/(ker θ)² → R[1/p] induced by θ. -/
def thickeningProj := Ideal.Quotient.lift (ker c.thetaGeneric ^ 2) _ (pow_le_self (by simp))

instance isLocalization_generic {S} [CommRing S] (f : S →+* c.ProdRing) :
  IsLocalization (.map f (.powers ↑p)) c.GenericRing := by simp; infer_instance

lemma thetaGeneric_spec : Surjective c.thickeningProj ∧ ker c.thetaGeneric =
  span {algebraMap _ _ xi} := ⟨(surjective_lift _).2 (map_surjective_of_surjective _ _ _
  fontaineTheta_surjective_of_isAIC), by simp [thetaGeneric, ker_map]; rfl⟩

/-- For a p-adic test with ring R, the kernel of the map π₀: W(R^♭)[1/p]/(ker θ)² → R[1/p]
induced by θ has square zero. -/
lemma ker_thickeningProj_sq :
  ker c.thickeningProj ^ 2 = ⊥ := by simp [thickeningProj, ker_quotient_lift, ← Ideal.map_pow]

/-- For a p-adic test with ring R there is a unique ℤ_p-algebra map ρ: Q̄_p → W(R^♭)[1/p]/(ker
θ)² lifting the map Q̄_p ⊂ ℂ_p → R[1/p] along θ. -/
lemma existsUnique_lift_thickening : ∃! ρ : PadicAlgCl p →ₐ[ℤ_[p]] _, ∀ z, c.thickeningProj (ρ z) =
  c.structMap z := let := restrictScalars ℤ_[p] ℂ_[p] c.GenericRing
  have := (FormallyEtale.of_isLocalization (nonZeroDivisors ℤ_[p])).comp _ ℚ_[p] (PadicAlgCl p)
  existsUnique_of_exists_of_unique ⟨_, liftOfSurjective_apply ⟨.comp _ (algebraMap ..), by tauto⟩
    ⟨_, (IsScalarTower.algebraMap_apply _ Ainf c.Thickening · ▸ (thetaGeneric_algebraMap_ainf
    ..).trans (congrArg _ ((OC.toPadicIntAlgHom _).2 _)))⟩ c.thetaGeneric_spec.1 ⟨2,
    c.ker_thickeningProj_sq⟩⟩ (ext' _ ⟨2, c.ker_thickeningProj_sq⟩ · · <| by simp [·, ·])

/-- For a p-adic test with ring R, the unique ℤ_p-algebra map Q̄_p → W(R^♭)[1/p]/(ker θ)²
lifting the structure map Q̄_p → R[1/p] along θ, packaged with its uniqueness. -/
@[instance_reducible]
def uniqueLift := ((unique_subtype_iff_existsUnique _).2 c.existsUnique_lift_thickening).some

variable {c d} (f : c ⟶ d)

/-- For a morphism of p-adic tests with rings R, R', the induced ℂ_p-algebra map R[1/p] →
R'[1/p]. -/
def mapGeneric : c.GenericRing →ₐ[ℂ_[p]] d.GenericRing := ⟨map _ f.1 (powers_le_comap_powers p _),
  fun _ ↦ by
  simp +instances [algebraMap_toAlgebra, algebraGenericRing, IsLocalization.map_map]; congr
  exact f.comp_algebraMap⟩

lemma mapGeneric_algebraMap x : mapGeneric f (algebraMap _ _ x) = algebraMap _ _ (f.1 x) :=
  lift_eq ..

/-- For a morphism of p-adic tests, the induced ring map between the quotients W(R^♭)[1/p]/(ker
θ)². -/
def mapThickening : c.Thickening →ₐ[Ainf] d.Thickening := quotientMapₐ _ ⟨map _ (_ :
  WittVector p c.TiltRing →+* WittVector p d.TiltRing) (powers_le_comap_powers p _),
  ((map_eq ..).trans <| congrArg _ <| ((tilt ⋙ wittFunctor).map f).1.2 ·)⟩
  (by simp [thetaGeneric_spec, span_singleton_pow, -AlgHom.coe_mk])

lemma thickeningProj_mapThickening : ∀ x, d.thickeningProj (mapThickening f x) =
  mapGeneric f (c.thickeningProj x) := ind fun x ↦ show d.thetaGeneric _ = mapGeneric f
  (c.thetaGeneric _) by simp [thetaGeneric, mapGeneric, IsLocalization.map_map, RingHom.comp,
  fontaineTheta_map_tiltMap, tilt, wittFunctor]

/-- The functor sending a p-adic test with ring R to R[1/p], as a ℂ_p-algebra. -/
def genericAlg : PadicTest ⥤ CommAlg ℂ_[p] := .mk _ (ofHom <| mapGeneric ·) (fun _ ↦
  hom_ext (AlgHom.ext map_id)) (by aesop (add simp [mapGeneric, IsLocalization.map_map]))

/-- The functor from p-adic tests to test rings sending S to S[1/p]. -/
def genericTest : PadicTest ⥤ TestRing := ObjectProperty.lift _ {genericAlg ⋙ forget₂ _
  CommRingCat with obj := _, map f := CommRingCat.ofHom (mapGeneric f).1} (·.isTest.localization)

end PadicTest

/-- The coefficient on p-adic tests sending a test with ring R to the additive group of R[1/p]. -/
abbrev genericCoeff := moduleCoeff (asModules genericAlg)

/-- On p-adic tests S there is a natural isomorphism of ℂ_p-modules from ℂ_p ⊗_{O_C} (O_C
⊗_{A_inf} W(S^♭))^, the hat denoting p-adic completion, to S[1/p], sending a ⊗ (1 ⊗ w) to
a·θ(w), θ being Fontaine's map. -/
lemma exists_periodAlg_iso_genericAlg : ∃ θ : asModules (tilt ⋙ periodAlg OC) ⋙ tensorWith _ _ ≅
  asModules genericAlg, ∀ c a w, θ.hom c (a ⊗ₜ .of _ _ (1 ⊗ₜ w)) = c.structMap a * algebraMap _ _
  (fontaineTheta _ p w) := let j := isoOfAppBijective (algFunctor.whiskerLeft (algCompletion.of ..))
                             (AdicCompletion.of_bijective_iff.2 ·.isAdicComplete_prodRing)
  ⟨isoWhiskerRight (isoWhiskerRight thetaIso _ ≪≫ j.symm) (asModules (𝟭 _) ⋙ tensorWith ..)
    ≪≫ NatIso.ofComponents (·.isLocalization_generic _ |> (isLocalization_iff_isPushout _ ℂ_[p]).1
    |>.symm.out.equiv.toModuleIso) fun f ↦ ModuleCat.hom_ext (tmul_ext fun _ _ ↦ by
    erw [map_smul (mapGeneric f), mapGeneric_algebraMap]; rfl), fun c a w ↦ .trans
    (congrArg (a • algebraMap c.ProdRing c.GenericRing ·) (c.thetaIso_hom_one_tmul w ▸ (congrArg _
    (adicMap_algebraMap ..)).trans (j.hom_inv_id_app_apply ..))) (c.algebraGenericRing.4 ..)⟩

end

variable {p k} [Field k] [EmbeddedInQpBar p k] (c : PadicTest)

instance : Algebra k ℂ_[p] := .restrictScalars k (PadicAlgCl p) _

instance : CoeffAction k genericCoeff := ⟨CoeffAction.act.comp (algebraMap k ℂ_[p])⟩

/-- For a field k with an embedding in Q̄_p, the functor sending a p-adic test with ring R to
R[1/p], as a k-algebra. -/
def genericOver := genericAlg ⋙ restrictAlg k _

instance : Algebra k c.Thickening := (c.uniqueLift.1.1.1.1.comp (algebraMap ..)).toAlgebra

/-- For a field k embedded in Q̄_p, the functor sending a p-adic test with ring R to
W(R^♭)[1/p]/(ker θ)², a k-algebra through the lift of `PadicTest.existsUnique_lift_thickening`. -/
def thickeningOver : PadicTest ⥤ CommAlg k := by
  refine ⟨(.of k ·.Thickening), fun {c d} f ↦ ofHom ⟨mapThickening f, fun _ ↦ congr($(d.uniqueLift.2
    ⟨.comp ((mapThickening f).restrictScalars _) _, ((thickeningProj_mapThickening f _).trans <|
    c.uniqueLift.1.1.2 · ▸ (mapGeneric f).2 _)⟩).1 _)⟩, ?_, ?_⟩ <;> intros <;> ext ⟨⟩ <;>
    congrm ⟦?_⟧ <;> simp; exacts [map_id _, .symm (IsLocalization.map_map ..)]

lemma hasZariskiDescent_genericOver {C} [Category C] Θ {F} (h : @HasPartitions C _ (Θ ⋙ ringFunctor)
  F) : HasZariskiDescent (Θ ⋙ genericOver ⋙ forget₂ ..) F := h.hasZariskiDescent
  ⟨_, by intros; ext; symm; apply mapGeneric_algebraMap⟩ (eq_zero_of_algebraMap_genericRing <|
  Θ ·) fun _ ↦ (PadicTest.isTest _).isComparableRing_of_associated exists_associated_localization

namespace thickeningOver

/-- The natural k-algebra map W(R^♭)[1/p]/(ker θ)² → R[1/p] induced by θ, on p-adic tests. -/
def proj : thickeningOver ⟶ genericOver := ⟨(CommAlg.homOfRingHom _ <| ·.uniqueLift.1.1.2 ∘'
  _), by intros; ext; apply thickeningProj_mapThickening⟩

/-- The additive map R[1/p] → W(R^♭)[1/p]/(ker θ)² sending θ(x) to the class of μx, where μ =
[ε] − 1. -/
def mulMu : genericOver c →+ thickeningOver c :=
  c.thickeningProj.toAddMonoidHom.liftOfSurjective c.thetaGeneric_spec.1 ⟨.mulLeft ⟦_⟧, fun _ h ↦
  (sq _).ge.trans_eq c.ker_thickeningProj_sq (mul_mem_mul c.thetaGeneric_mu h)⟩

lemma mulMu_thickeningProj b : mulMu c (c.thickeningProj b) = (algebraMap _ _ mu * b :) :=
  AddMonoidHom.liftOfRightInverse_comp_apply ..

lemma proj_mulMu : ∀ t, proj c (mulMu c t) = 0 := c.thetaGeneric_spec.1.forall.2 fun _ ↦ by
  erw [mulMu_thickeningProj, map_mul, thetaGeneric_mu, zero_mul]

lemma mulMu_proj_mul b : ∀ t, mulMu c (proj c b * t) = b * mulMu c t :=
  c.thetaGeneric_spec.1.forall.2 fun _ ↦ by
  erw [← map_mul, mulMu_thickeningProj, mulMu_thickeningProj, mul_left_comm]; rfl

lemma map_mulMu d (f : c ⟶ d) : ∀ t, thickeningOver.map f (mulMu c t) = mulMu d (genericOver.map f
  t) := c.thetaGeneric_spec.1.forall.2 fun _ ↦ by erw [← thickeningProj_mapThickening,
  mulMu_thickeningProj, mulMu_thickeningProj, map_mul (mapThickening f), AlgHom.commutes]

/-- For a p-adic test with ring R, K = R[1/p] and B = W(R^♭)[1/p]/(ker θ)², the sequence 0 → K →
B → K → 0 is exact, with π induced by θ and ι(θ(b)) = μb. -/
lemma exact_mulMu_proj : Surjective (proj c) ∧ Injective (mulMu c) ∧ Exact (mulMu c) (proj c) := by
  obtain ⟨⟨s, z⟩, t, u⟩ := c.thetaGeneric_spec, (IsUnit.mk0 (theta tau).1 (by simp)).map c.structMap
  have e y (a : c.GenericRing) : mulMu c a = ⟦algebraMap _ _ xi * y⟧ ↔ t * a =
    c.thetaGeneric y := by
    obtain ⟨⟨⟩, ⟨⟩⟩ := s a
    erw [mulMu_thickeningProj, Ideal.Quotient.eq, u, ← thetaGeneric_algebraMap_ainf, ← map_mul,
      ← sub_mem_ker_iff, z, span_singleton_pow]
    simp [← xi_mul_tau, mul_assoc, ← mul_sub, mem_span_singleton, sq]
    exact IsLeftRegular.dvd_cancel_left (IsSMulRegular.of_flat (R := WittVector p c.TiltRing)
      (.of_right_eq_zero_of_smul fun x h ↦ by_contra (verschiebung_nonzero · |>.elim fun j
      ⟨y, m, e⟩ ↦ m (IsLeftRegular.pow (R := c.TiltRing) (p ^ j) c.isPerfectTorsionFree_tilt.2 (by
      subst e; simpa using! (iterate_verschiebung_mul_coeff _ y 0 j).symm.trans congr(($h).1 _))))))
  use s, by simpa [injective_iff_map_eq_zero'] using! e 0, ind fun x ↦ ⟨fun h ↦ mem_span_singleton.1
    (z.le h) |>.elim fun _ ↦ (⟨_, · ▸ (e ..).2 (t.mul_inv_cancel_left _)⟩), by grind [proj_mulMu]⟩

/-- For a p-adic test with ring R, the multiplicative map x ↦ [x] from the tilt R^♭ to B =
W(R^♭)[1/p]/(ker θ)², the image of the Teichmüller lift. -/
def teichmullerLift : tilt c →* thickeningOver c :=
  (algebraMap _ c.Thickening).1.comp (@teichmuller p c.TiltRing ..)

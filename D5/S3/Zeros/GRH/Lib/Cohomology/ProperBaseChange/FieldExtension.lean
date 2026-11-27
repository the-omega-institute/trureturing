/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/FieldExtension
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/FieldExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.ProperBaseChange.FieldExtension. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/ProperBaseChange/FieldExtension.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.ProperSchemes
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Cohomology invariant under algebraically closed field extension; classes detected at
points. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor


open CategoryTheory RingHom CommRingCat Ideal HV Subfunctor IsLocalRing Algebra PrimeSpectrum Set
variable {ℓ n W} [ThePrime ℓ] {R S T : CommRingCat} {s : W ⟶ reprBy R} (h : IsProperOver s) (u :
  IsUnit (ℓ : R))

lemma HV.map_eq_zero_of_factors {Λ X Z v v' x w} (e : w ≫ v = v') :
    @map Λ W X v n x = 0 → @map _ Z _ v' n x = 0 := by simp_all [← e, map_comp]

include h u

/-- Let W be proper over R, ℓ a prime invertible in R, A an absolutely integrally closed
valuation ring over R with residue field k. The restriction H^n(W_A, ℤ/ℓ) → H^n(W_k, ℤ/ℓ) is
injective. -/
lemma IsProperOver.injective_map_residue {A} [CommRing A] [IsAICLocal A] [PreValuationRing A] {a} :
  (⇑(map ⟨ZMod ℓ⟩ (baseChangeTransition s (ofHom (residue A)) (a := a) rfl) n)).Injective := .of_ker
  _ fun _ ↦ (map_eq_zero_iff _ ((h.baseChange a).proper_base_change (by simpa using u.map a.1)
  n).1).1 ∘ map_eq_zero_of_factors (w := ⟨fun _ ↦ ↾fun y ↦ ⟨(_, ⟨ofHom (Ideal.Quotient.lift
  _ _ y.2)⟩), y.1.2⟩, by intros; ext; exact baseChangeOf.ext rfl (Quot.ind (by tauto))⟩) rfl

/-- Invariance under extension of algebraically closed fields: for W proper (`IsProperOver`)
over R, ℓ a prime invertible in R, and S → T algebraically closed fields over R, the map W_T
→ W_S induces bijections on all cohomology groups with coefficients ℤ/ℓ.

Known result: Proper base change; invariance under extension of algebraically closed fields. -/
lemma IsProperOver.isCohomEquiv_field_extension {a b} {φ : S ⟶ T} (e : a ≫ φ = b) (hS :
  IsField S) (hT : IsField T) (iS : IsAIC S) (iT : IsAIC T) :
  Components ⟨ZMod ℓ⟩ (baseChangeTransition s _ e) := e.rec fun n ↦ by
  algebraize [φ.1]; let := hS.toField; let := hT.toField
  rcases iS.isAlgClosed, iT.isAlgClosed; have β (t : Finset T) := (nullstellensatz_exists_le_ker
    (f := .adjoin_of_finite (R := S) t.finite_toSet) bot_ne_top).choose
  let b t : fibreProd s (reprMap a) ⟶ _ :=
    (baseChangeFunctor s).map ((Under.map a).map (β t).toUnder).op
  refine (h.isCohomContinuous.isFilteredColimit_adjoin s T a n).imp (fun p ↦ .of_ker _ fun x g ↦
    (p ∅ _ ((map_comp _ (baseChangeTransition s _ rfl) _).symm.trans g)).elim fun t witness ↦ witness.elim fun _ e ↦ by
    simpa [HV.map] using! map_eq_zero_of_factors (by ext; exact baseChangeOf.ext rfl (
    congrArg _ <| (β t).2 ·) : b t ≫ _ = 𝟙 _) ((map_comp ..).trans e)) (· · |>.elim fun t witness ↦ witness.elim fun x e ↦
    .elim (image_subset_nonunits_valuationSubring (A := (adjoin ..).toSubring) _
    (ker_ne_top (β t))) fun V W ↦ let i := ofHom (R := adjoin S _) (Subring.inclusion W.1)
    ⟨map _ (b t) n x, e ▸ (map_comp (baseChangeTransition s (ofHom V.subtype) rfl)
      (baseChangeTransition s (ofHom (algebraMap S _) ≫ i) rfl) _).trans ((congrArg _
      (h.injective_map_residue u ?_)).trans (map_comp _ (baseChangeTransition s i rfl) x).symm)⟩)
  repeat erw [← map_comp]
  congr 2 with; exact baseChangeOf.ext rfl fun _ ↦ congrArg _ (Ideal.Quotient.eq.2 (
    V.coe_mem_nonunits_iff.1 (W.2 ⟨_, (sub_mem_ker_iff _).2 ((β t).2 _), rfl⟩)))

/-- Let W be proper over R, ℓ invertible in R, T a test R-algebra, x ∈ H^n(W_T, ℤ/ℓ). The primes
P of T with x zero on the fibre over κ(P) form an open set; if it is all of Spec T, then x =
0. -/
lemma IsProperOver.isOpen_zero_set_and_eq_zero (T :
  TestRing) {a x} : let z := {P : PrimeSpectrum T.1 | map ⟨ZMod ℓ⟩ (baseChangeTransition s (ofHom
    (algebraMap T.1 P.1.ResidueField)) (a := a) rfl) n x = 0}; IsOpen z ∧ (z = univ → x = 0) := by
  intro z; let q := fibreProd.snd s (reprMap a)
  have v {I b} (k : ∀ c ∈ I, _) : unitPoints q {b} ≤ unitPoints q I :=
    fun _ _ h c i ↦ isUnit_of_dvd_unit (map_dvd _ (k c i)) (h b rfl)
  have w {I b} k := map_eq_zero_of_factors (x := x) (homOfLe_ι (@v I b k))
  let J : Ideal _ :=
    ⟨⟨⟨{b | map _ (unitPoints q {b}).ι n x = 0}, @fun b c i j ↦ let ⟨e, o, _⟩ := T.2.2 b c
    have l a {d} := @v {d} ((1 - a) * d) (by simp)
    (map_eq_zero_iff _ ((mayer_vietoris_injective (l e) (l _) (.of_preimage_le
      (hasPartitions_locConstCoeff.isCohomDense_partition _ o) (by exact .mk fun _ ↦
      ↾(⟨⟨·.1.1.2.1⟩⟩)) fun _ y ↦ by apply Or.imp <;> rintro k _ rfl <;> erw [map_mul, map_sub, k]
      <;> simpa using (y.2 _ rfl)) n rfl).2 fun _ k ↦ by
      simpa [*, ← map_mul, mul_mul_mul_comm] using (k.2.1 _ rfl).mul (k.2.2 _ rfl)).1).1
      (by ext <;> apply (H.map_map ..).trans <;> [apply w _ j; apply w _ i] <;> simp [*,
      mul_add, dvd_add])⟩, hasPartitions_locConstCoeff.eq_zero_of_zero_ring
    (by simp [unitPoints]) ..⟩, fun _ _ ↦ w (by simp)⟩
  rw [← (Set.ext fun P ↦ not_subset.trans ⟨fun ⟨b, k, l⟩ ↦ map_eq_zero_of_factors (lift_ι _ (by
    rintro _ _ ⟨y, rfl⟩ _ rfl; exact (Ne.isUnit (algebraMap_residueField_eq_zero.1.mt l)).map
      y.1.2.1.1)) k, fun e ↦ ?_⟩ : (zeroLocus J)ᶜ = z)]
  simpa [HV.map, eq_top_iff_one, isClosed_zeroLocus, zeroLocus_empty_iff_eq_top] using!
    map_eq_zero_of_factors (lift_ι (𝟙 _) fun _ ↦ by simp [unitPoints])
  have ⟨_, _, _⟩ := T.2.exists_valuationSubring_atPrime P; let M := P.1.primeCompl
  exact (((h.baseChange a).isCohomContinuous.isFilteredColimit_antitoneFamily (V := unitPoints q)
    (by tauto) (fun I ↦ isRelAffine_of_zero_unit_locus (⟨∅, baseRingMap q · '' I, by simp
    [unitPoints]⟩)) (D := (monotone_image.comp Finset.coeEmb.monotone).functor) (m :=
    ⟨M, .mk fun _ ↦ ⟨⟨image_val_subset⟩⟩⟩) (· {⟨·, ·⟩} _ (by simp))).1 ∅ _
    ((map_comp _ (ι _) _).symm.trans (map_eq_zero_of_factors ((isPullback_fibreProd.of_bot (v₁₁ :=
    baseChangeTransition s (ofHom (algebraMap T.1 (Localization M))) rfl) (v₁₂ := reprMap _) rfl
    isPullback_fibreProd).lift_snd _ (ι (.preimage _ q)) ((Category.assoc ..).trans ((fromPreimage
    .. ≫ homOfLe (unitPoints_le_range_reprMap _ M)) ≫= IsIso.inv_hom_id_assoc (toRange
    (uliftCoyoneda.map _)) (ι _)))) (h.injective_map_residue u (by simpa [← map_comp]))))).elim
    fun t witness ↦ witness.elim fun _ e ↦ ⟨_, w (forall_mem_image.2 fun
    _ ↦ t.dvd_prod_of_mem _) ((map_comp ..).trans e :), M.prod_mem fun c _ ↦ c.2⟩

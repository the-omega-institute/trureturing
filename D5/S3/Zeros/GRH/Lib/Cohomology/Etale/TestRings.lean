/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestRings
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/Etale/TestRings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.Etale.TestRings. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Etale/TestRings.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.TestCohomology
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Test rings: products, quotients, localisations; local rings are valuation rings of
algebraically closed fields. -/


open IsLocalRing Classical ValuationRing IsLocalization IsAIC LocallyConstant Ideal.Quotient
universe u
variable {A : Type u} {B : Type*} [CommRing A] [CommRing B] {M : Submonoid A} {f : A →+* B}
  (K : Type*) [Field K] [IsAlgClosed K]

instance : IsAICLocal K := {}

instance (V : ValuationSubring K) : IsAICLocal V := {of_isIntegrallyClosedIn K with}

/-- A subgroup S of the locally constant functions Spec A → Λ is the whole group if it contains,
for all a in Λ and idempotents e of A, the function equal to a on D(e) and 0 elsewhere. -/
lemma locallyConstant_mem_of_indicator {Λ} [AddCommGroup Λ] {S :
  AddSubgroup (LocallyConstant _ Λ)} (h : ∀ a (e : A)
  i, indicator (const _ a) (PrimeSpectrum.isClopen_iff.2 ⟨e, i, rfl⟩) ∈ S) y : y ∈ S := by
  choose e i H using (PrimeSpectrum.isClopen_iff.1 <| y.2.isClopen_fiber ·)
  convert sum_mem (t := y.range_finite.toFinset) fun a _ ↦ h a _ (i a)
  ext; erw [map_sum (evalAddMonoidHom _)]; simp [Set.indicator, ← H]

/-- Let φ: A → B be a ring map, where of any two elements of A one divides the other. Every x in
the extended ideal φ(J)B is divisible by φ(i) for some i ∈ J. -/
lemma exists_map_dvd_of_mem_map [PreValuationRing A] {J x} : x ∈ Ideal.map f J → ∃ i ∈ J,
  f i ∣ x := by apply Submodule.span_induction <;> simp <;>
  grind [map_dvd, dvd_trans, dvd_add, dvd_mul_left, J.zero_mem, dvd_total]

lemma isTest_of_preValuationRing [IsDomain A] [PreValuationRing A] [IsAIC A] : IsTest A :=
  ⟨‹_›, by simp [IsComparableRing, dvd_total], inferInstance⟩

/-- A product of any family of test rings (`IsTest`) is a test ring. -/
lemma IsTest.pi {ι} {K : ι → _} [∀ i, CommRing (K i)] (h : ∀ i, IsTest (K i) := by
    exact fun _ ↦ isTest_of_preValuationRing) : IsTest (∀ i, K i) := have := (h · |>.3)
  ⟨⟨fun P m d ↦ by simpa [P.eval₂_eq_sum_range, Polynomial.eval, funext_iff, skolem] using
    (h · |>.exists_eval₂_eq_zero (Pi.evalRingHom ..) m d)⟩, fun _ _ ↦ by simpa [IsIdempotentElem,
    funext_iff, pi_dvd_iff, skolem, forall_and] using (h · |>.2 ..), inferInstance⟩

lemma IsTest.isComparableRing_of_associated (h : IsTest A) (g : ∀ y, ∃ x, Associated (f x) y) :
  IsComparableRing f := fun y z ↦ by
  obtain ⟨⟨x, _, ⟨⟩⟩, z, _, ⟨⟩⟩ := g y, g z
  peel h.2 x z; simpa [← mul_assoc] using this.imp f.map_dvd f.map_dvd

lemma IsComparableRing.id : IsComparableRing f → IsComparableRing (@_root_.id B) :=
  (· · · |>.imp' f (by grind [IsIdempotentElem]))

lemma exists_associated_localization y : ∃ x, Associated (algebraMap A (Localization M) x) y :=
  ⟨_, .symm ⟨(map_units ..).unit, sec_spec M y⟩⟩

lemma IsTest.localization : IsTest A → IsTest (Localization M) | h@⟨_, _, _⟩ => ⟨of_isLocalization
  M, (h.isComparableRing_of_associated exists_associated_localization).id, inferInstance⟩

lemma IsTest.quotient (h : IsTest A) {J : Ideal A} : J.IsRadical → IsTest (A ⧸ J) :=
  (⟨h.of_surjective mk_surjective, .id (h.isComparableRing_of_associated
  (mk_surjective.forall.2 (⟨·, .rfl⟩))), J.isRadical_iff_quotient_reduced.1 ·⟩)

/-- For a test ring A and a prime p, the local ring A_p is an absolutely integrally closed local
domain, and some valuation ring of an algebraically closed field is a localisation of A at
p. -/
lemma IsTest.exists_valuationSubring_atPrime (h : IsTest A) (p :
  Ideal A) [p.IsPrime] : let L := Localization.AtPrime p
  IsAICLocal L ∧ PreValuationRing L ∧ ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
    (O : ValuationSubring K) (_ : Algebra A O), IsLocalization.AtPrime O p := by
  intro L; have ⟨_, c, _⟩ : IsTest L := h.localization
  have := PreValuationRing.iff_dvd_total.2
    ⟨(c · · |>.elim (by cases isUnit_or_isUnit_one_sub_self · <;> simp_all))⟩
  have := @NoZeroDivisors.to_isDomain L _ _ ⟨@fun x y e ↦ by
    simpa [e, ← sq] using (dvd_total y x).imp (mul_dvd_mul_left x) (mul_dvd_mul_right · y)⟩
  exact ⟨{}, ‹_›, FractionRing L, _, h.localization.localization.isAlgClosed,
    @Valuation.valuationSubring .., _,
    (isLocalization_iff_of_ringEquiv _ (@equivInteger L _ _ _ _ _ {} _)).1 inferInstance⟩

instance [IsAICLocal A] : IsAlgClosed (ResidueField A) :=
  isAlgClosed (.of_surjective residue_surjective)

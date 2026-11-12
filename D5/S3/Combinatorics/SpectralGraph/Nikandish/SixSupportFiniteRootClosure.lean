/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootClosure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supplied Nikandish tower and finite-root objects, pending current canonical admission. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteRootCount

/-! This identifies the concrete root primes and
localizations with primes and localizations of Lean's canonical integralClosure.
The explicit Order was itself proved an integral closure in Geometry01.
-/
namespace NikandishE3.FiniteDRoot
open Polynomial IsLocalRing WithZero
open scoped QuadraticAlgebra
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (k : Type*) [Field k] [CharZero k]

def closureRootIdeal (r : DRoot k) : Ideal (Closure k) :=
  (rootIdeal k r).comap (orderClosureEquiv k).symm.toRingHom

instance closureRootIdeal_prime (r : DRoot k) : (closureRootIdeal k r).IsPrime :=
  Ideal.comap_isPrime _ _
instance closureRootIdeal_maximal (r : DRoot k) : (closureRootIdeal k r).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (orderClosureEquiv k).symm.surjective

theorem closureRootIdeal_comap (r : DRoot k) :
    (closureRootIdeal k r).comap (orderClosureEquiv k).toRingHom = rootIdeal k r := by
  ext z
  change (orderClosureEquiv k).symm ((orderClosureEquiv k) z) ∈ rootIdeal k r ↔ _
  simp

theorem closureRootIdeal_under (r : DRoot k) :
    (closureRootIdeal k r).under (R k) = baseIdeal k r := by
  rw [← rootIdeal_under k r]
  ext p
  change (orderClosureEquiv k).symm (algebraMap (R k) (Closure k) p) ∈ rootIdeal k r ↔ _
  rw [(orderClosureEquiv k).symm.commutes]
  rfl

instance closureRootIdeal_liesOver (r : DRoot k) :
    (closureRootIdeal k r).LiesOver (baseIdeal k r) :=
  (Ideal.liesOver_iff _ _).mpr (closureRootIdeal_under k r).symm

theorem closure_unique_prime_above (r : DRoot k) (Q : Ideal (Closure k)) [Q.IsPrime]
    (hQ : Q.under (R k) = baseIdeal k r) : Q = closureRootIdeal k r := by
  have hunder : (Q.comap (orderClosureEquiv k).toRingHom).under (R k) = baseIdeal k r := by
    rw [← hQ]
    ext p
    change (orderClosureEquiv k) (algebraMap (R k) (Order k) p) ∈ Q ↔ _
    rw [(orderClosureEquiv k).commutes]
    rfl
  apply Ideal.comap_injective_of_surjective (orderClosureEquiv k).toRingHom
    (orderClosureEquiv k).surjective
  rw [closureRootIdeal_comap]
  exact unique_prime_above k r _ hunder

abbrev ClosureLocal (r : DRoot k) := Localization.AtPrime (closureRootIdeal k r)

theorem closure_primeCompl_map (r : DRoot k) :
    (rootIdeal k r).primeCompl.map (orderClosureEquiv k).toMonoidHom =
      (closureRootIdeal k r).primeCompl := by
  have he := (orderClosureEquiv k).toRingEquiv.map_primeCompl_comap_eq (closureRootIdeal k r)
  change Submonoid.map (orderClosureEquiv k).toMonoidHom
    ((closureRootIdeal k r).comap (orderClosureEquiv k).toRingHom).primeCompl =
      (closureRootIdeal k r).primeCompl at he
  simpa only [closureRootIdeal_comap] using he

@[irreducible] def closureLocalEquiv (r : DRoot k) : Local k r ≃ₐ[R k] ClosureLocal k r :=
  IsLocalization.algEquivOfAlgEquiv (Local k r) (ClosureLocal k r)
    (orderClosureEquiv k) (closure_primeCompl_map k r)

instance closureLocal_dvr (r : DRoot k) : IsDiscreteValuationRing (ClosureLocal k r) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (closureLocalEquiv k r)

theorem closureLocalEquiv_algebraMap (r : DRoot k) (w : Order k) :
    closureLocalEquiv k r (algebraMap (Order k) (Local k r) w) =
      algebraMap (Closure k) (ClosureLocal k r) (orderClosureEquiv k w) :=
  by
    unfold closureLocalEquiv
    exact IsLocalization.algEquivOfAlgEquiv_eq _ _

def closureY : Closure k := (orderClosureEquiv k) (Y k)
def closureLocalY (r : DRoot k) : ClosureLocal k r :=
  algebraMap (Closure k) (ClosureLocal k r) (closureY k)

theorem closureLocalEquiv_Y (r : DRoot k) :
    closureLocalEquiv k r (localY k r) = closureLocalY k r :=
  by
    unfold closureLocalEquiv
    exact IsLocalization.algEquivOfAlgEquiv_eq _ _

theorem closureLocal_maximalIdeal (r : DRoot k) :
    IsLocalRing.maximalIdeal (ClosureLocal k r) = Ideal.span {closureLocalY k r} := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer (closureLocalY k r)).mp
  rw [← closureLocalEquiv_Y]
  exact (MulEquiv.irreducible_iff (closureLocalEquiv k r)).mpr (localY_irreducible k r)

/-- This explicit embedding is compatible with the already fixed H embedding. -/
def closureLocalIntoH (r : DRoot k) : ClosureLocal k r →+* H k :=
  (localIntoH k r).comp (closureLocalEquiv k r).symm.toRingHom

theorem closureLocalIntoH_on_base (r : DRoot k) (z : Closure k) :
    closureLocalIntoH k r (algebraMap (Closure k) (ClosureLocal k r) z) = (z : H k) := by
  obtain ⟨w, rfl⟩ := (orderClosureEquiv k).surjective z
  rw [← closureLocalEquiv_algebraMap k r w]
  change localIntoH k r ((closureLocalEquiv k r).symm
    (closureLocalEquiv k r (algebraMap (Order k) (Local k r) w))) = _
  rw [AlgEquiv.symm_apply_apply]
  change (IsLocalization.lift (S := Local k r) (g := (intoH k).toRingHom) _)
    (algebraMap (Order k) (Local k r) w) = _
  rw [IsLocalization.lift_eq]
  exact (IsIntegralClosure.algebraMap_equiv (R k) (Order k) (H k) (Closure k) w).symm

theorem closureLocalIntoH_Y (r : DRoot k) :
    closureLocalIntoH k r (closureLocalY k r) = y k := by
  rw [closureLocalY, closureLocalIntoH_on_base]
  exact (IsIntegralClosure.algebraMap_equiv (R k) (Order k) (H k) (Closure k) (Y k)).trans
    (intoH_Y k)

instance closureStalkAlgebra (r : DRoot k) : Algebra (Closure k)
    ((affineClosure k).presheaf.stalk
      (⟨closureRootIdeal k r, inferInstance⟩ : PrimeSpectrum (Closure k))) :=
  AlgebraicGeometry.StructureSheaf.stalkAlgebra (CommRingCat.of (Closure k)) _

def closureStalkEquiv (r : DRoot k) : ClosureLocal k r ≃ₐ[Closure k]
    ((affineClosure k).presheaf.stalk
      (⟨closureRootIdeal k r, inferInstance⟩ : PrimeSpectrum (Closure k))) :=
  AlgebraicGeometry.StructureSheaf.stalkIso (Closure k) ⟨closureRootIdeal k r, inferInstance⟩

abbrev ClosureDPlace := {Q : PrimeSpectrum (Closure k) //
  ∃ r : DRoot k, Q.asIdeal.under (R k) = baseIdeal k r}

def rootToClosurePlace (r : DRoot k) : ClosureDPlace k :=
  ⟨⟨closureRootIdeal k r, inferInstance⟩, r, closureRootIdeal_under k r⟩

theorem rootToClosurePlace_bijective : Function.Bijective (rootToClosurePlace k) := by
  constructor
  · intro r s h
    apply rootIdeal_injective k
    have hi := congrArg (fun Q : ClosureDPlace k =>
      Q.1.asIdeal.comap (orderClosureEquiv k).toRingHom) h
    simpa only [rootToClosurePlace, closureRootIdeal_comap] using hi
  · intro Q
    obtain ⟨r, hr⟩ := Q.2
    refine ⟨r, ?_⟩
    apply Subtype.ext
    apply PrimeSpectrum.ext
    exact (closure_unique_prime_above k r Q.1.asIdeal hr).symm

def rootClosurePlaceEquiv : DRoot k ≃ ClosureDPlace k :=
  Equiv.ofBijective (rootToClosurePlace k) (rootToClosurePlace_bijective k)
instance closurePlaceFintype : Fintype (ClosureDPlace k) := Fintype.ofEquiv (DRoot k) (rootClosurePlaceEquiv k)

theorem actual_closure_place_count [IsAlgClosed k] : Fintype.card (ClosureDPlace k) = 8 := by
  calc
    Fintype.card (ClosureDPlace k) = Fintype.card (DRoot k) :=
      (Fintype.card_congr (rootClosurePlaceEquiv k)).symm
    _ = 8 := root_count k

theorem closure_mapped_baseIdeal_square (r : DRoot k) :
    (baseIdeal k r).map (algebraMap (R k) (ClosureLocal k r)) =
      IsLocalRing.maximalIdeal (ClosureLocal k r)^2 := by
  have he := congrArg (Ideal.map (closureLocalEquiv k r).toRingHom)
    (mapped_baseIdeal_square k r)
  rw [Ideal.map_map, Ideal.map_pow, local_maximalIdeal,
    Ideal.map_span, Set.image_singleton] at he
  change (baseIdeal k r).map
    ((closureLocalEquiv k r).toRingHom.comp (algebraMap (R k) (Local k r))) =
      (Ideal.span {closureLocalEquiv k r (localY k r)})^2 at he
  rw [closureLocalEquiv_Y, ← closureLocal_maximalIdeal] at he
  have hc : (closureLocalEquiv k r).toRingHom.comp (algebraMap (R k) (Local k r)) =
      algebraMap (R k) (ClosureLocal k r) :=
    RingHom.ext (fun p => (closureLocalEquiv k r).commutes p)
  rwa [hc] at he

theorem closure_ramification_two (r : DRoot k) :
    (closureRootIdeal k r).ramificationIdx (R k) = 2 := by
  rw [Ideal.ramificationIdx_eq (baseIdeal k r) (closureRootIdeal k r),
    closure_mapped_baseIdeal_square,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

theorem closure_residue_degree_one (r : DRoot k) :
    (closureRootIdeal k r).inertiaDeg (R k) = 1 := by
  have hp : ((closureRootIdeal k r).under (R k)).IsMaximal := by
    rw [closureRootIdeal_under]
    infer_instance
  letI := hp
  letI : Field ((R k) ⧸ (closureRootIdeal k r).under (R k)) := Ideal.Quotient.field _
  letI : Field ((Closure k) ⧸ closureRootIdeal k r) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg_eq_of_isMaximal ((closureRootIdeal k r).under (R k)) (closureRootIdeal k r)]
  apply Module.finrank_of_bijective_algebraMap
  refine ⟨Ideal.algebraMap_quotient_injective, ?_⟩
  intro z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨Ideal.Quotient.mk _ (C (((orderClosureEquiv k).symm w).re.eval r.1)), ?_⟩
  change Ideal.Quotient.mk _ (algebraMap (R k) (Closure k)
      (C (((orderClosureEquiv k).symm w).re.eval r.1))) = Ideal.Quotient.mk _ w
  apply Ideal.Quotient.eq.mpr
  change ((orderClosureEquiv k).symm (algebraMap (R k) (Closure k)
      (C (((orderClosureEquiv k).symm w).re.eval r.1)) - w)).re.eval r.1 = 0
  rw [map_sub, (orderClosureEquiv k).symm.commutes]
  simp

def closureLocalF (r : DRoot k) : ClosureLocal k r := closureLocalEquiv k r (localF k r)
theorem closureLocalF_unit (r : DRoot k) : IsUnit (closureLocalF k r) :=
  (localF_unit k r).map (closureLocalEquiv k r).toRingHom
theorem closureLocalF_intoH (r : DRoot k) :
    closureLocalIntoH k r (closureLocalF k r) = f k := by
  change localIntoH k r ((closureLocalEquiv k r).symm (closureLocalEquiv k r (localF k r))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact localF_intoH k r

instance closureLocalHAlgebra (r : DRoot k) : Algebra (ClosureLocal k r) (H k) :=
  (closureLocalIntoH k r).toAlgebra
instance closureLocalHTower (r : DRoot k) : IsScalarTower (Closure k) (ClosureLocal k r) (H k) :=
  IsScalarTower.of_algebraMap_eq (fun z => (closureLocalIntoH_on_base k r z).symm)
instance closureLocalHFractions (r : DRoot k) : IsFractionRing (ClosureLocal k r) (H k) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (closureRootIdeal k r).primeCompl
    (ClosureLocal k r) (H k)

def closureNormalizedValuation (r : DRoot k) : Valuation (H k) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (ClosureLocal k r)).valuation (H k)

theorem closure_valuation_y (r : DRoot k) :
    closureNormalizedValuation k r (y k) = WithZero.exp (-1 : ℤ) := by
  rw [← closureLocalIntoH_Y k r]
  change (IsDiscreteValuationRing.maximalIdeal (ClosureLocal k r)).valuation (H k)
    (algebraMap (ClosureLocal k r) (H k) (closureLocalY k r)) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
  · rw [← closureLocalEquiv_Y]
    simpa only [map_zero] using (closureLocalEquiv k r).injective.ne (localY_ne_zero k r)
  · exact closureLocal_maximalIdeal k r

theorem closure_valuation_local_unit (r : DRoot k) (z : ClosureLocal k r) (hz : IsUnit z) :
    closureNormalizedValuation k r (algebraMap (ClosureLocal k r) (H k) z) = 1 := by
  apply (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
    (IsDiscreteValuationRing.maximalIdeal (ClosureLocal k r))).mpr
  change z ∉ IsLocalRing.maximalIdeal (ClosureLocal k r)
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hz

theorem closure_valuation_f (r : DRoot k) : closureNormalizedValuation k r (f k) = 1 := by
  rw [← closureLocalF_intoH k r]
  exact closure_valuation_local_unit k r _ (closureLocalF_unit k r)

theorem closure_order_f_zero (r : DRoot k) :
    IsDiscreteValuationRing.addVal (ClosureLocal k r) (closureLocalF k r) = 0 :=
  IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (closureLocalF_unit k r)

theorem closure_valuation_delta (r : DRoot k) :
    closureNormalizedValuation k r (algebraMap (R k) (H k) (X - C r.1)) =
      WithZero.exp (-2 : ℤ) := by
  let d := closureLocalEquiv k r (localDelta k r)
  let u := closureLocalEquiv k r (localQuotient k r)
  have hu : IsUnit u := (localQuotient_unit k r).map (closureLocalEquiv k r).toRingHom
  have hy : (closureLocalY k r)^2 = d * u := by
    simpa only [map_pow, map_mul, closureLocalEquiv_Y] using
      congrArg (closureLocalEquiv k r) (localY_square k r)
  have hdH : algebraMap (ClosureLocal k r) (H k) d =
      algebraMap (R k) (H k) (X - C r.1) := by
    change localIntoH k r ((closureLocalEquiv k r).symm
      ((closureLocalEquiv k r) (localDelta k r))) = _
    rw [AlgEquiv.symm_apply_apply]
    exact localIntoH_delta k r
  have hyH : algebraMap (ClosureLocal k r) (H k) (closureLocalY k r) = y k :=
    closureLocalIntoH_Y k r
  have he := congrArg (fun z : ClosureLocal k r =>
    closureNormalizedValuation k r (algebraMap (ClosureLocal k r) (H k) z)) hy
  simp only [map_pow, map_mul, hyH, hdH, closure_valuation_y,
    closure_valuation_local_unit k r _ hu, mul_one] at he
  rw [← he]
  norm_num [pow_two, ← WithZero.exp_add]

theorem every_closure_place_data (Q : ClosureDPlace k) :
    ∃ r : DRoot k, Q.1.asIdeal = closureRootIdeal k r ∧
      IsDiscreteValuationRing (ClosureLocal k r) ∧
      IsLocalRing.maximalIdeal (ClosureLocal k r) = Ideal.span {closureLocalY k r} ∧
      (closureRootIdeal k r).ramificationIdx (R k) = 2 ∧
      (closureRootIdeal k r).inertiaDeg (R k) = 1 ∧
      IsUnit (closureLocalF k r) ∧ closureLocalIntoH k r (closureLocalF k r) = f k ∧
      closureNormalizedValuation k r (y k) = WithZero.exp (-1 : ℤ) ∧
      closureNormalizedValuation k r (algebraMap (R k) (H k) (X - C r.1)) =
        WithZero.exp (-2 : ℤ) ∧
      closureNormalizedValuation k r (f k) = 1 ∧
      IsDiscreteValuationRing.addVal (ClosureLocal k r) (closureLocalF k r) = 0 := by
  obtain ⟨r, hr⟩ := Q.2
  exact ⟨r, closure_unique_prime_above k r Q.1.asIdeal hr, inferInstance,
    closureLocal_maximalIdeal k r, closure_ramification_two k r,
    closure_residue_degree_one k r, closureLocalF_unit k r, closureLocalF_intoH k r,
    closure_valuation_y k r, closure_valuation_delta k r, closure_valuation_f k r,
    closure_order_f_zero k r⟩

end
end NikandishE3.FiniteDRoot

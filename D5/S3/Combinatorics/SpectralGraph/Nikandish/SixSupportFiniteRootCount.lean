/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supplied Nikandish tower and finite-root objects, pending current canonical admission. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteRootUnits

/-! The counted objects are actual prime ideals in
an actual integral closure of k[b] inside the accepted H, not roots relabelled as
places without a prime/localization construction. The root equivalence is proved.
-/
namespace NikandishE3.FiniteDRoot
open Polynomial WithZero
open scoped QuadraticAlgebra
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (k : Type*) [Field k] [CharZero k]

theorem D_map_degree : (pk k D).natDegree = 8 := by
  change (D.map (algebraMap ℚ k)).natDegree = 8
  rw [Polynomial.natDegree_map, degree_D]

theorem D_map_ne_zero : pk k D ≠ 0 := by
  intro hz
  have hd := D_map_degree k
  rw [hz, natDegree_zero] at hd
  omega

def rootSetEquiv : DRoot k ≃ (pk k D).rootSet k where
  toFun r := ⟨r.1, (Polynomial.mem_rootSet_of_ne (D_map_ne_zero k)).mpr (by simpa using r.2)⟩
  invFun r := ⟨r.1, by
    have hr := (Polynomial.mem_rootSet_of_ne (D_map_ne_zero k)).mp r.2
    simpa using hr⟩
  left_inv r := by apply Subtype.ext; rfl
  right_inv r := by apply Subtype.ext; rfl

instance rootFintype : Fintype (DRoot k) := Fintype.ofEquiv ((pk k D).rootSet k) (rootSetEquiv k).symm

theorem rootIdeal_injective : Function.Injective (rootIdeal k) := by
  intro r s hrs
  have hm : delta k r ∈ rootIdeal k s := hrs ▸ delta_mem k r
  have he : s.1 - r.1 = 0 := by simpa [delta] using hm
  apply Subtype.ext
  exact (sub_eq_zero.mp he).symm

/-- The domain is actual prime ideals of the actual order, lying over a D-root.
Its defining property assumes no DVR, ramification, unit, valuation or count. -/
abbrev FiniteDPlace := {Q : PrimeSpectrum (Order k) //
  ∃ r : DRoot k, Q.asIdeal.under (R k) = baseIdeal k r}

def rootToPlace (r : DRoot k) : FiniteDPlace k :=
  ⟨⟨rootIdeal k r, inferInstance⟩, r, rootIdeal_under k r⟩

theorem rootToPlace_bijective : Function.Bijective (rootToPlace k) := by
  constructor
  · intro r s hrs
    apply rootIdeal_injective k
    exact congrArg (fun Q : FiniteDPlace k => Q.1.asIdeal) hrs
  · intro Q
    obtain ⟨r, hr⟩ := Q.2
    refine ⟨r, ?_⟩
    apply Subtype.ext
    apply PrimeSpectrum.ext
    exact (unique_prime_above k r Q.1.asIdeal hr).symm

def rootPlaceEquiv : DRoot k ≃ FiniteDPlace k :=
  Equiv.ofBijective (rootToPlace k) (rootToPlace_bijective k)

instance placeFintype : Fintype (FiniteDPlace k) := Fintype.ofEquiv (DRoot k) (rootPlaceEquiv k)

theorem root_count [IsAlgClosed k] : Fintype.card (DRoot k) = 8 := by
  calc
    Fintype.card (DRoot k) = Fintype.card ((pk k D).rootSet k) :=
      Fintype.card_congr (rootSetEquiv k)
    _ = (pk k D).natDegree := Polynomial.card_rootSet_eq_natDegree
      (D_separable k) (IsAlgClosed.splits_domain _)
    _ = 8 := D_map_degree k

theorem actual_place_count [IsAlgClosed k] : Fintype.card (FiniteDPlace k) = 8 := by
  calc
    Fintype.card (FiniteDPlace k) = Fintype.card (DRoot k) :=
      (Fintype.card_congr (rootPlaceEquiv k)).symm
    _ = 8 := root_count k

/-- The actual prime picked by the inverse equivalence has all the previously
constructed data. This theorem introduces no target-bearing structure. -/
theorem every_place_data (Q : FiniteDPlace k) :
    ∃ r : DRoot k, Q.1.asIdeal = rootIdeal k r ∧
      IsDiscreteValuationRing (Local k r) ∧
      IsLocalRing.maximalIdeal (Local k r) = Ideal.span {localY k r} ∧
      (rootIdeal k r).ramificationIdx (R k) = 2 ∧
      (rootIdeal k r).inertiaDeg (R k) = 1 ∧
      IsUnit (localF k r) ∧ algebraMap (Local k r) (H k) (localF k r) = f k ∧
      normalizedValuation k r (y k) = WithZero.exp (-1 : ℤ) ∧
      normalizedValuation k r (algebraMap (R k) (H k) (X - C r.1)) = WithZero.exp (-2 : ℤ) ∧
      normalizedValuation k r (f k) = 1 := by
  obtain ⟨r, hr⟩ := Q.2
  exact ⟨r, unique_prime_above k r Q.1.asIdeal hr, inferInstance,
    local_maximalIdeal k r, ramification_two k r, residue_degree_one k r,
    localF_unit k r, localF_intoH k r, valuation_y k r, valuation_delta k r,
    valuation_f k r⟩

end
end NikandishE3.FiniteDRoot

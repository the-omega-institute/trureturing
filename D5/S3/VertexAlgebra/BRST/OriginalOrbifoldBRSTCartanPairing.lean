/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCartanPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCartanPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native inserted BPZ form has hyperbolic Cartan Gram matrix at momentum zero. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTCartan
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalPairing

/-! The skew current pairing and the inserted ghost pairing each contribute a
minus sign. Pairing against the two native Cartan classes detects both coordinates
of every class at momentum zero. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCartanPairing

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket vacuum)
open BcGhostFock (c)
open BcGhostCharge (charge)
open BcGhostHermitian (Homogeneous)
open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData hyperbolic_gram
  matterDatum orbifoldVertexAlgebra)
open OriginalOrbifoldBRSTBPZWard (betaTotal)
open OriginalOrbifoldBRSTCartan (cartanCycle cartanCycle_coe h h_mem_physicalMomentum_zero
  span_h_eq_physicalMomentum_zero)
open OriginalOrbifoldBRSTGhostBPZ (beta beta_c beta_vacuum_top)
open OriginalOrbifoldBRSTMomentum (momentumCurrent physicalMomentum)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ physicalBPZ_representatives)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ orbifoldBPZ_apply matterBPZ_charge)
open LatticeGeneratingFieldLocality (Charge)
open LatticeFiniteNegativeGeneration (neutralField neutralPolynomialMode)
open SourceBPZ.OriginalSourcePairing (integerWick integerWick_creation
  sourcePairing sourcePairing_single_single sourcePairing_vacuum)

open private opposite from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
open private betaTotal_tmul ket_homogeneous from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem cartanCycle_tensor (i : Fin hyperbolicData.rank) :
    ((cartanCycle i).1 : State) =
      (orbifoldVertexAlgebra.vacuum ⊗ₜ[ℂ] Finsupp.single (0 : Charge hyperbolicData)
        (MvPolynomial.X (opposite i, 0))) ⊗ₜ[ℂ] ket {1} := by
  have hmode : neutralPolynomialMode hyperbolicData (opposite i) 0 (-1) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (opposite i, 0)) :=
    LatticeSugawaraCurrents.neutralPolynomialMode_negative hyperbolicData (opposite i) 0 0
  simp only [cartanCycle_coe, momentumCurrent, VirasoroBRST.ghostC, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
    BcGhostFock.ghost_vacuum.2.2.1, LatticeAllStateField.vacuum,
    LatticeSugawaraCurrents.neutralField_ncoeff, LatticeSugawaraCurrents.neutralMode_single,
    hmode, LinearMap.mulLeft_apply, mul_one]

private theorem orbifoldBPZ_vacuum :
    orbifoldBPZ orbifoldVertexAlgebra.vacuum orbifoldVertexAlgebra.vacuum = 1 := by
  rw [orbifoldBPZ_apply]
  change sourcePairing leechData (LatticeAllStateField.vacuum leechData)
      (LatticeAllStateField.vacuum leechData) +
      TwistedGround.ActualChargedAdjoint.actualForm leechData leech_spec.2.1 0 0 = 1
  simp only [sourcePairing_vacuum, map_zero, add_zero]

private theorem integerWick_current (i j : Fin hyperbolicData.rank) :
    integerWick hyperbolicData (MvPolynomial.X (i, 0)) (MvPolynomial.X (j, 0)) =
      -(hyperbolicData.G i j : ℂ) := by
  have hv := sourcePairing_vacuum hyperbolicData
  change sourcePairing hyperbolicData (Finsupp.single 0 1) (Finsupp.single 0 1) = 1 at hv
  have hOne : integerWick hyperbolicData 1 1 = 1 := by
    simpa only [sourcePairing_single_single, neg_zero, ite_eq_left] using hv
  calc
    _ = integerWick hyperbolicData (MvPolynomial.X (i, 0) * 1) (MvPolynomial.X (j, 0)) := by
      rw [mul_one]
    _ = _ := by
      rw [integerWick_creation, LatticeActualAnnihilation.annihilate_X]
      simp only [Nat.cast_zero, zero_add, ite_eq_left, neg_one_smul, map_neg, map_smul,
        smul_eq_mul, hOne, mul_one]

private theorem ghostBPZ_cartan : beta (ket {1}) (c 0 (ket {1})) = -1 := by
  have hv : Homogeneous 0 vacuum := by
    have hcharge : charge (∅ : Finset ℕ) = 0 := by decide
    rw [CountableOccupationFock.vacuum, ← hcharge]
    exact ket_homogeneous ∅
  rw [← BcGhostFock.ghost_vacuum.2.2.1, beta_c 1 hv, beta_vacuum_top, zpow_zero, neg_one_mul]

/-- The physical Cartan Gram matrix is the integral hyperbolic Gram matrix over `ℂ`.
The diagonal entries are zero and both off-diagonal entries are one. -/
theorem physicalBPZ_h (i j : Fin hyperbolicData.rank) :
    physicalBPZ (h i) (h j) = (hyperbolicData.G i j : ℂ) := by
  calc
    _ = (hyperbolicData.G (opposite i) (opposite j) : ℂ) := by
      rw [physicalBPZ_representatives (h i) (h j) (cartanCycle i) (cartanCycle j) rfl rfl]
      change betaTotal ((cartanCycle i).1 : State)
        (VirasoroBRST.ghostC matterDatum 0 ((cartanCycle j).1 : State)) = _
      simp only [cartanCycle_tensor, VirasoroBRST.ghostC, BcGhostChargeTensor.C,
        BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply]
      rw [betaTotal_tmul, matterBPZ_charge, neg_zero, ite_eq_left rfl, orbifoldBPZ_vacuum,
        one_mul, integerWick_current, ghostBPZ_cartan, mul_neg_one, neg_neg]
    _ = _ := by
      rw [hyperbolic_gram]
      fin_cases i <;> fin_cases j <;> rfl

private theorem restrict_nondegenerate_of_hyperbolic_pair
    {V : Type*} [AddCommGroup V] [Module ℂ V] (B : LinearMap.BilinForm ℂ V)
    (W : Submodule ℂ V) (u v : V) (hu : u ∈ W) (hv : v ∈ W)
    (hspan : Submodule.span ℂ ({u, v} : Set V) = W)
    (huu : B u u = 0) (huv : B u v = 1) (hvu : B v u = 1) (hvv : B v v = 0) :
    (B.restrict W).Nondegenerate := by
  change (∀ x : W, (∀ y : W, B x.val y.val = 0) → x = 0) ∧
    (∀ x : W, (∀ y : W, B y.val x.val = 0) → x = 0)
  constructor <;> intro x hrad
  all_goals
    have hmem : x.val ∈ Submodule.span ℂ ({u, v} : Set V) := by
      rw [hspan]
      exact x.property
    obtain ⟨a, b, hx⟩ := Submodule.mem_span_pair.mp hmem
    have ha := hrad ⟨v, hv⟩
    have hb := hrad ⟨u, hu⟩
    dsimp only at ha hb
    rw [← hx] at ha hb
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      huu, huv, hvu, hvv, mul_zero, mul_one, add_zero, zero_add] at ha hb
    exact Subtype.ext (show x.val = (0 : V) by
      simpa only [ha, hb, zero_smul, add_zero] using hx.symm)

set_option maxHeartbeats 2000000 in
-- Elaborating the Cartan span and Gram entries requires reducing the physical BRST quotient's subtypes.
/-- The restriction of the inserted physical BPZ form to the actual momentum-zero
subspace has trivial left and right radicals. -/
theorem physicalBPZ_momentum_zero_nondegenerate :
    (physicalBPZ.restrict (physicalMomentum (0 : Charge hyperbolicData))).Nondegenerate := by
  have hrange : Set.range h = ({h 0, h 1} : Set DegreeOne) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact Set.mem_range_self 0
      · exact Set.mem_range_self 1
  have hspan : Submodule.span ℂ ({h 0, h 1} : Set DegreeOne) =
      physicalMomentum (0 : Charge hyperbolicData) := by
    rw [← hrange, span_h_eq_physicalMomentum_zero]
  have h00 : physicalBPZ (h 0) (h 0) = 0 := by
    rw [physicalBPZ_h, hyperbolic_gram, OrderedHyperbolicExtension.U_zero_zero, Int.cast_zero]
  have h01 : physicalBPZ (h 0) (h 1) = 1 := by
    rw [physicalBPZ_h, hyperbolic_gram, OrderedHyperbolicExtension.U_zero_one, Int.cast_one]
  have h10 : physicalBPZ (h 1) (h 0) = 1 := by
    rw [physicalBPZ_h, hyperbolic_gram, OrderedHyperbolicExtension.U_one_zero, Int.cast_one]
  have h11 : physicalBPZ (h 1) (h 1) = 0 := by
    rw [physicalBPZ_h, hyperbolic_gram, OrderedHyperbolicExtension.U_one_one, Int.cast_zero]
  exact restrict_nondegenerate_of_hyperbolic_pair physicalBPZ _ (h 0) (h 1)
    (h_mem_physicalMomentum_zero 0) (h_mem_physicalMomentum_zero 1) hspan h00 h01 h10 h11

#print axioms physicalBPZ_h
#print axioms physicalBPZ_momentum_zero_nondegenerate

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCartanPairing

end

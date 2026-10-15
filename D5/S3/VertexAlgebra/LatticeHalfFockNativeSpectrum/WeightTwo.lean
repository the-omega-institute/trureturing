/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/WeightTwo
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/WeightTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unrestricted occupation-one classification and the actual weight-two space. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Grading

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

def oneOccupation (D : LatticeData) (colour : Fin D.rank) : Occupation D :=
  Finsupp.single (colour, 0) 1

theorem oneOccupation_injective (D : LatticeData) : Function.Injective (oneOccupation D) := by
  classical
  intro left right equality
  by_contra different
  have coordinate := congrArg (fun exponent : Occupation D => exponent (left, 0)) equality
  simp [oneOccupation, Finsupp.single_apply, different] at coordinate

theorem occupation_one_iff (D : LatticeData) (exponent : Occupation D) :
    occupationWeight D exponent = 1 ↔ ∃! colour : Fin D.rank, exponent = oneOccupation D colour := by
  classical
  constructor
  · intro weight_one
    have nonzero : exponent ≠ 0 := by
      intro zero
      simp [occupationWeight, zero] at weight_one
    obtain ⟨index, member⟩ := Finsupp.support_nonempty_iff.mpr nonzero
    have positive : exponent index ≠ 0 := Finsupp.mem_support_iff.mp member
    have sub_weight := Finsupp.weight_sub_single_add
      (w := fun index : Index D => 2 * index.2 + 1) positive
    change occupationWeight D (exponent - Finsupp.single index 1) +
      (2 * index.2 + 1) = occupationWeight D exponent at sub_weight
    have mode_zero : index.2 = 0 := by omega
    have remainder_weight_zero : occupationWeight D (exponent - Finsupp.single index 1) = 0 := by
      omega
    have remainder_zero : exponent - Finsupp.single index 1 = 0 := by
      apply Finsupp.ext
      intro coordinate
      have bound := Finsupp.le_weight (fun index : Index D => 2 * index.2 + 1)
        (s := coordinate) (by omega) (exponent - Finsupp.single index 1)
      change (exponent - Finsupp.single index 1 : Occupation D) coordinate ≤
        occupationWeight D (exponent - Finsupp.single index 1) at bound
      simp only [remainder_weight_zero, Nat.le_zero] at bound
      exact bound
    have singleton : exponent = oneOccupation D index.1 := by
      have expansion := Finsupp.sub_add_single_one_cancel positive
      rw [remainder_zero, zero_add] at expansion
      rw [← expansion]
      cases index with
      | mk colour mode => simp only at mode_zero; subst mode; rfl
    refine ⟨index.1, singleton, ?_⟩
    intro colour equality
    exact oneOccupation_injective D (equality.symm.trans singleton)
  · rintro ⟨colour, equality, uniqueness⟩
    rw [equality]
    simp [occupationWeight, oneOccupation, Finsupp.weight_single]

theorem rank24_weight_two_iff (D : LatticeData) (rank24 : D.rank = 24) (level : ℕ) :
    weightValue D level = 2 ↔ level = 1 := by
  constructor
  · intro equality
    have cast : (level : ℂ) = 1 := by
      simp only [weightValue, rank24] at equality
      linear_combination 2 * equality
    exact_mod_cast cast
  · rintro rfl
    norm_num [weightValue, rank24]

def weightTwoCreation (D : LatticeData) (hu : IsUnit D.G.det) :
    (Fin D.rank → ActualGround D hu) →ₗ[ℂ] ActualTensor D hu where
  toFun ground := ∑ colour, (X (colour, 0) : Oscillator D) ⊗ₜ[ℂ] ground colour
  map_add' left right := by
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' scalar ground := by
    simp [TensorProduct.tmul_smul, Finset.smul_sum]

theorem creation_coordinate (D : LatticeData) (hu : IsUnit D.G.det)
    (ground : Fin D.rank → ActualGround D hu) (exponent : Occupation D) :
    coefficients D hu (weightTwoCreation D hu ground) exponent =
      ∑ colour, if oneOccupation D colour = exponent then ground colour else 0 := by
  classical
  simp only [weightTwoCreation, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Finsupp.finsetSum_apply, coefficients_tmul, MvPolynomial.coeff_X, oneOccupation]
  apply Finset.sum_congr rfl
  intro colour member
  split_ifs <;> simp_all

theorem creation_selected_coordinate (D : LatticeData) (hu : IsUnit D.G.det)
    (ground : Fin D.rank → ActualGround D hu) (colour : Fin D.rank) :
    coefficients D hu (weightTwoCreation D hu ground) (oneOccupation D colour) = ground colour := by
  classical
  rw [creation_coordinate]
  simp [(oneOccupation_injective D).eq_iff]

theorem creation_homogeneous (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) (ground : Fin D.rank → ActualGround D hu) :
    weightTwoCreation D hu ground ∈ eigenspace D hu H 2 := by
  rw [eigen_support_iff D hu H hHG hGH]
  intro exponent different
  rw [creation_coordinate]
  apply Finset.sum_eq_zero
  intro colour member
  have different_exponent : oneOccupation D colour ≠ exponent := by
    intro equality
    apply different
    rw [← equality]
    have one : occupationWeight D (oneOccupation D colour) = 1 :=
      (occupation_one_iff D _).mpr ⟨colour, rfl, fun other equality =>
        oneOccupation_injective D equality.symm⟩
    rw [one]
    exact (rank24_weight_two_iff D rank24 1).mpr rfl
  simp [different_exponent]

theorem weight_two_reconstruction (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) (state : eigenspace D hu H 2) :
    weightTwoCreation D hu (fun colour => coefficients D hu state.val (oneOccupation D colour)) =
      state.val := by
  classical
  apply (coefficients D hu).injective
  apply Finsupp.ext
  intro exponent
  by_cases weight_one : occupationWeight D exponent = 1
  · obtain ⟨colour, equality, uniqueness⟩ := (occupation_one_iff D exponent).mp weight_one
    rw [equality, creation_selected_coordinate]
  · have zero : coefficients D hu state.val exponent = 0 := by
      apply (eigen_support_iff D hu H hHG hGH _ state.val).mp state.property exponent
      exact fun equality => weight_one ((rank24_weight_two_iff D rank24 _).mp equality)
    rw [creation_coordinate, zero]
    apply Finset.sum_eq_zero
    intro colour member
    have different : oneOccupation D colour ≠ exponent := by
      intro equality
      apply weight_one
      rw [← equality]
      simp [oneOccupation, occupationWeight, Finsupp.weight_single]
    simp [different]

def weightTwoEquiv (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) :
    eigenspace D hu H 2 ≃ₗ[ℂ] (Fin D.rank → ActualGround D hu) where
  toFun state colour := coefficients D hu state.val (oneOccupation D colour)
  invFun ground := ⟨weightTwoCreation D hu ground, creation_homogeneous D hu H hHG hGH rank24 ground⟩
  left_inv state := Subtype.ext (weight_two_reconstruction D hu H hHG hGH rank24 state)
  right_inv ground := funext (creation_selected_coordinate D hu ground)
  map_add' left right := by
    funext colour
    simp
  map_smul' scalar state := by
    funext colour
    simp

def groundCoordinateEquiv (D : LatticeData) (hu : IsUnit D.G.det) :
    (Fin D.rank → ActualGround D hu) ≃ₗ[ℂ]
      (Fin D.rank × LatticeTwistedGroundRealization.Half (groundRank D hu) → ℂ) where
  toFun ground label := ground label.1 label.2
  invFun coordinates colour label := coordinates (colour, label)
  left_inv ground := rfl
  right_inv coordinates := rfl
  map_add' left right := rfl
  map_smul' scalar ground := rfl

def weightTwoBasis (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) :
    Module.Basis (Fin D.rank × LatticeTwistedGroundRealization.Half (groundRank D hu)) ℂ
      (eigenspace D hu H 2) :=
  (Pi.basisFun ℂ _).map ((weightTwoEquiv D hu H hHG hGH rank24).trans
    (groundCoordinateEquiv D hu)).symm

theorem weightTwoBasis_vector (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24)
    (label : Fin D.rank × LatticeTwistedGroundRealization.Half (groundRank D hu)) :
    (weightTwoBasis D hu H hHG hGH rank24 label).val =
      (X (label.1, 0) : Oscillator D) ⊗ₜ[ℂ] Pi.single label.2 (1 : ℂ) := by
  classical
  change (∑ colour, (X (colour, 0) : Oscillator D) ⊗ₜ[ℂ]
    (fun ground => (Pi.basisFun ℂ _) label (colour, ground))) = _
  rw [Finset.sum_eq_single label.1]
  · congr 1
    funext ground
    simp [Pi.basisFun_apply, Pi.single_apply, Prod.ext_iff]
  · intro colour member different
    have zero : (fun ground => (Pi.basisFun ℂ _) label (colour, ground)) =
        (0 : ActualGround D hu) := by
      funext ground
      simp [Pi.basisFun_apply, Pi.single_apply, Prod.ext_iff, different]
    rw [zero, TensorProduct.tmul_zero]
  · simp

theorem chosen_ground4096 (D : LatticeData) (hu : IsUnit D.G.det) (rank24 : D.rank = 24) :
    Module.finrank ℂ (ActualGround D hu) = 4096 := by
  have chosen := Classical.choose_spec
    (Classical.choose_spec (LatticeTwistedGroundRealization.actual_twisted_ground_representation D hu))
  have dimension : Module.finrank ℂ (ActualGround D hu) = 2 ^ 12 := chosen.2.2.2.2.1 rank24
  exact dimension.trans (by norm_num)

theorem weight_two_finrank (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) : Module.finrank ℂ (eigenspace D hu H 2) = 98304 := by
  rw [Module.finrank_eq_card_basis (weightTwoBasis D hu H hHG hGH rank24)]
  rw [Fintype.card_prod, Fintype.card_fin]
  have ground_card :
      Fintype.card (LatticeTwistedGroundRealization.Half (groundRank D hu)) = 4096 := by
    rw [← Module.finrank_fintype_fun_eq_card (R := ℂ)]
    exact chosen_ground4096 D hu rank24
  rw [ground_card, rank24]

end
end D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum

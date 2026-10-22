/- GID: D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original charge and energy support for the lattice bc-BRST neutral reduction. -/

import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
import D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Finset.Powerset
import D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance
import Mathlib.LinearAlgebra.Finsupp.Supported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology

open D5.S3.VertexAlgebra

namespace Support

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport LatticePositiveEnergy
open scoped BigOperators TensorProduct

noncomputable section

abbrev TensorLabel (D : LatticeData) := LatticePositiveEnergy.Label D × Finset ℕ

def stateBasis (D : LatticeData) : Module.Basis (TensorLabel D) ℂ (State D) :=
  (carrierBasis D).tensorProduct (Finsupp.basisSingleOne (ι := Finset ℕ) (R := ℂ))

def neutral (D : LatticeData) : Submodule ℂ (State D) :=
  (Finsupp.supported ℂ ℂ {label : TensorLabel D | label.1.1 = 0}).comap
    (stateBasis D).repr.toLinearMap

def zeroLabels (D : LatticeData) : Set (TensorLabel D) :=
  {label | label.1.1 = 0 ∧
    ((label.1.2 = 0 ∧
      (label.2 = ∅ ∨ label.2 = {3} ∨ label.2 = {1, 5} ∨ label.2 = {1, 3, 5})) ∨
     (∃ axis : Fin D.rank, label.1.2 = Finsupp.single (axis, 0) 1 ∧
       (label.2 = {1} ∨ label.2 = {1, 3})))}

theorem weight_nonneg_away_one (site : ℕ) (different : site ≠ 1) :
    0 ≤ BcGhostLZeroSpectrum.siteWeight site := by
  unfold BcGhostLZeroSpectrum.siteWeight
  split_ifs <;> omega

theorem weight_ge_two_away_small (site : ℕ)
    (notOne : site ≠ 1) (notThree : site ≠ 3) (notFive : site ≠ 5) :
    2 ≤ BcGhostLZeroSpectrum.siteWeight site := by
  unfold BcGhostLZeroSpectrum.siteWeight
  split_ifs <;> omega

theorem ghost_erase_one_bounds (subset : Finset ℕ) :
    0 ≤ BcGhostLZeroSpectrum.energy (subset.erase 1) ∧
      BcGhostLZeroSpectrum.energy (subset.erase 1) ≤
        BcGhostLZeroSpectrum.energy subset + 1 := by
  have nonnegative : 0 ≤ BcGhostLZeroSpectrum.energy (subset.erase 1) := by
    apply Finset.sum_nonneg
    intro site present
    exact weight_nonneg_away_one site (Finset.mem_erase.mp present).1
  refine ⟨nonnegative, ?_⟩
  by_cases present : 1 ∈ subset
  · have decomposition := Finset.sum_erase_add subset BcGhostLZeroSpectrum.siteWeight present
    change BcGhostLZeroSpectrum.energy (subset.erase 1) +
      BcGhostLZeroSpectrum.siteWeight 1 = BcGhostLZeroSpectrum.energy subset at decomposition
    norm_num [BcGhostLZeroSpectrum.siteWeight] at decomposition
    omega
  · rw [Finset.erase_eq_of_notMem present]
    omega

theorem ghost_energy_lower (subset : Finset ℕ) :
    -1 ≤ BcGhostLZeroSpectrum.energy subset := by
  have bounds := ghost_erase_one_bounds subset
  omega

theorem ghost_nonpositive_support (subset : Finset ℕ)
    (nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0) :
    subset ⊆ ({1, 3, 5} : Finset ℕ) := by
  intro site present
  by_contra outside
  have exclusions : site ≠ 1 ∧ site ≠ 3 ∧ site ≠ 5 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using outside
  have large := weight_ge_two_away_small site exclusions.1 exclusions.2.1 exclusions.2.2
  have erasedPresent : site ∈ subset.erase 1 :=
    Finset.mem_erase.mpr ⟨exclusions.1, present⟩
  have contribution : BcGhostLZeroSpectrum.siteWeight site ≤
      BcGhostLZeroSpectrum.energy (subset.erase 1) := by
    apply Finset.single_le_sum _ erasedPresent
    intro other occupied
    exact weight_nonneg_away_one other (Finset.mem_erase.mp occupied).1
  have bounds := ghost_erase_one_bounds subset
  omega

theorem ghost_nonpositive_cases (subset : Finset ℕ)
    (nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0) :
    (BcGhostLZeroSpectrum.energy subset = -1 ∧
      (subset = {1} ∨ subset = {1, 3})) ∨
    (BcGhostLZeroSpectrum.energy subset = 0 ∧
      (subset = ∅ ∨ subset = {3} ∨ subset = {1, 5} ∨ subset = {1, 3, 5})) := by
  have member := Finset.mem_powerset.mpr (ghost_nonpositive_support subset nonpositive)
  have enumeration : ({1, 3, 5} : Finset ℕ).powerset =
      {∅, {1}, {3}, {5}, {1, 3}, {1, 5}, {3, 5}, {1, 3, 5}} := by decide
  rw [enumeration] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight] at nonpositive
  all_goals norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight]

theorem oscillator_energy_one_iff (D : LatticeData) (exponent : Exponent D) :
    oscillatorEnergy exponent = 1 ↔
      ∃ axis : Fin D.rank, exponent = Finsupp.single (axis, 0) 1 := by
  classical
  constructor
  · intro energyOne
    have nonzero : exponent ≠ 0 := by
      intro equality
      simp [equality, oscillatorEnergy] at energyOne
    obtain ⟨⟨axis, level⟩, occupied⟩ := Finsupp.ne_iff.mp nonzero
    have levelBound := Finsupp.le_weight_of_ne_zero'
      (fun siteIndex : Index D => siteIndex.2 + 1) occupied
    change level + 1 ≤ oscillatorEnergy exponent at levelBound
    have levelZero : level = 0 := by omega
    have subtraction := Finsupp.weight_sub_single_add
      (w := fun siteIndex : Index D => siteIndex.2 + 1) occupied
    change oscillatorEnergy (exponent - Finsupp.single (axis, level) 1) + (level + 1) =
      oscillatorEnergy exponent at subtraction
    have residualZero : exponent - Finsupp.single (axis, level) 1 = 0 :=
      (oscillatorEnergy_eq_zero_iff D _).mp (by omega)
    have reconstruction := Finsupp.sub_add_single_one_cancel occupied
    rw [residualZero, zero_add] at reconstruction
    refine ⟨axis, ?_⟩
    simpa only [levelZero] using reconstruction.symm
  · rintro ⟨axis, rfl⟩
    simp [oscillatorEnergy, Finsupp.weight_single]

theorem neutral_energy_iff (D : LatticeData) (exponent : Exponent D)
    (subset : Finset ℕ) :
    (oscillatorEnergy exponent : ℤ) + BcGhostLZeroSpectrum.energy subset = 0 ↔
      ((exponent = 0 ∧
        (subset = ∅ ∨ subset = {3} ∨ subset = {1, 5} ∨ subset = {1, 3, 5})) ∨
       (∃ axis : Fin D.rank, exponent = Finsupp.single (axis, 0) 1 ∧
         (subset = {1} ∨ subset = {1, 3}))) := by
  constructor
  · intro zeroEnergy
    have lower := ghost_energy_lower subset
    have oscillatorNonnegative : 0 ≤ (oscillatorEnergy exponent : ℤ) := by positivity
    have ghostNonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0 := by omega
    have oscillatorBound : oscillatorEnergy exponent ≤ 1 := by omega
    have oscillatorCases : oscillatorEnergy exponent = 0 ∨ oscillatorEnergy exponent = 1 := by omega
    rcases oscillatorCases with vanishing | one
    · rcases ghost_nonpositive_cases subset ghostNonpositive with negative | zero
      · omega
      · exact Or.inl ⟨(oscillatorEnergy_eq_zero_iff D exponent).mp vanishing, zero.2⟩
    · rcases ghost_nonpositive_cases subset ghostNonpositive with negative | zero
      · obtain ⟨axis, equality⟩ := (oscillator_energy_one_iff D exponent).mp one
        exact Or.inr ⟨axis, equality, negative.2⟩
      · omega
  · rintro (⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨axis, rfl, rfl | rfl⟩) <;>
      norm_num [oscillatorEnergy, Finsupp.weight_single,
        BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight]

theorem stateBasis_apply (D : LatticeData) (label : TensorLabel D) :
    stateBasis D label = carrierBasis D label.1 ⊗ₜ[ℂ] Finsupp.single label.2 1 := by
  simp [stateBasis, Module.Basis.tensorProduct_apply', Finsupp.coe_basisSingleOne]

theorem actual_T0_basis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (label : TensorLabel D) :
    (M D H 0 + G D 0) (stateBasis D label) =
      ((LatticePositiveEnergy.energy D label.1 +
        BcGhostLZeroSpectrum.energy label.2 : ℤ) : ℂ) • stateBasis D label := by
  rw [stateBasis_apply]
  simp only [stateBasis_apply, LinearMap.add_apply, M, G, TensorProduct.map_tmul, LinearMap.id_apply,
    actualL0_basis D H hHG hGH, BcGhostLZeroSpectrum.L_zero_single,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, Int.cast_add, add_smul]

theorem actual_T0_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (label : TensorLabel D) :
    (stateBasis D).repr ((M D H 0 + G D 0) state) label =
      ((LatticePositiveEnergy.energy D label.1 +
        BcGhostLZeroSpectrum.energy label.2 : ℤ) : ℂ) * (stateBasis D).repr state label := by
  classical
  let coefficient : State D →ₗ[ℂ] ℂ :=
    (Finsupp.lapply label).comp (stateBasis D).repr.toLinearMap
  have diagonal : coefficient.comp (M D H 0 + G D 0) =
      (((LatticePositiveEnergy.energy D label.1 +
        BcGhostLZeroSpectrum.energy label.2 : ℤ) : ℂ)) • coefficient := by
    apply (stateBasis D).ext
    intro input
    simp only [LinearMap.comp_apply, actual_T0_basis D H hHG hGH,
      map_smul, LinearMap.smul_apply]
    by_cases equality : input = label
    · subst input
      simp [coefficient]
    · simp [coefficient, Finsupp.single_apply, equality, Ne.symm equality]
  have evaluated := LinearMap.congr_fun diagonal state
  simpa [coefficient, smul_eq_mul] using evaluated

theorem neutral_T0_kernel_eq_span (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    neutral D ⊓ LinearMap.ker (M D H 0 + G D 0) =
      Submodule.span ℂ (stateBasis D '' zeroLabels D) := by
  classical
  ext state
  rw [Submodule.mem_inf, LinearMap.mem_ker, (stateBasis D).mem_span_image]
  constructor
  · rintro ⟨neutralState, annihilated⟩ label occupied
    change (↑((stateBasis D).repr state).support : Set (TensorLabel D)) ⊆
      {input : TensorLabel D | input.1.1 = 0} at neutralState
    have chargeZero : label.1.1 = 0 := neutralState occupied
    have nonzero : (stateBasis D).repr state label ≠ 0 :=
      Finsupp.mem_support_iff.mp occupied
    have coefficient := actual_T0_coeff D H hHG hGH state label
    rw [annihilated, map_zero, Finsupp.zero_apply] at coefficient
    have complexEnergy :
        ((LatticePositiveEnergy.energy D label.1 +
          BcGhostLZeroSpectrum.energy label.2 : ℤ) : ℂ) = 0 :=
      (mul_eq_zero.mp coefficient.symm).resolve_right nonzero
    have integerEnergy : LatticePositiveEnergy.energy D label.1 +
        BcGhostLZeroSpectrum.energy label.2 = 0 := by exact_mod_cast complexEnergy
    have neutralEnergy : (oscillatorEnergy label.1.2 : ℤ) +
        BcGhostLZeroSpectrum.energy label.2 = 0 := by
      simpa only [LatticePositiveEnergy.energy, chargeZero, chargeEnergy_zero,
        zero_add] using integerEnergy
    exact ⟨chargeZero, (neutral_energy_iff D label.1.2 label.2).mp neutralEnergy⟩
  · intro supported
    constructor
    · change (↑((stateBasis D).repr state).support : Set (TensorLabel D)) ⊆
        {input : TensorLabel D | input.1.1 = 0}
      intro label occupied
      exact (supported occupied).1
    · apply (stateBasis D).repr.injective
      ext label
      rw [actual_T0_coeff D H hHG hGH, map_zero, Finsupp.zero_apply]
      by_cases vanishes : (stateBasis D).repr state label = 0
      · simp [vanishes]
      · have allowed := supported (Finsupp.mem_support_iff.mpr vanishes)
        have neutralEnergy := (neutral_energy_iff D label.1.2 label.2).mpr allowed.2
        have integerEnergy : LatticePositiveEnergy.energy D label.1 +
            BcGhostLZeroSpectrum.energy label.2 = 0 := by
          simpa only [LatticePositiveEnergy.energy, allowed.1, chargeEnergy_zero,
            zero_add] using neutralEnergy
        rw [integerEnergy]
        simp


end

end Support

namespace Image

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct Classical

noncomputable section

abbrev FullLabel (D : LatticeData) :=
  LatticePositiveEnergy.Label D × Finset ℕ

def fullBasis (D : LatticeData) :
    Module.Basis (FullLabel D) ℂ (State D) :=
  (LatticePositiveEnergy.carrierBasis D).tensorProduct
    (Finsupp.basisSingleOne (ι := Finset ℕ) (R := ℂ))

def totalEnergy (D : LatticeData) (label : FullLabel D) : ℤ :=
  LatticePositiveEnergy.energy D label.1 + BcGhostLZeroSpectrum.energy label.2

def neutral (D : LatticeData) : Submodule ℂ (State D) :=
  (Finsupp.supported ℂ ℂ {label : FullLabel D | label.1.1 = 0}).comap
    (fullBasis D).repr.toLinearMap

def jointLabels (D : LatticeData) : Set (FullLabel D) :=
  {label | label.1.1 = 0 ∧ totalEnergy D label = 0}

def jointProjection (D : LatticeData) : Module.End ℂ (State D) := by
  classical
  exact (fullBasis D).repr.symm.toLinearMap.comp
    ((Finsupp.supported ℂ ℂ (jointLabels D)).subtype.comp
      ((Finsupp.restrictDom ℂ ℂ (jointLabels D)).comp
        (fullBasis D).repr.toLinearMap))

def coefficientMap (D : LatticeData) (label : FullLabel D) :
    State D →ₗ[ℂ] ℂ :=
  (Finsupp.lapply label).comp (fullBasis D).repr.toLinearMap

theorem fullBasis_apply (D : LatticeData) (label : FullLabel D) :
    fullBasis D label =
      LatticePositiveEnergy.carrierBasis D label.1 ⊗ₜ[ℂ]
        Finsupp.single label.2 1 := by
  simp [fullBasis, Module.Basis.tensorProduct_apply', Finsupp.coe_basisSingleOne]

theorem totalZero_basis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (label : FullLabel D) :
    (M D H 0 + G D 0) (fullBasis D label) =
      (totalEnergy D label : ℂ) • fullBasis D label := by
  rw [fullBasis_apply]
  simp only [fullBasis_apply, LinearMap.add_apply, M, G, TensorProduct.map_tmul,
    LinearMap.id_apply, LatticePositiveEnergy.actualL0_basis D H hHG hGH,
    BcGhostLZeroSpectrum.L_zero_single, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, totalEnergy, Int.cast_add, add_smul]

theorem totalZero_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (label : FullLabel D) :
    (fullBasis D).repr ((M D H 0 + G D 0) state) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr state label := by
  classical
  have diagonal : (coefficientMap D label).comp (M D H 0 + G D 0) =
      (totalEnergy D label : ℂ) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label ((M D H 0 + G D 0) (fullBasis D input)) =
      (totalEnergy D label : ℂ) • coefficientMap D label (fullBasis D input)
    rw [totalZero_basis D H hHG hGH, map_smul]
    change (totalEnergy D input : ℂ) * (fullBasis D).repr (fullBasis D input) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input
      rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal state

theorem single_charge_coeff_zero (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (ghost : Fock ℂ) (output : FullLabel D)
    (different : output.1.1 ≠ charge) :
    (fullBasis D).repr (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) output = 0 := by
  classical
  change ((LatticePositiveEnergy.carrierBasis D).tensorProduct
    (Finsupp.basisSingleOne (ι := Finset ℕ) (R := ℂ))).repr
      (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) (output.1, output.2) = 0
  rw [Module.Basis.tensorProduct_repr_tmul_apply]
  change ghost output.2 •
    MvPolynomial.coeff output.1.2 ((Finsupp.single charge polynomial) output.1.1) = 0
  simp [Finsupp.single_apply, Ne.symm different]

theorem Q_charge_coeff_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (input output : FullLabel D) (different : output.1.1 ≠ input.1.1) :
    (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
  classical
  change coefficientMap D output (Q D H (fullBasis D input)) = 0
  rw [fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply, Q_tmul]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro mode modeMembership
  rw [map_add, map_smul, LatticeSugawaraVirasoro.sugawaraMode_single_sector]
  change (fullBasis D).repr
      (Finsupp.single input.1.1
        (LatticeSugawaraVirasoro.sectorSugawaraMode D H input.1.1 mode
          (MvPolynomial.monomial input.1.2 1)) ⊗ₜ[ℂ]
            BcGhostFockSupport.c (-mode) (Finsupp.single input.2 1)) output +
    (2 : ℂ)⁻¹ • (fullBasis D).repr
      (Finsupp.single input.1.1 (MvPolynomial.monomial input.1.2 1) ⊗ₜ[ℂ]
        BcGhostStressTails.outerNormalPair mode (Finsupp.single input.2 1)) output = 0
  rw [single_charge_coeff_zero D _ _ _ output different,
    single_charge_coeff_zero D _ _ _ output different]
  simp

theorem totalZero_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (M D H 0 + G D 0) * Q D H = Q D H * (M D H 0 + G D 0) := by
  have covariance := LatticeBcGhostBrstTotalCovariance.total_covariance D H hHG hGH 0
  have vanished : Q D H * (M D H 0 + G D 0) -
      (M D H 0 + G D 0) * Q D H = 0 := by
    simpa using covariance
  exact (sub_eq_zero.mp vanished).symm

theorem Q_energy_coeff_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (input output : FullLabel D)
    (different : totalEnergy D output ≠ totalEnergy D input) :
    (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
  have eigenvector : (M D H 0 + G D 0) (Q D H (fullBasis D input)) =
      (totalEnergy D input : ℂ) • Q D H (fullBasis D input) := by
    have equality := LinearMap.congr_fun (totalZero_commutes D H hHG hGH)
      (fullBasis D input)
    simpa only [Module.End.mul_apply, totalZero_basis D H hHG hGH, map_smul]
      using equality
  have coefficients := congrArg (fun state : State D => (fullBasis D).repr state output)
    eigenvector
  rw [totalZero_coeff D H hHG hGH] at coefficients
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at coefficients
  have separated : ((totalEnergy D output : ℂ) - (totalEnergy D input : ℂ)) *
      (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
    rw [sub_mul, coefficients, sub_self]
  have scalarNonzero : (totalEnergy D output : ℂ) - (totalEnergy D input : ℂ) ≠ 0 := by
    intro equality
    exact different (Int.cast_injective (sub_eq_zero.mp equality))
  exact (mul_eq_zero.mp separated).resolve_left scalarNonzero

theorem Q_coefficient_blocks (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (input output : FullLabel D)
    (nonzero : (fullBasis D).repr (Q D H (fullBasis D input)) output ≠ 0) :
    output.1.1 = input.1.1 ∧ totalEnergy D output = totalEnergy D input := by
  constructor
  · by_contra different
    exact nonzero (Q_charge_coeff_zero D H input output different)
  · by_contra different
    exact nonzero (Q_energy_coeff_zero D H hHG hGH input output different)

theorem jointProjection_repr (D : LatticeData) (state : State D) :
    (fullBasis D).repr (jointProjection D state) =
      Finsupp.filter (fun label => label ∈ jointLabels D) ((fullBasis D).repr state) := by
  classical
  simp [jointProjection]

theorem jointProjection_coeff (D : LatticeData) (state : State D)
    (label : FullLabel D) :
    (fullBasis D).repr (jointProjection D state) label =
      if label ∈ jointLabels D then (fullBasis D).repr state label else 0 := by
  classical
  rw [jointProjection_repr, Finsupp.filter_apply]

theorem jointProjection_basis (D : LatticeData) (input : FullLabel D) :
    jointProjection D (fullBasis D input) =
      if input ∈ jointLabels D then fullBasis D input else 0 := by
  classical
  apply (fullBasis D).repr.injective
  by_cases chosen : input ∈ jointLabels D
  · simp only [if_pos chosen, jointProjection_repr, (fullBasis D).repr_self,
      Finsupp.filter_single_of_pos (fun label => label ∈ jointLabels D) chosen]
  · simp only [if_neg chosen, jointProjection_repr, (fullBasis D).repr_self,
      Finsupp.filter_single_of_neg (fun label => label ∈ jointLabels D) chosen, map_zero]

theorem jointProjection_mem (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) :
    jointProjection D state ∈ neutral D ⊓ LinearMap.ker (M D H 0 + G D 0) := by
  classical
  constructor
  · change (fullBasis D).repr (jointProjection D state) ∈
      Finsupp.supported ℂ ℂ {label : FullLabel D | label.1.1 = 0}
    rw [Finsupp.mem_supported']
    intro output outside
    have excluded : output ∉ jointLabels D := fun chosen => outside chosen.1
    rw [jointProjection_coeff, if_neg excluded]
  · change (M D H 0 + G D 0) (jointProjection D state) = 0
    apply (fullBasis D).repr.injective
    ext output
    rw [totalZero_coeff D H hHG hGH, jointProjection_coeff]
    by_cases chosen : output ∈ jointLabels D
    · rw [if_pos chosen]
      have energyZero : totalEnergy D output = 0 := chosen.2
      simp [energyZero]
    · rw [if_neg chosen]
      simp

theorem jointProjection_fixed (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D)
    (membership : state ∈ neutral D ⊓ LinearMap.ker (M D H 0 + G D 0)) :
    jointProjection D state = state := by
  classical
  have neutralVanishing : ∀ label : FullLabel D, label.1.1 ≠ 0 →
      (fullBasis D).repr state label = 0 := by
    have supported : (fullBasis D).repr state ∈
        Finsupp.supported ℂ ℂ {label : FullLabel D | label.1.1 = 0} := membership.1
    exact (Finsupp.mem_supported' ℂ ((fullBasis D).repr state)).mp supported
  have zeroCoefficient (label : FullLabel D) :
      (totalEnergy D label : ℂ) * (fullBasis D).repr state label = 0 := by
    have killed : (M D H 0 + G D 0) state = 0 := LinearMap.mem_ker.mp membership.2
    have coefficients := totalZero_coeff D H hHG hGH state label
    rw [killed, map_zero, Finsupp.zero_apply] at coefficients
    exact coefficients.symm
  apply (fullBasis D).repr.injective
  ext label
  rw [jointProjection_coeff]
  by_cases chosen : label ∈ jointLabels D
  · rw [if_pos chosen]
  · rw [if_neg chosen]
    by_cases chargeZero : label.1.1 = 0
    · have energyNonzero : totalEnergy D label ≠ 0 := by
        intro energyZero
        exact chosen ⟨chargeZero, energyZero⟩
      have scalarNonzero : (totalEnergy D label : ℂ) ≠ 0 :=
        Int.cast_ne_zero.mpr energyNonzero
      exact ((mul_eq_zero.mp (zeroCoefficient label)).resolve_left scalarNonzero).symm
    · exact (neutralVanishing label chargeZero).symm

theorem jointProjection_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (jointProjection D).comp (Q D H) = (Q D H).comp (jointProjection D) := by
  classical
  apply (fullBasis D).ext
  intro input
  change jointProjection D (Q D H (fullBasis D input)) =
    Q D H (jointProjection D (fullBasis D input))
  rw [jointProjection_basis]
  by_cases chosen : input ∈ jointLabels D
  · rw [if_pos chosen]
    apply (fullBasis D).repr.injective
    ext output
    rw [jointProjection_coeff]
    by_cases zeroCoefficient : (fullBasis D).repr (Q D H (fullBasis D input)) output = 0
    · simp [zeroCoefficient]
    · have blocks := Q_coefficient_blocks D H hHG hGH input output zeroCoefficient
      have outputChosen : output ∈ jointLabels D :=
        ⟨blocks.1.trans chosen.1, blocks.2.trans chosen.2⟩
      rw [if_pos outputChosen]
  · rw [if_neg chosen, map_zero]
    apply (fullBasis D).repr.injective
    ext output
    rw [jointProjection_coeff, map_zero, Finsupp.zero_apply]
    by_cases zeroCoefficient : (fullBasis D).repr (Q D H (fullBasis D input)) output = 0
    · simp [zeroCoefficient]
    · have blocks := Q_coefficient_blocks D H hHG hGH input output zeroCoefficient
      have outputExcluded : output ∉ jointLabels D := by
        intro outputChosen
        exact chosen ⟨blocks.1.symm.trans outputChosen.1,
          blocks.2.symm.trans outputChosen.2⟩
      rw [if_neg outputExcluded]

theorem full_image_iff_restricted (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (y : State D) (hy : y ∈ neutral D ⊓ LinearMap.ker (M D H 0 + G D 0)) :
    y ∈ LinearMap.range (Q D H) ↔
      ∃ x : State D, x ∈ neutral D ⊓ LinearMap.ker (M D H 0 + G D 0) ∧ Q D H x = y := by
  constructor
  · rintro ⟨state, equality⟩
    refine ⟨jointProjection D state, jointProjection_mem D H hHG hGH state, ?_⟩
    have commutes := LinearMap.congr_fun (jointProjection_commutes D H hHG hGH) state
    change jointProjection D (Q D H state) = Q D H (jointProjection D state) at commutes
    rw [equality, jointProjection_fixed D H hHG hGH y hy] at commutes
    exact commutes.symm
  · rintro ⟨state, membership, equality⟩
    exact ⟨state, equality⟩

end

end Image

namespace Energy

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct Classical

noncomputable section

abbrev FullLabel (D : LatticeData) :=
  LatticePositiveEnergy.Label D × Finset ℕ

def fullBasis (D : LatticeData) :
    Module.Basis (FullLabel D) ℂ (State D) :=
  (LatticePositiveEnergy.carrierBasis D).tensorProduct
    (Finsupp.basisSingleOne (ι := Finset ℕ) (R := ℂ))

def totalEnergy (D : LatticeData) (label : FullLabel D) : ℤ :=
  LatticePositiveEnergy.energy D label.1 + BcGhostLZeroSpectrum.energy label.2

def coefficientMap (D : LatticeData) (label : FullLabel D) :
    State D →ₗ[ℂ] ℂ :=
  (Finsupp.lapply label).comp (fullBasis D).repr.toLinearMap

def energyWeight (D : LatticeData) (weight : ℤ → ℂ) :
    Module.End ℂ (State D) :=
  (fullBasis D).constr ℂ (fun label =>
    weight (totalEnergy D label) • fullBasis D label)

def P0 (D : LatticeData) : Module.End ℂ (State D) :=
  energyWeight D (fun energy => if energy = 0 then 1 else 0)

def EInv (D : LatticeData) : Module.End ℂ (State D) :=
  energyWeight D (fun energy => (energy : ℂ)⁻¹)

def h (D : LatticeData) : Module.End ℂ (State D) :=
  (B D 0).comp (EInv D)

theorem fullBasis_apply (D : LatticeData) (label : FullLabel D) :
    fullBasis D label =
      LatticePositiveEnergy.carrierBasis D label.1 ⊗ₜ[ℂ]
        Finsupp.single label.2 1 := by
  simp [fullBasis, Module.Basis.tensorProduct_apply', Finsupp.coe_basisSingleOne]

theorem totalZero_basis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (label : FullLabel D) :
    (M D H 0 + G D 0) (fullBasis D label) =
      (totalEnergy D label : ℂ) • fullBasis D label := by
  rw [fullBasis_apply]
  simp only [fullBasis_apply, LinearMap.add_apply, M, G, TensorProduct.map_tmul,
    LinearMap.id_apply, LatticePositiveEnergy.actualL0_basis D H hHG hGH,
    BcGhostLZeroSpectrum.L_zero_single, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, totalEnergy, Int.cast_add, add_smul]

theorem totalZero_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (label : FullLabel D) :
    (fullBasis D).repr ((M D H 0 + G D 0) state) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr state label := by
  classical
  have diagonal : (coefficientMap D label).comp (M D H 0 + G D 0) =
      (totalEnergy D label : ℂ) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label ((M D H 0 + G D 0) (fullBasis D input)) =
      (totalEnergy D label : ℂ) • coefficientMap D label (fullBasis D input)
    rw [totalZero_basis D H hHG hGH, map_smul]
    change (totalEnergy D input : ℂ) * (fullBasis D).repr (fullBasis D input) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input
      rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal state

theorem totalZero_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (M D H 0 + G D 0) * Q D H = Q D H * (M D H 0 + G D 0) := by
  have covariance := LatticeBcGhostBrstTotalCovariance.total_covariance D H hHG hGH 0
  have vanished : Q D H * (M D H 0 + G D 0) -
      (M D H 0 + G D 0) * Q D H = 0 := by
    simpa using covariance
  exact (sub_eq_zero.mp vanished).symm

theorem Q_energy_coeff_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (input output : FullLabel D)
    (different : totalEnergy D output ≠ totalEnergy D input) :
    (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
  have eigenvector : (M D H 0 + G D 0) (Q D H (fullBasis D input)) =
      (totalEnergy D input : ℂ) • Q D H (fullBasis D input) := by
    have equality := LinearMap.congr_fun (totalZero_commutes D H hHG hGH)
      (fullBasis D input)
    simpa only [Module.End.mul_apply, totalZero_basis D H hHG hGH, map_smul]
      using equality
  have coefficients := congrArg (fun state : State D => (fullBasis D).repr state output)
    eigenvector
  rw [totalZero_coeff D H hHG hGH] at coefficients
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at coefficients
  have separated : ((totalEnergy D output : ℂ) - (totalEnergy D input : ℂ)) *
      (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
    rw [sub_mul, coefficients, sub_self]
  have scalarNonzero : (totalEnergy D output : ℂ) - (totalEnergy D input : ℂ) ≠ 0 := by
    intro equality
    exact different (Int.cast_injective (sub_eq_zero.mp equality))
  exact (mul_eq_zero.mp separated).resolve_left scalarNonzero

theorem energyWeight_basis (D : LatticeData) (weight : ℤ → ℂ)
    (label : FullLabel D) :
    energyWeight D weight (fullBasis D label) =
      weight (totalEnergy D label) • fullBasis D label := by
  exact (fullBasis D).constr_basis ℂ
    (fun input => weight (totalEnergy D input) • fullBasis D input) label

theorem energyWeight_coeff (D : LatticeData) (weight : ℤ → ℂ)
    (state : State D) (label : FullLabel D) :
    (fullBasis D).repr (energyWeight D weight state) label =
      weight (totalEnergy D label) * (fullBasis D).repr state label := by
  classical
  have diagonal : (coefficientMap D label).comp (energyWeight D weight) =
      weight (totalEnergy D label) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label (energyWeight D weight (fullBasis D input)) =
      weight (totalEnergy D label) • coefficientMap D label (fullBasis D input)
    rw [energyWeight_basis, map_smul]
    change weight (totalEnergy D input) * (fullBasis D).repr (fullBasis D input) label =
      weight (totalEnergy D label) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input
      rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal state

theorem energyWeight_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (weight : ℤ → ℂ) :
    energyWeight D weight * Q D H = Q D H * energyWeight D weight := by
  classical
  apply (fullBasis D).ext
  intro input
  change energyWeight D weight (Q D H (fullBasis D input)) =
    Q D H (energyWeight D weight (fullBasis D input))
  rw [energyWeight_basis, map_smul]
  apply (fullBasis D).repr.injective
  ext output
  rw [energyWeight_coeff]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases zeroCoefficient : (fullBasis D).repr (Q D H (fullBasis D input)) output = 0
  · simp only [zeroCoefficient, mul_zero]
  · have equalEnergy : totalEnergy D output = totalEnergy D input := by
      by_contra different
      exact zeroCoefficient (Q_energy_coeff_zero D H hHG hGH input output different)
    rw [equalEnergy]

theorem totalZero_energyWeight_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (weight : ℤ → ℂ) :
    (M D H 0 + G D 0) * energyWeight D weight =
      energyWeight D weight * (M D H 0 + G D 0) := by
  apply (fullBasis D).ext
  intro label
  simp only [Module.End.mul_apply, energyWeight_basis,
    totalZero_basis D H hHG hGH, map_smul, smul_smul]
  rw [mul_comm]

theorem EInv_totalZero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    EInv D * (M D H 0 + G D 0) = 1 - P0 D := by
  classical
  apply (fullBasis D).ext
  intro label
  change EInv D ((M D H 0 + G D 0) (fullBasis D label)) =
    fullBasis D label - P0 D (fullBasis D label)
  rw [totalZero_basis D H hHG hGH, map_smul]
  change (totalEnergy D label : ℂ) •
      energyWeight D (fun energy => (energy : ℂ)⁻¹) (fullBasis D label) =
    fullBasis D label -
      energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D label)
  rw [energyWeight_basis, energyWeight_basis, smul_smul]
  by_cases zeroEnergy : totalEnergy D label = 0
  · simp [zeroEnergy]
  · have scalarNonzero : (totalEnergy D label : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr zeroEnergy
    simp [zeroEnergy, scalarNonzero]

theorem totalZero_P0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (M D H 0 + G D 0) * P0 D = 0 := by
  classical
  apply (fullBasis D).ext
  intro label
  change (M D H 0 + G D 0)
    (energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D label)) = 0
  rw [energyWeight_basis, map_smul, totalZero_basis D H hHG hGH, smul_smul]
  by_cases zeroEnergy : totalEnergy D label = 0 <;> simp [zeroEnergy]

theorem homotopy_identity (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Q D H * h D + h D * Q D H = 1 - P0 D := by
  have inverseCommutes : EInv D * Q D H = Q D H * EInv D :=
    energyWeight_commutes D H hHG hGH (fun energy => (energy : ℂ)⁻¹)
  have spectralCommutes : (M D H 0 + G D 0) * EInv D =
      EInv D * (M D H 0 + G D 0) :=
    totalZero_energyWeight_commutes D H hHG hGH (fun energy => (energy : ℂ)⁻¹)
  change Q D H * (B D 0 * EInv D) + (B D 0 * EInv D) * Q D H = 1 - P0 D
  calc
    Q D H * (B D 0 * EInv D) + (B D 0 * EInv D) * Q D H =
        (Q D H * B D 0 + B D 0 * Q D H) * EInv D := by
      simp only [add_mul, mul_assoc, inverseCommutes]
    _ = (M D H 0 + G D 0) * EInv D := by
      rw [LatticeBcGhostBrstCharge.ward_identity D H 0]
    _ = EInv D * (M D H 0 + G D 0) := spectralCommutes
    _ = 1 - P0 D := EInv_totalZero D H hHG hGH

theorem all_state_homotopy (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Q D H * (B D 0).comp (EInv D) + (B D 0).comp (EInv D) * Q D H =
      1 - P0 D := by
  exact homotopy_identity D H hHG hGH

theorem cycle_reduction (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : Q D H x = 0) :
    ∃ y : State D, (M D H 0 + G D 0) y = 0 ∧ Q D H y = 0 ∧
      x - y = Q D H ((B D 0).comp (EInv D) x) := by
  refine ⟨P0 D x, ?_, ?_, ?_⟩
  · have killed := LinearMap.congr_fun (totalZero_P0 D H hHG hGH) x
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using killed
  · have projectionCommutes : P0 D * Q D H = Q D H * P0 D :=
      energyWeight_commutes D H hHG hGH (fun energy => if energy = 0 then 1 else 0)
    have equality := LinearMap.congr_fun projectionCommutes x
    change P0 D (Q D H x) = Q D H (P0 D x) at equality
    rw [hx, map_zero] at equality
    exact equality.symm
  · change x - P0 D x = Q D H (h D x)
    have equality := LinearMap.congr_fun (homotopy_identity D H hHG hGH) x
    simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hx, map_zero, add_zero] using equality.symm

end

end Energy

end D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology

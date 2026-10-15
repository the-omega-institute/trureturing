import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary07
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def frequencyWeight (D : LatticeData) (index : Index D) : ℕ := index.2 + 1

theorem coordinate_frequency_homogeneous (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (index : Index D) :
    MvPolynomial.IsWeightedHomogeneous (frequencyWeight D) (coordinate D frame index) (index.2 + 1) := by
  classical
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ
  intro original originalMember
  exact (MvPolynomial.weightedHomogeneousSubmodule ℂ (frequencyWeight D) (index.2 + 1)).smul_mem
    (frame index.1 original)
      (MvPolynomial.isWeightedHomogeneous_X ℂ (frequencyWeight D) (original, index.2))

theorem coordinateSub_monomial_frequency (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (powers : Index D →₀ ℕ) (scalar : ℂ) :
    MvPolynomial.IsWeightedHomogeneous (frequencyWeight D)
      (coordinateSub D frame (MvPolynomial.monomial powers scalar))
      (Finsupp.weight (frequencyWeight D) powers) := by
  classical
  rw [coordinateSub, MvPolynomial.aeval_monomial]
  have productHomogeneous := MvPolynomial.IsWeightedHomogeneous.prod powers.support
    (fun index => coordinate D frame index ^ powers index)
    (fun index => powers index • frequencyWeight D index)
    (fun index _ => (coordinate_frequency_homogeneous D frame index).pow (powers index))
  simpa only [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod, MvPolynomial.algebraMap_eq]
    using productHomogeneous.C_mul scalar

theorem coordinateSub_preserves_frequency (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (polynomial : Oscillator D) (level : ℕ)
    (homogeneous : MvPolynomial.IsWeightedHomogeneous (frequencyWeight D) polynomial level) :
    MvPolynomial.IsWeightedHomogeneous (frequencyWeight D) (coordinateSub D frame polynomial) level := by
  classical
  induction homogeneous using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero ℂ (frequencyWeight D) level
  | add first second firstHomogeneous secondHomogeneous firstProof secondProof =>
      simpa only [map_add] using firstProof.add secondProof
  | monomial powers scalar sameLevel =>
      simpa only [sameLevel] using coordinateSub_monomial_frequency D frame powers scalar

theorem chosenH_native_norm (D : LatticeData) (charge : Charge D) :
    chosenH D charge = (bilinear D charge charge : ℂ) / 2 := by
  simp only [chosenH, gramPair, complexCharge, bilinear, Int.cast_sum, Int.cast_mul, div_eq_mul_inv]
  ring

theorem original_M_zero_coordinate_homogeneous (D : LatticeData)
    (H frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (charge : Charge D) (polynomial : Oscillator D) (ghost : Fock ℂ) (level : ℕ)
    (homogeneous : MvPolynomial.IsWeightedHomogeneous (frequencyWeight D) polynomial level) :
    M D H 0 (Finsupp.single charge (coordinateSub D frame polynomial) ⊗ₜ[ℂ] ghost) =
      (chosenH D charge + (level : ℂ)) •
        (Finsupp.single charge (coordinateSub D frame polynomial) ⊗ₜ[ℂ] ghost) := by
  have actual := sugawaraMode_weighted_homogeneous D H leftGramInverse rightGramInverse charge
    (coordinateSub D frame polynomial) level (coordinateSub_preserves_frequency D frame polynomial level homogeneous)
  simp only [M, TensorProduct.map_tmul, LinearMap.id_apply, actual,
    chosenH_native_norm, add_comm]
  rw [← TensorProduct.smul_tmul']

theorem original_M_zero_coordinate_monomial (D : LatticeData)
    (H frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (ghost : Fock ℂ) :
    M D H 0 (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ] ghost) =
      (chosenH D charge + (Finsupp.weight (frequencyWeight D) powers : ℂ)) •
        (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ] ghost) := by
  exact original_M_zero_coordinate_homogeneous D H frame leftGramInverse rightGramInverse
    charge (MvPolynomial.monomial powers scalar) ghost (Finsupp.weight (frequencyWeight D) powers)
    (MvPolynomial.isWeightedHomogeneous_monomial (frequencyWeight D) powers scalar rfl)

theorem original_total_energy_coordinate_polarized (D : LatticeData)
    (H frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) :
    (M D H 0 + G D 0)
      (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ]
        downWord subset down) =
      (chosenH D charge + (Finsupp.weight (frequencyWeight D) powers : ℂ) +
        (polarizedLevel subset : ℂ) - 1) •
      (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ]
        downWord subset down) := by
  have matter := original_M_zero_coordinate_monomial D H frame leftGramInverse rightGramInverse
    charge powers scalar (downWord subset down)
  have ghost := (original_polarized_state_sector D
    (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))) subset).2.1
  rw [LinearMap.add_apply, matter, ghost]
  push_cast
  module

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource

/- GID: D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational dual shifts give actual original-omega eigenspaces with finite energy fibers. -/

import D5.S3.VertexAlgebra.LatticeDualCosetVirasoro
import D5.S3.VertexAlgebra.LatticeDualCosetEnergy
import D5.S1.Eigenstructure.DiagonalTensorEigenspace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticeDualCosetEnergy
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeFiniteNegativeGeneration LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeDualCosetModule LatticeDualCosetConformal LatticeSugawaraVirasoro
open scoped BigOperators VertexOperator TensorProduct DirectSum
noncomputable section

variable (D : LatticeData)

private theorem pairing_symm (x y : Fin D.rank → ℚ) : pairing D x y = pairing D y x := by
  unfold pairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [D.symmetric j i]
  ring

private theorem pairing_add (x y : Fin D.rank → ℚ) :
    pairing D (x+y) (x+y) = pairing D x x + pairing D x y +
      pairing D y x + pairing D y y := by
  simp only [pairing,Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
  ring

/-- Exact duality makes all charge-energy differences integral. -/
theorem chargeWeight_expansion (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ)) (γ : Charge D) :
    chargeWeight D μ γ = chargeWeight D μ 0 + (chargeEnergy D γ : ℚ) +
      ((∑ i, γ i * β i : ℤ) : ℚ) := by
  have he : (2 : ℚ) * (chargeEnergy D γ : ℚ) =
      pairing D (fun i => (γ i : ℚ)) (fun i => (γ i : ℚ)) := by
    simpa [pairing,bilinear,Int.cast_sum,Int.cast_mul] using
      (show (2 : ℚ) * (chargeEnergy D γ : ℚ) = (bilinear D γ γ : ℚ) by
        exact_mod_cast two_chargeEnergy D γ)
  have hp := physical_pairing_integral D β μ hDual γ
  change pairing D (fun i => (γ i : ℚ)+μ i) (fun i => (γ i : ℚ)+μ i)/2 = _
  rw [show (fun i => (γ i : ℚ)+μ i) = (fun i => (γ i : ℚ))+μ by rfl,
    pairing_add, pairing_symm D μ (fun i => (γ i : ℚ))]
  have hq : chargeWeight D μ 0 = pairing D μ μ/2 := by simp [chargeWeight]
  change pairing D (fun i => (γ i : ℚ)) μ = _ at hp
  rw [hq]
  linear_combination -he/2 + hp

/-- The minimum is attained; its nonnegative integral differences give natural levels. -/
theorem weight_levels (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (γ₀ : Charge D) (hmin : ∀ γ, chargeWeight D μ γ₀ ≤ chargeWeight D μ γ)
    (a : Label D) : ∃ n : ℕ, weight D μ a = chargeWeight D μ γ₀ + (n : ℚ) := by
  let z : ℤ := chargeEnergy D a.1 - chargeEnergy D γ₀ +
    (∑ i, a.1 i * β i) - (∑ i, γ₀ i * β i)
  have hz : weight D μ a = chargeWeight D μ γ₀ +
      (oscillatorEnergy a.2 : ℚ) + (z : ℚ) := by
    rw [weight,chargeWeight_expansion D β μ hDual a.1,
      chargeWeight_expansion D β μ hDual γ₀]
    simp only [z,Int.cast_add,Int.cast_sub]
    ring
  have hn : 0 ≤ z := by
    have h := hmin a.1
    rw [chargeWeight_expansion D β μ hDual a.1,
      chargeWeight_expansion D β μ hDual γ₀] at h
    have hzq : (0 : ℚ) ≤ (z : ℚ) := by
      simp only [z,Int.cast_add,Int.cast_sub]
      linarith
    exact_mod_cast hzq
  refine ⟨oscillatorEnergy a.2 + z.toNat, ?_⟩
  have hcast : (z.toNat : ℚ)=(z : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn
  rw [hz,Nat.cast_add,hcast]
  ring

private theorem halfNorm_cast (μ : Fin D.rank → ℚ) :
    halfNorm D (fun i => (μ i : ℂ)) = (chargeWeight D μ 0 : ℂ) := by
  simp only [halfNorm,chargeWeight,pairing,Pi.zero_apply,Int.cast_zero,zero_add,
    Rat.cast_div,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat]
  ring

private theorem shiftCurrent_zero_basis (μ : Fin D.rank → ℚ) (a : Label D) :
    shiftCurrent D (fun i => (μ i : ℂ)) 0 (carrierBasis D a) =
      (pairing D (fun i => (a.1 i : ℚ)) μ : ℂ) • carrierBasis D a := by
  classical
  rw [carrierBasis_apply]
  simp only [shiftCurrent,LinearMap.sum_apply,LinearMap.smul_apply,neutralMode_zero_single,
    smul_smul,← Finset.sum_smul]
  congr 1
  simp only [chargeScalar,bilinear,unitCharge,Int.cast_sum,Int.cast_mul,Int.cast_ite,
    Int.cast_one,Int.cast_zero,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,pairing,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [D.symmetric j i]
  ring

/-- Every actual basis eigenvalue comes from the original omega module action. -/
theorem moduleL_basis_zero (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ)) (a : Label D) :
    moduleL D β H 0 (carrierBasis D a) = (weight D μ a : ℂ) • carrierBasis D a := by
  have hGu : ∀ i, ∑ j, (D.G i j : ℂ) * (μ j : ℂ) = (β i : ℂ) := by
    intro i
    exact_mod_cast hDual i
  rw [moduleL_shift_complex D β H hHG hGH _ hGu]
  simp only [ite_true,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
  rw [actualL0_basis D H hHG hGH,shiftCurrent_zero_basis,halfNorm_cast]
  rw [← add_smul,← add_smul]
  congr 1
  have he := chargeWeight_expansion D β μ hDual a.1
  have hp := physical_pairing_integral D β μ hDual a.1
  change pairing D (fun i => (a.1 i : ℚ)) μ = _ at hp
  have hq : (weight D μ a : ℂ) = (energy D a : ℂ) +
      (pairing D (fun i => (a.1 i : ℚ)) μ : ℂ) + (chargeWeight D μ 0 : ℂ) := by
    have h : weight D μ a = (energy D a : ℚ) +
        pairing D (fun i => (a.1 i : ℚ)) μ + chargeWeight D μ 0 := by
      simp only [weight,energy,Int.cast_add,Int.cast_natCast]
      rw [he,hp]
      ring
    exact_mod_cast h
  exact hq.symm

def rationalGrade (μ : Fin D.rank → ℚ) (e : ℚ) : Submodule ℂ (Carrier D) :=
  (Finsupp.supported ℂ ℂ {a : Label D | weight D μ a=e}).comap
    (carrierCoeffEquiv D).toLinearMap

/-- The sealed generic diagonal tensor supplier is specialized through the tensor unit. -/
theorem moduleL_coeff (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (v : Carrier D) (a : Label D) :
    carrierCoeffEquiv D (moduleL D β H 0 v) a =
      (weight D μ a : ℂ) * carrierCoeffEquiv D v a := by
  have h := D5.S1.Eigenstructure.DiagonalTensorEigenspace.coeff_action
    (carrierBasis D) (moduleL D β H 0) (fun a => (weight D μ a : ℂ))
    (moduleL_basis_zero D β H hHG hGH μ hDual) (v ⊗ₜ[ℂ] (1 : ℂ)) a
  simpa [D5.S1.Eigenstructure.DiagonalTensorEigenspace.coeffEquiv,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,carrierBasis] using h

/-- Both directions of the full eigenspace identity, for arbitrary mixed states. -/
theorem moduleL_eigen_iff (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (e : ℚ) (v : Carrier D) :
    moduleL D β H 0 v = (e : ℂ) • v ↔ v ∈ rationalGrade D μ e := by
  classical
  have h := D5.S1.Eigenstructure.DiagonalTensorEigenspace.eigen_iff_supported
    (carrierBasis D) (moduleL D β H 0) (fun a => (weight D μ a : ℂ))
    (moduleL_basis_zero D β H hHG hGH μ hDual) (e : ℂ) (v ⊗ₜ[ℂ] (1 : ℂ))
  have ht : TensorProduct.map (moduleL D β H 0) (LinearMap.id : Module.End ℂ ℂ)
      (v ⊗ₜ[ℂ] (1 : ℂ)) = (e : ℂ) • (v ⊗ₜ[ℂ] (1 : ℂ)) ↔
      moduleL D β H 0 v = (e : ℂ) • v := by
    rw [← (TensorProduct.rid ℂ (Carrier D)).injective.eq_iff]
    simp
  rw [ht] at h
  have hs : {a : Label D | (weight D μ a : ℂ)=(e : ℂ)} =
      {a : Label D | weight D μ a=e} := by
    ext a
    exact Rat.cast_inj
  simpa [D5.S1.Eigenstructure.DiagonalTensorEigenspace.coeffEquiv,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,carrierBasis,hs,rationalGrade] using h

def gradeCoeffEquiv (μ : Fin D.rank → ℚ) (e : ℚ) :
    rationalGrade D μ e ≃ₗ[ℂ] ({a : Label D // weight D μ a=e} →₀ ℂ) :=
  (LinearEquiv.ofSubmodule' (carrierCoeffEquiv D)
    (Finsupp.supported ℂ ℂ {a : Label D | weight D μ a=e})).trans
      (Finsupp.supportedEquivFinsupp _)

theorem eigenspace_finiteDimensional (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (e : ℚ) :
    FiniteDimensional ℂ ((moduleL D β H 0).eigenspace (e : ℂ)) := by
  have he : (moduleL D β H 0).eigenspace (e : ℂ) = rationalGrade D μ e := by
    ext v
    rw [Module.End.mem_eigenspace_iff]
    exact moduleL_eigen_iff D β H hHG hGH μ hDual e v
  rw [he]
  letI := fiber_finite D μ hD e
  exact Module.Finite.of_basis (Module.Basis.ofRepr (gradeCoeffEquiv D μ e))

end
end D5.S3.VertexAlgebra.LatticeDualCosetEnergy

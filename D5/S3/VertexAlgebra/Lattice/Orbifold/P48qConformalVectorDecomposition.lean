/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qConformalVectorDecomposition
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Decompose the native conformal state in fixed and opposite-eigenvalue bases. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingPairIterate
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero

/-! The actual P48q conformal state in the fixed and opposite-eigenvalue bases. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition

open LatticeGeneratingFieldLocality (Carrier Oscillator)
open LatticeAllStateField (Y)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (currentState current_minus_one_current conformalPolynomial)
open LatticeSugawaraCurrents (gramComplex)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open P48qTwistedChargeAction (lattice)
open P48qMomentumEnergy (Fixed fixedBasis fixedGramDual fixedGram_pair_dual)
open P48qFixedRankCertificateDraft (nebeOrderThree)
open P48qGramCertificateDraft
open ThirdEigenspacePairing
open ThirdTwistedIterate (currentAlong)
open MvPolynomial (X)
open scoped BigOperators Matrix VertexOperator

noncomputable section

private theorem gram_symm : p48qForm.IsSymm := by
  change (gramComplex lattice).toBilin'.IsSymm
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  exact Matrix.IsSymm.ext fun i j => congrArg (Int.castRingHom ℂ) (lattice.symmetric j i)

private theorem gram_invariant (x y : Fin 48 → ℂ) :
    p48qForm (p48qAction x) (p48qAction y) = p48qForm x y := by
  let cast := Int.castRingHom ℂ
  let G := cast.mapMatrix nebeGram
  let A := cast.mapMatrix nebeOrderThreeᵀ
  have h : Aᵀ * G * A = G := by
    change cast.mapMatrix nebeOrderThree * cast.mapMatrix nebeGram *
      cast.mapMatrix nebeOrderThreeᵀ = G
    rw [← map_mul, ← map_mul, gram_isometry_certificate]
  change (G.toBilin'.comp A.toLin' A.toLin') x y = G.toBilin' x y
  rw [Matrix.toBilin'_comp, h]

private theorem fixed_pairing_eq_zero (x : Fixed) {a : ℂ} {y : Fin 48 → ℂ}
    (hy : y ∈ p48qAction.eigenspace a) (ha : a ≠ 1) :
    p48qForm (x : Fin 48 → ℂ) y = 0 := by
  have hx : (x : Fin 48 → ℂ) ∈ p48qAction.eigenspace (1 : ℂ) := by
    rw [Module.End.eigenspace_def, one_smul]
    exact x.property
  exact eigenspace_pairing_eq_zero gram_invariant hx hy (by simpa only [one_mul] using ha)

private theorem gram_det_unit : IsUnit lattice.G.det := by
  change IsUnit nebeGram.det
  rw [← Matrix.det_transpose]
  exact Matrix.isUnit_det_of_left_inverse gram_inverse_certificate

/-- The native integral inverse extended to the complex oscillator coordinates. -/
theorem actualInverse_eq_complexInverse : actualInverse lattice = (gramComplex lattice)⁻¹ := by
  have h := actualInverse_left lattice gram_det_unit
  have hG := Matrix.mul_nonsing_inv (gramComplex lattice) (Matrix.isUnit_det_of_left_inverse h)
  calc
    actualInverse lattice = actualInverse lattice *
        (gramComplex lattice * (gramComplex lattice)⁻¹) := by rw [hG, Matrix.mul_one]
    _ = (gramComplex lattice)⁻¹ := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]

private abbrev BasisIndex := Fin 16 ⊕ (Fin 16 ⊕ Fin 16)

private def basisVector {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : BasisIndex → Fin 48 → ℂ :=
  Sum.elim (fun i => (fixedBasis i : Fin 48 → ℂ))
    (Sum.elim (fun i => (p48qBasis hζ i : Fin 48 → ℂ))
      (fun i => (p48qOppositeBasis hζ i : Fin 48 → ℂ)))

private def dualVector {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : BasisIndex → Fin 48 → ℂ :=
  Sum.elim (fun i => (fixedGramDual fixedBasis i : Fin 48 → ℂ))
    (Sum.elim (fun i => (p48qOppositeBasis hζ i : Fin 48 → ℂ))
      (fun i => (p48qBasis hζ i : Fin 48 → ℂ)))

private theorem pair_basis_dual {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (a b : BasisIndex) :
    p48qForm (basisVector hζ a) (dualVector hζ b) = if a = b then 1 else 0 := by
  have h₁ : ζ ≠ 1 := hζ.ne_one (by decide)
  have h₂ : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by decide : (2 : ℕ) ≠ 0) (by decide)
  obtain ⟨hIso₁, hIso₂⟩ := p48q_moving_isotropic hζ
  rcases a with i | (i | i) <;> rcases b with j | (j | j) <;>
    simp only [basisVector, dualVector, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, ite_false]
  · exact fixedGram_pair_dual fixedBasis i j
  · exact fixed_pairing_eq_zero (fixedBasis i) (p48qOppositeBasis hζ j).property h₂
  · exact fixed_pairing_eq_zero (fixedBasis i) (p48qBasis hζ j).property h₁
  · exact (gram_symm.eq _ _).trans
      (fixed_pairing_eq_zero (fixedGramDual fixedBasis j) (p48qBasis hζ i).property h₁)
  · exact p48q_pair_bases hζ i j
  · exact hIso₁ (p48qBasis hζ i) (p48qBasis hζ j)
  · exact (gram_symm.eq _ _).trans
      (fixed_pairing_eq_zero (fixedGramDual fixedBasis j) (p48qOppositeBasis hζ i).property h₂)
  · exact hIso₂ (p48qOppositeBasis hζ i) (p48qOppositeBasis hζ j)
  · rw [gram_symm.eq _ _, p48q_pair_bases] <;> simp only [eq_comm]

private theorem inverseGram_eq_sum {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (i j : Fin 48) :
    actualInverse lattice i j = ∑ a : BasisIndex, basisVector hζ a i * dualVector hζ a j := by
  let gram : Matrix (Fin 48) (Fin 48) ℂ := gramComplex lattice
  let basis : Matrix (Fin 48) BasisIndex ℂ := Matrix.of fun i a => basisVector hζ a i
  let dual : Matrix BasisIndex (Fin 48) ℂ := Matrix.of fun a j => dualVector hζ a j
  have hPair : (dual * gram) * basis = 1 := by
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_assoc, Matrix.one_apply]
    change dualVector hζ a ⬝ᵥ (gram *ᵥ basisVector hζ b) = _
    rw [← Matrix.toBilin'_apply']
    change p48qForm (dualVector hζ a) (basisVector hζ b) = _
    rw [gram_symm.eq _ _, pair_basis_dual hζ] <;> simp only [eq_comm]
  have hCard : Fintype.card BasisIndex = Fintype.card (Fin 48) := by
    simp [BasisIndex]
  have hComplete : basis * (dual * gram) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq BasisIndex (Fin 48) ℂ
      (A := dual * gram) (B := basis) hCard).mp hPair
  have hProduct : (basis * dual) * gram = 1 := by
    rw [Matrix.mul_assoc, hComplete]
  let inverse : Matrix (Fin 48) (Fin 48) ℂ := actualInverse lattice
  have hRight : gram * inverse = 1 := actualInverse_right lattice gram_det_unit
  have hInverse : inverse = basis * dual := by
    calc
      inverse = ((basis * dual) * gram) * inverse := by
        rw [hProduct, Matrix.one_mul]
      _ = basis * dual := by
        rw [Matrix.mul_assoc, hRight, Matrix.mul_one]
  simpa only [Matrix.mul_apply, basis, dual, inverse, Matrix.of_apply] using
    congrArg (fun H : Matrix (Fin 48) (Fin 48) ℂ => H i j) hInverse

/-- Each entry of the native inverse Gram matrix is the sum of the three paired blocks. -/
theorem inverseGram_apply {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (i j : Fin 48) :
    actualInverse lattice i j =
      (∑ a : Fin 16, (fixedBasis a : Fin 48 → ℂ) i * (fixedGramDual fixedBasis a : Fin 48 → ℂ) j) +
      ((∑ a : Fin 16, (p48qBasis hζ a : Fin 48 → ℂ) i * (p48qOppositeBasis hζ a : Fin 48 → ℂ) j) +
        ∑ a : Fin 16, (p48qOppositeBasis hζ a : Fin 48 → ℂ) i * (p48qBasis hζ a : Fin 48 → ℂ) j) := by
  rw [inverseGram_eq_sum hζ]
  simp only [Fintype.sum_sum_type, basisVector, dualVector, Sum.elim_inl, Sum.elim_inr]

/-- The untwisted `(-1)`-product of the actual currents in the given directions. -/
abbrev currentPair (u v : Fin 48 → ℂ) : Carrier lattice :=
  mu lattice (currentAlong lattice u) (-1) (currentAlong lattice v)

private theorem currentPair_eq_sum (u v : Fin 48 → ℂ) :
    currentPair u v = ∑ i : Fin 48, ∑ j : Fin 48,
      (u i * v j) • Finsupp.single 0 (X (i, 0) * X (j, 0)) := by
  have hCurrent : ((Y lattice (currentAlong lattice u))[[-1]]) =
      ∑ i : Fin lattice.rank, u i • ((Y lattice (currentState lattice i))[[-1]]) := by
    simp only [currentAlong, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  change ((Y lattice (currentAlong lattice u))[[-1]]) (currentAlong lattice v) =
    ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
      (u i * v j) • (Finsupp.single 0 (X (i, 0) * X (j, 0)) : Carrier lattice)
  rw [hCurrent]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [currentAlong, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_smul]
  change (u i * v j) • mu lattice (currentState lattice i) (-1) (currentState lattice j) = _
  rw [current_minus_one_current]

theorem currentPair_comm (u v : Fin 48 → ℂ) : currentPair u v = currentPair v u := by
  simp only [currentPair_eq_sum]
  calc
    _ = ∑ i : Fin 48, ∑ j : Fin 48,
        (v j * u i) • (Finsupp.single 0 (X (j, 0) * X (i, 0)) : Carrier lattice) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (u i) (v j), mul_comm (X (i, 0) : Oscillator lattice) (X (j, 0))]
    _ = _ := Finset.sum_comm

private theorem quadraticSum_eq_sum_basis {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    (∑ i : Fin 48, ∑ j : Fin 48,
      actualInverse lattice i j • (Finsupp.single 0 (X (i, 0) * X (j, 0)) : Carrier lattice)) =
      ∑ a : BasisIndex, currentPair (basisVector hζ a) (dualVector hζ a) := by
  simp only [inverseGram_eq_sum hζ, Finset.sum_smul, currentPair_eq_sum]
  let term (i j : Fin 48) (a : BasisIndex) : Carrier lattice :=
    (basisVector hζ a i * dualVector hζ a j) • Finsupp.single 0 (X (i, 0) * X (j, 0))
  change (∑ i, ∑ j, ∑ a, term i j a) = ∑ a, ∑ i, ∑ j, term i j a
  calc
    _ = ∑ i, ∑ a, ∑ j, term i j a :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The unscaled native oscillator quadratic sum contains both moving orders. -/
theorem native_quadratic_decomposition {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    (∑ i : Fin 48, ∑ j : Fin 48,
      actualInverse lattice i j • (Finsupp.single 0 (X (i, 0) * X (j, 0)) : Carrier lattice)) =
      (∑ a : Fin 16, currentPair (fixedBasis a) (fixedGramDual fixedBasis a)) +
      ((∑ a : Fin 16, currentPair (p48qBasis hζ a) (p48qOppositeBasis hζ a)) +
        ∑ a : Fin 16, currentPair (p48qOppositeBasis hζ a) (p48qBasis hζ a)) := by
  rw [quadraticSum_eq_sum_basis hζ]
  simp only [Fintype.sum_sum_type, basisVector, dualVector, Sum.elim_inl, Sum.elim_inr]

private theorem omega_eq_half_quadratic (H : Matrix (Fin 48) (Fin 48) ℂ) :
    LatticeActualConformalState.omega lattice H = (2 : ℂ)⁻¹ •
      ∑ i : Fin 48, ∑ j : Fin 48,
        H i j • (Finsupp.single 0 (X (i, 0) * X (j, 0)) : Carrier lattice) := by
  change (Finsupp.lsingle 0 : Oscillator lattice →ₗ[ℂ] Carrier lattice)
    (conformalPolynomial lattice H) = (2 : ℂ)⁻¹ •
      ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
        H i j • (Finsupp.single 0 (X (i, 0) * X (j, 0)) : Carrier lattice)
  simp only [conformalPolynomial, map_smul, map_sum, Finsupp.lsingle_apply]

/-- The fixed block contributes with coefficient one half and the opposite
fractional block with coefficient one in the actual untwisted conformal state. -/
theorem omega_decomposition {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    LatticeActualConformalState.omega lattice (actualInverse lattice) =
      (2 : ℂ)⁻¹ • (∑ a : Fin 16, currentPair (fixedBasis a) (fixedGramDual fixedBasis a)) +
        ∑ a : Fin 16, currentPair (p48qBasis hζ a) (p48qOppositeBasis hζ a) := by
  rw [omega_eq_half_quadratic, native_quadratic_decomposition hζ]
  have hSwap :
      (∑ a : Fin 16, currentPair (p48qOppositeBasis hζ a) (p48qBasis hζ a)) =
        ∑ a : Fin 16, currentPair (p48qBasis hζ a) (p48qOppositeBasis hζ a) :=
    Finset.sum_congr rfl fun a _ => currentPair_comm _ _
  rw [hSwap, ← two_smul ℂ, smul_add, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

theorem omega_complexInverse_decomposition {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    LatticeActualConformalState.omega lattice (gramComplex lattice)⁻¹ =
      (2 : ℂ)⁻¹ • (∑ a : Fin 16, currentPair (fixedBasis a) (fixedGramDual fixedBasis a)) +
        ∑ a : Fin 16, currentPair (p48qBasis hζ a) (p48qOppositeBasis hζ a) := by
  rw [← actualInverse_eq_complexInverse]
  exact omega_decomposition hζ

#print axioms inverseGram_apply
#print axioms native_quadratic_decomposition
#print axioms omega_decomposition
#print axioms omega_complexInverse_decomposition

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition

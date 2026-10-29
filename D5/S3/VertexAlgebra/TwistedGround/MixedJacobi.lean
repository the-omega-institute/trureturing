/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite Mobius coefficient transport for the mixed field calculation. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
import Batteries.Tactic.OpenPrivate

/-! Finite transport on the original carriers. The rectangle is bounded by
actual tensor supports before the change (i,j) -> (n=i+j,i). Neither a numeric
infinite exponential nor a full mixed Jacobi identity is assumed. The full
signed normalized mixed identity remains a separate proof obligation. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeHalfFockCorrectedField LatticePositiveEnergy LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint CorrectedInversion
open ActualOddGradeOrthogonality HalfFock.ActualEnergyCovariance
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeHalfFockFiniteCorrection (sourceWeight)
open private T lowering_killed originalL1
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private theorem lowering_after_tensor_support (D : LatticeData) (hu : IsUnit D.G.det)
    (v : ActualTensor D hu) (q : ℕ)
    (hq : (ActualEnergyRestrictedDual.maxOddWeight D hu v : ℤ) < 2*(q : ℤ)) :
    (T D hu ^ q) v = 0 := by
  classical
  let b := actualAmbientBasis D hu
  rw [← b.linearCombination_repr v]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  have bound : oddWeight D i.1 ≤ ActualEnergyRestrictedDual.maxOddWeight D hu v :=
    Finset.le_sup (f := fun i => oddWeight D i.1) hi
  have killed := lowering_killed D hu (oddWeight D i.1) (b i)
    (actual_basis_eigenvalue D hu i.1 i.2) q (by omega)
  rw [killed, smul_zero]

private theorem lowering_finite_family (D : LatticeData) (hu : IsUnit D.G.det)
    (J : ℕ) (v : ℕ → ActualTensor D hu) :
    let R := (Finset.range J).sup (fun j => ActualEnergyRestrictedDual.maxOddWeight D hu (v j)) + 1
    ∀ j < J, ∀ q : ℕ, R ≤ q → (T D hu ^ q) (v j) = 0 := by
  classical
  intro R j hj q hq
  apply lowering_after_tensor_support D hu (v j) q
  have bound := Finset.le_sup (f := fun j => ActualEnergyRestrictedDual.maxOddWeight D hu (v j))
    (Finset.mem_range.mpr hj)
  dsimp only [R] at hq
  omega

private def mobiusCutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) : ℕ :=
  let J := ActualEnergyRestrictedDual.maxOddWeight D hu x + 1
  max J ((Finset.range J).sup (fun j => ActualEnergyRestrictedDual.maxOddWeight D hu
    ((correctedField D hu a).coeff e ((T D hu ^ j) x))) + 1)

private theorem mobius_rectangle_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) (i j : ℕ)
    (outside : mobiusCutoff D hu a e x ≤ i ∨ mobiusCutoff D hu a e x ≤ j) :
    (T D hu ^ i) ((correctedField D hu a).coeff e ((T D hu ^ j) x)) = 0 := by
  classical
  let J := ActualEnergyRestrictedDual.maxOddWeight D hu x + 1
  have inputBound : J ≤ mobiusCutoff D hu a e x := le_max_left _ _
  by_cases hj : J ≤ j
  · have killed := lowering_after_tensor_support D hu x j (by dsimp [J] at hj; omega)
    rw [killed, map_zero, map_zero]
  · have hi : mobiusCutoff D hu a e x ≤ i := outside.resolve_right (by omega)
    have outputBound :
        (Finset.range J).sup (fun j => ActualEnergyRestrictedDual.maxOddWeight D hu
          ((correctedField D hu a).coeff e ((T D hu ^ j) x))) + 1 ≤ i :=
      le_trans (le_max_right _ _) hi
    exact lowering_finite_family D hu J
      (fun j => (correctedField D hu a).coeff e ((T D hu ^ j) x)) j (by omega) i outputBound

private theorem rectangle_to_diagonals {V : Type*} [AddCommGroup V]
    (R : ℕ) (f : ℕ → ℕ → V)
    (tail : ∀ i j, R ≤ i ∨ R ≤ j → f i j = 0) :
    (∑ i ∈ Finset.range R, ∑ j ∈ Finset.range R, f i j) =
      ∑ n ∈ Finset.range (2*R), ∑ i ∈ Finset.range (n+1), f i (n-i) := by
  classical
  have flip := Finset.sum_range_diag_flip (2*R) f
  calc
    _ = ∑ i ∈ Finset.range (2*R), ∑ j ∈ Finset.range (2*R-i), f i j := by
      symm
      calc
        _ = ∑ i ∈ Finset.range R, ∑ j ∈ Finset.range (2*R-i), f i j := by
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro i hi outside
          have bi : R ≤ i := by simpa using outside
          apply Finset.sum_eq_zero
          intro j hj
          exact tail i j (Or.inl bi)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          have bi := Finset.mem_range.mp hi
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro j hj outside
          exact tail i j (Or.inr (by simpa using outside))
    _ = _ := flip.symm

/-- The original all-order formal Mobius formula has an actual finite
rectangle evaluation on every source and tensor vector. Both target powers
are bounded before diagonal reindexing, including negative raw exponents. -/
theorem finite_mobius_transport (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) (z : ℂ) :
    let R := mobiusCutoff D hu a e x
    (∑ i ∈ Finset.range R, ∑ j ∈ Finset.range R,
      (z^i * (-z)^j / ((i.factorial : ℂ)*(j.factorial : ℂ))) •
        (T D hu ^ i) ((correctedField D hu a).coeff e ((T D hu ^ j) x))) =
    ∑ n ∈ Finset.range (2*R), z^n •
      (∑ h ∈ stateEnergies D a, ∑ k ∈ Finset.range (n+1),
        (Ring.choose (2*(h : ℂ)+(e : ℂ)/2-(k : ℂ)-1) (n-k) /
          (k.factorial : ℂ)) •
        (correctedField D hu ((originalL1 D ^ k) (gradeProjection D h a))).coeff
          (e-2*(n : ℤ)+2*(k : ℤ)) x) := by
  classical
  intro R
  let f (i j : ℕ) :=
    (z^i * (-z)^j / ((i.factorial : ℂ)*(j.factorial : ℂ))) •
      (T D hu ^ i) ((correctedField D hu a).coeff e ((T D hu ^ j) x))
  have tail (i j : ℕ) (outside : R ≤ i ∨ R ≤ j) : f i j = 0 := by
    dsimp only [f]
    rw [mobius_rectangle_tail D hu a e x i j outside, smul_zero]
  rw [rectangle_to_diagonals R f tail]
  apply Finset.sum_congr rfl
  intro n hn
  have transport := LinearMap.congr_fun
    (HalfFock.ActualMobiusAllOrder.corrected_field_mobius_coefficient D hu n e a) x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at transport
  rw [← transport, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [f]
  rw [smul_smul]
  congr 1
  have bound : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have split : i+(n-i)=n := Nat.add_sub_of_le bound
  rw [neg_pow]
  have hz : z^i * z^(n-i) = z^n := by rw [← pow_add, split]
  calc
    _ = (-1 : ℂ)^(n-i) * (z^i * z^(n-i)) /
        ((i.factorial : ℂ)*((n-i).factorial : ℂ)) := by ring
    _ = _ := by rw [hz]; ring

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

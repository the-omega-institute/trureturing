/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalForm
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every pair of local mutually unbiased bases in dimensions two and three has the standard measurement form. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMUBNormalFormTransport
import D5.S3.Quantum.Matrix.MonomialDiagonalPreserving

/-! The all-bases reduction for the qubit–qutrit anchor quadratic form. -/

noncomputable section

namespace AnchorMeasurement

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Tomography.MUB.MUBHadamardCompatibility
open D5.S3.Quantum.Matrix.MonomialDiagonalPreserving (monomial monomial_apply)

namespace MUBNormalForm

section LocalNormalForm

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem monomial_mul_entry (p : Equiv.Perm n) (a : n → ℂ) (X : Mat n) (i j : n) :
    (monomial p a * X) i j = a i * X (p i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (p i)]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

private theorem mul_monomial_entry (X : Mat n) (p : Equiv.Perm n)
    (a : n → ℂ) (i j : n) :
    (X * monomial p a) i (p j) = X i j * a j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have h : p j ≠ p k := fun h => hk (p.injective h).symm
    simp [h]
  · simp

private def monomialUnitary (p : Equiv.Perm n) (a : n → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1) : Matrix.unitaryGroup n ℂ := by
  refine ⟨monomial p a, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  rw [monomial_mul_entry, Matrix.conjTranspose_apply]
  by_cases h : i = j
  · subst j
    rw [monomial_apply, if_pos rfl, Matrix.one_apply_eq]
    exact phase_mul_star (ha i)
  · have hp : p i ≠ p j := fun h' => h (p.injective h')
    simp [hp, h]

/-- Factor the relative basis by a row monomial and a column monomial.
The row monomial is absorbed into the common change of coordinates. -/
private theorem pair_normalForm_of_equivalent (Q R H : Matrix.unitaryGroup n ℂ)
    (h : HadamardEquivalent ((Q : Mat n)ᴴ * (R : Mat n)) (H : Mat n)) :
    ∃ W : Matrix.unitaryGroup n ℂ, BasisRelabel Q (W * 1) ∧ BasisRelabel R (W * H) := by
  obtain ⟨p, q, a, b, ha, hb, he⟩ := hadamardEquivalent_symm h
  let M := monomialUnitary p a ha
  let W := Q * M
  refine ⟨W, ?_, ?_⟩
  · rw [mul_one]
    refine ⟨p, (fun j => star (a j)), ?_, ?_⟩
    · intro j
      simpa only [Complex.star_def, Complex.normSq_conj] using ha j
    · intro i j
      change (Q : Mat n) i j = ((Q : Mat n) * monomial p a) i (p j) * star (a j)
      rw [mul_monomial_entry, mul_assoc, phase_mul_star (ha j), mul_one]
  · refine ⟨q, b, hb, ?_⟩
    intro i j
    have hR : (Q : Mat n) * ((Q : Mat n)ᴴ * (R : Mat n)) = (R : Mat n) := by
      have hQ : (Q : Mat n) * (Q : Mat n)ᴴ = 1 := Unitary.coe_mul_star_self Q
      rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
    change (R : Mat n) i j =
      (((Q : Mat n) * monomial p a) * (H : Mat n)) i (q j) * b j
    rw [Matrix.mul_assoc]
    calc
      (R : Mat n) i j = ∑ k, (Q : Mat n) i k * ((Q : Mat n)ᴴ * (R : Mat n)) k j := by
        simpa only [Matrix.mul_apply] using congrArg (fun X : Mat n => X i j) hR.symm
      _ = (∑ k, (Q : Mat n) i k * (monomial p a * (H : Mat n)) k (q j)) * b j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        simp only [he, monomial_mul_entry, mul_assoc]
      _ = _ := by rw [Matrix.mul_apply]

end LocalNormalForm

theorem alice_pair_normalForm (Q R : Matrix.unitaryGroup Alice ℂ)
    (h : ∀ i j, Complex.normSq (((Q : Mat Alice)ᴴ * (R : Mat Alice)) i j) = (1 / 2 : ℝ)) :
    ∃ W : Matrix.unitaryGroup Alice ℂ,
      BasisRelabel Q (W * 1) ∧ BasisRelabel R (W * aliceR) := by
  apply pair_normalForm_of_equivalent
  exact flat_two_equivalent (star Q * R) h

theorem bob_pair_normalForm (Q R : Matrix.unitaryGroup Bob ℂ)
    (h : ∀ i j, Complex.normSq (((Q : Mat Bob)ᴴ * (R : Mat Bob)) i j) = (1 / 3 : ℝ)) :
    ∃ W : Matrix.unitaryGroup Bob ℂ,
      BasisRelabel Q (W * 1) ∧ BasisRelabel R (W * bobR) := by
  apply pair_normalForm_of_equivalent
  exact flat_three_equivalent (star Q * R) h

end MUBNormalForm

open MUBNormalForm

/-- Any two local MUB pairs give the standard-anchor quadratic on the
unitarily transported state and tangent. -/
theorem anchorQuadraticIn_eq_standard
    (UQ UR : Matrix.unitaryGroup Alice ℂ) (VQ VR : Matrix.unitaryGroup Bob ℂ)
    (hA : ∀ i j, Complex.normSq (((UQ : Mat Alice)ᴴ * (UR : Mat Alice)) i j) = (1 / 2 : ℝ))
    (hB : ∀ i j, Complex.normSq (((VQ : Mat Bob)ᴴ * (VR : Mat Bob)) i j) = (1 / 3 : ℝ)) :
    ∃ (W : Matrix.unitaryGroup Alice ℂ) (Z : Matrix.unitaryGroup Bob ℂ),
      ∀ (α : DensityState Alice) (β : DensityState Bob) (D : JointMatrix),
        anchorQuadraticIn UQ UR VQ VR α β D =
          anchorQuadratic (stateInBasis W α) (stateInBasis Z β)
            (inBasis (productBasis W Z) D) := by
  obtain ⟨W, hUQ, hUR⟩ := alice_pair_normalForm UQ UR hA
  obtain ⟨Z, hVQ, hVR⟩ := bob_pair_normalForm VQ VR hB
  exact ⟨W, Z, anchorQuadraticIn_normalForm W Z hUQ hUR hVQ hVR⟩

end AnchorMeasurement

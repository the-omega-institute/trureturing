/- GID: D5/S3/VertexAlgebra/SourceBPZ/ChargedPrimary
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/ChargedPrimary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charged-primary transpose of the actual original integer lattice field on all finite-charge states. -/

import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import D5.S3.VertexAlgebra.LatticeActualMixedLocality
import D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce

/-!
The bilinear transpose is proved on the literal original integer oscillator
ring and its finite-charge Carrier. The ground coefficient is fixed by the
actual exponential's weighted degree and the actual lattice cocycle. Two
polynomial inductions use the existing all-integer current/raw commutator.
No Gram inverse, positivity or nonzero-rank premise is needed.

Classical source: Frenkel--Lepowsky--Meurman, Vertex Operator Algebras and
the Monster, invariant bilinear forms; Bakalov--Kac, math/0402315v1,
section 4.1, for the actual lattice exponential conventions.
The signed Wick supplier retains its original attribution and license.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeAllStateField LatticePositiveEnergy
open LatticeActualGeneratorLocality LatticeActualProductKernel
open LatticeActualMixedLocality OriginalSourcePairing SourcePairingLaws
open MvPolynomial
open private wick_constant_right from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
open private epsilon_neg_right from
  D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce

private theorem creation_constant (D : LatticeData) (a : Charge D) (t : ℤ) :
    (creationCoeff D a t).coeff 0 = if t = 0 then 1 else 0 := by
  classical
  by_cases ht : t < 0
  · simp [creationCoeff, ht, ne_of_lt ht]
  by_cases hz : t = 0
  · subst t
    simp [creationCoeff, LatticeSugawaraConformal.exponential_constant]
  rw [if_neg hz]
  apply ((actual_creation_coefficient_transport D a a).1 t).coeff_eq_zero
  simp only [Finsupp.weight_zero]
  omega

private theorem ground_coefficient (D : LatticeData) (a d g : Charge D) (k : ℤ) :
    sourcePairing D (rawCoeff D a k (Finsupp.single d 1)) (Finsupp.single g 1) =
      if g = -(a+d) then epsilon D a d * (if k = bilinear D a d then 1 else 0)
      else 0 := by
  classical
  have ht : translatedPolynomial D a 1 = Polynomial.monomial 0 1 := by
    simp [translatedPolynomial]
  rw [raw_single_convolution, ht, convolution_monomial]
  simp only [Int.cast_zero, add_zero, one_mul, map_smul, LinearMap.smul_apply,
    sourcePairing_single_single, smul_eq_mul]
  have hw : integerWick D (creationCoeff D a (k-bilinear D a d)) 1 =
      if k = bilinear D a d then 1 else 0 := by
    change SignedOscillatorWick.wick D
      (retune D (creationCoeff D a (k-bilinear D a d))) (C 1) = _
    rw [wick_constant_right, retune_constant, creation_constant]
    simp only [one_mul, sub_eq_zero]
  rw [hw]
  split_ifs <;> simp_all

private theorem reflected_epsilon (D : LatticeData) (a d : Charge D) :
    epsilon D a d = paritySign (chargeEnergy D a) * epsilon D a (-(a+d)) := by
  have hs : epsilon D a a = paritySign (chargeEnergy D a) := by
    rw [epsilon, chargeEnergy_cocycle]
  rw [epsilon_neg_right, epsilon_add_right, hs, ← mul_assoc, paritySign_square, one_mul]

private theorem ground_transpose (D : LatticeData) (a d g : Charge D) (k : ℤ) :
    sourcePairing D (rawCoeff D a k (Finsupp.single d 1)) (Finsupp.single g 1) =
      paritySign (chargeEnergy D a) * sourcePairing D (Finsupp.single d 1)
        (rawCoeff D a (-k-bilinear D a a) (Finsupp.single g 1)) := by
  classical
  rw [sourcePairing_symmetric D (Finsupp.single d 1), ground_coefficient,
    ground_coefficient]
  by_cases hg : g = -(a+d)
  · have hd : d = -(a+g) := by rw [hg]; abel
    have hk : (-k-bilinear D a a = bilinear D a g) ↔ k = bilinear D a d := by
      rw [hg, bilinear_neg_right, bilinear_add_right]
      omega
    rw [if_pos hg, if_pos hd, hk, reflected_epsilon D a d, hg]
    ring
  · have hd : d ≠ -(a+g) := by
      intro h
      apply hg
      rw [h]
      abel
    rw [if_neg hg, if_neg hd, mul_zero]

private theorem current_raw_apply (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (a : Charge D) (k : ℤ) (u : Carrier D) :
    neutralMode D i m (rawCoeff D a k u) =
      rawCoeff D a k (neutralMode D i m u) +
        (bilinear D (unitCharge D i) a : ℂ) • rawCoeff D a (k-m) u := by
  have h := congrArg (fun f : Module.End ℂ (Carrier D) => f u)
    (neutral_raw_commutator D i m a k)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

private theorem raw_creator_apply (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (a : Charge D) (k : ℤ) (u : Carrier D) :
    rawCoeff D a k (neutralMode D i (-(n : ℤ)-1) u) =
      neutralMode D i (-(n : ℤ)-1) (rawCoeff D a k u) -
        (bilinear D (unitCharge D i) a : ℂ) • rawCoeff D a (k+(n : ℤ)+1) u := by
  rw [current_raw_apply, show k-(-(n : ℤ)-1) = k+(n : ℤ)+1 by omega,
    add_sub_cancel_right]

private theorem creator_single (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (d : Charge D) (p : Oscillator D) :
    neutralMode D i (-(n : ℤ)-1) (Finsupp.single d p) =
      Finsupp.single d (X (i,n) * p) := by
  rw [neutralMode_single, neutralPolynomialMode_negative]
  rfl

private theorem positive_ground (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (d : Charge D) :
    neutralMode D i ((n : ℤ)+1) (Finsupp.single d 1) = 0 := by
  simp [neutralMode_single, neutralPolynomialMode_positive, weightedPartial]

private theorem pairing_current_right (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (u v : Carrier D) :
    sourcePairing D u (neutralMode D i m v) =
      -sourcePairing D (neutralMode D i (-m) u) v := by
  have h := sourcePairing_neutralMode D i (-m) u v
  simpa only [neg_neg] using congrArg Neg.neg h.symm

private theorem ground_right_polynomial (D : LatticeData) (a d g : Charge D)
    (p : Oscillator D) : ∀ k : ℤ,
    sourcePairing D (rawCoeff D a k (Finsupp.single d 1)) (Finsupp.single g p) =
      paritySign (chargeEnergy D a) * sourcePairing D (Finsupp.single d 1)
        (rawCoeff D a (-k-bilinear D a a) (Finsupp.single g p)) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    intro k
    have hc : Finsupp.single g (C c) = c • (Finsupp.single g 1 : Carrier D) := by
      simp [← Finsupp.smul_single, MvPolynomial.smul_eq_C_mul]
    simp only [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, ground_transpose]
    ring
  | add p q hp hq =>
    intro k
    simp only [Finsupp.single_add, map_add, LinearMap.add_apply, hp, hq, mul_add]
  | mul_X p x hp =>
    rcases x with ⟨i,n⟩
    intro k
    have hpos := current_raw_apply D i ((n : ℤ)+1) a k (Finsupp.single d 1)
    rw [positive_ground, map_zero, zero_add] at hpos
    have hleft :
        sourcePairing D (rawCoeff D a k (Finsupp.single d 1))
          (neutralMode D i (-(n : ℤ)-1) (Finsupp.single g p)) =
        -(bilinear D (unitCharge D i) a : ℂ) *
          sourcePairing D (rawCoeff D a (k-((n : ℤ)+1)) (Finsupp.single d 1))
            (Finsupp.single g p) := by
      rw [pairing_current_right, show -(-(n : ℤ)-1) = (n : ℤ)+1 by omega, hpos]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, neg_mul]
    have hright :
        sourcePairing D (Finsupp.single d 1)
          (rawCoeff D a (-k-bilinear D a a)
            (neutralMode D i (-(n : ℤ)-1) (Finsupp.single g p))) =
        -(bilinear D (unitCharge D i) a : ℂ) *
          sourcePairing D (Finsupp.single d 1)
            (rawCoeff D a (-k-bilinear D a a+(n : ℤ)+1) (Finsupp.single g p)) := by
      rw [raw_creator_apply, map_sub, map_smul, pairing_current_right,
        show -(-(n : ℤ)-1) = (n : ℤ)+1 by omega, positive_ground]
      simp
    simp only [mul_comm p (X (i,n)), ← creator_single D i n g p]
    rw [hleft, hright, hp]
    rw [show -(k-((n : ℤ)+1))-bilinear D a a =
      -k-bilinear D a a+(n : ℤ)+1 by omega]
    ring

private theorem ground_right (D : LatticeData) (a d : Charge D) (v : Carrier D) :
    ∀ k : ℤ, sourcePairing D (rawCoeff D a k (Finsupp.single d 1)) v =
      paritySign (chargeEnergy D a) * sourcePairing D (Finsupp.single d 1)
        (rawCoeff D a (-k-bilinear D a a) v) := by
  induction v using Finsupp.induction_linear with
  | zero => intro k; simp
  | add v w hv hw =>
    intro k
    simp only [map_add, LinearMap.add_apply, hv, hw, mul_add]
  | single g p => exact ground_right_polynomial D a d g p

private theorem polynomial_left (D : LatticeData) (a d : Charge D)
    (p : Oscillator D) : ∀ (k : ℤ) (v : Carrier D),
    sourcePairing D (rawCoeff D a k (Finsupp.single d p)) v =
      paritySign (chargeEnergy D a) * sourcePairing D (Finsupp.single d p)
        (rawCoeff D a (-k-bilinear D a a) v) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    intro k v
    have hc : Finsupp.single d (C c) = c • (Finsupp.single d 1 : Carrier D) := by
      simp [← Finsupp.smul_single, MvPolynomial.smul_eq_C_mul]
    simp only [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, ground_right]
    ring
  | add p q hp hq =>
    intro k v
    simp only [Finsupp.single_add, map_add, LinearMap.add_apply, hp, hq, mul_add]
  | mul_X p x hp =>
    rcases x with ⟨i,n⟩
    intro k v
    simp only [mul_comm p (X (i,n)), ← creator_single D i n d p]
    rw [raw_creator_apply]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [sourcePairing_neutralMode,
      show -(-(n : ℤ)-1) = (n : ℤ)+1 by omega, hp, hp]
    rw [sourcePairing_neutralMode,
      show -(-(n : ℤ)-1) = (n : ℤ)+1 by omega, current_raw_apply]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [show -(k+(n : ℤ)+1)-bilinear D a a =
      (-k-bilinear D a a)-((n : ℤ)+1) by omega]
    ring

private theorem raw_transpose (D : LatticeData) (a : Charge D) (k : ℤ)
    (u v : Carrier D) :
    sourcePairing D (rawCoeff D a k u) v = paritySign (chargeEnergy D a) *
      sourcePairing D u (rawCoeff D a (-k-bilinear D a a) v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, hu, hw, mul_add]
  | single d p => exact polynomial_left D a d p k v

/-
proof_shape: sourcePairing_charged_primary: content
admission_basis: escape-witness
escape_witness: The actual charged exponential has the concrete bilinear
transpose on all oscillator polynomials and all finite charge supports;
the sign is forced by the diagonal lattice cocycle, and the reflected
standard mode is forced by the actual quadratic charge energy.
All private helpers are consumed by this theorem through raw_transpose.
-/
/-- Every actual charged-primary mode has its quadratic-energy reflected transpose. -/
theorem sourcePairing_charged_primary (D : LatticeData) (a : Charge D) (m : ℤ)
    (u v : Carrier D) :
    sourcePairing D ((Y D (Finsupp.single a 1))[[m]] u) v =
      paritySign (chargeEnergy D a) * sourcePairing D u
        ((Y D (Finsupp.single a 1))[[2*chargeEnergy D a-m-2]] v) := by
  have hm : -(2*chargeEnergy D a-m-2)-1 = -(-m-1)-bilinear D a a := by
    rw [← two_chargeEnergy]
    omega
  simp only [stateField_ground, actual_modes, hm]
  exact raw_transpose D a (-m-1) u v

#print axioms sourcePairing_charged_primary

end D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary

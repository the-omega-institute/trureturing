/- GID: D5/S3/VertexAlgebra/LatticeActualMixedLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualMixedLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual neutral and charged fields obey the order-one mixed locality law. -/

import D5.S3.VertexAlgebra.LatticeActualAnnihilation
import D5.S3.VertexAlgebra.LatticeActualOrderedProducts
import D5.S3.VertexAlgebra.FieldNormalProductLocality

/- Exact neutral-charged commutator and locality on the actual lattice carrier.
   Derived from actual multiplication, charge zero modes, and annihilation.
   Bakalov--Kac math/0402315v1, section 4.1, equations (4.5), (4.12). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeActualMixedLocality
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualGeneratorLocality
open LatticeActualProductKernel LatticeActualOrderedProducts LatticeActualAnnihilation
open scoped BigOperators VertexOperator
noncomputable section

theorem convolution_smul (D : LatticeData) (α : Charge D) (s : ℤ)
    (c : ℂ) (q : Polynomial (Oscillator D)) :
    convolution D α s (c • q) = c • convolution D α s q :=
  (convolution D α s).map_smul_of_tower c q

theorem positive_sector_raw (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (α δ : Charge D) (s : ℤ) (p : Oscillator D) :
    neutralPolynomialMode D i (α+δ) (n+1) (convolution D α s (translatedPolynomial D α p)) -
      convolution D α s (translatedPolynomial D α (neutralPolynomialMode D i δ (n+1) p)) =
      (bilinear D (unitCharge D i) α : ℂ) •
        convolution D α (s-(n+1 : ℕ)) (translatedPolynomial D α p) := by
  simp only [neutralPolynomialMode,show ¬(n+1 : ℤ) < 0 by omega,
    show (n+1 : ℤ) ≠ 0 by omega,if_false,
    show ((n+1 : ℤ)-1).toNat = n by omega,LinearMap.smul_apply,
    Int.cast_add,Int.cast_natCast,Int.cast_one]
  change (n+1 : ℂ) • annihilate D i n (convolution D α s (translatedPolynomial D α p)) -
    convolution D α s (translatedPolynomial D α ((n+1 : ℂ) • annihilate D i n p)) = _
  rw [LatticeSugawaraConformal.translated_smul,convolution_smul,annihilation_convolution,
    ←annihilation_transport,smul_add,add_sub_cancel_left,smul_smul]
  have h : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [←mul_assoc,mul_inv_cancel₀ h,one_mul]

theorem positive_current_raw (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (α : Charge D) (k : ℤ) :
    neutralMode D i (n+1) * rawCoeff D α k - rawCoeff D α k * neutralMode D i (n+1) =
      (bilinear D (unitCharge D i) α : ℂ) • rawCoeff D α (k-(n+1 : ℕ)) := by
  apply Finsupp.lhom_ext
  intro δ p
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LatticeSugawaraCurrents.neutralMode_single,raw_single_convolution,
    LinearMap.smul_apply,map_smul,←Finsupp.smul_single]
  rw [←smul_sub,←Finsupp.single_sub,positive_sector_raw]
  rw [show k-bilinear D α δ-(n+1 : ℕ) = k-(n+1 : ℕ)-bilinear D α δ by omega]
  rw [←Finsupp.smul_single,smul_comm]

theorem zero_current_raw (D : LatticeData) (i : Fin D.rank)
    (α : Charge D) (k : ℤ) :
    neutralMode D i 0 * rawCoeff D α k - rawCoeff D α k * neutralMode D i 0 =
      (bilinear D (unitCharge D i) α : ℂ) • rawCoeff D α k := by
  apply Finsupp.lhom_ext
  intro δ p
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LatticeSugawaraCurrents.neutralMode_single,raw_single_convolution,
    neutralPolynomialMode,lt_self_iff_false,if_false,if_true,LinearMap.smul_apply,
    LinearMap.id_apply,map_smul,LatticeSugawaraConformal.translated_smul,convolution_smul,←Finsupp.smul_single,
    bilinear_add_right,Int.cast_add]
  module

theorem negative_current_raw (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (α : Charge D) (k : ℤ) :
    neutralMode D i (-(n : ℤ)-1) * rawCoeff D α k -
      rawCoeff D α k * neutralMode D i (-(n : ℤ)-1) =
      (bilinear D (unitCharge D i) α : ℂ) • rawCoeff D α (k+(n+1 : ℕ)) := by
  have h := raw_creator_operator D α k (i,n)
  change rawCoeff D α k * neutralMode D i (-(n : ℤ)-1) =
    neutralMode D i (-(n : ℤ)-1) * rawCoeff D α k -
      (bilinear D α (unitCharge D i) : ℂ) • rawCoeff D α (k+(n+1 : ℕ)) at h
  rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D (unitCharge D i) α]
  rw [h]
  abel

/-- The exact all-integer current/charge commutator, on all finite input supports. -/
theorem neutral_raw_commutator (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (α : Charge D) (k : ℤ) :
    neutralMode D i m * rawCoeff D α k - rawCoeff D α k * neutralMode D i m =
      (bilinear D (unitCharge D i) α : ℂ) • rawCoeff D α (k-m) := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · let n := (-m-1).toNat
    have he : m = -(n : ℤ)-1 := by dsimp [n]; omega
    rw [he,show k-(-(n : ℤ)-1) = k+(n+1 : ℕ) by omega]
    exact negative_current_raw D i n α k
  · subst m
    simpa using zero_current_raw D i α k
  · let n := (m-1).toNat
    have he : m = (n+1 : ℕ) := by dsimp [n]; omega
    rw [he]
    exact positive_current_raw D i n α k

theorem neutral_actual_commutator (D : LatticeData) (i : Fin D.rank)
    (α : Charge D) (m n : ℤ) :
    FieldNormalProductLocality.commutator (neutralField D i) (actualField D α) m n =
      (bilinear D (unitCharge D i) α : ℂ) • (actualField D α)[[m+n]] := by
  simp only [FieldNormalProductLocality.commutator,LatticeSugawaraCurrents.neutralField_ncoeff,actual_modes]
  rw [neutral_raw_commutator]
  congr 2
  omega

/-- Uniform mixed locality, with the actual current conventions and order one. -/
theorem actual_neutral_charged_locality (D : LatticeData) (i : Fin D.rank) (α : Charge D) :
    FieldNormalProductLocality.delta^[1]
      (FieldNormalProductLocality.commutator (neutralField D i) (actualField D α)) = 0 := by
  funext m n
  simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,
    FieldNormalProductLocality.delta,neutral_actual_commutator,Pi.zero_apply]
  rw [show m+1+n = m+(n+1) by omega,sub_self]

end
end D5.S3.VertexAlgebra.LatticeActualMixedLocality

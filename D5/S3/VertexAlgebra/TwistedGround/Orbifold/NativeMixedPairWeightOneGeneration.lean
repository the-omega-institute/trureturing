import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeightOne
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddNeutralZhuReduction

/-! The ground coefficients generate the odd carrier under the existing
fixed-algebra modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeightOne

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality LatticeInvolution MvPolynomial
open LatticeFiniteNegativeGeneration (neutralMode)
open LatticeSugawaraCurrents (neutralMode_single neutralPolynomialMode_negative)
open Lattice.ActualFixedC2 (neutralWord neutralPolynomial)
open LatticeAllStateField (occurrences occurrences_product)
open NativeMixedPairField (mu)
open NativeOddTwistedIntertwiner (OddCarrier oddCurrent oddMode
  leechGroundVector leechUnit chargeZeroOdd current_pair_mem_map oddSource_eq_top)
open private oddCurrent_grade_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private stress stress_odd_zero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private oddNeutralWord oddSingleton_zero oddSingleton_translation theta_neutral_word
  oddPart_neutral_word from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddNeutralZhuReduction
open private oddPart oddPart_on_odd exists_single_charge_zero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance

local notation "ℒ" => leechData
local notation "H" => leechGroundVector

private theorem chargeZero_mem_of_currents (S : Submodule ℂ (OddCarrier ℒ))
    (hcurr : ∀ i, oddCurrent ℒ i ∈ S)
    (stable : ∀ a n b, b ∈ S → oddMode ℒ a n b ∈ S) :
    chargeZeroOdd ℒ ≤ S := by
  have hsingle (i : Fin (ℒ).rank) (k : ℕ)
      (hk : Odd ([(i, k)] : List (Index ℒ)).length) :
      oddNeutralWord ℒ [(i, k)] hk ∈ S := by
    induction k with
    | zero =>
      rw [oddSingleton_zero]
      exact hcurr i
    | succ k ih =>
      let b := oddNeutralWord ℒ [(i, k)] (by simp)
      have hb := stable (stress ℒ) 0 b (ih (by simp))
      rw [stress_odd_zero leechUnit, oddSingleton_translation ℒ i k _ hk] at hb
      have hscalar : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simpa only [smul_smul, inv_mul_cancel₀ hscalar, one_smul] using
        S.smul_mem (k + 1 : ℂ)⁻¹ hb
  have hword (w : List (Index ℒ)) (hw : Odd w.length) : oddNeutralWord ℒ w hw ∈ S := by
    induction w using List.twoStepInduction with
    | nil => simp at hw
    | singleton x => exact hsingle x.1 x.2 hw
    | cons_cons x y w ih _ =>
      have hw' : Odd w.length := by
        rw [Nat.odd_iff] at hw ⊢
        simp only [List.length_cons] at hw
        omega
      have hpair := current_pair_mem_map ℒ S stable _ (ih hw') x.1 y.1
        (-(x.2 : ℤ) - 1) (-(y.2 : ℤ) - 1)
      change neutralMode ℒ x.1 (-(x.2 : ℤ) - 1)
        (neutralMode ℒ y.1 (-(y.2 : ℤ) - 1)
          (Finsupp.single 0 (neutralPolynomial ℒ w))) ∈ S.map (minusSpace ℒ).subtype at hpair
      rw [neutralMode_single, neutralPolynomialMode_negative, LinearMap.mulLeft_apply,
        neutralMode_single, neutralPolynomialMode_negative, LinearMap.mulLeft_apply] at hpair
      obtain ⟨b, hb, hval⟩ := Submodule.mem_map.mp hpair
      have hEq : b = oddNeutralWord ℒ (x :: y :: w) hw := Subtype.ext hval
      rwa [hEq] at hb
  have hpart (w : List (Index ℒ)) : oddPart ℒ (neutralWord ℒ w) ∈ S := by
    rcases Nat.even_or_odd w.length with he | ho
    · have hz : oddPart ℒ (neutralWord ℒ w) = 0 := by
        apply Subtype.ext
        change (2 : ℂ)⁻¹ • (neutralWord ℒ w - theta ℒ (neutralWord ℒ w)) = 0
        rw [theta_neutral_word, he.neg_one_pow, one_smul, sub_self, smul_zero]
      rw [hz]
      exact S.zero_mem
    · rw [oddPart_neutral_word ℒ w ho]
      exact hword w ho
  intro a ha
  obtain ⟨p, hp⟩ := exists_single_charge_zero a.val ha
  let lift : Oscillator ℒ →ₗ[ℂ] OddCarrier ℒ := (oddPart ℒ).comp (Finsupp.lsingle 0)
  have hpMem : lift p ∈ S := by
    clear hp
    induction p using MvPolynomial.induction_on' with
    | monomial e z =>
      have he : monomial e z = z • neutralPolynomial ℒ (occurrences ℒ e) := by
        change monomial e z = z • ((occurrences ℒ e).map (fun x => (X x : Oscillator ℒ))).prod
        rw [occurrences_product, smul_monomial, smul_eq_mul, mul_one]
      rw [he, map_smul]
      exact S.smul_mem z (hpart (occurrences ℒ e))
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  have heq : lift p = a := by
    change oddPart ℒ (Finsupp.single 0 p) = a
    rw [← hp, oddPart_on_odd]
  rwa [heq] at hpMem

/-- The least submodule containing the literal ground coefficients and closed
under all modes of the actual fixed lattice algebra. -/
def groundCoefficientModeClosure : Submodule ℂ (OddCarrier ℒ) :=
  sInf {S | (∀ P : firstTwistedGrade, (mu true P.val).coeff (-5) H ∈ S) ∧
    (∀ (a : FixedCarrier ℒ) n b, b ∈ S → oddMode ℒ a n b ∈ S)}

/-- The fixed-algebra mode closure of the weight-one ground coefficients is
the full actual odd untwisted carrier. -/
theorem groundCoefficientModeClosure_eq_top : groundCoefficientModeClosure = ⊤ := by
  apply top_unique
  apply le_sInf
  intro S hS
  rcases hS with ⟨hcoeff, stable⟩
  have hcurr (i : Fin (ℒ).rank) : oddCurrent ℒ i ∈ S := by
    obtain ⟨P, hP, he⟩ :=
      exists_mu_true_negFive_ground_eq (oddCurrent ℒ i) (oddCurrent_grade_one ℒ i)
    exact he ▸ hcoeff ⟨P, hP⟩
  exact (oddSource_eq_top ℒ leech_spec.2.2.1 S
    (chargeZero_mem_of_currents S hcurr stable) stable).ge

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeightOne


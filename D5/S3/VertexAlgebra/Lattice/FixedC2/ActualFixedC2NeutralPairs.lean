/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Translation and quadratic cancellation reduce neutral pair classes to total index at most six. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The charge-zero two-oscillator slice of the actual fixed C₂ quotient.

The polynomial variable `X (i, a)` corresponds to the current mode `-a - 1`.
The fixed quadratic modes used below cancel at oscillator length four.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticeInvolution
open LatticeActualConformalState LatticeActualVertexAlgebra
open LatticeActualStateDerivative LatticeActualAnnihilation LatticeActualStateFieldCalculus
open LatticeFiniteNegativeGeneration FieldNormalProduct MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped VertexOperator

noncomputable section

local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The neutral state with two creation operators, indexed from zero. -/
def neutralPair (D : LatticeData) (i j : Fin D.rank) (a b : ℕ) : FixedCarrier D :=
  ⟨Finsupp.single 0 (X (i, a) * X (j, b)), by
    rw [mem_fixedSpace]
    change thetaLinear D (Finsupp.single 0 (X (i, a) * X (j, b))) = _
    simp only [theta_single, neg_zero, map_mul, sigma_X, neg_mul_neg]⟩

abbrev pairClass (D : LatticeData) (i j : Fin D.rank) (a b : ℕ) :
    FixedCarrier D ⧸ fixedC2 D :=
  (fixedC2 D).mkQ (neutralPair D i j a b)

private theorem pair_comm (D : LatticeData) (i j : Fin D.rank) (a b : ℕ) :
    neutralPair D i j a b = neutralPair D j i b a := by
  apply Subtype.ext
  simp [neutralPair, mul_comm]

/-- Translation of a fixed pair gives the transfer relation for its two indices. -/
theorem pair_class_transfer (D : LatticeData) (i j : Fin D.rank) (a b : ℕ) :
    (a + 1 : ℂ) • pairClass D i j (a + 1) b +
      (b + 1 : ℂ) • pairClass D i j a (b + 1) = 0 := by
  have h : fixedTranslation D (neutralPair D i j a b) =
      (a + 1 : ℂ) • neutralPair D i j (a + 1) b +
      (b + 1 : ℂ) • neutralPair D i j a (b + 1) := by
    apply Subtype.ext
    change translation D (Finsupp.single 0 (X (i, a) * X (j, b))) =
      (a + 1 : ℂ) • Finsupp.single 0 (X (i, a + 1) * X (j, b)) +
      (b + 1 : ℂ) • Finsupp.single 0 (X (i, a) * X (j, b + 1))
    rw [translation_single]
    change (Finsupp.lsingle 0 : Oscillator D →ₗ[ℂ] Carrier D) _ =
      (a + 1 : ℂ) • (Finsupp.lsingle 0 : Oscillator D →ₗ[ℂ] Carrier D) _ +
      (b + 1 : ℂ) • (Finsupp.lsingle 0 : Oscillator D →ₗ[ℂ] Carrier D) _
    rw [← map_smul, ← map_smul, ← map_add]
    suffices hp : oscillatorDerivation D (X (i, a) * X (j, b)) +
          chargePolynomial D 0 * (X (i, a) * X (j, b)) =
        (a + 1 : ℂ) • (X (i, a + 1) * X (j, b)) +
          (b + 1 : ℂ) • (X (i, a) * X (j, b + 1)) from
      congrArg (Finsupp.lsingle (R := ℂ) (0 : Charge D)) hp
    simp only [chargePolynomial, Pi.zero_apply, Int.cast_zero, zero_smul, Finset.sum_const_zero,
      zero_mul, add_zero, oscillatorDerivation, Derivation.leibniz,
      MvPolynomial.mkDerivation_X, smul_eq_mul, mul_smul_comm]
    rw [mul_comm (X (j, b)) (X (i, a + 1)), add_comm]
  have hz : (fixedC2 D).mkQ (fixedTranslation D (neutralPair D i j a b)) = 0 :=
    (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr
      (translation_mem_fixedC2 D (neutralPair D i j a b))
  simpa only [h, map_add, map_smul] using hz

/-- Transfer to the oscillator with index zero in the first coordinate. -/
theorem pair_class_normalize (D : LatticeData) (i j : Fin D.rank) (a b : ℕ) :
    pairClass D i j a b =
      ((-1 : ℂ) ^ a * ((a + b).choose a : ℂ)) • pairClass D i j 0 (a + b) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    have ha : (a + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
    have h := pair_class_transfer D i j a b
    rw [ih (b + 1), show a + (b + 1) = a + 1 + b by omega, smul_smul,
      add_eq_zero_iff_eq_neg] at h
    have hb := Nat.choose_succ_right_eq (n := a + b + 1) (k := a)
    have hc : ((a + 1 + b).choose (a + 1) : ℂ) * (a + 1) =
        ((a + 1 + b).choose a : ℂ) * (b + 1) := by
      exact_mod_cast (show (a + 1 + b).choose (a + 1) * (a + 1) =
        (a + 1 + b).choose a * (b + 1) by
          simpa only [show a + b + 1 = a + 1 + b by omega,
            show a + 1 + b - a = b + 1 by omega, mul_comm] using hb)
    apply (smul_right_injective _ ha)
    dsimp only
    rw [h, smul_smul, ← neg_smul, pow_succ]
    congr 1
    linear_combination ((-1 : ℂ) ^ a) * hc

/-- Odd total oscillator index in one colour gives zero in the intrinsic quotient. -/
theorem diagonal_pair_class_odd (D : LatticeData) (i : Fin D.rank) (a b : ℕ)
    (hab : Odd (a + b)) : pairClass D i i a b = 0 := by
  let n := a + b
  have h := congrArg (fun v : FixedCarrier D => (fixedC2 D).mkQ v) (pair_comm D i i n 0)
  change pairClass D i i n 0 = pairClass D i i 0 n at h
  rw [pair_class_normalize D i i n 0, add_zero, Nat.choose_self, Nat.cast_one, mul_one,
    hab.neg_one_pow, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul ℂ] at h
  have hn : pairClass D i i 0 n = 0 := (smul_eq_zero.mp h).resolve_left (by norm_num)
  rw [pair_class_normalize, hn, smul_zero]

private abbrev x (D : LatticeData) (i : Fin D.rank) (a : ℕ) : Oscillator D := X (i, a)
private abbrev embed (D : LatticeData) : Oscillator D →ₗ[ℂ] Carrier D := Finsupp.lsingle 0
private abbrev gram (D : LatticeData) (i j : Fin D.rank) : ℂ := D.G i j

private def create (D : LatticeData) (i : Fin D.rank) (a : ℕ) :
    Module.End ℂ (Carrier D) :=
  neutralMode D i (-(a : ℤ) - 1)

private theorem create_embed (D : LatticeData) (i : Fin D.rank) (a : ℕ)
    (p : Oscillator D) : create D i a (embed D p) = embed D (x D i a * p) := by
  change neutralMode D i (-(a : ℤ) - 1) (Finsupp.single 0 p) = _
  rw [neutralMode_single, neutralPolynomialMode_negative]
  rfl

private theorem translate_pair (D : LatticeData) (i : Fin D.rank) (a : ℕ) :
    translation D (neutralPair D i i a a).val =
      (2 * (a + 1) : ℂ) • embed D (x D i a * x D i (a + 1)) := by
  change translation D (Finsupp.single 0 (x D i a * x D i a)) = _
  rw [translation_single, ← map_smul]
  apply congrArg (fun p : Oscillator D => embed D p)
  simp only [chargePolynomial, Pi.zero_apply, Int.cast_zero, zero_smul, Finset.sum_const_zero,
    zero_mul, add_zero, oscillatorDerivation, Derivation.leibniz, MvPolynomial.mkDerivation_X,
    smul_eq_mul, mul_smul_comm]
  rw [← add_smul, ← two_mul]

private theorem translated_current (D : LatticeData) (i : Fin D.rank) :
    translation D (currentState D i) = embed D (x D i 1) := by
  simp [currentState, oscillatorDerivation, chargePolynomial]

private theorem positive_on_second_square (D : LatticeData) (i j : Fin D.rank) (n : ℕ) :
    mu D (currentState D j) n (neutralPair D i i 1 1).val =
      if n = 2 then (4 * gram D j i) • embed D (x D i 1) else 0 := by
  cases n with
  | zero =>
    rw [ite_eq_right (by decide : (0 : ℕ) ≠ 2)]
    change ((Y D (currentState D j))[[0]]) (Finsupp.single 0 (x D i 1 * x D i 1)) = _
    rw [current_state_field, neutralField_ncoeff, neutralMode_single]
    simp [neutralPolynomialMode, bilinear]
  | succ k =>
    change ((Y D (currentState D j))[[((k : ℤ) + 1)]])
      (Finsupp.single 0 (x D i 1 * x D i 1)) = _
    rw [current_state_field, neutralField_ncoeff, neutralMode_single,
      neutralPolynomialMode_positive, LinearMap.smul_apply]
    change embed D ((k + 1 : ℂ) • annihilate D j k (x D i 1 * x D i 1)) = _
    simp only [annihilate_mul, annihilate_X]
    by_cases hk : k = 1
    · subst k
      norm_num [map_smul, smul_mul_assoc, mul_smul_comm, ← add_smul, smul_smul]
      exact congrArg (fun c : ℂ => Finsupp.single (0 : Charge D) (c • x D i 1))
        (by unfold gram; ring)
    · rw [ite_eq_right hk, ite_eq_right (show k + 1 ≠ 2 by omega)]
      simp

private theorem mode_commute_basic (D : LatticeData) (i j : Fin D.rank) (a : ℕ)
    (v : Carrier D) :
    mu D (neutralPair D i i 0 0).val (-2) (create D j a v) =
      create D j a (mu D (neutralPair D i i 0 0).val (-2) v) +
        (2 * (a + 1) * gram D i j) • create D i (a + 3) v := by
  have h := LinearMap.congr_fun
    (quadraticSummand_current_commutator D i i j (-3) (-(a : ℤ) - 1)) v
  have hf : Y D (neutralPair D i i 0 0).val = quadraticSummand D i i :=
    quadratic_state_field D i i
  simp only [mu, hf]
  have hm : (-3 : ℤ) + (-(a : ℤ) - 1) = -((a + 3 : ℕ) : ℤ) - 1 := by
    push_cast; ring
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.add_apply, show (-3 : ℤ) + 1 = -2 by norm_num, hm,
    Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_sub, sub_neg_eq_add] at h
  have h' := sub_eq_iff_eq_add.mp h
  change ((quadraticSummand D i i)[[-2]]) (neutralMode D j (-(a : ℤ) - 1) v) = _
  rw [h']
  unfold create
  module

private theorem mode_commute_second (D : LatticeData) (i j : Fin D.rank) (a : ℕ)
    (v : Carrier D) :
    mu D (neutralPair D i i 1 1).val (-2) (create D j a v) =
      create D j a (mu D (neutralPair D i i 1 1).val (-2) v) +
        (-(4 * gram D j i * integerBinomial (-(a : ℤ) - 1) 2 * (a + 5))) •
          create D i (a + 5) v := by
  let q : ℤ := -(a : ℤ) - 1
  let A := (neutralPair D i i 1 1).val
  have hc := mode_commutator D (currentState D j) A q (-2)
  rw [finsum_eq_single _ 2] at hc
  · simp only [commutatorTerm, A, positive_on_second_square, ite_true] at hc
    rw [← translated_current D i, current_state_field D j] at hc
    have hd := state_derivative_modes D (currentState D i) (q + -2 - (2 : ℕ))
    rw [current_state_field] at hd
    rw [map_smul] at hc
    change _ = integerBinomial q 2 • ((4 * gram D j i) •
      ((Y D (translation D (currentState D i)))[[q + -2 - (2 : ℕ)]])) at hc
    rw [hd] at hc
    have h := LinearMap.congr_fun hc v
    have hq : q + -2 - ((2 : ℕ) : ℤ) - 1 = -((a + 5 : ℕ) : ℤ) - 1 := by
      dsimp [q]
      ring
    have hs : -((q + -2 - ((2 : ℕ) : ℤ) : ℤ) : ℂ) = (a + 5 : ℂ) := by
      dsimp [q]
      push_cast
      ring
    simp only [neutralField_ncoeff, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, hq, hs, smul_smul] at h
    change create D j a (mu D A (-2) v) -
      mu D A (-2) (create D j a v) = _ at h
    calc
      _ = create D j a (mu D A (-2) v) -
          (create D j a (mu D A (-2) v) - mu D A (-2) (create D j a v)) := by
        abel
      _ = _ := by
        rw [h]
        unfold create
        dsimp [q]
        module
  · intro n hn
    rw [commutatorTerm]
    change _ • ((Y D (mu D (currentState D j) n (neutralPair D i i 1 1).val))[[q + -2 - n]]) = _
    simp [positive_on_second_square, hn]

private theorem two_mode_expansion (D : LatticeData) (i j : Fin D.rank)
    (A : FixedCarrier D) (s t : ℕ) (c₁ c₂ : ℂ) (p : Oscillator D)
    (hv : mu D A.val (-2) (vacuum D) = embed D p)
    (hcomm₁ : ∀ a v, mu D A.val (-2) (create D i a v) =
      create D i a (mu D A.val (-2) v) + (c₁ * integerBinomial (-(a : ℤ) - 1) 2 *
        (a + 5)) • create D i (a + 5) v)
    (hcomm₂ : ∀ a v, mu D A.val (-2) (create D j a v) =
      create D j a (mu D A.val (-2) v) + (c₂ * integerBinomial (-(a : ℤ) - 1) 2 *
        (a + 5)) • create D i (a + 5) v) :
    mu D A.val (-2) (neutralPair D i j s t).val =
      embed D (x D i s * (x D j t * p)) +
      (c₂ * integerBinomial (-(t : ℤ) - 1) 2 * (t + 5)) • (neutralPair D i i s (t + 5)).val +
      (c₁ * integerBinomial (-(s : ℤ) - 1) 2 * (s + 5)) • (neutralPair D i j (s + 5) t).val := by
  have h : (neutralPair D i j s t).val = create D i s (create D j t (vacuum D)) := by
    change embed D (x D i s * x D j t) = create D i s (create D j t (embed D 1))
    rw [create_embed, create_embed, mul_one]
  rw [h, hcomm₁, hcomm₂, hv]
  simp only [map_add, map_smul, show vacuum D = embed D 1 from rfl,
    create_embed, mul_one, neutralPair]
  rfl

private theorem basic_expansion (D : LatticeData) (i j : Fin D.rank) (b : ℕ) :
    mu D (neutralPair D i i 0 0).val (-2) (neutralPair D i j 2 b).val =
      (2 : ℂ) • embed D (x D i 2 * (x D j b * (x D i 0 * x D i 1))) +
      (2 * (b + 1) * gram D i j) • (neutralPair D i i 2 (b + 3)).val +
      (6 * gram D i i) • (neutralPair D i j 5 b).val := by
  have h : (neutralPair D i j 2 b).val = create D i 2 (create D j b (vacuum D)) := by
    change embed D (x D i 2 * x D j b) = create D i 2 (create D j b (embed D 1))
    rw [create_embed, create_embed, mul_one]
  rw [h, mode_commute_basic D i i, mode_commute_basic D i j]
  have hv := translate_pair D i 0
  rw [translation_as_mode] at hv
  change mu D (neutralPair D i i 0 0).val (-2) (vacuum D) = _ at hv
  rw [hv]
  simp only [Nat.cast_zero, zero_add, mul_one, map_add, map_smul]
  change _ = _
  simp only [show vacuum D = embed D 1 from rfl, create_embed, mul_one, neutralPair]
  norm_num

private theorem second_expansion (D : LatticeData) (i j : Fin D.rank) (b : ℕ) :
    mu D (neutralPair D i i 1 1).val (-2) (neutralPair D i j 0 b).val =
      (4 : ℂ) • embed D (x D i 0 * (x D j b * (x D i 1 * x D i 2))) +
      (-(4 * gram D j i) * integerBinomial (-(b : ℤ) - 1) 2 * (b + 5)) •
        (neutralPair D i i 0 (b + 5)).val +
      (-(20 * gram D i i)) • (neutralPair D i j 5 b).val := by
  have hv := translate_pair D i 1
  rw [translation_as_mode] at hv
  change mu D (neutralPair D i i 1 1).val (-2) (vacuum D) = _ at hv
  have hv' : mu D (neutralPair D i i 1 1).val (-2) (vacuum D) =
      embed D ((4 : ℂ) • (x D i 1 * x D i 2)) := by
    rw [hv, map_smul]
    norm_num
  rw [two_mode_expansion D i j _ 0 b (-(4 * gram D i i)) (-(4 * gram D j i)) _ hv']
  · simp only [mul_smul_comm, map_smul]
    have hb : integerBinomial (-1) 2 = 1 := by
      have h := minus_one_binomial 2
      norm_num at h
      exact h
    rw [show -(↑(0 : ℕ) : ℤ) - 1 = -1 by norm_num, hb]
    simp only [Nat.cast_zero, zero_add, mul_one]
    module
  · intro a v
    rw [mode_commute_second]
    module
  · intro a v
    rw [mode_commute_second]
    module

/-- Twice the `(-2)` product of `X (i, 0)^2` with `X (i, 2) X (j, b)`,
minus the `(-2)` product of `X (i, 1)^2` with `X (i, 0) X (j, b)`,
cancels the four-oscillator terms and gives the following relation in the fixed quotient. -/
theorem fixed_quadratic_cancellation (D : LatticeData) (i j : Fin D.rank) (b : ℕ) :
    (32 * (D.G i i : ℂ)) • pairClass D i j 5 b +
      (4 * (D.G j i : ℂ) * integerBinomial (-(b : ℤ) - 1) 2 * (b + 5)) •
        pairClass D i i 0 (b + 5) +
      (4 * (b + 1) * (D.G i j : ℂ)) • pairClass D i i 2 (b + 3) = 0 := by
  let P := fixedMode D (neutralPair D i i 0 0) (-2) (neutralPair D i j 2 b)
  let Q := fixedMode D (neutralPair D i i 1 1) (-2) (neutralPair D i j 0 b)
  have hP : P ∈ fixedC2 D := Submodule.subset_span ⟨_, _, rfl⟩
  have hQ : Q ∈ fixedC2 D := Submodule.subset_span ⟨_, _, rfl⟩
  have hm := (fixedC2 D).sub_mem ((fixedC2 D).smul_mem (2 : ℂ) hP) hQ
  have he : (2 : ℂ) • P - Q =
      (32 * gram D i i) • neutralPair D i j 5 b +
        (4 * gram D j i * integerBinomial (-(b : ℤ) - 1) 2 * (b + 5)) •
          neutralPair D i i 0 (b + 5) +
        (4 * (b + 1) * gram D i j) • neutralPair D i i 2 (b + 3) := by
    apply Subtype.ext
    change (2 : ℂ) • mu D (neutralPair D i i 0 0).val (-2) (neutralPair D i j 2 b).val -
      mu D (neutralPair D i i 1 1).val (-2) (neutralPair D i j 0 b).val = _
    rw [basic_expansion, second_expansion]
    have hmul : x D i 2 * (x D j b * (x D i 0 * x D i 1)) =
        x D i 0 * (x D j b * (x D i 1 * x D i 2)) := by ac_rfl
    rw [hmul]
    change _ =
      (32 * gram D i i) • (neutralPair D i j 5 b).val +
      (4 * gram D j i * integerBinomial (-(b : ℤ) - 1) 2 * (b + 5)) •
        (neutralPair D i i 0 (b + 5)).val +
      (4 * (b + 1) * gram D i j) • (neutralPair D i i 2 (b + 3)).val
    module
  have hz : (fixedC2 D).mkQ ((2 : ℂ) • P - Q) = 0 :=
    (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr hm
  simpa only [he, map_add, map_smul] using hz

private theorem choose_five (b : ℕ) :
    ((b + 5).choose 5 : ℂ) = (b + 5) * (b + 4) * (b + 3) * (b + 2) * (b + 1) / 120 := by
  rw [Nat.cast_choose ℂ (by omega : 5 ≤ b + 5), show b + 5 - 5 = b by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hb : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero b)
  field_simp
  ring

private theorem negative_choose_two (b : ℕ) :
    integerBinomial (-(b : ℤ) - 1) 2 = (b + 2) * (b + 1) / 2 := by
  unfold integerBinomial
  rw [show -(b : ℤ) - 1 = -((b : ℤ) + 1) by ring, Ring.choose_neg]
  norm_num
  rw [show (b : ℤ) + 1 + 2 - 1 = ((b + 2 : ℕ) : ℤ) by push_cast; ring,
    Ring.choose_natCast, Int.negOnePow_even 2 even_two, one_smul, Int.cast_natCast, Nat.cast_choose_two]
  push_cast
  ring

/-- Fixed quadratic modes eliminate every same-colour neutral pair past index sum six. -/
theorem diagonal_pair_class_high (D : LatticeData) (i : Fin D.rank) (a b : ℕ)
    (hi : D.G i i ≠ 0) (hab : 7 ≤ a + b) : pairClass D i i a b = 0 := by
  rw [pair_class_normalize]
  suffices hh : pairClass D i i 0 (a + b) = 0 by rw [hh, smul_zero]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a + b = n + 5 := ⟨a + b - 5, by omega⟩
  rw [hn]
  have h := fixed_quadratic_cancellation D i i n
  rw [pair_class_normalize D i i 5 n, pair_class_normalize D i i 2 (n + 3),
    show 5 + n = n + 5 by omega, show 2 + (n + 3) = n+5 by omega,
    choose_five, Nat.cast_choose_two, negative_choose_two] at h
  push_cast at h
  norm_num only [show (-1 : ℂ) ^ 5 = -1 by norm_num, show (-1 : ℂ) ^ 2 = 1 by norm_num,
    one_mul, neg_one_mul] at h
  rw [smul_smul, smul_smul, ← add_smul, ← add_smul] at h
  have hc : (32 * gram D i i) *
        (-((n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) / 120)) +
      4 * gram D i i * ((n + 2) * (n + 1) / 2) * (n + 5) +
      4 * (n + 1) * gram D i i * ((n + 5) * ((n + 5) - 1) / 2) =
      -(4 / 15 : ℂ) * gram D i i * (n + 5) * (n + 1) * (n + 3) * (n + 7) * (n - 1) := by ring
  rw [hc] at h
  apply (smul_eq_zero.mp h).resolve_left
  have hn5 : (n + 5 : ℂ) ≠ 0 := by exact_mod_cast (show n + 5 ≠ 0 by omega)
  have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hn3 : (n + 3 : ℂ) ≠ 0 := by exact_mod_cast (show n + 3 ≠ 0 by omega)
  have hn7 : (n + 7 : ℂ) ≠ 0 := by exact_mod_cast (show n + 7 ≠ 0 by omega)
  have hnsub : (n - 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 1 by omega))
  simp [gram, hi, hn5, hn1, hn3, hn7, hnsub]


/-- Every charge-zero two-oscillator class of index sum at least seven vanishes. -/
theorem neutral_pair_class_high (D : LatticeData) (i j : Fin D.rank) (a b : ℕ)
    (hi : D.G i i ≠ 0) (hab : 7 ≤ a + b) : pairClass D i j a b = 0 := by
  rw [pair_class_normalize]
  suffices hz : pairClass D i j 0 (a + b) = 0 by rw [hz, smul_zero]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a + b = n + 5 := ⟨a + b - 5, by omega⟩
  rw [hn]
  have hc := fixed_quadratic_cancellation D i j n
  rw [diagonal_pair_class_high D i 0 (n + 5) hi (by omega),
    diagonal_pair_class_high D i 2 (n + 3) hi (by omega),
    smul_zero, smul_zero, add_zero, add_zero,
    pair_class_normalize D i j 5 n, show 5 + n = n + 5 by omega,
    smul_smul] at hc
  have hg : (D.G i i : ℂ) ≠ 0 := by exact_mod_cast hi
  have hchoose : ((n + 5).choose 5 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 5 ≤ n + 5)).ne'
  exact (smul_eq_zero.mp hc).resolve_left (by
    change 32 * (D.G i i : ℂ) * (((-1 : ℂ) ^ 5) * ((n + 5).choose 5 : ℂ)) ≠ 0
    simp [hg, hchoose])

/-- A positive-definite Gram matrix has nonzero diagonal in the given lattice basis. -/
theorem gram_diagonal_ne (D : LatticeData)
    (hD : (D.G.map (Int.cast : ℤ → ℝ)).PosDef) (i : Fin D.rank) :
    D.G i i ≠ 0 := by
  classical
  have hh := hD.2 (x := Finsupp.single i (1 : ℝ)) (Finsupp.single_ne_zero.mpr one_ne_zero)
  exact_mod_cast (show (D.G i i : ℝ) ≠ 0 from ne_of_gt (by simpa using hh))

end

end D5.S3.VertexAlgebra.Lattice.ActualFixedC2

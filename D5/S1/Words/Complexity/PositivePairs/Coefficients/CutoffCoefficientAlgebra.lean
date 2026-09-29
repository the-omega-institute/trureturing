/- GID: D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite cutoff word coefficients form a truncated multiplicative algebra. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra

open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.VivionBinomialConverseFails

variable {A : Type*}

abbrev RationalWordPolynomial (A : Type*) := MonoidAlgebra ℚ (FreeMonoid A)

/-- Coefficientwise extension of the integral word algebra to `ℚ`. -/
noncomputable def toRationalWordPolynomial :
    WordPolynomial A →+* RationalWordPolynomial A :=
  MonoidAlgebra.mapRingHom (FreeMonoid A) (Int.castRingHom ℚ)

/-- Words visible through filtration degree `r`. -/
abbrev CutoffWord (A : Type*) (r : ℕ) :=
  {w : FreeMonoid A // FreeMonoid.length w ≤ r}

/-- The finite coefficient carrier at degree at most `r`. -/
abbrev CutoffCoefficients (A : Type*) (r : ℕ) := CutoffWord A r → ℚ

/-- Restriction of a rational word polynomial to degrees at most `r`. -/
def cutoffRestriction (r : ℕ) (p : RationalWordPolynomial A) :
    CutoffCoefficients A r :=
  fun w => p.coeff w.1

/-- Extend bounded coefficients by zero to the full word algebra. -/
noncomputable def cutoffLift [Finite A] (r : ℕ) (p : CutoffCoefficients A r) :
    RationalWordPolynomial A := by
  letI : Fintype (CutoffWord A r) :=
    Set.Finite.fintype (List.finite_length_le A r)
  exact MonoidAlgebra.ofCoeff <|
    Finsupp.mapDomain (fun w : CutoffWord A r => w.1)
      (Finsupp.equivFunOnFinite.symm p)

/-- Split convolution over every cut of the target word. -/
def cutoffMul (r : ℕ) (p q : CutoffCoefficients A r) :
    CutoffCoefficients A r :=
  fun w =>
    ∑ i ∈ Finset.range (FreeMonoid.length w.1 + 1),
      p ⟨FreeMonoid.ofList ((FreeMonoid.toList w.1).take i), by
          change (List.take i (FreeMonoid.toList w.1)).length ≤ r
          rw [List.length_take]
          exact (Nat.min_le_right _ _).trans w.2⟩ *
        q ⟨FreeMonoid.ofList ((FreeMonoid.toList w.1).drop i), by
          change (List.drop i (FreeMonoid.toList w.1)).length ≤ r
          rw [List.length_drop]
          have hw : (FreeMonoid.toList w.1).length ≤ r := by
            simpa [FreeMonoid.length] using w.2
          exact (Nat.sub_le _ _).trans hw⟩

/-- The empty-word coefficient vector. -/
noncomputable def cutoffOne (r : ℕ) : CutoffCoefficients A r :=
  cutoffRestriction r 1

private noncomputable def wordSplits (w : FreeMonoid A) :
    Finset (FreeMonoid A × FreeMonoid A) := by
  classical
  exact (Finset.range (FreeMonoid.length w + 1)).image fun i =>
    (FreeMonoid.ofList ((FreeMonoid.toList w).take i),
      FreeMonoid.ofList ((FreeMonoid.toList w).drop i))

private theorem mem_wordSplits_iff
    (w : FreeMonoid A) (pair : FreeMonoid A × FreeMonoid A) :
    pair ∈ wordSplits w ↔ pair.1 * pair.2 = w := by
  classical
  change pair ∈ (Finset.range (FreeMonoid.length w + 1)).image
      (fun i =>
        (FreeMonoid.ofList ((FreeMonoid.toList w).take i),
          FreeMonoid.ofList ((FreeMonoid.toList w).drop i))) ↔ _
  constructor
  · intro hpair
    rcases Finset.mem_image.mp hpair with ⟨i, _, rfl⟩
    apply FreeMonoid.toList.injective
    simp [List.take_append_drop]
  · intro hpair
    apply Finset.mem_image.mpr
    refine ⟨FreeMonoid.length pair.1, ?_, ?_⟩
    · rw [Finset.mem_range, ← hpair, FreeMonoid.length_mul]
      omega
    · apply Prod.ext
      · apply FreeMonoid.toList.injective
        have hlist := congrArg FreeMonoid.toList hpair
        simpa [FreeMonoid.toList_mul, FreeMonoid.length,
          List.take_append_of_le_length] using
          congrArg (List.take (FreeMonoid.length pair.1)) hlist.symm
      · apply FreeMonoid.toList.injective
        have hlist := congrArg FreeMonoid.toList hpair
        simpa [FreeMonoid.toList_mul, FreeMonoid.length,
          List.drop_append_of_le_length] using
          congrArg (List.drop (FreeMonoid.length pair.1)) hlist.symm

private theorem coeff_mul_eq_split_sum
    (p q : RationalWordPolynomial A) (w : FreeMonoid A) :
    (p * q).coeff w =
      ∑ i ∈ Finset.range (FreeMonoid.length w + 1),
        p.coeff (FreeMonoid.ofList ((FreeMonoid.toList w).take i)) *
          q.coeff (FreeMonoid.ofList ((FreeMonoid.toList w).drop i)) := by
  classical
  rw [MonoidAlgebra.coeff_mul_antidiag p q w (wordSplits w)
    (fun {pair} => mem_wordSplits_iff w pair)]
  rw [wordSplits, Finset.sum_image]
  intro i hi j hj hij
  have hi' : i ≤ FreeMonoid.length w := by
    have hi0 : i < FreeMonoid.length w + 1 := by simpa using hi
    omega
  have hj' : j ≤ FreeMonoid.length w := by
    have hj0 : j < FreeMonoid.length w + 1 := by simpa using hj
    omega
  have hi'' : i ≤ (FreeMonoid.toList w).length := by
    simpa [FreeMonoid.length] using hi'
  have hj'' : j ≤ (FreeMonoid.toList w).length := by
    simpa [FreeMonoid.length] using hj'
  have hlength := congrArg (fun pair : FreeMonoid A × FreeMonoid A =>
    FreeMonoid.length pair.1) hij
  simpa [FreeMonoid.length, List.length_take, Nat.min_eq_left hi'',
    Nat.min_eq_left hj''] using hlength

/-- Restriction to bounded word length genuinely preserves multiplication when
the target multiplication is the split convolution. -/
theorem cutoffRestriction_mul (r : ℕ)
    (p q : RationalWordPolynomial A) :
    cutoffRestriction r (p * q) =
      cutoffMul r (cutoffRestriction r p) (cutoffRestriction r q) := by
  funext w
  rw [cutoffRestriction, coeff_mul_eq_split_sum]
  rfl

/-- A cutoff coefficient vector has no terms below degree `d`. -/
def VanishesBelow (r d : ℕ) (p : CutoffCoefficients A r) : Prop :=
  ∀ w, FreeMonoid.length w.1 < d → p w = 0

/-- Filtration degrees add under the actual split convolution. -/
theorem cutoffMul_vanishesBelow (r d e : ℕ)
    (p q : CutoffCoefficients A r)
    (hp : VanishesBelow r d p) (hq : VanishesBelow r e q) :
    VanishesBelow r (d + e) (cutoffMul r p q) := by
  intro w hw
  apply Finset.sum_eq_zero
  intro i hi
  have hi_le : i ≤ FreeMonoid.length w.1 := by
    have : i < FreeMonoid.length w.1 + 1 := by simpa using hi
    omega
  have hi_list : i ≤ (FreeMonoid.toList w.1).length := by
    simpa [FreeMonoid.length] using hi_le
  by_cases hid : i < d
  · rw [hp _]
    · simp
    · simpa [FreeMonoid.length, List.length_take,
        Nat.min_eq_left hi_list] using hid
  · rw [hq _]
    · simp
    · change (List.drop i (FreeMonoid.toList w.1)).length < e
      rw [List.length_drop]
      have hw' : (FreeMonoid.toList w.1).length < d + e := by
        simpa [FreeMonoid.length] using hw
      omega

/-- Powers formed inside the finite cutoff algebra. -/
noncomputable def cutoffPow [Finite A] (r : ℕ)
    (p : CutoffCoefficients A r) : ℕ → CutoffCoefficients A r
  | 0 => cutoffOne r
  | n + 1 => cutoffMul r p (cutoffPow r p n)

/-- Cutoff powers are the actual bounded coefficients of powers in the full
word algebra. -/
theorem cutoffPow_eq_restriction_pow [Finite A] (r : ℕ)
    (p : CutoffCoefficients A r) :
    ∀ n, cutoffPow r p n = cutoffRestriction r ((cutoffLift r p) ^ n) := by
  intro n
  have hrestrict : cutoffRestriction r (cutoffLift r p) = p := by
    funext w
    simp [cutoffRestriction, cutoffLift,
      Finsupp.mapDomain_apply Subtype.val_injective]
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        cutoffPow r p (n + 1) =
            cutoffMul r p
              (cutoffRestriction r ((cutoffLift r p) ^ n)) := by
                rw [cutoffPow, ih]
        _ = cutoffMul r (cutoffRestriction r (cutoffLift r p))
              (cutoffRestriction r ((cutoffLift r p) ^ n)) := by
                exact congrArg
                  (fun x => cutoffMul r x
                    (cutoffRestriction r ((cutoffLift r p) ^ n)))
                  hrestrict.symm
        _ = cutoffRestriction r
              (cutoffLift r p * (cutoffLift r p) ^ n) :=
                (cutoffRestriction_mul r (cutoffLift r p)
                  ((cutoffLift r p) ^ n)).symm
        _ = cutoffRestriction r ((cutoffLift r p) ^ (n + 1)) := by
                rw [pow_succ']

/-- A positive-degree element gains one vanishing degree with each cutoff
power. -/
theorem cutoffPow_vanishesBelow [Finite A] (r : ℕ)
    (p : CutoffCoefficients A r) (hp : VanishesBelow r 1 p) :
    ∀ n, VanishesBelow r n (cutoffPow r p n) := by
  intro n
  induction n with
  | zero =>
      intro w hw
      omega
  | succ n ih =>
      simpa [cutoffPow, Nat.add_comm] using
        cutoffMul_vanishesBelow r 1 n p (cutoffPow r p n) hp ih

/-- The finite geometric series used to invert `1 + c` in the cutoff algebra. -/
noncomputable def cutoffGeometricInverse [Finite A] (r : ℕ)
    (c : CutoffCoefficients A r) : CutoffCoefficients A r :=
  cutoffRestriction r <|
    ∑ i ∈ Finset.range (r + 1), (cutoffLift r (-c)) ^ i

/-- A positive-degree perturbation of one has the displayed right inverse in
the finite word cutoff. -/
theorem cutoffMul_geometricInverse [Finite A] (r : ℕ)
    (c : CutoffCoefficients A r) (hc : VanishesBelow r 1 c) :
    cutoffMul r (cutoffOne r + c) (cutoffGeometricInverse r c) =
      cutoffOne r := by
  have hneg : VanishesBelow r 1 (-c) := by
    intro w hw
    simp [hc w hw]
  have hpow : cutoffPow r (-c) (r + 1) = 0 := by
    funext w
    apply cutoffPow_vanishesBelow r (-c) hneg (r + 1) w
    omega
  rw [cutoffPow_eq_restriction_pow] at hpow
  have hfactor : cutoffOne r + c =
      cutoffRestriction r (1 - cutoffLift r (-c)) := by
    funext w
    simp [cutoffOne, cutoffRestriction, cutoffLift,
      Finsupp.mapDomain_apply Subtype.val_injective]
  rw [hfactor, cutoffGeometricInverse, ← cutoffRestriction_mul,
    mul_neg_geom_sum]
  funext w
  have := congrFun hpow w
  simp [cutoffOne, cutoffRestriction] at this ⊢
  exact this

/-- The same finite geometric series is also a left inverse. -/
theorem geometricInverse_cutoffMul [Finite A] (r : ℕ)
    (c : CutoffCoefficients A r) (hc : VanishesBelow r 1 c) :
    cutoffMul r (cutoffGeometricInverse r c) (cutoffOne r + c) =
      cutoffOne r := by
  have hneg : VanishesBelow r 1 (-c) := by
    intro w hw
    simp [hc w hw]
  have hpow : cutoffPow r (-c) (r + 1) = 0 := by
    funext w
    apply cutoffPow_vanishesBelow r (-c) hneg (r + 1) w
    omega
  rw [cutoffPow_eq_restriction_pow] at hpow
  have hfactor : cutoffOne r + c =
      cutoffRestriction r (1 - cutoffLift r (-c)) := by
    funext w
    simp [cutoffOne, cutoffRestriction, cutoffLift,
      Finsupp.mapDomain_apply Subtype.val_injective]
  rw [hfactor, cutoffGeometricInverse, ← cutoffRestriction_mul,
    geom_sum_mul_neg]
  funext w
  have := congrFun hpow w
  simp [cutoffOne, cutoffRestriction] at this ⊢
  exact this


end D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra

/- GID: D5/S1/Words/Complexity/PositivePairWordCoefficients
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairWordCoefficients
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Full positive-pair Magnus coefficients are actual scattered-count differences. -/

import D5.S1.Words.Complexity.LyndonStandardBracket
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Positive-pair word coefficients

This is the first source-owned checkpoint on the direct rational word-algebra
route to Nilforoushan-Parvaresh Conjecture 8.1.  It keeps the entire recursively
generated family, including distinct indices that can evaluate to duplicate
pairs.  No nonzero leading coefficient is assumed.

The result connects three actual objects: products of `1 + X_a` in the word
algebra, the frozen scattered-subword counter, and coefficientwise restriction
to rational words of bounded degree.  It also proves the successor Magnus
difference and ratio leading-bracket identities.  Full-family spanning,
independent digit selection, power substitution, padding, and the source upper
bound are downstream obligations.
-/

namespace D5.S1.Words.Complexity.PositivePairWordCoefficients

open D5.S1.Words.Complexity.LyndonStandardBracket
open D5.S1.Words.Complexity.VivionBinomialConverseFails

variable {A : Type*}

/-- Rational noncommutative polynomials whose monomials are finite words. -/
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

/-- The actual Magnus polynomial `M(w) = ∏ (1 + X_a)`, in source order. -/
noncomputable def magnusPolynomial : List A → WordPolynomial A
  | [] => 1
  | a :: source =>
      (1 + wordMonomial [a]) * magnusPolynomial source

/-- The actual Magnus polynomial sends word concatenation to multiplication. -/
theorem magnusPolynomial_append (left right : List A) :
    magnusPolynomial (left ++ right) =
      magnusPolynomial left * magnusPolynomial right := by
  induction left with
  | nil => simp [magnusPolynomial]
  | cons a left ih =>
      simp only [List.cons_append, magnusPolynomial, ih, mul_assoc]

/-- The coefficient of a word in the actual Magnus polynomial is its frozen
scattered-subword count. -/
theorem magnusPolynomial_coeff_scatteredCount [DecidableEq A]
    (source pattern : List A) :
    (magnusPolynomial source).coeff (FreeMonoid.ofList pattern) =
      (scatteredCount pattern source : ℤ) := by
  classical
  have generator_mul_coeff (a : A) (p : WordPolynomial A) (pattern : List A) :
      (wordMonomial [a] * p).coeff (FreeMonoid.ofList pattern) =
        match pattern with
        | [] => 0
        | b :: tail => if b = a then p.coeff (FreeMonoid.ofList tail) else 0 := by
    cases pattern with
    | nil =>
        simp [wordMonomial, MonoidAlgebra.coeff_mul]
    | cons b tail =>
        by_cases h : b = a
        · subst b
          simp [wordMonomial]
        · simp only [if_neg h]
          rw [← Finsupp.notMem_support_iff]
          intro hmem
          have hproduct := MonoidAlgebra.support_coeff_mul_subset
            (wordMonomial [a]) p hmem
          rcases Finset.mem_mul.mp hproduct with ⟨left, hleft, right, _, heq⟩
          simp only [wordMonomial, MonoidAlgebra.coeff_single,
            Finsupp.support_single _ one_ne_zero,
            Finset.mem_singleton] at hleft
          subst left
          have lists := congrArg FreeMonoid.toList heq
          simp only [FreeMonoid.toList_mul, FreeMonoid.toList_ofList,
            List.singleton_append, List.cons.injEq] at lists
          exact h lists.1.symm
  induction source generalizing pattern with
  | nil =>
      cases pattern <;>
        simp [magnusPolynomial, scatteredCount, MonoidAlgebra.one_def]
  | cons a source ih =>
      rw [magnusPolynomial]
      simp only [add_mul, one_mul, MonoidAlgebra.coeff_add,
        Finsupp.add_apply, generator_mul_coeff]
      cases pattern with
      | nil => simpa [scatteredCount] using ih []
      | cons b tail =>
          change
            (magnusPolynomial source).coeff (FreeMonoid.ofList (b :: tail)) +
                (if b = a then
                  (magnusPolynomial source).coeff (FreeMonoid.ofList tail)
                else 0) =
              (scatteredCount (b :: tail) (a :: source) : ℤ)
          rw [ih (b :: tail)]
          by_cases h : b = a
          · subst b
            rw [ih tail]
            simp [scatteredCount]
          · simp [scatteredCount, h]

/-- The degree-one part of a word is its abelianized letter sum. -/
noncomputable def wordAbelianization : List A → WordPolynomial A
  | [] => 0
  | a :: source => wordMonomial [a] + wordAbelianization source

theorem wordAbelianization_append (left right : List A) :
    wordAbelianization (left ++ right) =
      wordAbelianization left + wordAbelianization right := by
  induction left with
  | nil => simp [wordAbelianization]
  | cons a left ih => simp [wordAbelianization, ih, add_assoc]

theorem wordAbelianization_coeff_singleton [DecidableEq A]
    (source : List A) (b : A) :
    (wordAbelianization source).coeff (FreeMonoid.ofList [b]) =
      (scatteredCount [b] source : ℤ) := by
  induction source with
  | nil => simp [wordAbelianization, scatteredCount]
  | cons a source ih =>
      rw [wordAbelianization, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]
      by_cases h : b = a
      · subst b
        simp [wordMonomial, scatteredCount, add_comm]
      · have hab : (FreeMonoid.of a : FreeMonoid A) ≠ FreeMonoid.of b := by
          intro hab
          have lists := congrArg FreeMonoid.toList hab
          exact h (by simpa using lists.symm)
        simp [wordMonomial, scatteredCount, h, hab]

theorem wordAbelianization_coeff_empty (source : List A) :
    (wordAbelianization source).coeff 1 = 0 := by
  induction source with
  | nil => simp [wordAbelianization]
  | cons a source ih =>
      have hne : (FreeMonoid.of a : FreeMonoid A) ≠ 1 := by
        intro h
        have lists := congrArg FreeMonoid.toList h
        simp at lists
      simp [wordAbelianization, wordMonomial, hne, ih]

/-- An index retains every recursive choice.  At level `r` it is a word of
`r` choices, so equal evaluated pairs are not identified. -/
abbrev PositivePairIndex (A : Type*) (r : ℕ) := Fin r → A

/-- Full recursively generated positive-pair family.  Level one is
`(a, [])`; every later level applies `(u,v,a) ↦ (uav,vau)`. -/
def positivePairWords : (r : ℕ) → PositivePairIndex A r → List A × List A
  | 0, _ => ([], [])
  | 1, index => ([index 0], [])
  | r + 2, index =>
      let previous := positivePairWords (r + 1) (Fin.init index)
      let a := index (Fin.last (r + 1))
      (previous.1 ++ [a] ++ previous.2,
        previous.2 ++ [a] ++ previous.1)

/-- The actual Magnus polynomial, restricted to the finite word cutoff. -/
noncomputable def cutoffMagnus [Finite A] (r : ℕ) (source : List A) :
    CutoffCoefficients A r :=
  cutoffRestriction r (toRationalWordPolynomial (magnusPolynomial source))

/-- The level-`r` full-family ratio `M(u) M(v)⁻¹`, observed through an
independent word cutoff.  The independent cutoff lets a level participate in
the construction of its successor without changing carriers. -/
noncomputable def positivePairRatio [Finite A] (cutoff r : ℕ)
    (index : PositivePairIndex A r) : CutoffCoefficients A cutoff :=
  let pair := positivePairWords r index
  cutoffMul cutoff (cutoffMagnus cutoff pair.1)
    (cutoffGeometricInverse cutoff
      (cutoffMagnus cutoff pair.2 - cutoffOne cutoff))

/-- Every recursively generated pair agrees below its level, and its actual
cutoff Magnus ratio consequently differs from one only in that level and
above.  The recursion retains the full indexed family, including duplicate
pairs and zero leading directions. -/
theorem full_positivePair_ratio_filtration [Finite A]
    (cutoff r : ℕ) (index : PositivePairIndex A r) :
    VanishesBelow cutoff r
        (cutoffMagnus cutoff (positivePairWords r index).1 -
          cutoffMagnus cutoff (positivePairWords r index).2) ∧
      VanishesBelow cutoff r
        (positivePairRatio cutoff r index - cutoffOne cutoff) := by
  classical
  let rationalMagnus (source : List A) : RationalWordPolynomial A :=
    toRationalWordPolynomial (magnusPolynomial source)
  have rationalMagnus_append (left right : List A) :
      rationalMagnus (left ++ right) =
        rationalMagnus left * rationalMagnus right := by
    simp [rationalMagnus, magnusPolynomial_append]
  have constant_coeff (source : List A) :
      (rationalMagnus source).coeff 1 = 1 := by
    induction source with
    | nil => simp [rationalMagnus, magnusPolynomial]
    | cons a source ih =>
        rw [show rationalMagnus (a :: source) =
          rationalMagnus [a] * rationalMagnus source by
            simpa using rationalMagnus_append [a] source]
        rw [coeff_mul_eq_split_sum]
        have hne : (FreeMonoid.of a : FreeMonoid A) ≠ 1 := by
          intro h
          have := congrArg FreeMonoid.toList h
          simp at this
        have hletter : (rationalMagnus [a]).coeff 1 = 1 := by
          simp [rationalMagnus, magnusPolynomial, toRationalWordPolynomial,
            MonoidAlgebra.coeff_mapRingHom, wordMonomial, hne]
        simpa [FreeMonoid.length, hletter, ih]
  have minus_one_vanishes (cutoff : ℕ) (source : List A) :
      VanishesBelow cutoff 1
        (cutoffRestriction cutoff (rationalMagnus source - 1)) := by
    intro w hw
    have hlength : FreeMonoid.length w.1 = 0 := by omega
    have hword : w.1 = 1 := by
      apply FreeMonoid.toList.injective
      apply List.length_eq_zero_iff.mp
      simpa [FreeMonoid.length] using hlength
    simp [cutoffRestriction, hword, constant_coeff]
  have filtration : ∀ level (familyIndex : PositivePairIndex A level)
      (cutoff : ℕ),
      VanishesBelow cutoff level
        (cutoffRestriction cutoff
          (rationalMagnus (positivePairWords level familyIndex).1 -
            rationalMagnus (positivePairWords level familyIndex).2)) := by
    intro level
    induction level using Nat.twoStepInduction with
    | zero =>
        intro familyIndex cutoff w hw
        omega
    | one =>
        intro familyIndex cutoff
        simpa [positivePairWords, rationalMagnus, magnusPolynomial] using
          minus_one_vanishes cutoff [familyIndex 0]
    | more level ih0 ih1 =>
        intro familyIndex cutoff
        let previous := positivePairWords (level + 1) (Fin.init familyIndex)
        let a := familyIndex (Fin.last (level + 1))
        let difference := rationalMagnus previous.1 - rationalMagnus previous.2
        have hdifference : VanishesBelow cutoff (level + 1)
            (cutoffRestriction cutoff difference) := by
          simpa [difference, previous] using
            ih1 (Fin.init familyIndex) cutoff
        have hright : VanishesBelow cutoff 1
            (cutoffRestriction cutoff
              (rationalMagnus ([a] ++ previous.2) - 1)) :=
          minus_one_vanishes cutoff ([a] ++ previous.2)
        have hleft : VanishesBelow cutoff 1
            (cutoffRestriction cutoff
              (rationalMagnus (previous.2 ++ [a]) - 1)) :=
          minus_one_vanishes cutoff (previous.2 ++ [a])
        have hfirst := cutoffMul_vanishesBelow cutoff (level + 1) 1
          (cutoffRestriction cutoff difference)
          (cutoffRestriction cutoff
            (rationalMagnus ([a] ++ previous.2) - 1)) hdifference hright
        have hsecond := cutoffMul_vanishesBelow cutoff 1 (level + 1)
          (cutoffRestriction cutoff
            (rationalMagnus (previous.2 ++ [a]) - 1))
          (cutoffRestriction cutoff difference) hleft hdifference
        have hpolynomial :
            rationalMagnus (previous.1 ++ [a] ++ previous.2) -
                rationalMagnus (previous.2 ++ [a] ++ previous.1) =
              difference * (rationalMagnus ([a] ++ previous.2) - 1) -
                (rationalMagnus (previous.2 ++ [a]) - 1) * difference := by
          simp only [rationalMagnus_append]
          dsimp [difference]
          noncomm_ring
        rw [show positivePairWords (level + 2) familyIndex =
            (previous.1 ++ [a] ++ previous.2,
              previous.2 ++ [a] ++ previous.1) by
              simp [positivePairWords, previous, a],
          hpolynomial]
        rw [show cutoffRestriction cutoff
              (difference * (rationalMagnus ([a] ++ previous.2) - 1) -
                (rationalMagnus (previous.2 ++ [a]) - 1) * difference) =
            cutoffMul cutoff (cutoffRestriction cutoff difference)
                (cutoffRestriction cutoff
                  (rationalMagnus ([a] ++ previous.2) - 1)) -
              cutoffMul cutoff
                (cutoffRestriction cutoff
                  (rationalMagnus (previous.2 ++ [a]) - 1))
                (cutoffRestriction cutoff difference) by
              funext w
              rw [Pi.sub_apply, ← cutoffRestriction_mul,
                ← cutoffRestriction_mul]
              rfl]
        intro w hw
        rw [Pi.sub_apply, hfirst w (by omega), hsecond w (by omega), sub_zero]
  have hdifference := filtration r index cutoff
  have hdifference' : VanishesBelow cutoff r
      (cutoffMagnus cutoff (positivePairWords r index).1 -
        cutoffMagnus cutoff (positivePairWords r index).2) := by
    intro w hw
    simpa [cutoffMagnus, rationalMagnus, cutoffRestriction] using
      hdifference w hw
  refine ⟨?_, ?_⟩
  · exact hdifference'
  · let pair := positivePairWords r index
    let denominatorTail := cutoffMagnus cutoff pair.2 - cutoffOne cutoff
    let inverse := cutoffGeometricInverse cutoff denominatorTail
    have htail : VanishesBelow cutoff 1 denominatorTail := by
      intro w hw
      simpa [denominatorTail, cutoffMagnus, rationalMagnus, cutoffOne,
        cutoffRestriction] using minus_one_vanishes cutoff pair.2 w hw
    have hinverse : cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse =
        cutoffOne cutoff := by
      have hone : cutoffMagnus cutoff pair.2 =
          cutoffOne cutoff + denominatorTail := by
        simp [denominatorTail]
      rw [hone]
      exact cutoffMul_geometricInverse cutoff denominatorTail htail
    have hproduct :
        positivePairRatio cutoff r index - cutoffOne cutoff =
          cutoffMul cutoff
            (cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2)
            inverse := by
      change cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
          cutoffOne cutoff = _
      rw [show cutoffMul cutoff
              (cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2) inverse =
            cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
              cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse by
            funext w
            simp [cutoffMul, Finset.sum_sub_distrib, sub_mul],
        hinverse]
    rw [hproduct]
    exact cutoffMul_vanishesBelow cutoff r 0
      (cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2) inverse
      (by simpa [pair] using hdifference')
      (by intro w hw; omega)

/-- In the successor cutoff, the actual full-family Magnus difference is the
commutator of the preceding leading difference with `ab(v) + X_a`.  Terms of
degree at least two in the two Magnus tails land beyond the cutoff. -/
theorem full_positivePair_successor_leading_bracket [Finite A] [DecidableEq A]
    (r : ℕ) (index : PositivePairIndex A (r + 2)) :
    let previous := positivePairWords (r + 1) (Fin.init index)
    let a := index (Fin.last (r + 1))
    let c := cutoffMagnus (r + 2) previous.1 -
      cutoffMagnus (r + 2) previous.2
    let x := cutoffRestriction (r + 2) <|
      toRationalWordPolynomial
        (wordAbelianization previous.2 + wordMonomial [a])
    cutoffMagnus (r + 2) (positivePairWords (r + 2) index).1 -
        cutoffMagnus (r + 2) (positivePairWords (r + 2) index).2 =
      cutoffMul (r + 2) c x - cutoffMul (r + 2) x c := by
  classical
  let cutoff := r + 2
  let previous := positivePairWords (r + 1) (Fin.init index)
  let a := index (Fin.last (r + 1))
  let rationalMagnus (source : List A) : RationalWordPolynomial A :=
    toRationalWordPolynomial (magnusPolynomial source)
  let linear (source : List A) : CutoffCoefficients A cutoff :=
    cutoffRestriction cutoff (toRationalWordPolynomial (wordAbelianization source))
  let difference := cutoffMagnus cutoff previous.1 - cutoffMagnus cutoff previous.2
  let x := linear previous.2 + linear [a]
  have rationalMagnus_append (left right : List A) :
      rationalMagnus (left ++ right) =
        rationalMagnus left * rationalMagnus right := by
    simp [rationalMagnus, magnusPolynomial_append]
  have tail_vanishes (source : List A) :
      VanishesBelow cutoff 2
        (cutoffMagnus cutoff source - cutoffOne cutoff - linear source) := by
    intro w hw
    by_cases hzero : FreeMonoid.length w.1 = 0
    · have hword : w.1 = 1 := by
        apply FreeMonoid.toList.injective
        apply List.length_eq_zero_iff.mp
        simpa [FreeMonoid.length] using hzero
      have hm : (magnusPolynomial source).coeff 1 = 1 := by
        simpa only [FreeMonoid.ofList_nil, scatteredCount, Nat.cast_one] using
          magnusPolynomial_coeff_scatteredCount source []
      simp only [Pi.sub_apply, cutoffMagnus, cutoffOne, cutoffRestriction,
        linear, hword, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom]
      rw [hm, wordAbelianization_coeff_empty]
      norm_num
    · have hone : FreeMonoid.length w.1 = 1 := by omega
      obtain ⟨b, hlist⟩ := List.length_eq_one_iff.mp (by
        simpa [FreeMonoid.length] using hone)
      have hword : w.1 = FreeMonoid.ofList [b] := by
        apply FreeMonoid.toList.injective
        simpa using hlist
      have hm := magnusPolynomial_coeff_scatteredCount source [b]
      have ha := wordAbelianization_coeff_singleton source b
      have hletter : (FreeMonoid.of b : FreeMonoid A) =
          FreeMonoid.ofList [b] := rfl
      have hne : (FreeMonoid.of b : FreeMonoid A) ≠ 1 := by
        intro h
        have lists := congrArg FreeMonoid.toList h
        simp at lists
      simp only [Pi.sub_apply, cutoffMagnus, cutoffOne, cutoffRestriction,
        linear, hword, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom]
      rw [hm, ha]
      simp [MonoidAlgebra.one_def, ← hletter, hne]
  have hprevious : VanishesBelow cutoff (r + 1) difference := by
    simpa [cutoff, difference, previous] using
      (full_positivePair_ratio_filtration cutoff (r + 1)
        (Fin.init index)).1
  have hrightTail : VanishesBelow cutoff 2
      (cutoffRestriction cutoff
          (rationalMagnus ([a] ++ previous.2) - 1) - x) := by
    intro w hw
    have htail := tail_vanishes ([a] ++ previous.2) w hw
    simpa [cutoffMagnus, cutoffOne, rationalMagnus, linear, x,
      cutoffRestriction, wordAbelianization_append, wordAbelianization,
      add_comm, add_left_comm, add_assoc] using htail
  have hleftTail : VanishesBelow cutoff 2
      (cutoffRestriction cutoff
          (rationalMagnus (previous.2 ++ [a]) - 1) - x) := by
    intro w hw
    have htail := tail_vanishes (previous.2 ++ [a]) w hw
    simpa [cutoffMagnus, cutoffOne, rationalMagnus, linear, x, cutoffRestriction,
      wordAbelianization_append, wordAbelianization, add_comm,
      add_left_comm, add_assoc] using htail
  have hrightError := cutoffMul_vanishesBelow cutoff (r + 1) 2
    difference
    (cutoffRestriction cutoff
      (rationalMagnus ([a] ++ previous.2) - 1) - x)
    hprevious hrightTail
  have hleftError := cutoffMul_vanishesBelow cutoff 2 (r + 1)
    (cutoffRestriction cutoff
      (rationalMagnus (previous.2 ++ [a]) - 1) - x)
    difference hleftTail hprevious
  have hrightZero : cutoffMul cutoff difference
      (cutoffRestriction cutoff
        (rationalMagnus ([a] ++ previous.2) - 1) - x) = 0 := by
    funext w
    exact hrightError w (by have := w.2; omega)
  have hleftZero : cutoffMul cutoff
      (cutoffRestriction cutoff
        (rationalMagnus (previous.2 ++ [a]) - 1) - x)
      difference = 0 := by
    funext w
    exact hleftError w (by have := w.2; omega)
  have hrightMul : cutoffMul cutoff difference
      (cutoffRestriction cutoff
        (rationalMagnus ([a] ++ previous.2) - 1)) =
      cutoffMul cutoff difference x := by
    have hsub : cutoffMul cutoff difference
        (cutoffRestriction cutoff
          (rationalMagnus ([a] ++ previous.2) - 1) - x) =
        cutoffMul cutoff difference
            (cutoffRestriction cutoff
              (rationalMagnus ([a] ++ previous.2) - 1)) -
          cutoffMul cutoff difference x := by
      funext w
      simp [cutoffMul, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    rw [hsub] at hrightZero
    exact sub_eq_zero.mp hrightZero
  have hleftMul : cutoffMul cutoff
      (cutoffRestriction cutoff
        (rationalMagnus (previous.2 ++ [a]) - 1)) difference =
      cutoffMul cutoff x difference := by
    have hsub : cutoffMul cutoff
        (cutoffRestriction cutoff
          (rationalMagnus (previous.2 ++ [a]) - 1) - x) difference =
        cutoffMul cutoff
            (cutoffRestriction cutoff
              (rationalMagnus (previous.2 ++ [a]) - 1)) difference -
          cutoffMul cutoff x difference := by
      funext w
      simp [cutoffMul, Finset.sum_sub_distrib, sub_mul]
    rw [hsub] at hleftZero
    exact sub_eq_zero.mp hleftZero
  have hpolynomial :
      rationalMagnus (previous.1 ++ [a] ++ previous.2) -
          rationalMagnus (previous.2 ++ [a] ++ previous.1) =
        (rationalMagnus previous.1 - rationalMagnus previous.2) *
            (rationalMagnus ([a] ++ previous.2) - 1) -
          (rationalMagnus (previous.2 ++ [a]) - 1) *
            (rationalMagnus previous.1 - rationalMagnus previous.2) := by
    simp only [rationalMagnus_append]
    noncomm_ring
  have hdifferenceRestriction : difference = cutoffRestriction cutoff
      (rationalMagnus previous.1 - rationalMagnus previous.2) := by
    funext w
    rfl
  have hxRestriction : x = cutoffRestriction cutoff
      (toRationalWordPolynomial
        (wordAbelianization previous.2 + wordMonomial [a])) := by
    funext w
    simp [x, linear, cutoffRestriction, wordAbelianization]
  change cutoffMagnus cutoff (positivePairWords (r + 2) index).1 -
      cutoffMagnus cutoff (positivePairWords (r + 2) index).2 = _
  rw [show positivePairWords (r + 2) index =
      (previous.1 ++ [a] ++ previous.2,
        previous.2 ++ [a] ++ previous.1) by
      simp [positivePairWords, previous, a], cutoffMagnus]
  change cutoffRestriction cutoff
      (rationalMagnus (previous.1 ++ [a] ++ previous.2) -
        rationalMagnus (previous.2 ++ [a] ++ previous.1)) = _
  rw [hpolynomial]
  rw [show cutoffRestriction cutoff
        ((rationalMagnus previous.1 - rationalMagnus previous.2) *
            (rationalMagnus ([a] ++ previous.2) - 1) -
          (rationalMagnus (previous.2 ++ [a]) - 1) *
            (rationalMagnus previous.1 - rationalMagnus previous.2)) =
      cutoffMul cutoff difference
          (cutoffRestriction cutoff
            (rationalMagnus ([a] ++ previous.2) - 1)) -
        cutoffMul cutoff
          (cutoffRestriction cutoff
            (rationalMagnus (previous.2 ++ [a]) - 1)) difference by
      funext w
      rw [hdifferenceRestriction]
      rw [Pi.sub_apply, ← cutoffRestriction_mul, ← cutoffRestriction_mul]
      rfl,
    hrightMul, hleftMul]
  rw [hxRestriction]

/-- The finite inverse has constant coefficient one, so the preceding
commutator is also the actual leading term of the successor ratio. -/
theorem full_positivePair_successor_ratio_leading_bracket
    [Finite A] [DecidableEq A]
    (r : ℕ) (index : PositivePairIndex A (r + 2)) :
    let previous := positivePairWords (r + 1) (Fin.init index)
    let a := index (Fin.last (r + 1))
    let c := cutoffMagnus (r + 2) previous.1 -
      cutoffMagnus (r + 2) previous.2
    let x := cutoffRestriction (r + 2) <|
      toRationalWordPolynomial
        (wordAbelianization previous.2 + wordMonomial [a])
    positivePairRatio (r + 2) (r + 2) index - cutoffOne (r + 2) =
      cutoffMul (r + 2) c x - cutoffMul (r + 2) x c := by
  classical
  let cutoff := r + 2
  let pair := positivePairWords cutoff index
  let difference := cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2
  let tail := cutoffMagnus cutoff pair.2 - cutoffOne cutoff
  let inverse := cutoffGeometricInverse cutoff tail
  have htail : VanishesBelow cutoff 1 tail := by
    intro w hw
    have hlength : FreeMonoid.length w.1 = 0 := by omega
    have hword : w.1 = 1 := by
      apply FreeMonoid.toList.injective
      apply List.length_eq_zero_iff.mp
      simpa [FreeMonoid.length] using hlength
    have hm : (magnusPolynomial pair.2).coeff 1 = 1 := by
      simpa only [FreeMonoid.ofList_nil, scatteredCount, Nat.cast_one] using
        magnusPolynomial_coeff_scatteredCount pair.2 []
    simp [tail, cutoffMagnus, cutoffOne, cutoffRestriction, hword,
      toRationalWordPolynomial, hm]
  have hinverse : cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse =
      cutoffOne cutoff := by
    have hone : cutoffMagnus cutoff pair.2 = cutoffOne cutoff + tail := by
      simp [tail]
    rw [hone]
    exact cutoffMul_geometricInverse cutoff tail htail
  let emptyWord : CutoffWord A cutoff := ⟨1, by simp⟩
  have hinverseConstant : inverse emptyWord = 1 := by
    have hi := congrFun hinverse emptyWord
    have hm : (magnusPolynomial pair.2).coeff 1 = 1 := by
      simpa only [FreeMonoid.ofList_nil, scatteredCount, Nat.cast_one] using
        magnusPolynomial_coeff_scatteredCount pair.2 []
    simpa [cutoffMul, emptyWord, cutoffMagnus, cutoffOne,
      cutoffRestriction, toRationalWordPolynomial, hm] using hi
  have hdifference : VanishesBelow cutoff cutoff difference := by
    simpa [difference, pair] using
      (full_positivePair_ratio_filtration cutoff cutoff index).1
  have hmul : cutoffMul cutoff difference inverse = difference := by
    funext w
    rw [cutoffMul, Finset.sum_eq_single (FreeMonoid.length w.1)]
    · simp only [FreeMonoid.length, List.take_length, List.drop_length,
        FreeMonoid.ofList_toList]
      change difference w * inverse emptyWord = difference w
      rw [hinverseConstant, mul_one]
    · intro i hi hne
      have hi_le : i ≤ FreeMonoid.length w.1 := by
        simpa [Finset.mem_range] using hi
      have hi_lt : i < FreeMonoid.length w.1 := lt_of_le_of_ne hi_le hne
      rw [hdifference]
      · simp
      · simp only [FreeMonoid.length, FreeMonoid.toList_ofList,
          List.length_take]
        have hw := w.2
        omega
    · simp
  have hproduct : positivePairRatio cutoff cutoff index - cutoffOne cutoff =
      cutoffMul cutoff difference inverse := by
    change cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
        cutoffOne cutoff = _
    rw [show cutoffMul cutoff difference inverse =
        cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
          cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse by
        funext w
        simp [difference, cutoffMul, Finset.sum_sub_distrib, sub_mul],
      hinverse]
  rw [hproduct, hmul]
  simpa [cutoff, pair, difference] using
    full_positivePair_successor_leading_bracket r index

/-- The first vertical checkpoint: every full-family pair after level one is
made of equally long positive words, and after genuine coefficientwise
`ℤ → ℚ` extension and cutoff restriction, its Magnus difference is exactly
the difference of the frozen scattered-subword counts. -/
theorem full_positivePair_coefficient_checkpoint [Finite A] [DecidableEq A]
    (r : ℕ) (index : PositivePairIndex A r) :
    (2 ≤ r →
      (positivePairWords r index).1 ≠ [] ∧
      (positivePairWords r index).2 ≠ [] ∧
      (positivePairWords r index).1.length =
        (positivePairWords r index).2.length) ∧
    ∀ pattern : CutoffWord A r,
      cutoffRestriction r
          (toRationalWordPolynomial
            (magnusPolynomial (positivePairWords r index).1 -
              magnusPolynomial (positivePairWords r index).2)) pattern =
        (scatteredCount (FreeMonoid.toList pattern.1)
              (positivePairWords r index).1 : ℚ) -
          (scatteredCount (FreeMonoid.toList pattern.1)
              (positivePairWords r index).2 : ℚ) := by
  classical
  constructor
  · intro hr
    obtain ⟨level, rfl⟩ : ∃ level, r = level + 2 := ⟨r - 2, by omega⟩
    simp only [positivePairWords]
    let previous := positivePairWords (level + 1) (Fin.init index)
    let a := index (Fin.last (level + 1))
    change
      previous.1 ++ [a] ++ previous.2 ≠ [] ∧
      previous.2 ++ [a] ++ previous.1 ≠ [] ∧
      (previous.1 ++ [a] ++ previous.2).length =
        (previous.2 ++ [a] ++ previous.1).length
    simp only [List.length_append, List.length_singleton]
    exact ⟨by simp, by simp, by omega⟩
  · intro pattern
    change
      (toRationalWordPolynomial
        (magnusPolynomial (positivePairWords r index).1 -
          magnusPolynomial (positivePairWords r index).2)).coeff pattern.1 = _
    simp only [toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom,
      map_sub, MonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    rw [show pattern.1 = FreeMonoid.ofList (FreeMonoid.toList pattern.1) by
      exact (FreeMonoid.ofList_toList pattern.1).symm,
      magnusPolynomial_coeff_scatteredCount,
      magnusPolynomial_coeff_scatteredCount]
    norm_num

#print axioms full_positivePair_coefficient_checkpoint
#print axioms full_positivePair_ratio_filtration
#print axioms full_positivePair_successor_leading_bracket
#print axioms full_positivePair_successor_ratio_leading_bracket
#print axioms cutoffMul_geometricInverse
#print axioms geometricInverse_cutoffMul

end D5.S1.Words.Complexity.PositivePairWordCoefficients

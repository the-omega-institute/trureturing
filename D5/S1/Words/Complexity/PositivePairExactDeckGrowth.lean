/- GID: D5/S1/Words/Complexity/PositivePairExactDeckGrowth
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairExactDeckGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact k-decks of fixed-length positive words have the predicted lower exponent. -/
import D5.S1.Words.Complexity.PositivePairBallGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Actual exact-k-deck growth

The exact length-`k` scattered-subword deck of a length-`n` word recovers every
shorter scattered-subword count when `k ≤ n`.  Padding representatives of the
cutoff-Magnus ball to length `n` then loses exactly one polynomial exponent.
-/
namespace D5.S1.Words.Complexity.PositivePairExactDeckGrowth

open scoped BigOperators
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LyndonStandardBracket
open D5.S1.Words.Complexity.PositivePairWordCoefficients
open D5.S1.Words.Complexity.PositivePairCentralDigits
open D5.S1.Words.Complexity.PositivePairBallGrowth

variable {A : Type*}

private theorem scatteredCount_eq_count_sublistsLen [DecidableEq A]
    (pattern source : List A) :
    scatteredCount pattern source =
      (source.sublistsLen pattern.length).count pattern := by
  induction source generalizing pattern with
  | nil =>
      cases pattern <;> simp [scatteredCount]
  | cons first source ih =>
      cases pattern with
      | nil => simp [scatteredCount]
      | cons letter pattern =>
          rw [scatteredCount, List.length_cons, List.sublistsLen_succ_cons,
            List.count_append, ih]
          by_cases h : letter = first
          · subst first
            simp [List.count_map_of_injective, ih]
          · have hzero :
                (List.map (List.cons first)
                  (List.sublistsLen pattern.length source)).count
                    (letter :: pattern) = 0 := by
              apply List.count_eq_zero.mpr
              intro hmem
              rw [List.mem_map] at hmem
              obtain ⟨middle, _, hmiddle⟩ := hmem
              exact h (List.cons.inj hmiddle).1.symm
            simp [h, hzero]

private def nestedSelectionMass [DecidableEq A]
    (lower upper : Nat) (pattern source : List A) : Nat :=
  ((source.sublistsLen upper).map
    (fun middle => (middle.sublistsLen lower).count pattern)).sum

private theorem nestedSelectionMass_identity [DecidableEq A]
    (pattern source : List A) (lower upper : Nat)
    (hpattern : pattern.length = lower) (hlower : lower ≤ upper) :
    nestedSelectionMass lower upper pattern source =
      Nat.choose (source.length - lower) (upper - lower) *
        (source.sublistsLen lower).count pattern := by
  have hcount_cons_map_cons :
      ∀ (first letter : A) (pattern : List A) (lists : List (List A)),
        (lists.map (List.cons first)).count (letter :: pattern) =
          if letter = first then lists.count pattern else 0 := by
    intro first letter pattern lists
    by_cases h : letter = first
    · subst first
      simp [List.count_map_of_injective]
    · rw [if_neg h, List.count_eq_zero]
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨middle, _, hmiddle⟩ := hmem
      exact h (List.cons.inj hmiddle).1.symm
  have hsucc :
      ∀ (first letter : A) (pattern source : List A) (lower upper : Nat),
        nestedSelectionMass (lower + 1) (upper + 1)
            (letter :: pattern) (first :: source) =
          nestedSelectionMass (lower + 1) (upper + 1)
              (letter :: pattern) source +
            nestedSelectionMass (lower + 1) upper
              (letter :: pattern) source +
            if letter = first then
              nestedSelectionMass lower upper pattern source else 0 := by
    intro first letter pattern source lower upper
    unfold nestedSelectionMass
    rw [List.sublistsLen_succ_cons, List.map_append, List.sum_append]
    simp only [List.map_map, Function.comp_def]
    simp_rw [List.sublistsLen_succ_cons, List.count_append,
      hcount_cons_map_cons]
    rw [List.sum_map_add]
    by_cases h : letter = first <;> simp [h, Nat.add_assoc]
  have hzero_of_lt :
      ∀ (pattern source : List A) (lower upper : Nat), upper < lower →
        nestedSelectionMass lower upper pattern source = 0 := by
    intro pattern source lower upper h
    unfold nestedSelectionMass
    apply List.sum_eq_zero
    intro count hcount
    rw [List.mem_map] at hcount
    obtain ⟨middle, hmiddle, rfl⟩ := hcount
    have hlength : middle.length = upper := List.length_of_sublistsLen hmiddle
    rw [List.sublistsLen_of_length_lt (hlength.trans_lt h)]
    simp
  induction source generalizing pattern lower upper with
  | nil =>
      cases pattern with
      | nil =>
          have hlower0 : lower = 0 := by simpa using hpattern.symm
          subst lower
          cases upper <;> simp [nestedSelectionMass]
      | cons letter pattern =>
          cases lower with
          | zero => simp at hpattern
          | succ lower =>
              cases upper <;>
                simp [nestedSelectionMass, List.sublistsLen_succ_nil]
  | cons first source ih =>
      cases upper with
      | zero =>
          have hlower0 : lower = 0 := by omega
          have hpattern0 : pattern = [] :=
            List.length_eq_zero_iff.mp (hpattern.trans hlower0)
          subst lower
          subst pattern
          simp [nestedSelectionMass]
      | succ upper =>
          cases lower with
          | zero =>
              have hpattern0 : pattern = [] := List.length_eq_zero_iff.mp hpattern
              subst pattern
              simp [nestedSelectionMass, Function.comp_def,
                List.length_sublistsLen, Nat.choose_succ_succ, Nat.add_comm]
          | succ lower =>
              cases pattern with
              | nil => simp at hpattern
              | cons letter pattern =>
                  have hpattern' : pattern.length = lower := by
                    simpa using hpattern
                  have hlower' : lower ≤ upper := by omega
                  rw [hsucc]
                  have hfirst :=
                    ih (letter :: pattern) (lower + 1) (upper + 1)
                      (by simp [hpattern']) (by omega)
                  have hthird := ih pattern lower upper hpattern' hlower'
                  by_cases heq : lower = upper
                  · subst upper
                    have hzero := hzero_of_lt
                      (letter :: pattern) source (lower + 1) lower (by omega)
                    rw [hfirst, hzero, hthird]
                    simp only [List.length_cons, List.sublistsLen_succ_cons,
                      List.count_append, hcount_cons_map_cons,
                      Nat.succ_sub_succ_eq_sub, Nat.sub_self,
                      Nat.choose_zero_right, Nat.one_mul]
                    by_cases hletter : letter = first <;> simp [hletter]
                  · have hlt : lower < upper := lt_of_le_of_ne hlower' heq
                    have hsecond := ih (letter :: pattern) (lower + 1) upper
                      (by simp [hpattern']) (by omega)
                    rw [hfirst, hsecond, hthird]
                    simp only [List.length_cons, List.sublistsLen_succ_cons,
                      List.count_append, hcount_cons_map_cons,
                      Nat.succ_sub_succ_eq_sub]
                    have hsourcePred :
                        source.length - (lower + 1) =
                          source.length - lower - 1 := by
                      omega
                    have huppPred : upper - (lower + 1) =
                        upper - lower - 1 := by
                      omega
                    rw [hsourcePred, huppPred]
                    by_cases hn : lower < source.length
                    · rw [show source.length - lower =
                          (source.length - lower - 1) + 1 by omega,
                        show upper - lower = (upper - lower - 1) + 1 by omega,
                        Nat.choose_succ_succ]
                      by_cases hletter : letter = first <;>
                        simp [hletter] <;> ring
                    · have hsle : source.length ≤ lower := by omega
                      have hzeroSucc :
                          List.sublistsLen (lower + 1) source = [] :=
                        List.sublistsLen_of_length_lt (by omega)
                      rw [hzeroSucc]
                      by_cases hsourceEq : source.length = lower
                      · subst lower
                        simp [hsourceEq]
                      · have hslt : source.length < lower := by omega
                        have hzeroLower :
                            List.sublistsLen lower source = [] :=
                          List.sublistsLen_of_length_lt hslt
                        rw [hzeroLower]
                        simp

noncomputable def exactKDeck [Fintype A] (k : ℕ) (source : List A) :
    {pattern : List A // pattern.length = k} → ℕ :=
  by
    classical
    exact fun pattern ↦ scatteredCount pattern.1 source

noncomputable def exactKDeckImage [Fintype A] (k n : ℕ) :
    Finset ({pattern : List A // pattern.length = k} → ℕ) := by
  classical
  letI : Fintype {source : List A // source.length = n} :=
    Set.Finite.fintype (List.finite_length_eq A n)
  exact Finset.univ.image
    (fun source : {source : List A // source.length = n} ↦
      exactKDeck k source.1)

private theorem sublistsLen_perm_of_exactKDeck_eq [Fintype A]
    (k : ℕ) (left right : List A)
    (hdeck : exactKDeck k left = exactKDeck k right) :
    List.Perm (left.sublistsLen k) (right.sublistsLen k) := by
  classical
  rw [List.perm_iff_count]
  intro pattern
  by_cases hpattern : pattern.length = k
  · have hcount := congrFun hdeck ⟨pattern, hpattern⟩
    simpa only [exactKDeck, scatteredCount_eq_count_sublistsLen,
      hpattern] using hcount
  · have hleft : (left.sublistsLen k).count pattern = 0 := by
      apply List.count_eq_zero.mpr
      intro hmem
      exact hpattern (List.length_of_sublistsLen hmem)
    have hright : (right.sublistsLen k).count pattern = 0 := by
      apply List.count_eq_zero.mpr
      intro hmem
      exact hpattern (List.length_of_sublistsLen hmem)
    rw [hleft, hright]

theorem scatteredCount_eq_of_exactKDeck_eq [Fintype A] [DecidableEq A]
    (k n : ℕ) (left right pattern : List A)
    (hleft : left.length = n) (hright : right.length = n)
    (hkn : k ≤ n) (hpattern : pattern.length ≤ k)
    (hdeck : exactKDeck k left = exactKDeck k right) :
    scatteredCount pattern left = scatteredCount pattern right := by
  classical
  let j := pattern.length
  have hjk : j ≤ k := hpattern
  have hperm := sublistsLen_perm_of_exactKDeck_eq k left right hdeck
  have hmass : nestedSelectionMass j k pattern left =
      nestedSelectionMass j k pattern right := by
    unfold nestedSelectionMass
    exact (hperm.map
      (fun middle ↦ (middle.sublistsLen j).count pattern)).sum_eq
  rw [nestedSelectionMass_identity pattern left j k rfl hjk,
    nestedSelectionMass_identity pattern right j k rfl hjk,
    hleft, hright] at hmass
  have hchoose : 0 < Nat.choose (n - j) (k - j) := by
    apply Nat.choose_pos
    omega
  have hcount := Nat.eq_of_mul_eq_mul_left hchoose hmass
  simpa only [scatteredCount_eq_count_sublistsLen] using hcount

theorem exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length [Fintype A]
    (k n : ℕ) (left right : List A)
    (hleft : left.length = n) (hright : right.length = n) (hkn : k ≤ n) :
    exactKDeck k left = exactKDeck k right ↔
      cutoffMagnus k left = cutoffMagnus k right := by
  classical
  constructor
  · intro hdeck
    funext word
    let pattern := FreeMonoid.toList word.1
    have hpattern : pattern.length ≤ k := by
      simpa [pattern, FreeMonoid.length] using word.2
    have hcount := scatteredCount_eq_of_exactKDeck_eq k n left right pattern
      hleft hright hkn hpattern hdeck
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom]
    rw [show word.1 = FreeMonoid.ofList pattern by
      apply FreeMonoid.toList.injective
      simp [pattern]]
    simp only [magnusPolynomial_coeff_scatteredCount]
    have hq : (scatteredCount pattern left : ℚ) =
        (scatteredCount pattern right : ℚ) := by
      exact_mod_cast hcount
    simpa using hq
  · intro hcutoff
    funext pattern
    change scatteredCount pattern.1 left = scatteredCount pattern.1 right
    have hcoeff := congrFun hcutoff
      (⟨FreeMonoid.ofList pattern.1, by
        simp [FreeMonoid.length, pattern.2]⟩ : CutoffWord A k)
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom,
      magnusPolynomial_coeff_scatteredCount] at hcoeff
    have hq : (scatteredCount pattern.1 left : ℚ) =
        (scatteredCount pattern.1 right : ℚ) := by
      simpa using hcoeff
    exact_mod_cast hq

theorem actual_exactKDeckImage_weightedLyndon_lower_bound
    [Fintype A] [LinearOrder A] (hq : 2 ≤ Fintype.card A)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C N : ℕ, 0 < C ∧
      ∀ n, N ≤ n →
        n ^ (weightedLyndonExponent (A := A) k - 1) ≤
          C * (exactKDeckImage (A := A) k n).card := by
  classical
  have mem_positiveWordBall_iff (n : ℕ) (x : CutoffCoefficients A k) :
      x ∈ positiveWordBall (A := A) k n ↔
        ∃ source : List A,
          source.length ≤ n ∧ cutoffMagnus k source = x := by
    simp [positiveWordBall]
  have mem_exactKDeckImage_iff (n : ℕ)
      (deck : {pattern : List A // pattern.length = k} → ℕ) :
      deck ∈ exactKDeckImage (A := A) k n ↔
        ∃ source : List A,
          source.length = n ∧ exactKDeck k source = deck := by
    simp [exactKDeckImage]
  let ballRepresentative (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) : List A :=
    Classical.choose ((mem_positiveWordBall_iff n x.1).mp x.2)
  have ballRepresentative_length (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) :
      (ballRepresentative n x).length ≤ n :=
    (Classical.choose_spec
      ((mem_positiveWordBall_iff n x.1).mp x.2)).1
  have ballRepresentative_cutoff (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) :
      cutoffMagnus k (ballRepresentative n x) = x.1 :=
    (Classical.choose_spec
      ((mem_positiveWordBall_iff n x.1).mp x.2)).2
  let fixedLetter : A :=
    Classical.choice (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card A))
  let paddedWord (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) : List A :=
    ballRepresentative n x ++
      List.replicate (n - (ballRepresentative n x).length) fixedLetter
  have paddedWord_length (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) :
      (paddedWord n x).length = n := by
    dsimp only [paddedWord]
    rw [List.length_append, List.length_replicate]
    have hlength := ballRepresentative_length n x
    omega
  have cutoffMagnus_append (r : ℕ) (left right : List A) :
      cutoffMagnus r (left ++ right) =
        cutoffMul r (cutoffMagnus r left) (cutoffMagnus r right) := by
    simp only [cutoffMagnus, magnusPolynomial_append, map_mul,
      cutoffRestriction_mul]
  have cutoffMagnus_empty_coeff (r : ℕ) (source : List A) :
      cutoffMagnus r source ⟨1, by simp⟩ = 1 := by
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom]
    change ((magnusPolynomial source).coeff (FreeMonoid.ofList []) : ℚ) = 1
    rw [magnusPolynomial_coeff_scatteredCount source []]
    norm_num [scatteredCount]
  have cutoffMagnus_tail_vanishes (r : ℕ) (source : List A) :
      VanishesBelow r 1 (cutoffMagnus r source - cutoffOne r) := by
    intro word hword
    have hlength : FreeMonoid.length word.1 = 0 := by omega
    have hempty : word.1 = 1 := by
      apply FreeMonoid.toList.injective
      apply List.length_eq_zero_iff.mp
      simpa [FreeMonoid.length] using hlength
    have hwordSubtype : word = ⟨1, by simp⟩ := Subtype.ext hempty
    rw [hwordSubtype]
    simp [cutoffMagnus_empty_coeff, cutoffOne, cutoffRestriction]
  have cutoffMagnus_eq_one_add_tail (r : ℕ) (source : List A) :
      cutoffMagnus r source =
        cutoffOne r + (cutoffMagnus r source - cutoffOne r) := by
    abel
  have cutoffRightUnit (r : ℕ) (p : CutoffCoefficients A r) :
      cutoffMul r p (cutoffOne r) = p := by
    have hrestrict : cutoffRestriction r (cutoffLift r p) = p := by
      funext w
      simp [cutoffRestriction, cutoffLift,
        Finsupp.mapDomain_apply Subtype.val_injective]
    calc
      _ = cutoffMul r (cutoffRestriction r (cutoffLift r p))
          (cutoffRestriction r 1) := by rw [cutoffOne, hrestrict]
      _ = cutoffRestriction r (cutoffLift r p * 1) :=
        (cutoffRestriction_mul r (cutoffLift r p) 1).symm
      _ = p := by simpa using hrestrict
  have cutoffAssoc (r : ℕ) (p q s : CutoffCoefficients A r) :
      cutoffMul r (cutoffMul r p q) s = cutoffMul r p (cutoffMul r q s) := by
    have hrestrict (x : CutoffCoefficients A r) :
        cutoffRestriction r (cutoffLift r x) = x := by
      funext w
      simp [cutoffRestriction, cutoffLift,
        Finsupp.mapDomain_apply Subtype.val_injective]
    have hp := hrestrict p
    have hq := hrestrict q
    have hs := hrestrict s
    calc
      _ = cutoffRestriction r
          ((cutoffLift r p * cutoffLift r q) * cutoffLift r s) := by
            rw [cutoffRestriction_mul, cutoffRestriction_mul, hp, hq, hs]
      _ = cutoffRestriction r
          (cutoffLift r p * (cutoffLift r q * cutoffLift r s)) := by rw [mul_assoc]
      _ = _ := by rw [cutoffRestriction_mul, cutoffRestriction_mul, hp, hq, hs]
  have cutoffMagnus_cancel_right (r : ℕ)
      (left right suffixLeft suffixRight : List A)
      (hsuffix : cutoffMagnus r suffixLeft = cutoffMagnus r suffixRight)
      (h : cutoffMagnus r (left ++ suffixLeft) =
        cutoffMagnus r (right ++ suffixRight)) :
      cutoffMagnus r left = cutoffMagnus r right := by
    rw [cutoffMagnus_append, cutoffMagnus_append, hsuffix] at h
    let tail := cutoffMagnus r suffixRight - cutoffOne r
    let inverse := cutoffGeometricInverse r tail
    have htail : VanishesBelow r 1 tail :=
      cutoffMagnus_tail_vanishes r suffixRight
    have hinverse : cutoffMul r (cutoffMagnus r suffixRight) inverse =
        cutoffOne r := by
      rw [cutoffMagnus_eq_one_add_tail r suffixRight]
      exact cutoffMul_geometricInverse r tail htail
    have h' := congrArg (fun x ↦ cutoffMul r x inverse) h
    simpa only [cutoffAssoc, hinverse, cutoffRightUnit] using h'
  have ball_card_le_exact (n : ℕ) (hkn : k ≤ n) :
      (positiveWordBall (A := A) k n).card ≤
        (n + 1) * (exactKDeckImage (A := A) k n).card := by
    let embed : ↑(positiveWordBall (A := A) k n) →
        Fin (n + 1) × ↑(exactKDeckImage (A := A) k n) :=
      fun x ↦
        (⟨(ballRepresentative n x).length,
            Nat.lt_succ_of_le (ballRepresentative_length n x)⟩,
          ⟨exactKDeck k (paddedWord n x),
            (mem_exactKDeckImage_iff n _).2
              ⟨paddedWord n x, paddedWord_length n x, rfl⟩⟩)
    have hinjective : Function.Injective embed := by
      intro left right heq
      have hlength : (ballRepresentative n left).length =
          (ballRepresentative n right).length :=
        congrArg (fun output ↦ output.1.val) heq
      have hdeck : exactKDeck k (paddedWord n left) =
          exactKDeck k (paddedWord n right) :=
        congrArg (fun output ↦ output.2.val) heq
      have hpaddedCutoff :=
        (exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length
          k n (paddedWord n left) (paddedWord n right)
          (paddedWord_length n left) (paddedWord_length n right) hkn).mp hdeck
      have hsuffixWords :
          List.replicate (n - (ballRepresentative n left).length) fixedLetter =
            List.replicate
              (n - (ballRepresentative n right).length) fixedLetter := by
        rw [hlength]
      have hsuffixCutoff :
          cutoffMagnus k
              (List.replicate
                (n - (ballRepresentative n left).length) fixedLetter) =
            cutoffMagnus k
              (List.replicate
                (n - (ballRepresentative n right).length) fixedLetter) := by
        rw [hsuffixWords]
      dsimp only [paddedWord] at hpaddedCutoff
      have hrepresentatives := cutoffMagnus_cancel_right k
        (ballRepresentative n left) (ballRepresentative n right)
        (List.replicate
          (n - (ballRepresentative n left).length) fixedLetter)
        (List.replicate
          (n - (ballRepresentative n right).length) fixedLetter)
        hsuffixCutoff hpaddedCutoff
      apply Subtype.ext
      rw [← ballRepresentative_cutoff n left,
        ← ballRepresentative_cutoff n right]
      exact hrepresentatives
    have hcard := Fintype.card_le_of_injective embed hinjective
    simpa only [Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe] using hcard
  have exponent_pos :
      1 ≤ weightedLyndonExponent (A := A) k := by
    have hcountOne : 1 ≤ actualLyndonCount (A := A) 1 := by
      unfold actualLyndonCount
      have hpos : 0 < Fintype.card (ActualLyndonWord A 1) :=
        Fintype.card_pos_iff.mpr ⟨⟨[fixedLetter], by
          exact ⟨rfl, isLyndon_singleton fixedLetter⟩⟩⟩
      omega
    have hone_mem : 1 ∈ Finset.range (k + 1) := by simp; omega
    have hterm : 1 * actualLyndonCount (A := A) 1 ≤
        ∑ i ∈ Finset.range (k + 1),
          i * actualLyndonCount (A := A) i := by
      exact Finset.single_le_sum
        (fun i _ ↦ Nat.zero_le
          (i * actualLyndonCount (A := A) i)) hone_mem
    unfold weightedLyndonExponent
    exact hcountOne.trans (by simpa using hterm)
  obtain ⟨C, N, hC, hball⟩ :=
    actual_positiveWordBall_weightedLyndon_lower_bound
      (A := A) hq k hk
  refine ⟨2 * C, max N (max k 1), by positivity, ?_⟩
  intro n hn
  have hnN : N ≤ n := (Nat.le_max_left N (max k 1)).trans hn
  have hnk : k ≤ n :=
    (Nat.le_max_right N (max k 1)).trans hn |>.trans' (Nat.le_max_left k 1)
  have hnpos : 0 < n := by
    have : 1 ≤ n :=
      (Nat.le_max_right N (max k 1)).trans hn |>.trans' (Nat.le_max_right k 1)
    omega
  have hballBound := hball n hnN
  have hcard := ball_card_le_exact n hnk
  have hcancel :
      n ^ (weightedLyndonExponent (A := A) k - 1) * n ≤
        ((2 * C) * (exactKDeckImage (A := A) k n).card) * n := by
    calc
      n ^ (weightedLyndonExponent (A := A) k - 1) * n =
          n ^ (weightedLyndonExponent (A := A) k - 1 + 1) := by
        rw [pow_succ]
      _ = n ^ weightedLyndonExponent (A := A) k := by
        rw [Nat.sub_add_cancel exponent_pos]
      _ ≤ C * (positiveWordBall (A := A) k n).card := hballBound
      _ ≤ C * ((n + 1) * (exactKDeckImage (A := A) k n).card) :=
        Nat.mul_le_mul_left C hcard
      _ ≤ C * ((2 * n) * (exactKDeckImage (A := A) k n).card) := by
        gcongr
        omega
      _ = ((2 * C) * (exactKDeckImage (A := A) k n).card) * n := by
        ring
  exact Nat.le_of_mul_le_mul_right hcancel hnpos

#print axioms exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length
#print axioms actual_exactKDeckImage_weightedLyndon_lower_bound

end D5.S1.Words.Complexity.PositivePairExactDeckGrowth

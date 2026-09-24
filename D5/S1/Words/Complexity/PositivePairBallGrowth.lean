/- GID: D5/S1/Words/Complexity/PositivePairBallGrowth
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/PositivePairBallGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual positive-word cutoff balls have weighted Lyndon polynomial growth. -/
import D5.S1.Words.Complexity.PositivePairCentralDigits
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Actual positive-word ball growth

Actual cutoff-Magnus images of positive words contain a product of the preceding
ball with the independently selected central digits at every degree.
-/
namespace D5.S1.Words.Complexity.PositivePairBallGrowth

open scoped BigOperators
open D5.S1.Words.Complexity.LyndonStandardBracket
open D5.S1.Words.Complexity.PositivePairWordCoefficients
open D5.S1.Words.Complexity.PositivePairCentralDigits

variable {A : Type*}

/-! ## Actual positive-word balls -/

/-- The finite image of the actual degree-`r` cutoff Magnus map on positive
words of length at most `n`. -/
noncomputable def positiveWordBall [Fintype A] (r n : ℕ) :
    Finset (CutoffCoefficients A r) := by
  classical
  letI : Fintype {w : List A // w.length ≤ n} :=
    Set.Finite.fintype (List.finite_length_le A n)
  exact Finset.univ.image
    (fun w : {w : List A // w.length ≤ n} ↦ cutoffMagnus r w.1)

/-! ## The complete degree-one letter box -/

private noncomputable def letterOrder [Fintype A] [LinearOrder A] : List A :=
  Finset.univ.sort (· ≤ ·)

private noncomputable def letterBoxWord [Fintype A] [LinearOrder A] (t : ℕ)
    (digits : A → Fin (t + 1)) : List A :=
  (letterOrder (A := A)).flatMap
    (fun a ↦ List.replicate (digits a : ℕ) a)

private theorem scatteredCount_singleton_eq_count [DecidableEq A]
    (a : A) (source : List A) :
    D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
      [a] source = source.count a := by
  induction source with
  | nil => simp [D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount]
  | cons b source ih =>
      simp only [D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount,
        ih, List.count_cons]
      by_cases h : a = b
      · subst b
        simp
      · simp [h, Ne.symm h]

private theorem count_flatMap_replicate_of_nodup [DecidableEq A]
    (order : List A) (horder : order.Nodup) (multiplicity : A → ℕ)
    (a : A) (ha : a ∈ order) :
    (order.flatMap (fun b ↦ List.replicate (multiplicity b) b)).count a =
      multiplicity a := by
  induction order with
  | nil => simp at ha
  | cons b order ih =>
      have hb : b ∉ order := (List.nodup_cons.mp horder).1
      have horder' : order.Nodup := (List.nodup_cons.mp horder).2
      simp only [List.flatMap_cons, List.count_append, List.count_replicate]
      by_cases hab : a = b
      · subst b
        have hcount :
            (order.flatMap
              (fun c ↦ List.replicate (multiplicity c) c)).count a = 0 := by
          apply List.count_eq_zero.mpr
          intro hamem
          rw [List.mem_flatMap] at hamem
          obtain ⟨c, hc, hac⟩ := hamem
          have hca : c = a := (List.eq_of_mem_replicate hac).symm
          exact hb (hca ▸ hc)
        simp [hcount]
      · have ha' : a ∈ order := by simpa [hab] using ha
        simp [Ne.symm hab, ih horder' ha']

private theorem length_flatMap_replicate_le
    (order : List A) (multiplicity : A → ℕ) (t : ℕ)
    (hmul : ∀ a ∈ order, multiplicity a ≤ t) :
    (order.flatMap (fun a ↦ List.replicate (multiplicity a) a)).length ≤
      order.length * t := by
  induction order with
  | nil => simp
  | cons a order ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_replicate,
        List.length_cons]
      have ha := hmul a (by simp)
      have htail := ih (fun b hb ↦ hmul b (by simp [hb]))
      calc
        multiplicity a +
            (order.flatMap
              (fun b ↦ List.replicate (multiplicity b) b)).length ≤
            t + order.length * t := Nat.add_le_add ha htail
        _ = (order.length + 1) * t := by
          simp [Nat.add_mul, Nat.add_comm]

private noncomputable def letterActualLyndonEquiv
    [Fintype A] [LinearOrder A] : A ≃ ActualLyndonWord A 1 where
  toFun a := ⟨[a], by exact ⟨rfl, isLyndon_singleton a⟩⟩
  invFun w := w.1.get ⟨0, by rw [w.2.1]; omega⟩
  left_inv a := by simp
  right_inv w := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp w.2.1
    simp [ha]

/-! ## Quantitative all-radius estimates -/

/-- The weighted number of actual Lyndon directions through degree `r`. -/
noncomputable def weightedLyndonExponent
    [Fintype A] [LinearOrder A] (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1),
    i * actualLyndonCount (A := A) i

private noncomputable def scaleDenominator
    [Fintype A] [LinearOrder A] (r : ℕ) : ℕ :=
  max (baseLength (A := A) r) 1

private noncomputable def fittingScale
    [Fintype A] [LinearOrder A] (r m : ℕ) : ℕ :=
  Nat.log 2 (m / scaleDenominator (A := A) r + 1)

/-- For every fixed positive cutoff degree and every finite linearly ordered
alphabet with at least two letters, the actual positive-word cutoff-Magnus ball
has the full weighted-Lyndon polynomial lower bound at every sufficiently large
radius.  The natural constant `C` represents the positive rational lower
constant `1 / C`. -/
theorem actual_positiveWordBall_weightedLyndon_lower_bound
    [Fintype A] [LinearOrder A] (hq : 2 ≤ Fintype.card A)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ C N : ℕ, 0 < C ∧
      ∀ n, N ≤ n →
        n ^ weightedLyndonExponent (A := A) r ≤
          C * (positiveWordBall (A := A) r n).card := by
  classical
  have mem_positiveWordBall_iff (r n : ℕ) (x : CutoffCoefficients A r) :
      x ∈ positiveWordBall (A := A) r n ↔
        ∃ w : List A, w.length ≤ n ∧ cutoffMagnus r w = x := by
    simp [positiveWordBall]
  let ballRepresentative (r n : ℕ)
      (x : ↑(positiveWordBall (A := A) r n)) : List A :=
    Classical.choose ((mem_positiveWordBall_iff r n x.1).mp x.2)
  have ballRepresentative_length (r n : ℕ)
      (x : ↑(positiveWordBall (A := A) r n)) :
      (ballRepresentative r n x).length ≤ n :=
    (Classical.choose_spec ((mem_positiveWordBall_iff r n x.1).mp x.2)).1
  have ballRepresentative_cutoff (r n : ℕ)
      (x : ↑(positiveWordBall (A := A) r n)) :
      cutoffMagnus r (ballRepresentative r n x) = x.1 :=
    (Classical.choose_spec ((mem_positiveWordBall_iff r n x.1).mp x.2)).2
  let ballDigitProductWord (r m t : ℕ)
      (input : ↑(positiveWordBall (A := A) (r - 1) m) ×
        DigitArray (A := A) r t) : List A :=
    ballRepresentative (r - 1) m input.1 ++
      multiScaleWord (A := A) r t input.2
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
    norm_num [D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount]
  have cutoffMagnus_tail_vanishes (r : ℕ) (source : List A) :
      VanishesBelow r 1 (cutoffMagnus r source - cutoffOne r) := by
    intro w hw
    have hlength : FreeMonoid.length w.1 = 0 := by omega
    have hword : w.1 = 1 := by
      apply FreeMonoid.toList.injective
      apply List.length_eq_zero_iff.mp
      simpa [FreeMonoid.length] using hlength
    have hwSubtype : w = ⟨1, by simp⟩ := Subtype.ext hword
    rw [hwSubtype]
    simp [cutoffMagnus_empty_coeff, cutoffOne, cutoffRestriction]
  have cutoffMagnus_eq_one_add_tail (r : ℕ) (source : List A) :
      cutoffMagnus r source =
        cutoffOne r + (cutoffMagnus r source - cutoffOne r) := by
    abel
  have cutoffLeftUnit (r : ℕ) (p : CutoffCoefficients A r) :
      cutoffMul r (cutoffOne r) p = p := by
    have hrestrict : cutoffRestriction r (cutoffLift r p) = p := by
      funext w
      simp [cutoffRestriction, cutoffLift,
        Finsupp.mapDomain_apply Subtype.val_injective]
    calc
      _ = cutoffMul r (cutoffRestriction r 1)
          (cutoffRestriction r (cutoffLift r p)) := by rw [cutoffOne, hrestrict]
      _ = cutoffRestriction r (1 * cutoffLift r p) :=
        (cutoffRestriction_mul r 1 (cutoffLift r p)).symm
      _ = p := by simpa using hrestrict
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
  have cutoffMagnus_cancel_left (r : ℕ)
      (prefixWord left right : List A)
      (h : cutoffMagnus r (prefixWord ++ left) =
        cutoffMagnus r (prefixWord ++ right)) :
      cutoffMagnus r left = cutoffMagnus r right := by
    rw [cutoffMagnus_append, cutoffMagnus_append] at h
    let tail := cutoffMagnus r prefixWord - cutoffOne r
    let inverse := cutoffGeometricInverse r tail
    have htail : VanishesBelow r 1 tail :=
      cutoffMagnus_tail_vanishes r prefixWord
    have hinverse : cutoffMul r inverse (cutoffMagnus r prefixWord) =
        cutoffOne r := by
      rw [cutoffMagnus_eq_one_add_tail r prefixWord]
      exact geometricInverse_cutoffMul r tail htail
    have h' := congrArg (cutoffMul r inverse) h
    simpa only [← cutoffAssoc, hinverse, cutoffLeftUnit] using h'
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
  have cutoffMagnus_eq_of_higher_eq (low high : ℕ) (hlow : low ≤ high)
      (left right : List A)
      (h : cutoffMagnus high left = cutoffMagnus high right) :
      cutoffMagnus low left = cutoffMagnus low right := by
    funext w
    have hcoeff := congrFun h
      (⟨w.1, w.2.trans hlow⟩ : CutoffWord A high)
    simpa only [cutoffMagnus, cutoffRestriction] using hcoeff
  have multiScaleWord_cutoff_lower_eq (r t : ℕ) (hr : 2 ≤ r)
      (left right : DigitArray (A := A) r t) :
      cutoffMagnus (r - 1) (multiScaleWord (A := A) r t left) =
        cutoffMagnus (r - 1) (multiScaleWord (A := A) r t right) := by
    funext w
    let pattern := FreeMonoid.toList w.1
    have hpattern : pattern.length < r := by
      have hw : pattern.length ≤ r - 1 := by
        simpa [pattern, FreeMonoid.length] using w.2
      omega
    have hcentral :=
      (actual_positivePair_multiScale_central_digits (A := A) r t hr).2.2.1
    have hcount :
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern (multiScaleWord (A := A) r t left) =
          D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern (multiScaleWord (A := A) r t right) :=
      (hcentral left pattern hpattern).trans
        (hcentral right pattern hpattern).symm
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom]
    rw [show w.1 = FreeMonoid.ofList pattern by
      apply FreeMonoid.toList.injective
      simp [pattern]]
    simp only [magnusPolynomial_coeff_scatteredCount]
    simpa using congrArg (fun z : ℕ ↦ (z : ℚ)) hcount
  have ballDigitProduct_cutoff_injective (r m t : ℕ) (hr : 2 ≤ r) :
      Function.Injective (fun input :
        ↑(positiveWordBall (A := A) (r - 1) m) ×
          DigitArray (A := A) r t ↦
        cutoffMagnus r (ballDigitProductWord r m t input)) := by
    rintro ⟨leftClass, leftDigits⟩ ⟨rightClass, rightDigits⟩ h
    have hlower := cutoffMagnus_eq_of_higher_eq (r - 1) r (by omega)
      (ballDigitProductWord r m t (leftClass, leftDigits))
      (ballDigitProductWord r m t (rightClass, rightDigits)) h
    have hsuffix := multiScaleWord_cutoff_lower_eq r t hr leftDigits rightDigits
    dsimp only [ballDigitProductWord] at hlower
    have hclassCutoff := cutoffMagnus_cancel_right (r - 1)
      (ballRepresentative (r - 1) m leftClass)
      (ballRepresentative (r - 1) m rightClass)
      (multiScaleWord (A := A) r t leftDigits)
      (multiScaleWord (A := A) r t rightDigits) hsuffix hlower
    have hclass : leftClass = rightClass := by
      apply Subtype.ext
      rw [← ballRepresentative_cutoff (r - 1) m leftClass,
        ← ballRepresentative_cutoff (r - 1) m rightClass]
      exact hclassCutoff
    subst rightClass
    change cutoffMagnus r (ballDigitProductWord r m t (leftClass, leftDigits)) =
      cutoffMagnus r (ballDigitProductWord r m t (leftClass, rightDigits)) at h
    dsimp only [ballDigitProductWord] at h
    have hdigitCutoff := cutoffMagnus_cancel_left r
      (ballRepresentative (r - 1) m leftClass)
      (multiScaleWord (A := A) r t leftDigits)
      (multiScaleWord (A := A) r t rightDigits) h
    have hdigits : leftDigits = rightDigits :=
      (actual_positivePair_multiScale_central_digits
        (A := A) r t hr).2.2.2.2.1 hdigitCutoff
    subst rightDigits
    rfl
  have ballDigitProduct_length (r m t : ℕ) (hr : 2 ≤ r)
      (input : ↑(positiveWordBall (A := A) (r - 1) m) ×
        DigitArray (A := A) r t) :
      (ballDigitProductWord r m t input).length ≤
        m + baseLength (A := A) r * (2 ^ t - 1) := by
    dsimp only [ballDigitProductWord]
    rw [List.length_append,
      (actual_positivePair_multiScale_central_digits
        (A := A) r t hr).2.2.2.2.2.2 input.2]
    exact Nat.add_le_add_right
      (ballRepresentative_length (r - 1) m input.1) _
  have positiveWordBall_card_step (r m t n : ℕ) (hr : 2 ≤ r)
      (hfit : m + baseLength (A := A) r * (2 ^ t - 1) ≤ n) :
      (positiveWordBall (A := A) (r - 1) m).card *
          digitBase r ^ (t * actualLyndonCount (A := A) r) ≤
        (positiveWordBall (A := A) r n).card := by
    let embed :
        ↑(positiveWordBall (A := A) (r - 1) m) ×
            DigitArray (A := A) r t →
          ↑(positiveWordBall (A := A) r n) :=
      fun input ↦ ⟨cutoffMagnus r (ballDigitProductWord r m t input),
        (mem_positiveWordBall_iff r n _).2
          ⟨ballDigitProductWord r m t input,
            (ballDigitProduct_length r m t hr input).trans hfit, rfl⟩⟩
    have hinjective : Function.Injective embed := by
      intro left right heq
      apply ballDigitProduct_cutoff_injective r m t hr
      exact congrArg Subtype.val heq
    have hcard := Fintype.card_le_of_injective embed hinjective
    simpa only [Fintype.card_prod, Fintype.card_coe,
      (actual_positivePair_multiScale_central_digits
        (A := A) r t hr).2.2.2.2.2.1] using hcard
  have letterOrder_nodup : (letterOrder (A := A)).Nodup := by
    simp [letterOrder]
  have mem_letterOrder (a : A) : a ∈ letterOrder (A := A) := by
    simp [letterOrder]
  have letterBoxWord_scatteredCount (t : ℕ)
      (digits : A → Fin (t + 1)) (a : A) :
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          [a] (letterBoxWord (A := A) t digits) = digits a := by
    rw [scatteredCount_singleton_eq_count]
    exact count_flatMap_replicate_of_nodup
      (letterOrder (A := A)) letterOrder_nodup
      (fun b ↦ (digits b : ℕ)) a (mem_letterOrder a)
  have letterBoxWord_length (t : ℕ) (digits : A → Fin (t + 1)) :
      (letterBoxWord (A := A) t digits).length ≤ Fintype.card A * t := by
    have h := length_flatMap_replicate_le
      (letterOrder (A := A)) (fun a ↦ (digits a : ℕ)) t
      (fun a _ ↦ Nat.le_of_lt_succ (digits a).2)
    simpa [letterBoxWord, letterOrder] using h
  have letterBox_cutoff_injective (t : ℕ) :
      Function.Injective (fun digits : A → Fin (t + 1) ↦
        cutoffMagnus 1 (letterBoxWord (A := A) t digits)) := by
    intro left right h
    funext a
    have hcoeff := congrFun h
      (⟨FreeMonoid.ofList [a], by simp [FreeMonoid.length]⟩ : CutoffWord A 1)
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom,
      magnusPolynomial_coeff_scatteredCount] at hcoeff
    have hcount :
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            [a] (letterBoxWord (A := A) t left) =
          D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            [a] (letterBoxWord (A := A) t right) := by
      have hq :
          (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              [a] (letterBoxWord (A := A) t left) : ℚ) =
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              [a] (letterBoxWord (A := A) t right) : ℚ) := by
        simpa using hcoeff
      exact_mod_cast hq
    rw [letterBoxWord_scatteredCount, letterBoxWord_scatteredCount] at hcount
    exact Fin.ext hcount
  have positiveWordBall_one_card_lower (t : ℕ) :
      (t + 1) ^ Fintype.card A ≤
        (positiveWordBall (A := A) 1 (Fintype.card A * t)).card := by
    let embed : (A → Fin (t + 1)) →
        ↑(positiveWordBall (A := A) 1 (Fintype.card A * t)) :=
      fun digits ↦ ⟨cutoffMagnus 1 (letterBoxWord (A := A) t digits),
        (mem_positiveWordBall_iff 1 (Fintype.card A * t) _).2
          ⟨letterBoxWord (A := A) t digits,
            letterBoxWord_length t digits, rfl⟩⟩
    have hinjective : Function.Injective embed := by
      intro left right heq
      apply letterBox_cutoff_injective t
      exact congrArg Subtype.val heq
    have hcard := Fintype.card_le_of_injective embed hinjective
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using hcard
  have actualLyndonCount_one :
      actualLyndonCount (A := A) 1 = Fintype.card A := by
    unfold actualLyndonCount
    exact (Fintype.card_congr letterActualLyndonEquiv).symm
  have weightedLyndonExponent_one :
      weightedLyndonExponent (A := A) 1 = Fintype.card A := by
    unfold weightedLyndonExponent
    rw [show 1 + 1 = 1 + 1 by rfl, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simpa using actualLyndonCount_one
  have weightedLyndonExponent_step (r : ℕ) (hr : 1 ≤ r) :
      weightedLyndonExponent (A := A) r =
        weightedLyndonExponent (A := A) (r - 1) +
          r * actualLyndonCount (A := A) r := by
    unfold weightedLyndonExponent
    have hrange : r - 1 + 1 = r := by omega
    rw [hrange, Finset.sum_range_succ]
  have positiveWordBall_mono (r left right : ℕ) (h : left ≤ right) :
      (positiveWordBall (A := A) r left).card ≤
        (positiveWordBall (A := A) r right).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨word, hlength, hcutoff⟩ :=
      (mem_positiveWordBall_iff r left x).mp hx
    exact (mem_positiveWordBall_iff r right x).2
      ⟨word, hlength.trans h, hcutoff⟩
  have self_lt_mul_div_add_one (n d : ℕ) (hd : 0 < d) :
      n < d * (n / d + 1) := by
    have hmod : n % d < d := Nat.mod_lt n hd
    nth_rewrite 1 [← Nat.div_add_mod n d]
    rw [Nat.mul_add]
    omega
  have positiveWordBall_one_polynomial :
      ∀ n,
        n ^ weightedLyndonExponent (A := A) 1 ≤
          (Fintype.card A) ^ weightedLyndonExponent (A := A) 1 *
            (positiveWordBall (A := A) 1 n).card := by
    intro n
    let q := Fintype.card A
    let t := n / q
    have hqpos : 0 < q := by omega
    have hn : n ≤ q * (t + 1) :=
      (self_lt_mul_div_add_one n q hqpos).le
    have hqt : q * t ≤ n := Nat.mul_div_le n q
    have hbox := positiveWordBall_one_card_lower t
    have hmono := positiveWordBall_mono 1 (q * t) n hqt
    rw [weightedLyndonExponent_one]
    calc
      n ^ q ≤ (q * (t + 1)) ^ q := Nat.pow_le_pow_left hn q
      _ = q ^ q * (t + 1) ^ q := by rw [Nat.mul_pow]
      _ ≤ q ^ q * (positiveWordBall (A := A) 1 (q * t)).card :=
        Nat.mul_le_mul_left _ hbox
      _ ≤ q ^ q * (positiveWordBall (A := A) 1 n).card :=
        Nat.mul_le_mul_left _ hmono
  have scaleDenominator_pos (r : ℕ) :
      0 < scaleDenominator (A := A) r := by
    simp [scaleDenominator]
  have scaleDenominator_ge_baseLength (r : ℕ) :
      baseLength (A := A) r ≤ scaleDenominator (A := A) r := by
    exact Nat.le_max_left _ _
  have fittingScale_length_le (r m : ℕ) :
      baseLength (A := A) r * (2 ^ fittingScale (A := A) r m - 1) ≤ m := by
    let d := scaleDenominator (A := A) r
    let t := fittingScale (A := A) r m
    have hd : 0 < d := scaleDenominator_pos r
    have hpow : 2 ^ t ≤ m / d + 1 := by
      dsimp only [t, fittingScale, d]
      exact Nat.pow_log_le_self 2 (Nat.add_one_ne_zero _)
    have hsub : 2 ^ t - 1 ≤ m / d := by
      rw [Nat.sub_le_iff_le_add]
      simpa [Nat.add_comm] using hpow
    calc
      baseLength (A := A) r * (2 ^ t - 1) ≤ d * (2 ^ t - 1) :=
        Nat.mul_le_mul_right _ (scaleDenominator_ge_baseLength r)
      _ ≤ d * (m / d) := Nat.mul_le_mul_left d hsub
      _ ≤ m := Nat.mul_div_le m d
  have fittingScale_quantitative (r m : ℕ) :
      m < 2 * scaleDenominator (A := A) r *
        2 ^ fittingScale (A := A) r m := by
    let d := scaleDenominator (A := A) r
    let t := fittingScale (A := A) r m
    have hd : 0 < d := scaleDenominator_pos r
    have hm : m < d * (m / d + 1) := self_lt_mul_div_add_one m d hd
    have hx : m / d + 1 < 2 ^ (Nat.log 2 (m / d + 1)).succ :=
      Nat.lt_pow_succ_log_self (by omega) _
    have hmul : d * (m / d + 1) <
        d * 2 ^ (Nat.log 2 (m / d + 1)).succ :=
      (Nat.mul_lt_mul_left hd).2 hx
    calc
      m < d * (m / d + 1) := hm
      _ < d * 2 ^ (Nat.log 2 (m / d + 1)).succ := hmul
      _ = 2 * d * 2 ^ t := by
        dsimp only [t, fittingScale, d]
        rw [pow_succ]
        ac_rfl
  have half_bounds (n : ℕ) (hn : 2 ≤ n) :
      let m := n / 2
      1 ≤ m ∧ n ≤ 3 * m ∧ 2 * m ≤ n := by
    let m := n / 2
    have hdecomp := Nat.div_add_mod n 2
    have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
    dsimp only [m]
    omega
  have digitCard_eq_scalePower (r t : ℕ) :
      digitBase r ^ (t * actualLyndonCount (A := A) r) =
        (2 ^ t) ^ (r * actualLyndonCount (A := A) r) := by
    unfold digitBase
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    congr 1
    ac_rfl
  have combine_polynomial_bounds
      (n m scale q r c previousBall ball three k : ℕ)
      (hnm : n ≤ three * m) (hns : n ≤ k * scale)
      (hprevious : m ^ q ≤ c * previousBall)
      (hstep : previousBall * scale ^ r ≤ ball) :
      n ^ (q + r) ≤ (three ^ q * k ^ r * c) * ball := by
    calc
      n ^ (q + r) = n ^ q * n ^ r := Nat.pow_add _ _ _
      _ ≤ (three * m) ^ q * (k * scale) ^ r :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hnm q)
          (Nat.pow_le_pow_left hns r)
      _ = (three ^ q * k ^ r) * (m ^ q * scale ^ r) := by
        simp only [Nat.mul_pow]
        ac_rfl
      _ ≤ (three ^ q * k ^ r) * ((c * previousBall) * scale ^ r) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hprevious)
      _ = (three ^ q * k ^ r) * (c * (previousBall * scale ^ r)) := by
        ac_rfl
      _ ≤ (three ^ q * k ^ r) * (c * ball) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hstep)
      _ = (three ^ q * k ^ r * c) * ball := by ac_rfl
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hrone : r = 1
      · subst r
        refine ⟨(Fintype.card A) ^
            weightedLyndonExponent (A := A) 1, 0, ?_, ?_⟩
        · positivity
        · intro n _
          exact positiveWordBall_one_polynomial n
      · have hr2 : 2 ≤ r := by omega
        have hrprev : 1 ≤ r - 1 := by omega
        obtain ⟨C, N, hC, hprevious⟩ :=
          ih (r - 1) (by omega) hrprev
        let Q := weightedLyndonExponent (A := A) (r - 1)
        let R := r * actualLyndonCount (A := A) r
        let d := scaleDenominator (A := A) r
        let K := 6 * d
        let Cnew := 3 ^ Q * K ^ R * C
        let Nnew := max 2 (2 * N)
        refine ⟨Cnew, Nnew, ?_, ?_⟩
        · have hd : 0 < d := scaleDenominator_pos r
          dsimp only [Cnew, K]
          positivity
        · intro n hn
          let m := n / 2
          let t := fittingScale (A := A) r m
          have hn2 : 2 ≤ n :=
            (Nat.le_max_left 2 (2 * N)).trans hn
          have hhalves := half_bounds n hn2
          have hmN : N ≤ m := by
            have h2N : 2 * N ≤ n :=
              (Nat.le_max_right 2 (2 * N)).trans hn
            have hdecomp := Nat.div_add_mod n 2
            have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
            dsimp only [m]
            omega
          have hIH : m ^ Q ≤
              C * (positiveWordBall (A := A) (r - 1) m).card := by
            exact hprevious m hmN
          have hdigit : baseLength (A := A) r * (2 ^ t - 1) ≤ m := by
            exact fittingScale_length_le r m
          have hfit :
              m + baseLength (A := A) r * (2 ^ t - 1) ≤ n := by
            have htwom : 2 * m ≤ n := hhalves.2.2
            omega
          have hcardStep := positiveWordBall_card_step r m t n hr2 hfit
          rw [digitCard_eq_scalePower] at hcardStep
          have hscale : m < 2 * d * 2 ^ t := by
            exact fittingScale_quantitative r m
          have hnK : n ≤ K * 2 ^ t := by
            have hthree : n ≤ 3 * m := hhalves.2.1
            have hmul : 3 * m < 3 * (2 * d * 2 ^ t) :=
              (Nat.mul_lt_mul_left (by omega : 0 < 3)).2 hscale
            have hle := hthree.trans hmul.le
            calc
              n ≤ 3 * (2 * d * 2 ^ t) := hle
              _ = K * 2 ^ t := by
                dsimp only [K]
                ring
          rw [weightedLyndonExponent_step r (by omega)]
          exact combine_polynomial_bounds n m (2 ^ t) Q R C
            (positiveWordBall (A := A) (r - 1) m).card
            (positiveWordBall (A := A) r n).card 3 K
            hhalves.2.1 hnK hIH hcardStep

#print axioms actual_positiveWordBall_weightedLyndon_lower_bound

end D5.S1.Words.Complexity.PositivePairBallGrowth

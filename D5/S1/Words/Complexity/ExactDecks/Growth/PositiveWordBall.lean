/- GID: D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual central digits inject the preceding cutoff ball into the next degree. -/

import D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitInjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall

open scoped BigOperators
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
open D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords
open D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitInjection

variable {A : Type*}

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
  toFun a := ⟨[a], by
    refine ⟨rfl, ?_⟩
    refine ⟨by simp, ?_⟩
    intro u v hu hv huv
    have hlen := congrArg List.length huv
    simp only [List.length_singleton, List.length_append] at hlen
    have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
    have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
    omega⟩
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

/-- Central degree-r digits inject the preceding cutoff ball into the next ball
whenever the combined representative length fits the target radius. -/
theorem positiveWordBall_card_step [Fintype A] [LinearOrder A]
    (r m t n : ℕ) (hr : 2 ≤ r)
    (hfit : m + baseLength (A := A) r * (2 ^ t - 1) ≤ n) :
    (positiveWordBall (A := A) (r - 1) m).card *
        digitBase r ^ (t * actualLyndonCount (A := A) r) ≤
      (positiveWordBall (A := A) r n).card := by
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
    have hclassCutoff := (cutoffMagnus_cancellation (A := A)).2 (r - 1)
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
    have hdigitCutoff := (cutoffMagnus_cancellation (A := A)).1 r
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

end D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall

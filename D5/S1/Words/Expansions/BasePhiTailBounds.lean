/- GID: D5/S1/Words/Expansions/BasePhiTailBounds
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiTailBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical negative base-phi tails lie across the inverse-golden cut. -/

import D5.S1.Words.Expansions.BasePhiCanonicalExpansion

namespace D5.S1.Words.Expansions.BasePhiTailBounds

open D5.S0.Carrier
open D5.S1.Words.Expansions.BasePhiNegative

noncomputable section

private noncomputable def inverseGolden : Real := Real.goldenRatio⁻¹

private def inverseWordValue : List Nat → Real
  | [] => 0
  | digit :: tail => inverseGolden * (digit + inverseWordValue tail)

private theorem inverseGolden_pos : 0 < inverseGolden := by
  exact inv_pos.mpr Real.goldenRatio_pos

private theorem inverseGolden_lt_one : inverseGolden < 1 := by
  exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

private theorem inverseGolden_add_sq :
    inverseGolden + inverseGolden ^ 2 = 1 := by
  dsimp [inverseGolden]
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private def BinaryNonadjacent : List Nat → Prop
  | [] => True
  | digit :: tail =>
      digit ≤ 1 ∧
        (match tail with
          | [] => True
          | next :: _ => digit = 1 → next = 0) ∧
        BinaryNonadjacent tail

private theorem binaryNonadjacent_tail {digit : Nat} {tail : List Nat}
    (h : BinaryNonadjacent (digit :: tail)) : BinaryNonadjacent tail := by
  exact h.2.2

private theorem inverseWordValue_bounds : ∀ digits : List Nat,
    BinaryNonadjacent digits →
      0 ≤ inverseWordValue digits ∧ inverseWordValue digits < 1
  | [], _ => by
      simp [inverseWordValue]
  | digit :: tail, h => by
      have htail := inverseWordValue_bounds tail (binaryNonadjacent_tail h)
      have hdigit : digit = 0 ∨ digit = 1 := by
        have := h.1
        omega
      rcases hdigit with rfl | rfl
      · simp only [inverseWordValue, Nat.cast_zero, zero_add]
        constructor
        · exact mul_nonneg inverseGolden_pos.le htail.1
        · have hscaled : inverseGolden * inverseWordValue tail <
              inverseGolden :=
            mul_lt_of_lt_one_right inverseGolden_pos htail.2
          exact hscaled.trans inverseGolden_lt_one
      · cases tail with
        | nil =>
            simp [inverseWordValue, inverseGolden_pos.le, inverseGolden_lt_one]
        | cons next rest =>
            have hnext : next = 0 := by
              exact h.2.1 rfl
            subst next
            have hrest : BinaryNonadjacent rest := by
              exact binaryNonadjacent_tail (binaryNonadjacent_tail h)
            have hrestBounds := inverseWordValue_bounds rest hrest
            simp only [inverseWordValue, Nat.cast_one, Nat.cast_zero, zero_add]
            constructor
            · exact mul_nonneg inverseGolden_pos.le
                (add_nonneg zero_le_one
                  (mul_nonneg inverseGolden_pos.le hrestBounds.1))
            · have hscaled : inverseGolden * inverseWordValue rest <
                  inverseGolden := by
                exact mul_lt_of_lt_one_right inverseGolden_pos hrestBounds.2
              nlinarith [inverseGolden_add_sq]

private theorem inverseWordValue_lt_inverse_of_head_zero {tail : List Nat}
    (h : BinaryNonadjacent (0 :: tail)) :
    inverseWordValue (0 :: tail) < inverseGolden := by
  have htail := inverseWordValue_bounds tail (binaryNonadjacent_tail h)
  simp only [inverseWordValue, Nat.cast_zero, zero_add]
  nlinarith [inverseGolden_pos]

private theorem inverseGolden_le_inverseWordValue_of_head_one {tail : List Nat} :
    inverseGolden ≤ inverseWordValue (1 :: tail) := by
  have hnonnegative : 0 ≤ inverseWordValue tail := by
    induction tail with
    | nil => simp [inverseWordValue]
    | cons digit rest ih =>
        simp only [inverseWordValue]
        exact mul_nonneg inverseGolden_pos.le
          (add_nonneg (Nat.cast_nonneg digit) ih)
  simp only [inverseWordValue, Nat.cast_one]
  nlinarith [inverseGolden_pos]

/-- The embedding `i ↦ -(i+1)` enumerates all strictly negative exponents. -/
def negativeIndexEmbedding : Nat ↪ Int where
  toFun i := -((i + 1 : Nat) : Int)
  inj' := by
    intro i j h
    push_cast at h
    omega

/-- The finite raw word obtained by reindexing the negative exponents from zero. -/
noncomputable def negativeDigits (expansion : BasePhiNegativeExpansion)
    (N : Nat) : Nat →₀ Nat :=
  (Finsupp.comapDomain.addMonoidHom
    (f := negativeIndexEmbedding) negativeIndexEmbedding.injective)
      (expansion.digit N)

@[simp] theorem negativeDigits_apply (expansion : BasePhiNegativeExpansion)
    (N i : Nat) :
    negativeDigits expansion N i =
      expansion.digit N (-((i + 1 : Nat) : Int)) := by
  rfl

/-- Put a reindexed negative word back at its original integer exponents. -/
noncomputable def negativePart (expansion : BasePhiNegativeExpansion)
    (N : Nat) : Int →₀ Nat :=
  Finsupp.embDomain negativeIndexEmbedding (negativeDigits expansion N)

/-- The real value of the complete finite negative-position tail. -/
noncomputable def negativeTailReal (expansion : BasePhiNegativeExpansion)
    (N : Nat) : Real :=
  (negativeDigits expansion N).sum fun i coefficient =>
    (coefficient : Real) * inverseGolden ^ (i + 1)

private def negativeSupportDepth (expansion : BasePhiNegativeExpansion)
    (N : Nat) : Nat :=
  if negativeDigits expansion N = 0 then 0
  else (negativeDigits expansion N).support.sup id + 1

/-- A finite window in the negative-exponent digit tail. -/
private def negativeWordFrom (expansion : BasePhiNegativeExpansion)
    (N start depth : Nat) : List Nat :=
  List.ofFn fun i : Fin depth =>
    negativeDigits expansion N (start + i.1)

/-- The digits at negative exponents, cut off after `depth` positions. -/
def negativeWord (expansion : BasePhiNegativeExpansion) (N depth : Nat) : List Nat :=
  negativeWordFrom expansion N 0 depth

@[simp] theorem negativeWord_length (expansion : BasePhiNegativeExpansion)
    (N depth : Nat) : (negativeWord expansion N depth).length = depth := by
  simp [negativeWord, negativeWordFrom]

@[simp] theorem negativeWord_get (expansion : BasePhiNegativeExpansion)
    (N depth : Nat) (i : Fin depth) :
    (negativeWord expansion N depth)[i.1] =
      expansion.digit N (-((i.1 + 1 : Nat) : Int)) := by
  simp [negativeWord, negativeWordFrom]

private theorem negativeWordFrom_succ (expansion : BasePhiNegativeExpansion)
    (N start depth : Nat) :
    negativeWordFrom expansion N start (depth + 1) =
      expansion.digit N (-((start + 1 : Nat) : Int)) ::
        negativeWordFrom expansion N (start + 1) depth := by
  rw [negativeWordFrom, List.ofFn_succ]
  congr 1
  unfold negativeWordFrom
  apply congrArg List.ofFn
  funext i
  congr 1
  rw [Fin.val_succ]
  omega

private theorem negativeWordFrom_binaryNonadjacent
    (expansion : BasePhiNegativeExpansion) (N start : Nat) :
    ∀ depth : Nat, BinaryNonadjacent (negativeWordFrom expansion N start depth)
  | 0 => by simp [negativeWordFrom, BinaryNonadjacent]
  | depth + 1 => by
      rw [negativeWordFrom_succ]
      refine ⟨(by simpa using (expansion.binary N
          (-((start + 1 : Nat) : Int)))), ?_,
        negativeWordFrom_binaryNonadjacent expansion N (start + 1) depth⟩
      cases depth with
      | zero => trivial
      | succ depth =>
          rw [negativeWordFrom_succ]
          dsimp
          intro hone
          by_contra hnext
          have hnext_pos : 0 <
              expansion.digit N (-(((start + 1) + 1 : Nat) : Int)) := by
            simpa using Nat.pos_of_ne_zero hnext
          have hnext_one :
              expansion.digit N (-(((start + 1) + 1 : Nat) : Int)) = 1 := by
            have hnext_le := expansion.binary N
              (-(((start + 1) + 1 : Nat) : Int))
            omega
          have hzero := expansion.canonical N
            (-(((start + 1) + 1 : Nat) : Int)) hnext_one
          have hindex : -(((start + 1) + 1 : Nat) : Int) + 1 =
              -((start + 1 : Nat) : Int) := by
            push_cast
            ring
          rw [hindex] at hzero
          have hcurrent :
              expansion.digit N (-((start + 1 : Nat) : Int)) = 0 := hzero
          have hsame : -((start : Int) + 1) =
              -((start + 1 : Nat) : Int) := by
            push_cast
            ring
          rw [hsame] at hone
          rw [hcurrent] at hone
          omega

theorem negativeWord_binaryNonadjacent (expansion : BasePhiNegativeExpansion)
    (N depth : Nat) : BinaryNonadjacent (negativeWord expansion N depth) := by
  exact negativeWordFrom_binaryNonadjacent expansion N 0 depth

private theorem inverseWordValue_negativeWordFrom
    (expansion : BasePhiNegativeExpansion) (N start : Nat) :
    ∀ depth : Nat,
      inverseWordValue (negativeWordFrom expansion N start depth) =
        ∑ i ∈ Finset.range depth,
          (negativeDigits expansion N (start + i) : Real) *
            inverseGolden ^ (i + 1)
  | 0 => by simp [negativeWordFrom, inverseWordValue]
  | depth + 1 => by
      rw [negativeWordFrom_succ, inverseWordValue,
        inverseWordValue_negativeWordFrom expansion N (start + 1) depth,
        Finset.sum_range_succ']
      have htail : inverseGolden *
          (∑ i ∈ Finset.range depth,
            (negativeDigits expansion N (start + 1 + i) : Real) *
              inverseGolden ^ (i + 1)) =
          ∑ i ∈ Finset.range depth,
            (negativeDigits expansion N (start + (i + 1)) : Real) *
              inverseGolden ^ (i + 1 + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show start + 1 + i = start + (i + 1) by omega,
          pow_succ]
        ring
      rw [mul_add, htail]
      simp only [negativeDigits_apply]
      ring

private theorem negativeSupportDepth_covers
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    (negativeDigits expansion N).support ⊆
      Finset.range (negativeSupportDepth expansion N) := by
  intro i hi
  rw [Finset.mem_range]
  rw [negativeSupportDepth]
  split
  · rename_i hzero
    rw [hzero] at hi
    simp at hi
  · have hle : i ≤ (negativeDigits expansion N).support.sup id := by
      exact Finset.le_sup (f := id) hi
    omega

private theorem inverseWordValue_complete (expansion : BasePhiNegativeExpansion)
    (N : Nat) :
    inverseWordValue
        (negativeWord expansion N (negativeSupportDepth expansion N)) =
      negativeTailReal expansion N := by
  rw [negativeWord, inverseWordValue_negativeWordFrom]
  simp only [zero_add]
  unfold negativeTailReal
  change (∑ i ∈ Finset.range (negativeSupportDepth expansion N),
      (negativeDigits expansion N i : Real) * inverseGolden ^ (i + 1)) =
    ∑ i ∈ (negativeDigits expansion N).support,
      (negativeDigits expansion N i : Real) * inverseGolden ^ (i + 1)
  symm
  apply Finset.sum_subset (negativeSupportDepth_covers expansion N)
  intro i hiRange hiSupport
  have hzero : negativeDigits expansion N i = 0 := by
    simpa [Finsupp.mem_support_iff] using hiSupport
  simp [hzero]

private theorem negativeDigits_ne_zero_of_reaches
    (expansion : BasePhiNegativeExpansion) (N depth : Nat)
    (h : reachesNegativeDepth expansion N depth) :
    negativeDigits expansion N ≠ 0 := by
  obtain ⟨hdepth, i, hiSupport, hiDepth⟩ := h
  have hiNeg : i < 0 := by
    have hcast : (0 : Int) < (depth : Int) := by exact_mod_cast hdepth
    omega
  let index : Nat := (-i).toNat - 1
  have hminusPos : 0 < (-i).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hindex : -((index + 1 : Nat) : Int) = i := by
    have hcast : ((-i).toNat : Int) = -i :=
      Int.toNat_of_nonneg (by omega)
    have hnat : index + 1 = (-i).toNat := by
      dsimp [index]
      exact Nat.sub_add_cancel (by omega)
    rw [hnat]
    rw [hcast]
    ring
  intro hzero
  have hdigit : expansion.digit N i = 0 := by
    have := DFunLike.congr_fun hzero index
    rw [negativeDigits_apply, hindex] at this
    simpa using this
  exact (Finsupp.mem_support_iff.mp hiSupport) hdigit

private theorem negativeTailReal_pos_of_ne_zero
    (expansion : BasePhiNegativeExpansion) (N : Nat)
    (h : negativeDigits expansion N ≠ 0) :
    0 < negativeTailReal expansion N := by
  rw [negativeTailReal]
  have hsupport : (negativeDigits expansion N).support.Nonempty := by
    simpa [Finsupp.support_nonempty_iff] using h
  obtain ⟨i, hi⟩ := hsupport
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg inverseGolden_pos.le _)
  · refine ⟨i, hi, mul_pos ?_ (pow_pos inverseGolden_pos _)⟩
    exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)

/-- A nonempty canonical negative tail has value in `(0,1)`. Its first digit
selects the side of the inverse-golden cut. -/
theorem negative_tail_real_bounds (expansion : BasePhiNegativeExpansion)
    (N : Nat) (hreaches : ∃ depth, reachesNegativeDepth expansion N depth) :
    0 < negativeTailReal expansion N ∧
      negativeTailReal expansion N < 1 ∧
      (negativeDigit expansion N 0 = true →
        Real.goldenRatio⁻¹ ≤ negativeTailReal expansion N) ∧
      (negativeDigit expansion N 0 = false →
        negativeTailReal expansion N < Real.goldenRatio⁻¹) := by
  obtain ⟨depth, hdepth⟩ := hreaches
  have hnonzero := negativeDigits_ne_zero_of_reaches expansion N depth hdepth
  have hdepthPositive : 0 < negativeSupportDepth expansion N := by
    rw [negativeSupportDepth, if_neg hnonzero]
    omega
  obtain ⟨tailDepth, htailDepth⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hdepthPositive)
  have hcanonical := negativeWord_binaryNonadjacent expansion N
    (negativeSupportDepth expansion N)
  have hwordBounds := inverseWordValue_bounds _ hcanonical
  rw [htailDepth] at hcanonical hwordBounds
  have hcomplete := inverseWordValue_complete expansion N
  rw [htailDepth] at hcomplete
  refine ⟨negativeTailReal_pos_of_ne_zero expansion N hnonzero,
    hcomplete ▸ hwordBounds.2, ?_, ?_⟩
  · intro hone
    have hdigit : expansion.digit N (-1) = 1 := by
      exact of_decide_eq_true hone
    rw [negativeWord, negativeWordFrom_succ] at hcomplete hcanonical
    have hlower := inverseGolden_le_inverseWordValue_of_head_one
      (tail := negativeWordFrom expansion N 1 tailDepth)
    rw [← hcomplete]
    simpa [hdigit, inverseGolden] using hlower
  · intro hzero
    have hdigit : expansion.digit N (-1) = 0 := by
      have hne : expansion.digit N (-1) ≠ 1 := by
        simpa [negativeDigit] using hzero
      have hle := expansion.binary N (-1)
      omega
    rw [negativeWord, negativeWordFrom_succ] at hcomplete hcanonical
    have hupper := inverseWordValue_lt_inverse_of_head_zero
      (tail := negativeWordFrom expansion N 1 tailDepth) (by simpa [hdigit] using hcanonical)
    rw [← hcomplete]
    simpa [hdigit, inverseGolden] using hupper

@[simp] theorem negativePart_apply (expansion : BasePhiNegativeExpansion)
    (N i : Nat) :
    negativePart expansion N (-((i + 1 : Nat) : Int)) =
      expansion.digit N (-((i + 1 : Nat) : Int)) := by
  change negativePart expansion N (negativeIndexEmbedding i) =
    expansion.digit N (negativeIndexEmbedding i)
  rw [negativePart, Finsupp.embDomain_apply_self, negativeDigits_apply]
  rfl

theorem negativePart_eq_zero_of_nonnegative
    (expansion : BasePhiNegativeExpansion) (N : Nat) {i : Int}
    (hi : 0 ≤ i) : negativePart expansion N i = 0 := by
  rw [negativePart, Finsupp.embDomain_apply]
  split
  · rename_i h
    obtain ⟨j, hj⟩ := h
    have : negativeIndexEmbedding j < 0 := by
      change -((j + 1 : Nat) : Int) < 0
      omega
    omega
  · rfl

private theorem natLift_eq_zero_of_negative
    (digits : D5.S1.Digit.RawDigits) {i : Int} (hi : i < 0) :
    D5.S1.Words.Expansions.BasePhiCanonicalExpansion.natLift digits i = 0 := by
  rw [D5.S1.Words.Expansions.BasePhiCanonicalExpansion.natLift,
    Finsupp.embDomain_apply]
  split
  · rename_i h
    obtain ⟨j, hj⟩ := h
    change (j : Int) = i at hj
    have : (0 : Int) ≤ (j : Int) := by positivity
    omega
  · rfl

/-- Split the canonical two-sided digits into their negative and nonnegative
parts without changing either side. -/
theorem digit_eq_negativePart_add_natLift
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    expansion.digit N = negativePart expansion N +
      D5.S1.Words.Expansions.BasePhiCanonicalExpansion.natLift
        (D5.S1.Words.Expansions.BasePhiCarryTransducer.nonnegativeDigits
          expansion N) := by
  apply Finsupp.ext
  intro i
  by_cases hi : i < 0
  · have hposZero := natLift_eq_zero_of_negative
      (D5.S1.Words.Expansions.BasePhiCarryTransducer.nonnegativeDigits
        expansion N) hi
    let index : Nat := (-i).toNat - 1
    have hminusPos : 0 < (-i).toNat := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have := Int.toNat_eq_zero.mp hzero
      omega
    have hcast : ((-i).toNat : Int) = -i :=
      Int.toNat_of_nonneg (by omega)
    have hnat : index + 1 = (-i).toNat := by
      dsimp [index]
      exact Nat.sub_add_cancel (by omega)
    have hindex : -((index + 1 : Nat) : Int) = i := by
      rw [hnat, hcast]
      ring
    change expansion.digit N i = negativePart expansion N i +
      D5.S1.Words.Expansions.BasePhiCanonicalExpansion.natLift
        (D5.S1.Words.Expansions.BasePhiCarryTransducer.nonnegativeDigits
          expansion N) i
    rw [hposZero, add_zero, ← hindex, negativePart_apply]
  · have hiNonnegative : 0 ≤ i := le_of_not_gt hi
    have hnegativeZero := negativePart_eq_zero_of_nonnegative expansion N
      hiNonnegative
    have hindex : (i.toNat : Int) = i := Int.toNat_of_nonneg hiNonnegative
    change expansion.digit N i = negativePart expansion N i +
      D5.S1.Words.Expansions.BasePhiCanonicalExpansion.natLift
        (D5.S1.Words.Expansions.BasePhiCarryTransducer.nonnegativeDigits
          expansion N) i
    rw [hnegativeZero, zero_add, ← hindex,
      D5.S1.Words.Expansions.BasePhiCanonicalExpansion.natLift_apply,
      D5.S1.Words.Expansions.BasePhiCarryTransducer.nonnegativeDigits_apply]

theorem basePhiValue_add (digits₁ digits₂ : Int →₀ Nat) :
    basePhiValue (digits₁ + digits₂) =
      basePhiValue digits₁ + basePhiValue digits₂ := by
  classical
  change (digits₁ + digits₂).sum (fun i coefficient =>
      (coefficient : GoldenInt) *
        (((D5.S0.Carrier.phiUnit ^ i : GoldenIntˣ) : GoldenInt))) =
    digits₁.sum (fun i coefficient =>
      (coefficient : GoldenInt) *
        (((D5.S0.Carrier.phiUnit ^ i : GoldenIntˣ) : GoldenInt))) +
    digits₂.sum (fun i coefficient =>
      (coefficient : GoldenInt) *
        (((D5.S0.Carrier.phiUnit ^ i : GoldenIntˣ) : GoldenInt)))
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast
    ring

/-- The exact base-phi value splits over the negative/nonnegative digit cut. -/
theorem basePhiValue_digit_decomposition
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    basePhiValue (expansion.digit N) =
      basePhiValue (negativePart expansion N) +
        basePhiValue
          (D5.S1.Words.Expansions.BasePhiCanonicalExpansion.natLift
            (D5.S1.Words.Expansions.BasePhiCarryTransducer.nonnegativeDigits
              expansion N)) := by
  rw [digit_eq_negativePart_add_natLift, basePhiValue_add]

/-- The real embedding of the negative-position part is its inverse-power
polynomial value. -/
theorem embedding_basePhiValue_negativePart
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    D5.S1.Scale.embedding (basePhiValue (negativePart expansion N)) =
      negativeTailReal expansion N := by
  change D5.S1.Scale.embedding
      ((negativePart expansion N).sum (fun i coefficient =>
        (coefficient : GoldenInt) *
          (((D5.S0.Carrier.phiUnit ^ i : GoldenIntˣ) : GoldenInt)))) =
    negativeTailReal expansion N
  rw [negativePart, Finsupp.sum_embDomain]
  change D5.S1.Scale.embedding
      (∑ i ∈ (negativeDigits expansion N).support,
        (negativeDigits expansion N i : GoldenInt) *
          (((D5.S0.Carrier.phiUnit ^
            (negativeIndexEmbedding i) : GoldenIntˣ) : GoldenInt))) =
    negativeTailReal expansion N
  rw [map_sum]
  unfold negativeTailReal
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_natCast]
  have hunit :
      D5.S1.Scale.embedding
          (((D5.S0.Carrier.phiUnit ^
            (negativeIndexEmbedding i) : GoldenIntˣ) : GoldenInt)) =
        Real.goldenRatio ^ (negativeIndexEmbedding i) := by
    simpa [D5.S1.Scale.phiUnitZPowMul] using
      (D5.S1.Scale.embedding_phiUnitZPowMul
        (negativeIndexEmbedding i) (1 : GoldenInt))
  rw [hunit]
  change (negativeDigits expansion N i : Real) *
      Real.goldenRatio ^ (-((i + 1 : Nat) : Int)) =
    (negativeDigits expansion N i : Real) * inverseGolden ^ (i + 1)
  congr 1
  rw [zpow_neg]
  rw [zpow_natCast, ← inv_pow]
  rfl

end

end D5.S1.Words.Expansions.BasePhiTailBounds

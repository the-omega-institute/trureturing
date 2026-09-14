/- GID: D5/S1/Digit/Infinite/SignedSeriesFibres
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SignedSeriesFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed golden series has exactly two streams over each uniquely indexed seam and one stream over every other value in its interval. -/

import D5.S1.Digit.Infinite.SignedSeriesRange
import D5.S0.Automata.BinaryZeckendorfBlockSkeletonCore

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SignedSeriesFibres

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S0.Automata.BinaryZeckendorfBlockSkeleton

/-- The alphabet consisting of the return blocks zero and one followed by zero. -/
abbrev Block := ReturnBlock

/-- The Boolean digits of a finite word of return blocks. -/
def digitsOf (w : List Block) : List Bool :=
  (expand w .recurrent).map (fun d => decide (d = 1))

/-- The digit length of a finite block word. -/
def len (w : List Block) : ℕ := (digitsOf w).length

private def prependBlock (c : Block) (x : LegalDigits) : LegalDigits :=
  match c with
  | .zero => ⟨fun n => match n with | 0 => false | k + 1 => x.val k, by
      intro j; cases j with
      | zero => simp
      | succ j => exact x.property j⟩
  | .oneZero => ⟨fun n => match n with | 0 => true | 1 => false | k + 2 => x.val k, by
      intro j; cases j with
      | zero => simp
      | succ j => cases j with
        | zero => simp
        | succ j => exact x.property j⟩

/-- Prepend a finite block word to an infinite legal stream. -/
def prependWord : List Block → LegalDigits → LegalDigits
  | [], x => x
  | c :: w, x => prependBlock c (prependWord w x)

/-- The signed contraction ratio. -/
noncomputable def r : ℝ := -alpha

/-- The finite signed sum of the expanded digits, indexed from zero. -/
noncomputable def S (w : List Block) : ℝ :=
  ∑ j ∈ Finset.range (len w), (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) *
    (if (digitsOf w)[j]?.getD false then 1 else 0)

/-- The affine action of a finite block word on series values. -/
noncomputable def f (w : List Block) (t : ℝ) : ℝ := S w + r ^ len w * t

/-- The common boundary value of the first two block intervals. -/
noncomputable def q : ℝ := -(alpha ^ 3)

/-- The seam value indexed by a finite block word. -/
noncomputable def seam (w : List Block) : ℝ := f w q

/-- The stream obtained by appending the zero block and the upper alternating stream. -/
def leftStream (w : List Block) : LegalDigits := prependWord (w ++ [.zero]) v

/-- The stream obtained by appending the one-zero block and the upper alternating stream. -/
def rightStream (w : List Block) : LegalDigits := prependWord (w ++ [.oneZero]) v

/-- Each seam has exactly its two displayed streams, the indexing word is unique,
and each other value in the closed interval has exactly one stream. -/
theorem signed_series_fibres :
    (∀ w : List Block, leftStream w ≠ rightStream w ∧
      (∀ x : LegalDigits, signedValue x = seam w ↔
        x = leftStream w ∨ x = rightStream w)) ∧
    Function.Injective seam ∧
    (∀ t ∈ Set.Icc a b, t ∉ Set.range seam → ∃! x : LegalDigits, signedValue x = t) := by
  classical
  have hp : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
  have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have ha : alpha ^ 2 + alpha = 1 := by
    dsimp [alpha]; rw [Real.inv_goldenRatio]; nlinarith [Real.goldenConj_sq]
  have hc : alpha ^ 3 + alpha ^ 2 = alpha := by
    nlinarith [congrArg (fun z : ℝ => alpha * z) ha]
  have hd : alpha ^ 4 + alpha ^ 3 = alpha ^ 2 := by
    nlinarith [congrArg (fun z : ℝ => alpha ^ 2 * z) ha]
  let shift (x : LegalDigits) (n : ℕ) : LegalDigits :=
    ⟨fun j => x.val (j + n), fun j => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using x.property (j + n)⟩
  let B : Block → ℝ → ℝ
    | .zero, t => -alpha * t
    | .oneZero, t => -alpha ^ 2 + alpha ^ 2 * t
  have Binj (c : Block) : Function.Injective (B c) := by
    intro s t h; cases c <;> dsimp [B] at h
    · nlinarith
    · nlinarith [sq_pos_of_pos hp]
  have pinj (c : Block) : Function.Injective (prependBlock c) := by
    intro x y h
    apply Subtype.ext; funext n
    cases c with
    | zero => exact congrArg (fun z : LegalDigits => z.val (n + 1)) h
    | oneZero => exact congrArg (fun z : LegalDigits => z.val (n + 2)) h
  have parse (x : LegalDigits) : ∃ c y, x = prependBlock c y := by
    cases h : x.val 0 with
    | false =>
      refine ⟨.zero, shift x 1, ?_⟩
      apply Subtype.ext; funext n; cases n <;> simp [prependBlock, shift, h]
    | true =>
      have h1 : x.val 1 = false := by
        cases h1 : x.val 1
        · rfl
        · exact False.elim (x.property 0 ⟨h, h1⟩)
      refine ⟨.oneZero, shift x 2, ?_⟩
      apply Subtype.ext; funext n
      cases n with
      | zero => exact h
      | succ n => cases n <;> simp [prependBlock, shift, h1, Nat.add_assoc]
  let term (x : LegalDigits) (j : ℕ) : ℝ :=
    (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) * (if x.val j then 1 else 0)
  have summable_term (x : LegalDigits) : Summable (term x) := by
    apply ((summable_geometric_of_lt_one hp.le hlt).mul_right (alpha ^ 2)).of_norm_bounded
    intro j
    dsimp [term]
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos hp]
    cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg hp.le j) (sq_nonneg alpha)]
  have recval (x : LegalDigits) : signedValue x =
      -alpha ^ 2 * (if x.val 0 then 1 else 0) + (-alpha) * signedValue (shift x 1) := by
    change (∑' j, term x j) = _
    rw [(summable_term x).tsum_eq_zero_add]
    have ht (j : ℕ) : term x (j + 1) = (-alpha) * term (shift x 1) j := by
      simp [term, shift, pow_add]; ring
    simp_rw [ht]
    rw [tsum_mul_left]
    simp [term, signedValue]
  have valB (c : Block) (x : LegalDigits) :
      signedValue (prependBlock c x) = B c (signedValue x) := by
    have h0 (y : LegalDigits) : shift (prependBlock .zero y) 1 = y := rfl
    have h1 : shift (prependBlock .oneZero x) 1 = prependBlock .zero x := by
      apply Subtype.ext; funext n; cases n <;> rfl
    cases c with
    | zero => simpa [prependBlock, h0, B] using recval (prependBlock .zero x)
    | oneZero =>
      rw [recval, h1, recval, h0]
      simp [prependBlock, B]; ring
  let P (p : List Bool) : ℝ :=
    ∑ j ∈ Finset.range p.length, (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) *
      (if p[j]?.getD false then 1 else 0)
  have Pcons (d : Bool) (p : List Bool) :
      P (d :: p) = -alpha ^ 2 * (if d then 1 else 0) + r * P p := by
    dsimp [P]
    rw [Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Nat.zero_add, pow_one, neg_mul, one_mul]
    rw [Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [pow_add, r]; ring
  have Srec (c : Block) (w : List Block) : S (c :: w) = B c (S w) := by
    cases c with
    | zero =>
      change P (false :: digitsOf w) = -alpha * P (digitsOf w)
      rw [Pcons]; simp [r]
    | oneZero =>
      change P (true :: false :: digitsOf w) = -alpha ^ 2 + alpha ^ 2 * P (digitsOf w)
      rw [Pcons, Pcons]; simp [r]; ring
  have frec (c : Block) (w : List Block) (t : ℝ) : f (c :: w) t = B c (f w t) := by
    dsimp [f]
    rw [Srec]
    cases c <;> simp [len, digitsOf, expand, r, B, pow_add] <;> ring
  have fempty (t : ℝ) : f [] t = t := by simp [f, S, len, digitsOf, expand]
  have srec (c : Block) (w : List Block) : seam (c :: w) = B c (seam w) := frec c w q
  have sempty : seam [] = q := fempty q
  have bounds (x : LegalDigits) : signedValue x ∈ Set.Icc a b := by
    rw [← signed_series_range.1]; exact ⟨x, rfl⟩
  have edge (c : Block) (t : ℝ) (ht : t ∈ Set.Icc a b) :
      (B c t = q ↔ t = b) ∧
      (c = .zero → q ≤ B c t) ∧ (c = .oneZero → B c t ≤ q) := by
    rcases ht with ⟨hl, hu⟩
    dsimp [a, b] at hl hu
    cases c <;> dsimp [B, q, b] <;> constructor
    · constructor <;> intro h <;> nlinarith
    · constructor <;> intro h <;> try contradiction
      nlinarith
    · constructor <;> intro h <;> nlinarith [sq_pos_of_pos hp]
    · constructor <;> intro h <;> try contradiction
      nlinarith [sq_pos_of_pos hp]
  have interior (c : Block) (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      B c t ∈ Set.Ioo a b ∧
      (c = .zero → q < B c t) ∧ (c = .oneZero → B c t < q) := by
    rcases ht with ⟨hl, hu⟩
    dsimp [a, b] at hl hu
    cases c with
    | zero =>
      dsimp [B, a, b, q]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · nlinarith [mul_pos hp (sub_pos.mpr hu)]
      · nlinarith [mul_pos hp (sub_pos.mpr hl)]
      · intro _; nlinarith [mul_pos hp (sub_pos.mpr hu)]
      · intro h; contradiction
    | oneZero =>
      dsimp [B, a, b, q]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · nlinarith [mul_pos (sq_pos_of_pos hp) (sub_pos.mpr hl)]
      · nlinarith [mul_pos (sq_pos_of_pos hp) (sub_pos.mpr hu)]
      · intro h; contradiction
      · intro _; nlinarith [mul_pos (sq_pos_of_pos hp) (sub_pos.mpr hu)]
  have smem (w : List Block) : seam w ∈ Set.Ioo a b := by
    induction w with
    | nil => rw [sempty]; dsimp [q, a, b]; constructor <;> nlinarith [pow_pos hp 3]
    | cons c w ih => rw [srec]; exact (interior c _ ih).1
  have lrrec (c : Block) (w : List Block) :
      leftStream (c :: w) = prependBlock c (leftStream w) ∧
      rightStream (c :: w) = prependBlock c (rightStream w) := ⟨rfl, rfl⟩
  have lrne (w : List Block) : leftStream w ≠ rightStream w := by
    induction w with
    | nil =>
      intro h
      have hh := congrArg (fun z : LegalDigits => z.val 0) h
      simp [leftStream, rightStream, prependWord, prependBlock] at hh
    | cons c w ih => exact fun h => ih (pinj c h)
  have separate (c d : Block) (s t : ℝ) (hne : c ≠ d)
      (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Icc a b) : B c s ≠ B d t := by
    have hi := interior c s hs
    have he := edge d t ht
    cases c <;> cases d
    · exact False.elim (hne rfl)
    · exact ne_of_gt (lt_of_le_of_lt (he.2.2 rfl) (hi.2.1 rfl))
    · exact ne_of_lt (lt_of_lt_of_le (hi.2.2 rfl) (he.2.1 rfl))
    · exact False.elim (hne rfl)
  have values (w : List Block) : signedValue (leftStream w) = seam w ∧
      signedValue (rightStream w) = seam w := by
    induction w with
    | nil =>
      have hv : signedValue v = b := (signed_series_range.2.2 v).mpr rfl
      constructor
      · change signedValue (prependBlock .zero v) = seam []
        rw [valB, sempty]; exact (edge .zero _ (bounds v)).1.mpr hv
      · change signedValue (prependBlock .oneZero v) = seam []
        rw [valB, sempty]; exact (edge .oneZero _ (bounds v)).1.mpr hv
    | cons c w ih =>
      rw [(lrrec c w).1, (lrrec c w).2, valB, valB, ih.1, ih.2, srec]
      exact ⟨rfl, rfl⟩
  have fibre (w : List Block) (x : LegalDigits) (hx : signedValue x = seam w) :
      x = leftStream w ∨ x = rightStream w := by
    induction w generalizing x with
    | nil =>
      obtain ⟨c, y, rfl⟩ := parse x
      rw [valB, sempty] at hx
      have hy : y = v := (signed_series_range.2.2 y).mp ((edge c _ (bounds y)).1.mp hx)
      subst y; cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    | cons c w ih =>
      obtain ⟨d, y, rfl⟩ := parse x
      rw [valB, srec] at hx
      by_cases hcd : c = d
      · subst d
        rcases ih y (Binj c hx) with h | h
        · exact Or.inl (congrArg (prependBlock c) h)
        · exact Or.inr (congrArg (prependBlock c) h)
      · exact False.elim (separate c d _ _ hcd (smem w) (bounds y) hx.symm)
  have sinj : Function.Injective seam := by
    intro w
    induction w with
    | nil =>
      intro z hz
      cases z with
      | nil => rfl
      | cons d z =>
        rw [sempty, srec] at hz
        have hi := interior d _ (smem z)
        cases d
        · exact False.elim ((ne_of_lt (hi.2.1 rfl)) hz)
        · exact False.elim ((ne_of_gt (hi.2.2 rfl)) hz)
    | cons c w ih =>
      intro z hz
      cases z with
      | nil =>
        rw [sempty, srec] at hz
        have hi := interior c _ (smem w)
        cases c
        · exact False.elim ((ne_of_gt (hi.2.1 rfl)) hz)
        · exact False.elim ((ne_of_lt (hi.2.2 rfl)) hz)
      | cons d z =>
        rw [srec, srec] at hz
        by_cases hcd : c = d
        · subst d; exact congrArg (List.cons c) (ih (Binj c hz))
        · exact False.elim (separate c d _ _ hcd (smem w)
            ⟨(smem z).1.le, (smem z).2.le⟩ hz)
  have different (c d : Block) (x y : LegalDigits) (hcd : c ≠ d)
      (heq : B c (signedValue x) = B d (signedValue y)) : x = v ∧ y = v := by
    have ex := edge c _ (bounds x)
    have ey := edge d _ (bounds y)
    have hq : B c (signedValue x) = q := by
      cases c <;> cases d
      · exact False.elim (hcd rfl)
      · exact le_antisymm (heq.trans_le (ey.2.2 rfl)) (ex.2.1 rfl)
      · exact le_antisymm (ex.2.2 rfl) ((ey.2.1 rfl).trans_eq heq.symm)
      · exact False.elim (hcd rfl)
    exact ⟨(signed_series_range.2.2 x).mp (ex.1.mp hq),
      (signed_series_range.2.2 y).mp (ey.1.mp (heq.symm.trans hq))⟩
  have classify (n : ℕ) (x y : LegalDigits) (hn : x.val n ≠ y.val n)
      (heq : signedValue x = signedValue y) :
      ∃ w : List Block, (x = leftStream w ∧ y = rightStream w) ∨
        (x = rightStream w ∧ y = leftStream w) := by
    induction n using Nat.strong_induction_on generalizing x y with
    | h n ih =>
      obtain ⟨c, x, rfl⟩ := parse x
      obtain ⟨d, y, rfl⟩ := parse y
      rw [valB, valB] at heq
      by_cases hcd : c = d
      · subst d
        have hv := Binj c heq
        have smaller : ∃ k < n, x.val k ≠ y.val k := by
          cases c with
          | zero =>
            cases n with
            | zero => exact False.elim (hn rfl)
            | succ k => exact ⟨k, Nat.lt_succ_self k, hn⟩
          | oneZero =>
            cases n with
            | zero => exact False.elim (hn rfl)
            | succ n => cases n with
              | zero => exact False.elim (hn rfl)
              | succ k => exact ⟨k, by omega, hn⟩
        obtain ⟨k, hk, hxy⟩ := smaller
        obtain ⟨w, hw | hw⟩ := ih k hk x y hxy hv
        · exact ⟨c :: w, Or.inl ⟨congrArg (prependBlock c) hw.1,
            congrArg (prependBlock c) hw.2⟩⟩
        · exact ⟨c :: w, Or.inr ⟨congrArg (prependBlock c) hw.1,
            congrArg (prependBlock c) hw.2⟩⟩
      · obtain ⟨rfl, rfl⟩ := different c d x y hcd heq
        refine ⟨[], ?_⟩
        cases c <;> cases d
        · exact False.elim (hcd rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (hcd rfl)
  refine ⟨fun w => ⟨lrne w, fun x => ⟨fibre w x, ?_⟩⟩, sinj, ?_⟩
  · rintro (rfl | rfl)
    · exact (values w).1
    · exact (values w).2
  · intro t ht hns
    obtain ⟨x, hx⟩ := signed_series_range.1.symm ▸ ht
    refine ⟨x, hx, ?_⟩
    intro y hy
    by_contra hne
    have hdiff : ∃ n, y.val n ≠ x.val n := by
      by_contra h
      push Not at h
      exact hne (Subtype.ext (funext h))
    obtain ⟨n, hn⟩ := hdiff
    obtain ⟨w, hw | hw⟩ := classify n y x hn (hy.trans hx.symm)
    · exact hns ⟨w, (values w).1.symm.trans (hw.1 ▸ hy)⟩
    · exact hns ⟨w, (values w).2.symm.trans (hw.1 ▸ hy)⟩

end D5.S1.Digit.Infinite.SignedSeriesFibres

/- GID: D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal power substitution realizes actual positive pairs at controlled degree. -/

import D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyBracketSpan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution

open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairLeadingCoefficients

variable {A : Type*}

/-- Replace each letter of a word by `m` consecutive literal copies. -/
def literalPowerWord (m : ℕ) (source : List A) : List A := source.flatMap fun a => List.replicate m a
private noncomputable def letterPowerTail (m : ℕ) (a : A) : RationalWordPolynomial A :=
  toRationalWordPolynomial (magnusPolynomial (List.replicate m a)) - 1
private theorem letterPowerTail_coeff_singleton [DecidableEq A]
    (m : ℕ) (a b : A) :
    (letterPowerTail m a).coeff (FreeMonoid.ofList [b]) = if b = a then (m : ℚ) else 0 := by
  have hcount :
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          [b] (List.replicate m a) =
        if b = a then m else 0 := by
    induction m with
    | zero => simp [D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount]
    | succ m ih =>
        rw [List.replicate_succ]
        by_cases h : b = a
        · subst b
          simp only at ih ⊢
          simp [D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount,
            ih]
        · simp [D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount,
            ih, h]
  rw [letterPowerTail]
  have hm := magnusPolynomial_coeff_scatteredCount (List.replicate m a) [b]
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom] at hm ⊢
  rw [hm, hcount]
  have hne : (FreeMonoid.ofList [b] : FreeMonoid A) ≠ 1 := by
    intro h
    have := congrArg FreeMonoid.toList h
    simp at this
  simp [MonoidAlgebra.one_def]
private theorem wordPowerTail_vanishesBelow [Finite A] [DecidableEq A]
    (cutoff m : ℕ) (source : List A) :
    VanishesBelow cutoff source.length (cutoffRestriction cutoff
        ((FreeMonoid.lift (letterPowerTail (A := A) m))
          (FreeMonoid.ofList source))) := by
  induction source with
  | nil =>
      intro w hw
      simp at hw
  | cons a source ih =>
      rw [FreeMonoid.lift_ofList]
      simp only [List.map_cons, List.prod_cons]
      rw [cutoffRestriction_mul]
      simpa [Nat.add_comm] using cutoffMul_vanishesBelow cutoff 1 source.length
        (cutoffRestriction cutoff (letterPowerTail m a))
        (cutoffRestriction cutoff
          ((FreeMonoid.lift (letterPowerTail (A := A) m))
            (FreeMonoid.ofList source)))
        (by
          intro w hw
          have hword : w.1 = 1 := FreeMonoid.toList.injective <|
            List.length_eq_zero_iff.mp (by
              simpa [FreeMonoid.length] using (show FreeMonoid.length w.1 = 0 by omega))
          have hm' : (magnusPolynomial (List.replicate m a)).coeff 1 = 1 := by
            simpa only [FreeMonoid.ofList_nil,
              D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount,
              Nat.cast_one] using magnusPolynomial_coeff_scatteredCount
                (List.replicate m a) ([] : List A)
          rw [cutoffRestriction, hword, letterPowerTail]
          simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
            toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom]
          rw [hm']; norm_num [MonoidAlgebra.one_def]) ih
private theorem wordPowerTail_coeff_sameLength [Finite A] [DecidableEq A]
    (cutoff m : ℕ) (source pattern : List A)
    (hcutoff : source.length ≤ cutoff)
    (hlength : pattern.length = source.length) :
    cutoffRestriction cutoff
        ((FreeMonoid.lift (letterPowerTail (A := A) m))
          (FreeMonoid.ofList source))
        ⟨FreeMonoid.ofList pattern, by
          simpa [FreeMonoid.length, hlength] using hcutoff⟩ =
      if pattern = source then (m : ℚ) ^ source.length else 0 := by
  induction source generalizing pattern cutoff with
  | nil =>
      have hp : pattern = [] := List.length_eq_zero_iff.mp hlength
      subst pattern
      simp [cutoffRestriction]
  | cons a source ih =>
      cases pattern with
      | nil => simp at hlength
      | cons b pattern =>
          have htail : pattern.length = source.length := by simpa using hlength
          rw [FreeMonoid.lift_ofList]
          simp only [List.map_cons, List.prod_cons]
          rw [cutoffRestriction_mul, cutoffMul]
          rw [Finset.sum_eq_single 1]
          · simp only [FreeMonoid.toList_ofList, List.take_succ_cons,
              List.take_zero, List.drop_succ_cons, List.drop_zero,
              FreeMonoid.ofList_singleton]
            simp only [cutoffRestriction]
            rw [← FreeMonoid.lift_ofList]
            change (letterPowerTail m a).coeff (FreeMonoid.ofList [b]) *
                ((FreeMonoid.lift (letterPowerTail (A := A) m))
                  (FreeMonoid.ofList source)).coeff (FreeMonoid.ofList pattern) = _
            rw [letterPowerTail_coeff_singleton]
            have hsourceCutoff : source.length ≤ cutoff :=
              (Nat.le_succ source.length).trans (by simpa using hcutoff)
            have hiCoeff := ih cutoff pattern hsourceCutoff htail
            change ((FreeMonoid.lift (letterPowerTail (A := A) m))
              (FreeMonoid.ofList source)).coeff (FreeMonoid.ofList pattern) = _ at hiCoeff
            rw [hiCoeff]
            by_cases hba : b = a
            · subst b
              by_cases hps : pattern = source
              · subst pattern
                simp [pow_succ']
              · simp [hps]
            · simp [hba]
          · intro i hi hne
            simp only [FreeMonoid.toList_ofList]
            have hi_le : i ≤ (b :: pattern).length := by
              simp only [Finset.mem_range] at hi
              simpa [FreeMonoid.length] using Nat.le_of_lt_succ hi
            by_cases hi0 : i = 0
            · subst i
              have hconstant : VanishesBelow cutoff 1
                  (cutoffRestriction cutoff (letterPowerTail m a)) := by
                intro w hw
                have hword : w.1 = 1 := FreeMonoid.toList.injective <|
                  List.length_eq_zero_iff.mp (by simpa [FreeMonoid.length] using
                    (show FreeMonoid.length w.1 = 0 by omega))
                have hm' : (magnusPolynomial (List.replicate m a)).coeff 1 = 1 := by
                  simpa only [FreeMonoid.ofList_nil,
                    D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount,
                    Nat.cast_one] using magnusPolynomial_coeff_scatteredCount
                      (List.replicate m a) ([] : List A)
                rw [cutoffRestriction, hword, letterPowerTail]
                simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
                  toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom]
                rw [hm']; norm_num [MonoidAlgebra.one_def]
              rw [hconstant]
              · simp
              · simp [FreeMonoid.length]
            · have hi_two : 2 ≤ i := by omega
              rw [← FreeMonoid.lift_ofList]
              change cutoffRestriction cutoff (letterPowerTail m a) _ *
                  cutoffRestriction cutoff
                    ((FreeMonoid.lift (letterPowerTail (A := A) m))
                      (FreeMonoid.ofList source)) _ = 0
              rw [wordPowerTail_vanishesBelow cutoff m source]
              · simp
              · simp only [FreeMonoid.length, FreeMonoid.toList_ofList,
                  List.length_drop]
                have hpat : (b :: pattern).length = source.length + 1 := by
                  simp [htail]
                omega
          · simp
private theorem powerSubstitution_magnus [Finite A] [DecidableEq A]
    (m : ℕ) (source : List A) :
    (MonoidAlgebra.lift ℚ (RationalWordPolynomial A) (FreeMonoid A)
      (FreeMonoid.lift (letterPowerTail m)))
        (toRationalWordPolynomial (magnusPolynomial source)) =
      toRationalWordPolynomial
        (magnusPolynomial (literalPowerWord m source)) := by
  induction source with
  | nil => simp [literalPowerWord, magnusPolynomial]
  | cons a source ih =>
      rw [literalPowerWord, List.flatMap_cons]
      simp only [magnusPolynomial, List.map_append, List.prod_append]
      change (MonoidAlgebra.lift ℚ (RationalWordPolynomial A) (FreeMonoid A)
        (FreeMonoid.lift (letterPowerTail m)))
          (toRationalWordPolynomial
            ((1 + wordMonomial [a]) * magnusPolynomial source)) = _
      simp only [map_mul, map_add, map_one, ih]
      rw [show (MonoidAlgebra.lift ℚ (RationalWordPolynomial A) (FreeMonoid A)
        (FreeMonoid.lift (letterPowerTail m)))
          (toRationalWordPolynomial (wordMonomial [a])) =
          letterPowerTail m a by
        simp [toRationalWordPolynomial, wordMonomial]]
      simp only [letterPowerTail]
      congr 1
      abel
private theorem powerSubstitution_coeff_of_vanishesBelow
    [Finite A] [DecidableEq A] (m r : ℕ)
    (p : RationalWordPolynomial A)
    (hp : ∀ w, FreeMonoid.length w < r → p.coeff w = 0)
    (pattern : List A) (hpattern : pattern.length ≤ r) :
    ((MonoidAlgebra.lift ℚ (RationalWordPolynomial A) (FreeMonoid A)
      (FreeMonoid.lift (letterPowerTail m))) p).coeff (FreeMonoid.ofList pattern) =
      if pattern.length = r then
        (m : ℚ) ^ r * p.coeff (FreeMonoid.ofList pattern)
      else 0 := by
  classical
  rw [MonoidAlgebra.lift_apply]
  change (MonoidAlgebra.coeff
    (p.coeff.sum fun a b => b •
      (FreeMonoid.lift (letterPowerTail (A := A) m)) a))
      (FreeMonoid.ofList pattern) = _
  rw [MonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply]
  rw [Finsupp.sum]
  by_cases heq : pattern.length = r
  · rw [if_pos heq]
    have hsummand (w : FreeMonoid A) (hw : w ∈ p.coeff.support) :
        (p.coeff w • (FreeMonoid.lift
            (letterPowerTail (A := A) m)) w).coeff
              (FreeMonoid.ofList pattern) =
          if w = FreeMonoid.ofList pattern then
            (m : ℚ) ^ r * p.coeff (FreeMonoid.ofList pattern)
          else 0 := by
      have hwge : r ≤ FreeMonoid.length w := by
        by_contra hwlt
        have hzero := hp w (by omega)
        exact (Finsupp.mem_support_iff.mp hw) hzero
      by_cases hwlen : FreeMonoid.length w = r
      · have hlead := wordPowerTail_coeff_sameLength r m
            (FreeMonoid.toList w) pattern
            (by simpa [FreeMonoid.length] using hwlen.le)
            (by rw [heq, ← hwlen]; simp [FreeMonoid.length])
        change p.coeff w *
            ((FreeMonoid.lift (letterPowerTail (A := A) m)) w).coeff
              (FreeMonoid.ofList pattern) = _
        have hlead' :
            ((FreeMonoid.lift (letterPowerTail (A := A) m)) w).coeff
                (FreeMonoid.ofList pattern) =
              if pattern = FreeMonoid.toList w then
                (m : ℚ) ^ (FreeMonoid.toList w).length else 0 := by
          simpa only [cutoffRestriction, FreeMonoid.ofList_toList] using hlead
        rw [hlead']
        by_cases hwp : w = FreeMonoid.ofList pattern
        · subst w
          simp [heq, mul_comm]
        · have hlist : pattern ≠ FreeMonoid.toList w := by
            intro h
            apply hwp
            rw [show w = FreeMonoid.ofList (FreeMonoid.toList w) by
              exact (FreeMonoid.ofList_toList w).symm, ← h]
          simp [hwp, hlist]
      · have hwgt : r < FreeMonoid.length w := by omega
        have hvan := wordPowerTail_vanishesBelow r m (FreeMonoid.toList w)
        have hzero := hvan
          ⟨FreeMonoid.ofList pattern, by simpa [FreeMonoid.length, heq]⟩
          (by simpa [FreeMonoid.length, heq] using hwgt)
        change p.coeff w *
            ((FreeMonoid.lift (letterPowerTail (A := A) m)) w).coeff
              (FreeMonoid.ofList pattern) = _
        have hzero' :
            ((FreeMonoid.lift (letterPowerTail (A := A) m)) w).coeff
                (FreeMonoid.ofList pattern) = 0 := by
          simpa only [cutoffRestriction, FreeMonoid.ofList_toList] using hzero
        have hwp : w ≠ FreeMonoid.ofList pattern := by
          intro h
          subst w
          simp [FreeMonoid.length, heq] at hwgt
        simp [hzero', hwp]
    calc
      ∑ w ∈ p.coeff.support,
          (p.coeff w • (FreeMonoid.lift
            (letterPowerTail (A := A) m)) w).coeff
              (FreeMonoid.ofList pattern) =
          ∑ w ∈ p.coeff.support,
            if w = FreeMonoid.ofList pattern then
              (m : ℚ) ^ r * p.coeff (FreeMonoid.ofList pattern)
            else 0 := Finset.sum_congr rfl hsummand
      _ = (m : ℚ) ^ r * p.coeff (FreeMonoid.ofList pattern) := by
        by_cases hmem : FreeMonoid.ofList pattern ∈ p.coeff.support
        · simp [hmem]
        · have hzero := Finsupp.notMem_support_iff.mp hmem
          simp [hzero]
  · rw [if_neg heq]
    have hlt : pattern.length < r := by omega
    apply Finset.sum_eq_zero
    intro w hw
    have hwge : r ≤ FreeMonoid.length w := by
      by_contra hwlt
      have hzero := hp w (by omega)
      exact (Finsupp.mem_support_iff.mp hw) hzero
    have hvan := wordPowerTail_vanishesBelow r m (FreeMonoid.toList w)
    have hzero := hvan
      ⟨FreeMonoid.ofList pattern, by simpa [FreeMonoid.length] using hpattern⟩
      (by simpa [FreeMonoid.length] using lt_of_lt_of_le hlt hwge)
    change p.coeff w *
        ((FreeMonoid.lift (letterPowerTail (A := A) m)) w).coeff
          (FreeMonoid.ofList pattern) = 0
    have hzero' :
        ((FreeMonoid.lift (letterPowerTail (A := A) m)) w).coeff
            (FreeMonoid.ofList pattern) = 0 := by
      simpa only [cutoffRestriction, FreeMonoid.ofList_toList] using hzero
    simp [hzero']
/-- Literal `m`-copy substitution preserves lower scattered coefficients and
scales the first possible unequal degree by `m^r`, including degenerate levels. -/
theorem literalPowerSubstitution_actual_positivePair
    [Finite A] [DecidableEq A] (m r : ℕ)
    (index : PositivePairIndex A r) :
    let pair := positivePairWords r index
    let powered :=
      (literalPowerWord m pair.1, literalPowerWord m pair.2)
    powered.1.length = pair.1.length * m ∧
      powered.2.length = pair.2.length * m ∧
      (2 ≤ r → powered.1.length = powered.2.length) ∧
      (0 < m → 2 ≤ r → powered.1 ≠ [] ∧ powered.2 ≠ []) ∧
      (∀ pattern : List A, pattern.length < r →
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern powered.1 =
          D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern powered.2) ∧
      ∀ pattern : List A, pattern.length = r →
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern powered.1 : ℚ) -
          (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern powered.2 : ℚ) =
        (m : ℚ) ^ r *
          ((D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              pattern pair.1 : ℚ) -
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              pattern pair.2 : ℚ)) := by
  classical
  dsimp only
  let pair := positivePairWords r index
  let powered := (literalPowerWord m pair.1, literalPowerWord m pair.2)
  have hlength (source : List A) :
      (literalPowerWord m source).length = source.length * m := by
    induction source with
    | nil => simp [literalPowerWord]
    | cons a source ih => simp [literalPowerWord, Nat.add_mul, Nat.add_comm]
  have hpair (hr : 2 ≤ r) :
      (positivePairWords r index).1 ≠ [] ∧
      (positivePairWords r index).2 ≠ [] ∧
      (positivePairWords r index).1.length =
        (positivePairWords r index).2.length := by
    obtain ⟨level, rfl⟩ : ∃ level, r = level + 2 := ⟨r - 2, by omega⟩
    simp only [positivePairWords]
    let previous := positivePairWords (level + 1) (Fin.init index)
    let a := index (Fin.last (level + 1))
    change previous.1 ++ [a] ++ previous.2 ≠ [] ∧
      previous.2 ++ [a] ++ previous.1 ≠ [] ∧
      (previous.1 ++ [a] ++ previous.2).length =
        (previous.2 ++ [a] ++ previous.1).length
    simp only [List.length_append, List.length_singleton]
    exact ⟨by simp, by simp, by omega⟩
  let p : RationalWordPolynomial A := toRationalWordPolynomial
    (magnusPolynomial pair.1 - magnusPolynomial pair.2)
  have hp : ∀ w, FreeMonoid.length w < r → p.coeff w = 0 := by
    intro w hw
    have hfiltration := (full_positivePair_ratio_filtration r r index).1
      ⟨w, Nat.le_of_lt hw⟩ hw
    simpa [p, pair, cutoffMagnus, cutoffRestriction] using hfiltration
  have hmap : (MonoidAlgebra.lift ℚ (RationalWordPolynomial A) (FreeMonoid A)
      (FreeMonoid.lift (letterPowerTail m))) p =
      toRationalWordPolynomial (magnusPolynomial powered.1 - magnusPolynomial powered.2) := by
    simp only [p, map_sub, powerSubstitution_magnus]
    rfl
  have coeffDifference (left right pattern : List A) :
      (toRationalWordPolynomial (magnusPolynomial left - magnusPolynomial right)).coeff
          (FreeMonoid.ofList pattern) =
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern left : ℚ) -
          (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern right : ℚ) := by
    simp only [toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom,
      map_sub, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      magnusPolynomial_coeff_scatteredCount]
    norm_num
  refine ⟨hlength pair.1, hlength pair.2, ?_, ?_, ?_, ?_⟩
  · intro hr
    simpa only [hlength] using
      congrArg (fun n => n * m) (hpair hr).2.2
  · intro hm hr
    obtain ⟨hleft, hright, _⟩ := hpair hr
    refine ⟨?_, ?_⟩
    · apply List.ne_nil_of_length_pos
      rw [hlength]
      exact Nat.mul_pos (List.length_pos_of_ne_nil hleft) hm
    · apply List.ne_nil_of_length_pos
      rw [hlength]
      exact Nat.mul_pos (List.length_pos_of_ne_nil hright) hm
  · intro pattern hpattern
    have hcoeff := powerSubstitution_coeff_of_vanishesBelow m r p hp pattern
      (Nat.le_of_lt hpattern)
    rw [if_neg (Nat.ne_of_lt hpattern)] at hcoeff
    rw [hmap, coeffDifference] at hcoeff
    exact_mod_cast sub_eq_zero.mp hcoeff
  · intro pattern hpattern
    have hcoeff := powerSubstitution_coeff_of_vanishesBelow m r p hp pattern
      (by omega)
    rw [if_pos hpattern] at hcoeff
    rw [hmap, coeffDifference, coeffDifference] at hcoeff
    exact hcoeff

end D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution

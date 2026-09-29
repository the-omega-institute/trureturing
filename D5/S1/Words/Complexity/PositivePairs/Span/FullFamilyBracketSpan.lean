/- GID: D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual full-family differences span every rational Lyndon standard bracket. -/

import D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyBracketSpan

open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization
open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyHomogeneity
open private actualLeadingDifference_one actualLeadingDifference_successor from
  D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyHomogeneity

variable {A : Type*}

private theorem generator_right_letter_mem [Finite A] [LinearOrder A]
    (r : ℕ) (index : PositivePairIndex A (r + 1)) (b : A) :
    ⁅actualLeadingDifference (r + 1) index,
      toRationalWordPolynomial (wordMonomial [b])⁆ ∈
      fullFamilySpan (A := A) (r + 2) := by
  classical
  let pair := positivePairWords (r + 1) index
  let v := pair.2
  let p := actualLeadingDifference (r + 1) index
  let u := toRationalWordPolynomial (wordAbelianization v)
  let letter : A → RationalWordPolynomial A :=
    fun a => toRationalWordPolynomial (wordMonomial [a])
  let bracketRight : RationalWordPolynomial A →ₗ[ℚ] RationalWordPolynomial A :=
    { toFun := fun q => ⁅p, q⁆
      map_add' := by
        intro q s
        simp [Ring.lie_def, mul_add, add_mul]
        abel
      map_smul' := by
        intro c q
        simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm,
          RingHom.id_apply, smul_sub] }
  let y : A → RationalWordPolynomial A :=
    fun a => bracketRight (u + letter a)
  have hy (a : A) : y a ∈ fullFamilySpan (A := A) (r + 2) := by
    have hgenerator : actualLeadingDifference (r + 2) (Fin.snoc index a) ∈
        fullFamilySpan (A := A) (r + 2) := by
      apply Submodule.subset_span
      exact ⟨Fin.snoc index a, rfl⟩
    rw [actualLeadingDifference_successor r (Fin.snoc index a)] at hgenerator
    simp only [Fin.init_snoc, Fin.snoc_last] at hgenerator
    change ⁅p,
      toRationalWordPolynomial (wordAbelianization v + wordMonomial [a])⁆ ∈
        fullFamilySpan (A := A) (r + 2) at hgenerator
    have hlinear :
        toRationalWordPolynomial (wordAbelianization v + wordMonomial [a]) =
          u + letter a := by
      simp [u, letter]
    rw [hlinear] at hgenerator
    exact hgenerator
  have hsumMem : (v.map y).sum ∈ fullFamilySpan (A := A) (r + 2) := by
    induction v with
    | nil => simp
    | cons a tail ih =>
        simpa using (fullFamilySpan (A := A) (r + 2)).add_mem (hy a) ih
  have hab : (v.map letter).sum = u := by
    have hsum : toRationalWordPolynomial (wordAbelianization v) =
        (v.map fun a =>
          toRationalWordPolynomial (wordMonomial [a])).sum := by
      induction v with
      | nil => simp [wordAbelianization]
      | cons a tail ih =>
          change toRationalWordPolynomial
            (wordMonomial [a] + wordAbelianization tail) = _
          simp [map_add, ih]
    simpa [u, letter] using hsum.symm
  have hsum : (v.map y).sum =
      ((v.length + 1 : ℕ) : ℚ) • ⁅p, u⁆ := by
    rw [show (v.map y).sum =
        (v.length : ℚ) • ⁅p, u⁆ + ⁅p, (v.map letter).sum⁆ by
      change (v.map fun a => bracketRight (u + letter a)).sum =
        (v.length : ℚ) • bracketRight u + bracketRight (v.map letter).sum
      calc
        _ = bracketRight ((v.map fun a => u + letter a).sum) := by
          symm
          simpa [List.map_map, Function.comp_def] using
            map_list_sum bracketRight.toAddMonoidHom
              (v.map fun a => u + letter a)
        _ = bracketRight
            ((v.map fun _ => u).sum + (v.map letter).sum) := by
          rw [List.sum_map_add]
        _ = bracketRight ((v.length : ℚ) • u) +
            bracketRight (v.map letter).sum := by
          rw [show (v.map fun _ => u).sum = (v.length : ℚ) • u by
            simp [Algebra.smul_def], bracketRight.map_add]
        _ = _ := by rw [bracketRight.map_smul], hab]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  have huMem : ⁅p, u⁆ ∈
      fullFamilySpan (A := A) (r + 2) := by
    let n : ℚ := ((v.length + 1 : ℕ) : ℚ)
    have hn : n ≠ 0 := by
      positivity
    have hinv : n⁻¹ • (v.map y).sum = ⁅p, u⁆ := by
      rw [hsum, smul_smul]
      change (n⁻¹ * n) • ⁅p, u⁆ = _
      rw [inv_mul_cancel₀ hn, one_smul]
    rw [← hinv]
    exact (fullFamilySpan (A := A) (r + 2)).smul_mem n⁻¹ hsumMem
  have hyb := hy b
  have hsplit : y b = ⁅p, u⁆ + ⁅p, letter b⁆ := by
    change bracketRight (u + letter b) =
      bracketRight u + bracketRight (letter b)
    exact bracketRight.map_add u (letter b)
  rw [hsplit] at hyb
  have := (fullFamilySpan (A := A) (r + 2)).sub_mem hyb huMem
  simpa [p, letter, y] using this

private theorem fullFamilySpan_bracket_standard [Finite A] [LinearOrder A]
    (m : ℕ) (hm : 1 ≤ m) {p : RationalWordPolynomial A}
    (hp : p ∈ fullFamilySpan (A := A) m) (w : List A) :
    ⁅p, toRationalWordPolynomial (standardBracket w)⁆ ∈
      fullFamilySpan (A := A) (m + w.length) := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w m p with
  | h n ih =>
      subst n
      cases w with
      | nil =>
          simp [standardBracket, Ring.lie_def]
      | cons a tail =>
          cases tail with
          | nil =>
              obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
              have hright : ⁅p,
                    toRationalWordPolynomial (wordMonomial [a])⁆ ∈
                  fullFamilySpan (A := A) (r + 2) := by
                induction hp using Submodule.span_induction with
                | mem p hp =>
                    rcases hp with ⟨index, rfl⟩
                    exact generator_right_letter_mem r index a
                | zero =>
                    simpa [Ring.lie_def] using
                      (Submodule.zero_mem
                        (fullFamilySpan (A := A) (r + 2)))
                | add p q _ _ hp hq =>
                    have hleft : ⁅p + q,
                        toRationalWordPolynomial (wordMonomial [a])⁆ =
                          ⁅p, toRationalWordPolynomial (wordMonomial [a])⁆ +
                            ⁅q, toRationalWordPolynomial (wordMonomial [a])⁆ := by
                      simp [Ring.lie_def, mul_add, add_mul]
                      abel
                    rw [hleft]
                    exact Submodule.add_mem _ hp hq
                | smul c p _ hp =>
                    have hsmul : ⁅c • p,
                        toRationalWordPolynomial (wordMonomial [a])⁆ =
                          c • ⁅p, toRationalWordPolynomial (wordMonomial [a])⁆ := by
                      simp only [Ring.lie_def, smul_mul_assoc,
                        mul_smul_comm]
                      rw [smul_sub]
                    rw [hsmul]
                    exact Submodule.smul_mem _ c hp
              simpa [standardBracket] using hright
          | cons b tail =>
              let w := a :: b :: tail
              let htwo : 2 ≤ w.length := by simp [w]
              let left := standardLeft w htwo
              let right := standardRight w htwo
              have hcut := @Nat.find_spec _ (Classical.decPred _)
                (exists_lyndon_suffix_cut w htwo)
              change 0 < standardCut w htwo ∧ standardCut w htwo < w.length ∧
                IsLyndon (w.drop (standardCut w htwo)) at hcut
              have hleft : left.length < w.length := by
                simp only [left, standardLeft, List.length_take]
                omega
              have hright : right.length < w.length := by
                simp only [right, standardRight, List.length_drop]
                omega
              have hleftPos : 1 ≤ left.length := by
                simp only [left, standardLeft, List.length_take]
                omega
              have hrightPos : 1 ≤ right.length := by
                simp only [right, standardRight, List.length_drop]
                omega
              have hfactor := congrArg List.length (show
                standardLeft w htwo ++ standardRight w htwo = w by
                  simpa [standardLeft, standardRight] using
                    List.take_append_drop (standardCut w htwo) w)
              simp only [List.length_append] at hfactor
              change left.length + right.length = w.length at hfactor
              have hpLeft : ⁅p,
                    toRationalWordPolynomial (standardBracket left)⁆ ∈
                  fullFamilySpan (A := A) (m + left.length) :=
                ih left.length hleft m hm hp left rfl
              have hpRight : ⁅p,
                    toRationalWordPolynomial (standardBracket right)⁆ ∈
                  fullFamilySpan (A := A) (m + right.length) :=
                ih right.length hright m hm hp right rfl
              have hleftRight : ⁅
                    ⁅p, toRationalWordPolynomial (standardBracket left)⁆,
                    toRationalWordPolynomial (standardBracket right)⁆ ∈
                  fullFamilySpan (A := A) (m + w.length) := by
                have hrec := ih right.length hright (m + left.length)
                  (by omega)
                  hpLeft right rfl
                simpa [hfactor, Nat.add_assoc] using hrec
              have hrightLeft : ⁅
                    ⁅p, toRationalWordPolynomial (standardBracket right)⁆,
                    toRationalWordPolynomial (standardBracket left)⁆ ∈
                  fullFamilySpan (A := A) (m + w.length) := by
                have hrec := ih left.length hleft (m + right.length)
                  (by omega)
                  hpRight left rfl
                simpa [hfactor, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec
              rw [standardBracket]
              have hmap :
                  toRationalWordPolynomial
                      (LyndonBrackets.LyndonBracketAlgebra.commutator
                        (standardBracket left) (standardBracket right)) =
                    ⁅toRationalWordPolynomial (standardBracket left),
                      toRationalWordPolynomial (standardBracket right)⁆ := by
                simp [LyndonBrackets.LyndonBracketAlgebra.commutator, Ring.lie_def]
              rw [hmap]
              have hjac : ⁅p,
                    ⁅toRationalWordPolynomial (standardBracket left),
                      toRationalWordPolynomial (standardBracket right)⁆⁆ =
                  ⁅⁅p, toRationalWordPolynomial (standardBracket left)⁆,
                      toRationalWordPolynomial (standardBracket right)⁆ -
                    ⁅⁅p, toRationalWordPolynomial (standardBracket right)⁆,
                      toRationalWordPolynomial (standardBracket left)⁆ := by
                simp only [Ring.lie_def]
                noncomm_ring
              rw [hjac]
              exact Submodule.sub_mem _ hleftRight hrightLeft

theorem every_standardBracket_mem [Finite A] [LinearOrder A]
    (w : List A) :
    toRationalWordPolynomial (standardBracket w) ∈
      fullFamilySpan (A := A) w.length := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil =>
          simp [standardBracket]
      | cons a tail =>
          cases tail with
          | nil =>
              let index : PositivePairIndex A 1 := fun _ => a
              have hgenerator : actualLeadingDifference 1 index ∈
                  fullFamilySpan (A := A) 1 := by
                apply Submodule.subset_span
                exact ⟨index, rfl⟩
              rw [actualLeadingDifference_one] at hgenerator
              simpa [index, standardBracket] using hgenerator
          | cons b tail =>
              let w := a :: b :: tail
              let htwo : 2 ≤ w.length := by simp [w]
              let left := standardLeft w htwo
              let right := standardRight w htwo
              have hcut := @Nat.find_spec _ (Classical.decPred _)
                (exists_lyndon_suffix_cut w htwo)
              change 0 < standardCut w htwo ∧ standardCut w htwo < w.length ∧
                IsLyndon (w.drop (standardCut w htwo)) at hcut
              have hleft : left.length < w.length := by
                simp only [left, standardLeft, List.length_take]
                omega
              have hright : right.length < w.length := by
                simp only [right, standardRight, List.length_drop]
                omega
              have hleftPos : 1 ≤ left.length := by
                simp only [left, standardLeft, List.length_take]
                omega
              have hfactor := congrArg List.length (show
                standardLeft w htwo ++ standardRight w htwo = w by
                  simpa [standardLeft, standardRight] using
                    List.take_append_drop (standardCut w htwo) w)
              simp only [List.length_append] at hfactor
              change left.length + right.length = w.length at hfactor
              have hleftSpan : toRationalWordPolynomial (standardBracket left) ∈
                  fullFamilySpan (A := A) left.length :=
                ih left.length hleft left rfl
              have hcomm := fullFamilySpan_bracket_standard left.length hleftPos
                hleftSpan right
              rw [standardBracket]
              have hmap :
                  toRationalWordPolynomial
                      (LyndonBrackets.LyndonBracketAlgebra.commutator
                        (standardBracket left) (standardBracket right)) =
                    ⁅toRationalWordPolynomial (standardBracket left),
                      toRationalWordPolynomial (standardBracket right)⁆ := by
                simp [LyndonBrackets.LyndonBracketAlgebra.commutator, Ring.lie_def]
              rw [hmap]
              change ⁅toRationalWordPolynomial (standardBracket left),
                toRationalWordPolynomial (standardBracket right)⁆ ∈
                  fullFamilySpan (A := A) w.length
              simpa [hfactor] using hcomm


end D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyBracketSpan

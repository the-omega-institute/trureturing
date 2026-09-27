/- GID: D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Lyndon words index independent directions in the full positive-pair family. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketLeading
import D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyBracketSpan
import Mathlib.Data.List.Indexes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections

open scoped BigOperators
open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketLeading
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyHomogeneity
open D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyBracketSpan

variable {A : Type*}

def ActualLyndonWord (A : Type*) [LinearOrder A] (r : ℕ) :=
  {w : List A // w.length = r ∧ IsLyndon w}

noncomputable instance [LinearOrder A] (r : ℕ) :
    LinearOrder (ActualLyndonWord A r) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

noncomputable instance [Fintype A] [LinearOrder A] (r : ℕ) :
    Fintype (ActualLyndonWord A r) := by
  let intoVector : ActualLyndonWord A r → List.Vector A r :=
    fun w ↦ ⟨w.1, w.2.1⟩
  exact Fintype.ofInjective intoVector (fun x y h ↦
    Subtype.ext (congrArg (fun z : List.Vector A r ↦ z.1) h))

/-- The actual number of Lyndon words of length `r`. -/
noncomputable def actualLyndonCount [Fintype A] [LinearOrder A] (r : ℕ) : ℕ :=
  Fintype.card (ActualLyndonWord A r)

private theorem exists_actual_independent_directions
    [Fintype A] [LinearOrder A] (r : ℕ) :
    ∃ select : Fin (actualLyndonCount (A := A) r) → PositivePairIndex A r,
      LinearIndependent ℚ (fun i ↦ actualLeadingDifference r (select i)) := by
  classical
  have hRationalLI : LinearIndependent ℚ
      (fun w : ActualLyndonWord A r ↦
        toRationalWordPolynomial (standardBracket w.1)) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    by_contra hgi
    let t := s.filter (fun j ↦ g j ≠ 0)
    have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
    let m := t.min' ht
    have hm : m ∈ t := Finset.min'_mem t ht
    have hms : m ∈ s := (Finset.mem_filter.mp hm).1
    have hmg : g m ≠ 0 := (Finset.mem_filter.mp hm).2
    have hcoeff := congrArg
      (fun p : RationalWordPolynomial A ↦ p.coeff (FreeMonoid.ofList m.1)) hsum
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at hcoeff
    have hself :
        (toRationalWordPolynomial (standardBracket m.1)).coeff
            (FreeMonoid.ofList m.1) = 1 := by
      simp only [toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom]
      norm_num [(standardBracket_hasLeadingWord m.1
        (isLyndon_standardFactorClosed m.1 m.2.2)).2.1]
    have hother : ∀ j ∈ s, j ≠ m →
        g j • (toRationalWordPolynomial (standardBracket j.1)).coeff
          (FreeMonoid.ofList m.1) = 0 := by
      intro j hjs hjm
      by_cases hgj : g j = 0
      · simp [hgj]
      have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
      have hmj : m < j :=
        lt_of_le_of_ne (Finset.min'_le t j hjt) (Ne.symm hjm)
      change m.1 < j.1 at hmj
      have hcoeff0 :
          (standardBracket j.1).coeff (FreeMonoid.ofList m.1) = 0 := by
        rw [← Finsupp.notMem_support_iff]
        intro hmem
        have hjmle : j.1 ≤ m.1 :=
          (standardBracket_hasLeadingWord j.1
            (isLyndon_standardFactorClosed j.1 j.2.2)).2.2 _ hmem
        exact (not_lt_of_ge hjmle) hmj
      simp [toRationalWordPolynomial, hcoeff0]
    rw [Finset.sum_eq_single m hother (fun hmnot ↦ (hmnot hms).elim),
      hself] at hcoeff
    exact hmg (by simpa using hcoeff)
  let generators : Set (RationalWordPolynomial A) :=
    Set.range (actualLeadingDifference (A := A) r)
  let V := Submodule.span ℚ generators
  let lyndonInV : ActualLyndonWord A r → V := fun w ↦
    ⟨toRationalWordPolynomial (standardBracket w.1),
      by
        change toRationalWordPolynomial (standardBracket w.1) ∈
          fullFamilySpan (A := A) r
        have h := every_standardBracket_mem (A := A) w.1
        have heq : fullFamilySpan (A := A) w.1.length =
            fullFamilySpan (A := A) r := congrArg _ w.2.1
        exact heq ▸ h⟩
  have hL : LinearIndependent ℚ lyndonInV := by
    apply LinearIndependent.of_comp (Submodule.subtype V)
    change LinearIndependent ℚ
      (fun w : ActualLyndonWord A r ↦
        toRationalWordPolynomial (standardBracket w.1))
    exact hRationalLI
  letI : Module.Finite ℚ V := by
    dsimp only [V]
    exact Module.Finite.span_of_finite ℚ (Set.finite_range _)
  have hcount : actualLyndonCount (A := A) r ≤ Module.finrank ℚ V := by
    simpa [actualLyndonCount] using hL.fintype_card_le_finrank
  obtain ⟨basisSet, hbasisSubset, hbasisCard, _, hbasisLI⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℚ generators
  obtain ⟨chosen, hchosenSubset, hchosenCard⟩ :=
    Finset.exists_subset_card_eq
      (s := basisSet) (n := actualLyndonCount (A := A) r)
      (by simpa [hbasisCard, V] using hcount)
  let enumerate : Fin (actualLyndonCount (A := A) r) ≃ chosen :=
    (Finset.equivFinOfCardEq hchosenCard).symm
  have hchosenLI :
      LinearIndependent ℚ ((↑) : chosen → RationalWordPolynomial A) :=
    hbasisLI.mono (by
      intro x hx
      exact hchosenSubset hx)
  choose preimage hpreimage using fun i : Fin (actualLyndonCount (A := A) r) ↦
    hbasisSubset (hchosenSubset (enumerate i).2)
  refine ⟨preimage, ?_⟩
  have henum : LinearIndependent ℚ
      (fun i ↦ ((enumerate i : chosen) : RationalWordPolynomial A)) :=
    hchosenLI.comp (fun i ↦ enumerate i) enumerate.injective
  have heq :
      (fun i ↦ ((enumerate i : chosen) : RationalWordPolynomial A)) =
        (fun i ↦ actualLeadingDifference r (preimage i)) := by
    funext i
    exact (hpreimage i).symm
  rw [heq] at henum
  exact henum

/-- Deterministic classical selection of independent directions from the full
actual indexed positive-pair family. -/
noncomputable def selectedDirection [Fintype A] [LinearOrder A] (r : ℕ) :
    Fin (actualLyndonCount (A := A) r) → PositivePairIndex A r :=
  Classical.choose (exists_actual_independent_directions (A := A) r)

end D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections

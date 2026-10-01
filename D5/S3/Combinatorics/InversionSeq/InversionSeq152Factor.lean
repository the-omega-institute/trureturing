/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Factor
   mirror-E: none(waiver:unique-dyck-run-factorization)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Unique Dyck run factorizations preserve size and complete ascent-run statistics. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Factor

open DyckStep
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse

def ascentWord (factors : List DyckWord) : DyckWord :=
  factors.foldl (fun inner next => inner.nest + next) 0

def descentWord (factors : List DyckWord) : DyckWord :=
  factors.foldr (fun next inner => next + inner.nest) 0

def ascentFactors (path : DyckWord) : List DyckWord :=
  if _h : path = 0 then [] else ascentFactors path.insidePart ++ [path.outsidePart]
termination_by path.semilength
decreasing_by exact DyckWord.semilength_insidePart_lt _h

theorem runFactorization :
    ∃ ascent descent : List DyckWord ≃ DyckWord,
      (∀ factors, ascent factors = ascentWord factors ∧
        (ascent factors).toList = List.replicate factors.length U ++
          (factors.map (fun path => D :: path.toList)).flatten ∧
        ((ascent factors).toList.takeWhile (· == U)).length = factors.length ∧
        (ascent factors).semilength =
          factors.length + (factors.map DyckWord.semilength).sum ∧
        (((ascent factors).toList.splitOn D).map List.length).filter (· != 0) =
          (if factors = [] then [] else [factors.length]) ++
            factors.flatMap (fun path =>
              ((path.toList.splitOn D).map List.length).filter (· != 0))) ∧
      (∀ factors, descent factors = descentWord factors ∧
        (descent factors).toList =
          (factors.map (fun path => path.toList ++ [U])).flatten ++
            List.replicate factors.length D ∧
        ((descent factors).toList.reverse.takeWhile (· == D)).length = factors.length ∧
        (descent factors).semilength =
          factors.length + (factors.map DyckWord.semilength).sum) ∧
      (∀ path, ascent.symm path = ascentFactors path) ∧
      (∀ path, descent.symm path =
        ((ascentFactors (reflection path)).reverse.map reflection)) := by
  have hzero : (0 : DyckWord).toList = [] := rfl
  have happend (factors : List DyckWord) (next : DyckWord) :
      ascentWord (factors ++ [next]) = (ascentWord factors).nest + next := by
    simp [ascentWord, List.foldl_append]
  have hnonzero (inner next : DyckWord) : inner.nest + next ≠ 0 := by
    intro h
    have hh := congrArg DyckWord.toList h
    change ([U] ++ inner.toList ++ [D] ++ next.toList) = [] at hh
    simp at hh
  have hparse : ∀ factors : List DyckWord, ascentFactors (ascentWord factors) = factors := by
    intro factors
    induction factors using List.reverseRecOn with
    | nil => simp [ascentWord, ascentFactors]
    | append_singleton factors next ih =>
      rw [happend, ascentFactors, dif_neg (hnonzero _ _)]
      simp only [DyckWord.insidePart_add DyckWord.nest_ne_zero,
        DyckWord.insidePart_nest, DyckWord.outsidePart_add DyckWord.nest_ne_zero,
        DyckWord.outsidePart_nest, zero_add, ih]
  have hreconstruct : ∀ bound : ℕ, ∀ path : DyckWord, path.semilength = bound →
      ascentWord (ascentFactors path) = path := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro path hsize
      by_cases hp : path = 0
      · subst path
        simp [ascentFactors, ascentWord]
      · rw [ascentFactors, dif_neg hp, happend]
        have hlt : path.insidePart.semilength < bound := by
          rw [← hsize]
          exact DyckWord.semilength_insidePart_lt hp
        rw [ih _ hlt path.insidePart rfl]
        exact DyckWord.nest_insidePart_add_outsidePart hp
  have hstopU : ∀ steps following : List DyckStep,
      (steps ++ D :: following).takeWhile (· == U) = steps.takeWhile (· == U) := by
    intro steps
    induction steps with
    | nil => intro following; simp
    | cons step rest ih => intro following; cases step <;> simp [ih]
  have hstopD : ∀ steps following : List DyckStep,
      (steps ++ U :: following).takeWhile (· == D) = steps.takeWhile (· == D) := by
    intro steps
    induction steps with
    | nil => intro following; simp
    | cons step rest ih => intro following; cases step <;> simp [ih]
  have hfirst : ∀ factors : List DyckWord,
      (ascentWord factors).toList = List.replicate factors.length U ++
        (factors.map (fun path => D :: path.toList)).flatten ∧
      ((ascentWord factors).toList.takeWhile (· == U)).length = factors.length ∧
      (ascentWord factors).semilength =
        factors.length + (factors.map DyckWord.semilength).sum := by
    intro factors
    induction factors using List.reverseRecOn with
    | nil => simp [ascentWord, hzero]
    | append_singleton factors next ih =>
      rw [happend]
      refine ⟨?_, ?_, ?_⟩
      · change [U] ++ (ascentWord factors).toList ++ [D] ++ next.toList = _
        rw [ih.1]
        simp [List.replicate_succ, List.append_assoc]
      · change (([U] ++ (ascentWord factors).toList ++ [D] ++ next.toList).takeWhile
            (· == U)).length = (factors ++ [next]).length
        simp [List.append_assoc, hstopU, ih.2.1]
      · simp only [DyckWord.semilength_add, DyckWord.semilength_nest, ih.2.2,
          List.length_append, List.length_singleton, List.map_append, List.map_cons,
          List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
        omega
  have hsplitBlocks : ∀ factors : List DyckWord, ∀ initial : List DyckStep,
      (initial ++ (factors.map (fun path => D :: path.toList)).flatten).splitOn D =
        initial.splitOn D ++ factors.flatMap (fun path => path.toList.splitOn D) := by
    intro factors
    induction factors with
    | nil => intro initial; simp
    | cons next factors ih =>
      intro initial
      simp only [List.map_cons, List.flatten_cons, List.cons_append, List.flatMap_cons]
      rw [List.splitOn_append_cons_self, ih]
  have hascentRuns (factors : List DyckWord) :
      (((ascentWord factors).toList.splitOn D).map List.length).filter (· != 0) =
        (if factors = [] then [] else [factors.length]) ++
          factors.flatMap (fun path =>
            ((path.toList.splitOn D).map List.length).filter (· != 0)) := by
    rw [(hfirst factors).1, hsplitBlocks]
    rw [List.splitOn_eq_singleton (by simp)]
    simp only [List.map_append, List.map_cons, List.map_nil, List.length_replicate,
      List.map_flatMap, List.filter_append, List.filter_flatMap]
    cases factors <;> simp
  have hlast : ∀ factors : List DyckWord,
      (descentWord factors).toList =
        (factors.map (fun path => path.toList ++ [U])).flatten ++
          List.replicate factors.length D ∧
      ((descentWord factors).toList.reverse.takeWhile (· == D)).length = factors.length ∧
      (descentWord factors).semilength =
        factors.length + (factors.map DyckWord.semilength).sum := by
    intro factors
    induction factors with
    | nil => simp [descentWord, hzero]
    | cons next factors ih =>
      change (next + (descentWord factors).nest).toList = _ ∧ _ ∧ _
      refine ⟨?_, ?_, ?_⟩
      · change next.toList ++ ([U] ++ (descentWord factors).toList ++ [D]) = _
        rw [ih.1]
        simp [List.replicate_succ', List.append_assoc]
      · change ((next.toList ++ ([U] ++ (descentWord factors).toList ++ [D])).reverse
            |>.takeWhile (· == D)).length = (next :: factors).length
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, List.append_assoc]
        simp [hstopD, ih.2.1]
      · change (next + (descentWord factors).nest).semilength = _
        simp only [DyckWord.semilength_add, DyckWord.semilength_nest, ih.2.2,
          List.length_cons, List.map_cons, List.sum_cons]
        omega
  let exchange : DyckStep → DyckStep
    | U => D
    | D => U
  have hreflectList (path : DyckWord) :
      (reflection path).toList = path.toList.reverse.map exchange := rfl
  have hreflectTwice (path : DyckWord) : reflection (reflection path) = path :=
    reflection.left_inv path
  have hreflectAdd (first second : DyckWord) :
      reflection (first + second) = reflection second + reflection first := by
    apply DyckWord.ext
    change ((first.toList ++ second.toList).reverse.map exchange) =
      second.toList.reverse.map exchange ++ first.toList.reverse.map exchange
    simp
  have hreflectNest (path : DyckWord) : reflection path.nest = (reflection path).nest := by
    apply DyckWord.ext
    change (([U] ++ path.toList ++ [D]).reverse.map exchange) =
      [U] ++ path.toList.reverse.map exchange ++ [D]
    simp [exchange]
  have hreflectBuild : ∀ factors : List DyckWord,
      reflection (ascentWord (factors.reverse.map reflection)) = descentWord factors := by
    intro factors
    induction factors with
    | nil =>
      apply DyckWord.ext
      simp [ascentWord, descentWord, hreflectList, hzero]
    | cons next factors ih =>
      rw [List.reverse_cons, List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [happend, hreflectAdd, hreflectNest, hreflectTwice, ih]
      rfl
  have hmirrorTwice (factors : List DyckWord) :
      (factors.reverse.map reflection).reverse.map reflection = factors := by
    rw [← List.map_reverse, List.reverse_reverse, List.map_map]
    have hh : reflection ∘ reflection = id := by
      funext path
      exact hreflectTwice path
    rw [hh, List.map_id]
  let mirror : List DyckWord ≃ List DyckWord :=
    { toFun := fun factors => factors.reverse.map reflection
      invFun := fun factors => factors.reverse.map reflection
      left_inv := hmirrorTwice
      right_inv := hmirrorTwice }
  let ascent : List DyckWord ≃ DyckWord :=
    { toFun := ascentWord
      invFun := ascentFactors
      left_inv := hparse
      right_inv := fun path => hreconstruct path.semilength path rfl }
  let descent : List DyckWord ≃ DyckWord := mirror.trans (ascent.trans reflection)
  refine ⟨ascent, descent, ?_, ?_, ?_, ?_⟩
  · intro factors
    exact ⟨rfl, (hfirst factors).1, (hfirst factors).2.1,
      (hfirst factors).2.2, hascentRuns factors⟩
  · intro factors
    have hh : descent factors = descentWord factors := hreflectBuild factors
    rw [hh]
    exact ⟨rfl, hlast factors⟩
  · intro path; rfl
  · intro path; rfl

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Factor

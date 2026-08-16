/- GID: D5/S1/Words/Mechanical/MechanicalRightSpecial
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every length-n lower mechanical factor prefixes one of length n+1; at an irrational slope in [0,1), complexity rises by one and exactly one factor is right-special. -/
import D5.S1.Words.Mechanical.MechanicalFactorComplexity
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.OfFn
/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT

Repository reuse:
* `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lean:15-16` defines
  `lowerMechanicalFactor` as a `List.ofFn` window.
* `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lean:23-33` characterizes membership
  in `lowerMechanicalFactorSet` by a starting index.
* `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lean:351-354` proves the frozen
  factor-complexity formula used twice in the first-difference theorem.

Pinned-mathlib reuse:
* `Mathlib/Data/List/OfFn.lean:51-56`: `List.ofFn_succ'` splits a finite tuple into its
  initial tuple and last entry.
* Lean core `Init/Data/List/Sublist.lean:664`: `List.prefix_append` supplies the prefix
  witness for that split.
* `Mathlib/Data/List/Basic.lean:199-200`: `List.append_left_injective` proves that appending
  a fixed one-letter suffix is injective.
* `Mathlib/Data/List/Basic.lean:372-375`: `List.getLast?_append_of_ne_nil` distinguishes the
  images obtained by appending `false` and `true`.
* `Mathlib/Data/Finset/Filter.lean:127`, `Image.lean:284`, and
  `Lattice/Basic.lean:104-110,198-208`: the filter, image, union, and intersection membership
  characterizations drive the two-class decomposition.
* `Mathlib/Data/Finset/Disjoint.lean:47`: `Finset.disjoint_left` reduces disjointness to
  incompatible membership.
* `Mathlib/Data/Finset/Card.lean:249-251`: `Finset.card_image_of_injective` preserves the
  cardinality of each extension image.
* `Mathlib/Data/Finset/Card.lean:554-556`: `Finset.card_union_add_card_inter` turns the two
  extension classes into the right-special count.
* `Mathlib/Data/Finset/Card.lean:575-577`: `Finset.card_union_of_disjoint` counts the
  disjoint last-letter decomposition.
* `Mathlib/Data/Finset/Card.lean:679-681`: `Finset.card_eq_one` extracts the unique factor.

Negative findings:
* `rg -n 'rightSpecial|right_special|special_factor' D5`, excluding this file, returned zero
  hits, so this repository contains no reusable right-special theorem.
* `rg -n 'Sturmian|mechanicalWord|rightSpecial' .lake/packages/mathlib/Mathlib` returned zero
  hits; the finite two-extension count is therefore proved locally below.
-/

namespace D5.S1.Words.Mechanical.MechanicalRightSpecial

private theorem lowerMechanicalFactor_succ (alpha rho : Real) (n i : Nat) :
    lowerMechanicalFactor alpha rho (n + 1) i =
      lowerMechanicalFactor alpha rho n i ++
        [lowerMechanicalWord alpha rho (i + n)] := by
  unfold lowerMechanicalFactor
  rw [List.ofFn_succ']
  simp

/-- Every occurring length-`n` factor is a prefix of an occurring length-`n + 1` factor. -/
theorem lower_mechanical_factor_has_prefix_extension (alpha rho : Real) (n : Nat) :
    ∀ w ∈ lowerMechanicalFactorSet alpha rho n,
      ∃ v ∈ lowerMechanicalFactorSet alpha rho (n + 1), w <+: v := by
  intro w hw
  obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hw
  refine ⟨lowerMechanicalFactor alpha rho (n + 1) i,
    mem_lowerMechanicalFactorSet.mpr ⟨i, rfl⟩, ?_⟩
  rw [lowerMechanicalFactor_succ]
  exact List.prefix_append _ _

/-- This is only the first difference of the frozen formula `p(n) = n + 1`, applied at
`n` and `n + 1`. -/
theorem lower_mechanical_factor_complexity_first_difference {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (halpha_irr : Irrational alpha) (n : Nat) :
    (lowerMechanicalFactorSet alpha rho (n + 1)).card =
      (lowerMechanicalFactorSet alpha rho n).card + 1 := by
  have hn := lower_mechanical_factor_complexity (rho := rho) halpha0 halpha1 halpha_irr n
  have hsucc := lower_mechanical_factor_complexity (rho := rho) halpha0 halpha1 halpha_irr (n + 1)
  omega

/-- A length-`n` lower mechanical factor is right-special when both Boolean one-letter
extensions occur at length `n + 1`. -/
def IsLowerMechanicalRightSpecial (alpha rho : Real) (n : Nat) (w : List Bool) : Prop :=
  w ∈ lowerMechanicalFactorSet alpha rho n ∧
    w ++ [false] ∈ lowerMechanicalFactorSet alpha rho (n + 1) ∧
    w ++ [true] ∈ lowerMechanicalFactorSet alpha rho (n + 1)

private noncomputable def rightExtensionBases
    (alpha rho : Real) (n : Nat) (b : Bool) : Finset (List Bool) :=
  (lowerMechanicalFactorSet alpha rho n).filter fun w =>
    w ++ [b] ∈ lowerMechanicalFactorSet alpha rho (n + 1)

private theorem rightExtensionBases_union (alpha rho : Real) (n : Nat) :
    rightExtensionBases alpha rho n false ∪ rightExtensionBases alpha rho n true =
      lowerMechanicalFactorSet alpha rho n := by
  classical
  ext w
  simp only [rightExtensionBases, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
  · intro hw
    obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hw
    have hbase : lowerMechanicalFactor alpha rho n i ∈
        lowerMechanicalFactorSet alpha rho n :=
      mem_lowerMechanicalFactorSet.mpr ⟨i, rfl⟩
    have hext : lowerMechanicalFactor alpha rho n i ++
        [lowerMechanicalWord alpha rho (i + n)] ∈
          lowerMechanicalFactorSet alpha rho (n + 1) := by
      rw [← lowerMechanicalFactor_succ]
      exact mem_lowerMechanicalFactorSet.mpr ⟨i, rfl⟩
    cases hbit : lowerMechanicalWord alpha rho (i + n) with
    | false =>
        left
        exact ⟨hbase, by simpa [hbit] using hext⟩
    | true =>
        right
        exact ⟨hbase, by simpa [hbit] using hext⟩

private theorem lowerMechanicalFactorSet_succ_decomposition (alpha rho : Real) (n : Nat) :
    lowerMechanicalFactorSet alpha rho (n + 1) =
      (rightExtensionBases alpha rho n false).image (fun w => w ++ [false]) ∪
      (rightExtensionBases alpha rho n true).image (fun w => w ++ [true]) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hv
    have hbase : lowerMechanicalFactor alpha rho n i ∈
        lowerMechanicalFactorSet alpha rho n :=
      mem_lowerMechanicalFactorSet.mpr ⟨i, rfl⟩
    have hsucc : lowerMechanicalFactor alpha rho (n + 1) i ∈
        lowerMechanicalFactorSet alpha rho (n + 1) :=
      mem_lowerMechanicalFactorSet.mpr ⟨i, rfl⟩
    cases hbit : lowerMechanicalWord alpha rho (i + n) with
    | false =>
        apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨lowerMechanicalFactor alpha rho n i, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨hbase, by
            simpa [lowerMechanicalFactor_succ, hbit] using hsucc⟩
        · simp [lowerMechanicalFactor_succ, hbit]
    | true =>
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨lowerMechanicalFactor alpha rho n i, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨hbase, by
            simpa [lowerMechanicalFactor_succ, hbit] using hsucc⟩
        · simp [lowerMechanicalFactor_succ, hbit]
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2

private theorem rightExtensionImages_disjoint (alpha rho : Real) (n : Nat) :
    Disjoint
      ((rightExtensionBases alpha rho n false).image (fun w => w ++ [false]))
      ((rightExtensionBases alpha rho n true).image (fun w => w ++ [true])) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro v hvfalse hvtrue
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hvfalse
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hvtrue
  have hlast := congrArg List.getLast? (hw.trans hu.symm)
  simp at hlast

private theorem lowerMechanicalFactorSet_succ_card (alpha rho : Real) (n : Nat) :
    (lowerMechanicalFactorSet alpha rho (n + 1)).card =
      (rightExtensionBases alpha rho n false).card +
        (rightExtensionBases alpha rho n true).card := by
  classical
  rw [lowerMechanicalFactorSet_succ_decomposition,
    Finset.card_union_of_disjoint (rightExtensionImages_disjoint alpha rho n),
    Finset.card_image_of_injective _ (List.append_left_injective [false]),
    Finset.card_image_of_injective _ (List.append_left_injective [true])]

private theorem rightSpecial_iff_mem_inter (alpha rho : Real) (n : Nat) (w : List Bool) :
    IsLowerMechanicalRightSpecial alpha rho n w ↔
      w ∈ rightExtensionBases alpha rho n false ∩ rightExtensionBases alpha rho n true := by
  classical
  simp only [IsLowerMechanicalRightSpecial, rightExtensionBases, Finset.mem_inter,
    Finset.mem_filter]
  aesop

/-- For an irrational slope in `[0,1)`, exactly one length-`n` lower mechanical factor has
both Boolean right extensions. -/
theorem exists_unique_lower_mechanical_right_special {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (halpha_irr : Irrational alpha) (n : Nat) :
    ∃! w : List Bool, IsLowerMechanicalRightSpecial alpha rho n w := by
  classical
  let leftBases := rightExtensionBases alpha rho n false
  let rightBases := rightExtensionBases alpha rho n true
  have hsplit : (lowerMechanicalFactorSet alpha rho (n + 1)).card =
      leftBases.card + rightBases.card :=
    lowerMechanicalFactorSet_succ_card alpha rho n
  have hunion : leftBases ∪ rightBases = lowerMechanicalFactorSet alpha rho n :=
    rightExtensionBases_union alpha rho n
  have hfirst := lower_mechanical_factor_complexity_first_difference
    (rho := rho) halpha0 halpha1 halpha_irr n
  have hcard : (leftBases ∩ rightBases).card = 1 := by
    have hcount := Finset.card_union_add_card_inter leftBases rightBases
    rw [hunion] at hcount
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  refine ⟨w, ?_, ?_⟩
  · apply (rightSpecial_iff_mem_inter alpha rho n w).2
    rw [hw]
    simp
  · intro y hy
    have hy' := (rightSpecial_iff_mem_inter alpha rho n y).1 hy
    rw [hw] at hy'
    simpa using hy'

#print axioms lower_mechanical_factor_has_prefix_extension
#print axioms lower_mechanical_factor_complexity_first_difference
#print axioms exists_unique_lower_mechanical_right_special

end D5.S1.Words.Mechanical.MechanicalRightSpecial

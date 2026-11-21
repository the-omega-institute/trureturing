/- GID: D5/S3/Combinatorics/ElekMagicWordConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/ElekMagicWordConverseRefutation
   mirror-E: none(waiver:direct-refutation-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.Coxeter.Length, mathlib/module/Mathlib.LinearAlgebra.Matrix.Cartan.Basic]
   digest: The type B₂ interval from s to sts is Boolean and has no magic word. -/

/-
The five lift declarations below are adapted from Mathlib PR #43703.
Copyright (c) 2026 Jeromie N. Beasley. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors of the lift: Jeromie N. Beasley
Source: https://github.com/dicipler-pixel/mathlib4/blob/08e259a357c8e0caed76ca53aef41f40286b3694/Mathlib/GroupTheory/Coxeter/Dihedral.lean
Retire the local lift and generator lemmas when the project's pinned Mathlib
exposes the equivalent canonical homomorphism and its two generator equations.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CoxeterMatrix.I

open DihedralGroup

private def dihedralSimple (m : ℕ) : Fin 2 → DihedralGroup (m + 2) := fun i =>
  if i = 0 then sr 0 else sr 1

private theorem dihedralSimple_isLiftable (m : ℕ) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.I m) (dihedralSimple m) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dihedralSimple, CoxeterMatrix.I, DihedralGroup.r_pow]

/-- The canonical homomorphism to the corresponding dihedral group. -/
def toDihedral (m : ℕ) :
    (CoxeterMatrix.I m).Group →* DihedralGroup (m + 2) :=
  (CoxeterMatrix.I m).toCoxeterSystem.lift
    ⟨dihedralSimple m, dihedralSimple_isLiftable m⟩

@[simp] theorem toDihedral_simple_zero (m : ℕ) :
    toDihedral m ((CoxeterMatrix.I m).simple (0 : Fin 2)) = sr 0 := by
  simpa [toDihedral, dihedralSimple] using
    (CoxeterMatrix.I m).toCoxeterSystem.lift_apply_simple
      (dihedralSimple_isLiftable m) (0 : Fin 2)

@[simp] theorem toDihedral_simple_one (m : ℕ) :
    toDihedral m ((CoxeterMatrix.I m).simple (1 : Fin 2)) = sr 1 := by
  simpa [toDihedral, dihedralSimple] using
    (CoxeterMatrix.I m).toCoxeterSystem.lift_apply_simple
      (dihedralSimple_isLiftable m) (1 : Fin 2)

end CoxeterMatrix.I

namespace D5.S3.Combinatorics.ElekMagicWordConverseRefutation

open DihedralGroup CoxeterMatrix.I

private theorem entries_I_two_eq_B_two :
    ∀ i j : Fin 2, (CoxeterMatrix.I 2) i j = (CoxeterMatrix.B 2) i j := by
  simp only [Fin.forall_fin_two]; decide +kernel

def cartanExponent (a : ℤ) : ℕ :=
  if a = 0 then 2 else if a = 1 then 3 else
  if a = 2 then 4 else if a = 3 then 6 else 0

def CartanOrigin {S : Type} (M : CoxeterMatrix S) : Prop :=
  Finite S ∧ ∃ A : Matrix S S ℤ,
    (∀ i, A i i = 2) ∧
    (∀ i j, i ≠ j →
      A i j ≤ 0 ∧ (A i j = 0 ↔ A j i = 0) ∧
        M i j = cartanExponent (A i j * A j i))

private theorem cartan_origin_I_two : CartanOrigin (CoxeterMatrix.I 2) := by
  refine ⟨inferInstance, CartanMatrix.B 2, ?_, ?_⟩
  · rw [CartanMatrix.B_two]
    simp only [Fin.forall_fin_two]; decide +kernel
  · have cartanB : ∀ i j : Fin 2, i ≠ j →
          CartanMatrix.B 2 i j ≤ 0 ∧
          (CartanMatrix.B 2 i j = 0 ↔ CartanMatrix.B 2 j i = 0) ∧
          (CoxeterMatrix.B 2) i j =
            cartanExponent (CartanMatrix.B 2 i j * CartanMatrix.B 2 j i) := by
      rw [CartanMatrix.B_two]
      simp only [Fin.forall_fin_two]; decide +kernel
    intro i j hij
    rw [entries_I_two_eq_B_two i j]
    exact cartanB i j hij


private abbrev cs₂ := (CoxeterMatrix.I 2).toCoxeterSystem
private abbrev w₂ := cs₂.wordProd ([0, 1, 0] : List (Fin 2))

private def evalWord (Q : List (Fin 2)) : DihedralGroup 4 :=
  (Q.map (CoxeterMatrix.I.dihedralSimple 2)).prod

private theorem map_wordProd (Q : List (Fin 2)) :
    toDihedral 2 (cs₂.wordProd Q) = evalWord Q := by
  induction Q with
  | nil =>
    rw [CoxeterSystem.wordProd_nil, map_one]
    rfl
  | cons i Q ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih]
    change toDihedral 2 (cs₂.simple i) * evalWord Q =
      CoxeterMatrix.I.dihedralSimple 2 i * evalWord Q
    have simpleImage : ∀ i : Fin 2, toDihedral 2 (cs₂.simple i) =
        CoxeterMatrix.I.dihedralSimple 2 i :=
      Fin.forall_fin_two.mpr ⟨toDihedral_simple_zero 2, toDihedral_simple_one 2⟩
    rw [simpleImage]

/-- The cases of lengths zero through three give one, two, four and eight words. -/
private theorem evalWord_eq_sr_three (Q : List (Fin 2)) (hQ : Q.length ≤ 3) :
    evalWord Q = sr 3 ↔ Q = [0, 1, 0] := by
  rcases Q with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · decide +kernel
  · clear hQ
    revert a
    simp only [Fin.forall_fin_two]; decide +kernel
  · clear hQ
    revert a b
    simp only [Fin.forall_fin_two]; decide +kernel
  · clear hQ
    revert a b c
    simp only [Fin.forall_fin_two]; decide +kernel
  · simp only [List.length_cons] at hQ
    omega

private theorem length_and_unique_reduced :
    let M₂ := CoxeterMatrix.I 2
    let cs₂ := M₂.toCoxeterSystem
    let w₂ := cs₂.wordProd ([0, 1, 0] : List (Fin 2))
    cs₂.length w₂ = 3 ∧
      ∀ Q : List (Fin 2), cs₂.IsReduced Q → cs₂.wordProd Q = w₂ → Q = [0, 1, 0] := by
  change cs₂.length w₂ = 3 ∧
    ∀ Q : List (Fin 2), cs₂.IsReduced Q → cs₂.wordProd Q = w₂ → Q = [0, 1, 0]
  have lengthBound : cs₂.length w₂ ≤ 3 := cs₂.length_wordProd_le [0, 1, 0]
  have targetImage : evalWord [0, 1, 0] = sr 3 :=
    (evalWord_eq_sr_three [0, 1, 0] (by decide)).mpr rfl
  have forced (Q : List (Fin 2)) (reduced : cs₂.IsReduced Q)
      (product : cs₂.wordProd Q = w₂) : Q = [0, 1, 0] := by
    have short : Q.length ≤ 3 := calc
      Q.length = cs₂.length (cs₂.wordProd Q) := reduced.eq.symm
      _ = cs₂.length w₂ := congrArg cs₂.length product
      _ ≤ 3 := lengthBound
    apply (evalWord_eq_sr_three Q short).mp
    calc
      evalWord Q = toDihedral 2 (cs₂.wordProd Q) := (map_wordProd Q).symm
      _ = toDihedral 2 w₂ := congrArg (fun w => toDihedral 2 w) product
      _ = evalWord [0, 1, 0] := map_wordProd [0, 1, 0]
      _ = sr 3 := targetImage
  refine ⟨?_, forced⟩
  obtain ⟨Q, reduced, product⟩ := cs₂.exists_isReduced w₂
  calc
    cs₂.length w₂ = cs₂.length (cs₂.wordProd Q) := congrArg cs₂.length product
    _ = Q.length := reduced.eq
    _ = 3 := congrArg List.length (forced Q reduced product.symm)

/-- Keep precisely the letters selected by the Boolean mask, in their source order.
The predicates that use this function require a bit for each letter. -/
def retained {S : Type} : List S → List Bool → List S
  | [], _ => []
  | _ :: _, [] => []
  | i :: Q, b :: mask =>
      if b then i :: retained Q mask else retained Q mask

section Source

variable {S W : Type} [Group W] {M : CoxeterMatrix S}

/-- Elek's positional product, with omitted letters contributing the identity. -/
def positionalProduct (cs : CoxeterSystem M W) (Q : List S) (mask : List Bool) : W :=
  cs.wordProd (retained Q mask)

/-- A source subword must select among exactly the positions of `Q`. -/
def MaskFor (cs : CoxeterSystem M W) (Q : List S) (u : W) (mask : List Bool) : Prop :=
  mask.length = Q.length ∧ positionalProduct cs Q mask = u

/-- The subword criterion uses some reduced expression of the upper element.
Deleting letters from a nonreduced retained word extracts a reduced word with its product. -/
def BruhatLE (cs : CoxeterSystem M W) (u w : W) : Prop :=
  ∃ Q : List S, cs.IsReduced Q ∧ cs.wordProd Q = w ∧
    ∃ mask : List Bool, MaskFor cs Q u mask

def BruhatInterval (cs : CoxeterSystem M W) (v w : W) :=
  {u : W // BruhatLE cs v u ∧ BruhatLE cs u w}

/-- A finite Boolean lattice under inclusion, with the order preserved and reflected. -/
def IsHypercube (cs : CoxeterSystem M W) (v w : W) : Prop :=
  ∃ n : ℕ, ∃ f : BruhatInterval cs v w ≃ Finset (Fin n),
    ∀ x y, BruhatLE cs x.val y.val ↔ f x ⊆ f y

/-- Elek's uniqueness counts all positional masks with the required product. -/
def MagicFor (cs : CoxeterSystem M W) (v w : W) (Q : List S) : Prop :=
  cs.IsReduced Q ∧ cs.wordProd Q = w ∧ ∃! mask : List Bool, MaskFor cs Q v mask

end Source

/-- Elek, Conjecture 3.3 in the Weyl setting of §2.1.
https://arxiv.org/html/2610.22730v1#S3.Thmtheorem3 -/
def claim : Prop :=
  ∀ (S : Type) (M : CoxeterMatrix S) (W : Type) [Group W]
    (cs : CoxeterSystem M W) (v w : W),
    CartanOrigin M → BruhatLE cs v w →
      (IsHypercube cs v w ↔ ∃ Q : List S, MagicFor cs v w Q)

private def retainedWords {S : Type} : List S → List (List S)
  | [] => [[]]
  | i :: Q => retainedWords Q ++ (retainedWords Q).map (i :: ·)

private theorem mem_retainedWords {S : Type} (Q R : List S) :
    R ∈ retainedWords Q ↔ ∃ mask : List Bool, mask.length = Q.length ∧ retained Q mask = R := by
  induction Q generalizing R with
  | nil =>
    constructor
    · intro h
      have hR : R = [] := by simpa [retainedWords] using h
      exact ⟨[], rfl, hR.symm⟩
    · rintro ⟨mask, _, hR⟩
      have hnil : [] = R := by simpa only [retained] using hR
      subst R
      exact List.mem_cons_self
  | cons i Q ih =>
    rw [retainedWords, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨R', h, rfl⟩)
      · obtain ⟨mask, hlen, hR⟩ := (ih R).mp h
        exact ⟨false :: mask, congrArg Nat.succ hlen, hR⟩
      · obtain ⟨mask, hlen, hR⟩ := (ih R').mp h
        exact ⟨true :: mask, congrArg Nat.succ hlen, congrArg (i :: ·) hR⟩
    · rintro ⟨mask, hlen, hR⟩
      cases mask with
      | nil => simp at hlen
      | cons b mask =>
        have hlen' : mask.length = Q.length := Nat.succ.inj hlen
        cases b
        · exact Or.inl ((ih R).mpr ⟨mask, hlen', hR⟩)
        · exact Or.inr ⟨retained Q mask, (ih _).mpr ⟨mask, hlen', rfl⟩, hR⟩

private abbrev W₂ := (CoxeterMatrix.I 2).Group

/-- Only the six candidates produced by masks of `sts`, with their candidate minimum words. -/
private def shortWord : Fin 6 → List (Fin 2) := ![[], [0], [1], [0, 1], [1, 0], [0, 1, 0]]

private abbrev word₂ (i : Fin 6) : W₂ := cs₂.wordProd (shortWord i)
private abbrev s₂ : W₂ := word₂ 1

private theorem shortImage_iff (i : Fin 6) (hi : i ≠ 5) (Q : List (Fin 2))
    (hQ : Q.length ≤ (shortWord i).length) :
    evalWord Q = evalWord (shortWord i) ↔ Q = shortWord i := by
  rcases Q with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
  · clear hi
    revert hQ
    fin_cases i <;> decide +kernel
  · clear hi
    revert a hQ
    fin_cases i
    all_goals (simp only [Fin.forall_fin_two]; decide +kernel)
  · clear hi
    revert a b hQ
    fin_cases i
    all_goals (simp only [Fin.forall_fin_two]; decide +kernel)
  · have hshort : (shortWord i).length ≤ 2 := by
      revert hi
      fin_cases i <;> decide +kernel
    simp only [List.length_cons] at hQ
    omega

/-- The lift separates candidate spellings. The least lengths are attained in the
Coxeter presentation and are bounded below by considering a minimum word there. -/
private theorem minimum_words (i : Fin 6) :
    cs₂.length (word₂ i) = (shortWord i).length ∧
    ∀ Q : List (Fin 2), cs₂.IsReduced Q → cs₂.wordProd Q = word₂ i → Q = shortWord i := by
  by_cases hi : i = 5
  · subst i
    exact length_and_unique_reduced
  · have hbound := cs₂.length_wordProd_le (shortWord i)
    have forced (Q : List (Fin 2)) (hred : cs₂.IsReduced Q)
        (hprod : cs₂.wordProd Q = word₂ i) : Q = shortWord i := by
      have hlength : Q.length ≤ (shortWord i).length := calc
        Q.length = cs₂.length (cs₂.wordProd Q) := hred.eq.symm
        _ = cs₂.length (word₂ i) := congrArg cs₂.length hprod
        _ ≤ (shortWord i).length := hbound
      apply (shortImage_iff i hi Q hlength).mp
      calc
        evalWord Q = toDihedral 2 (cs₂.wordProd Q) := (map_wordProd Q).symm
        _ = toDihedral 2 (word₂ i) := congrArg (toDihedral 2) hprod
        _ = evalWord (shortWord i) := map_wordProd (shortWord i)
    obtain ⟨Q, hred, hprod⟩ := cs₂.exists_isReduced (word₂ i)
    refine ⟨?_, forced⟩
    calc
      cs₂.length (word₂ i) = cs₂.length (cs₂.wordProd Q) := congrArg cs₂.length hprod
      _ = Q.length := hred.eq
      _ = (shortWord i).length := congrArg List.length (forced Q hred hprod.symm)

private theorem word₂_injective : Function.Injective word₂ := by
  have separate (i j : Fin 6) :
      evalWord (shortWord i) = evalWord (shortWord j) → i = j := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  intro i j heq
  apply separate
  calc
    evalWord (shortWord i) = toDihedral 2 (word₂ i) := (map_wordProd _).symm
    _ = toDihedral 2 (word₂ j) := congrArg (toDihedral 2) heq
    _ = evalWord (shortWord j) := map_wordProd _

private theorem below_word (x : W₂) (i : Fin 6) :
    BruhatLE cs₂ x (word₂ i) ↔ x ∈ (retainedWords (shortWord i)).map cs₂.wordProd := by
  constructor
  · rintro ⟨Q, hred, hprod, mask, hlen, hmask⟩
    have hQ := (minimum_words i).2 Q hred hprod
    subst Q
    apply List.mem_map.mpr
    exact ⟨retained (shortWord i) mask, (mem_retainedWords _ _).mpr ⟨mask, hlen, rfl⟩, hmask⟩
  · intro hx
    obtain ⟨R, hR, hprod⟩ := List.mem_map.mp hx
    obtain ⟨mask, hlen, hmask⟩ := (mem_retainedWords _ _).mp hR
    exact ⟨shortWord i, (minimum_words i).1, rfl, mask, hlen,
      (congrArg cs₂.wordProd hmask).trans hprod⟩

/-- Each row preserves one entry per mask in lexicographic order, including duplicates. -/
private def shortLowers : Fin 6 → List (Fin 6) :=
  ![[0], [0, 1], [0, 2], [0, 2, 1, 3], [0, 1, 2, 4], [0, 1, 2, 4, 1, 0, 3, 5]]

private theorem lower_products (i : Fin 6) :
    (retainedWords (shortWord i)).map cs₂.wordProd = (shortLowers i).map word₂ := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change [word₂ 0, s₂, word₂ 2, word₂ 4, s₂, cs₂.wordProd [0, 0], word₂ 3, w₂] =
      [word₂ 0, s₂, word₂ 2, word₂ 4, s₂, word₂ 0, word₂ 3, w₂]
    have ss : cs₂.wordProd [0, 0] = word₂ 0 := by
      change cs₂.wordProd [0, 0] = cs₂.wordProd []
      rw [cs₂.wordProd_cons, cs₂.wordProd_singleton, cs₂.simple_mul_simple_self, cs₂.wordProd_nil]
    rw [ss]

private theorem lower_iff (x : W₂) (i : Fin 6) :
    BruhatLE cs₂ x (word₂ i) ↔ x ∈ (shortLowers i).map word₂ := by
  rw [below_word x i, lower_products i]

private theorem comparison (i j : Fin 6) :
    BruhatLE cs₂ (word₂ i) (word₂ j) ↔ i ∈ shortLowers j := by
  rw [lower_iff, List.mem_map]
  constructor
  · rintro ⟨k, hk, heq⟩
    exact (word₂_injective heq) ▸ hk
  · intro hi
    exact ⟨i, hi, rfl⟩

private def cubeIndex : Fin 4 → Fin 6 := ![1, 3, 4, 5]

/-- Full interval membership. The two remaining candidates below the top,
the identity and `t`, fail the lower-endpoint relation. -/
private theorem interval_iff (x : W₂) :
    (BruhatLE cs₂ s₂ x ∧ BruhatLE cs₂ x w₂) ↔ ∃ j, word₂ (cubeIndex j) = x := by
  constructor
  · rintro ⟨hlo, hhi⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ((lower_iff x 5).mp hhi)
    have hi := (comparison 1 i).mp hlo
    fin_cases i
    · exact ((by decide +kernel : ¬ ((1 : Fin 6) ∈ shortLowers 0)) hi).elim
    · exact ⟨0, rfl⟩
    · exact ((by decide +kernel : ¬ ((1 : Fin 6) ∈ shortLowers 2)) hi).elim
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨(comparison 1 (cubeIndex j)).mpr ?_, (comparison (cubeIndex j) 5).mpr ?_⟩
    all_goals (fin_cases j <;> decide +kernel)

/-- In particular the two longer dihedral elements lie outside the lower set of `sts`. -/
private theorem longer_words_excluded :
    ¬ BruhatLE cs₂ (cs₂.wordProd [1, 0, 1]) w₂ ∧
    ¬ BruhatLE cs₂ (cs₂.wordProd [0, 1, 0, 1]) w₂ := by
  have exclude (Q : List (Fin 2))
      (different : ∀ i : Fin 6, evalWord (shortWord i) ≠ evalWord Q) :
      ¬ BruhatLE cs₂ (cs₂.wordProd Q) w₂ := by
    intro h
    obtain ⟨i, _, hi⟩ := List.mem_map.mp ((lower_iff (cs₂.wordProd Q) 5).mp h)
    apply different i
    calc
      evalWord (shortWord i) = toDihedral 2 (word₂ i) := (map_wordProd _).symm
      _ = toDihedral 2 (cs₂.wordProd Q) := congrArg (toDihedral 2) hi
      _ = evalWord Q := map_wordProd Q
  constructor
  · apply exclude
    intro i
    fin_cases i <;> decide +kernel
  · apply exclude
    intro i
    fin_cases i <;> decide +kernel

private def cubeSet : Fin 4 → Finset (Fin 2) := ![∅, {0}, {1}, {0, 1}]

private theorem cubeIndex_injective : Function.Injective cubeIndex := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem cubeSet_bijective : Function.Bijective cubeSet := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro a
    by_cases h0 : (0 : Fin 2) ∈ a
    · by_cases h1 : (1 : Fin 2) ∈ a
      · refine ⟨3, Finset.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
        · exact iff_of_true (by decide +kernel) h0
        · exact iff_of_true (by decide +kernel) h1
      · refine ⟨1, Finset.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
        · exact iff_of_true (by decide +kernel) h0
        · exact iff_of_false (by decide +kernel) h1
    · by_cases h1 : (1 : Fin 2) ∈ a
      · refine ⟨2, Finset.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
        · exact iff_of_false (by decide +kernel) h0
        · exact iff_of_true (by decide +kernel) h1
      · refine ⟨0, Finset.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
        · exact iff_of_false (by decide +kernel) h0
        · exact iff_of_false (by decide +kernel) h1

/-- All sixteen comparisons, in both directions, including the incomparable middle pair. -/
private theorem cube_order_indices (i j : Fin 4) :
    BruhatLE cs₂ (word₂ (cubeIndex i)) (word₂ (cubeIndex j)) ↔ cubeSet i ⊆ cubeSet j := by
  rw [comparison]
  fin_cases i <;> fin_cases j <;> decide +kernel

private abbrev interval₂ := BruhatInterval cs₂ s₂ w₂

private def toInterval (i : Fin 4) : interval₂ :=
  ⟨word₂ (cubeIndex i), (interval_iff _).mpr ⟨i, rfl⟩⟩

private noncomputable def intervalEquiv : Fin 4 ≃ interval₂ :=
  Equiv.ofBijective toInterval ⟨
    fun _ _ hi => cubeIndex_injective (word₂_injective (congrArg Subtype.val hi)),
    fun x => by
      obtain ⟨i, hi⟩ := (interval_iff x.val).mp x.property
      exact ⟨i, Subtype.ext hi⟩⟩

private noncomputable def b2Cube : interval₂ ≃ Finset (Fin 2) :=
  intervalEquiv.symm.trans (Equiv.ofBijective cubeSet cubeSet_bijective)

private theorem b2Cube_order (x y : interval₂) :
    BruhatLE cs₂ x.val y.val ↔ b2Cube x ⊆ b2Cube y := by
  obtain ⟨i, rfl⟩ := intervalEquiv.surjective x
  obtain ⟨j, rfl⟩ := intervalEquiv.surjective y
  simp only [b2Cube, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact cube_order_indices i j

/-- The bits are written in source order, so the two masks keep different occurrences of `s`. -/
private theorem collision :
    MaskFor cs₂ (shortWord 5) s₂ [true, false, false] ∧
    MaskFor cs₂ (shortWord 5) s₂ [false, false, true] ∧
    ([true, false, false] : List Bool) ≠ [false, false, true] := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by decide +kernel⟩

/-- The descent obstruction in Elek, Lemma 2.17, and the interval in Umutabazi, §4,
give prior ingredients. The positional collision gives a direct certificate here.
https://arxiv.org/html/2610.22730v1#S2.Thmtheorem17
https://arxiv.org/pdf/2206.06538v1#page=5 -/
private theorem no_magic : ¬ ∃ Q : List (Fin 2), MagicFor cs₂ s₂ w₂ Q := by
  rintro ⟨Q, hred, hprod, mask, _, unique⟩
  have hQ : Q = shortWord 5 := (minimum_words 5).2 Q hred hprod
  subst Q
  obtain ⟨firstMask, lastMask, distinct⟩ := collision
  exact distinct ((unique _ firstMask).trans (unique _ lastMask).symm)

/-- The exact source-valid instance and the failure of the Boolean-to-magic implication. -/
private theorem b2_witness :
    CartanOrigin (CoxeterMatrix.I 2) ∧ BruhatLE cs₂ s₂ w₂ ∧
      IsHypercube cs₂ s₂ w₂ ∧ ¬ ∃ Q : List (Fin 2), MagicFor cs₂ s₂ w₂ Q :=
  ⟨cartan_origin_I_two, (comparison 1 5).mpr (by decide +kernel),
    ⟨2, b2Cube, b2Cube_order⟩, no_magic⟩

/-- The full Weyl-domain biconditional is false. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨cartan, comparable, cube, noMagic⟩ := b2_witness
  exact noMagic ((h (Fin 2) (CoxeterMatrix.I 2) W₂ cs₂ s₂ w₂ cartan comparable).mp cube)

end D5.S3.Combinatorics.ElekMagicWordConverseRefutation

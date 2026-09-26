/- GID: D5/S3/Combinatorics/CrosswordPermutationGridRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordPermutationGridRefutation
   mirror-E: none(waiver:direct-refutation-of-external-conjecture)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Perm]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/CrosswordPermutationGridRefutation.claim; result=D5/S3/Combinatorics/CrosswordPermutationGridRefutation.result; claim=D5/S3/Combinatorics/CrosswordPermutationGridRefutation.claim
   digest: A permutation grid has 155 complete rook placements, refuting Conjecture 3.10. -/

import D5.S3.Combinatorics.CrosswordRookCountsDefs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordPermutationGridRefutation

open D5.S3.Combinatorics.CrosswordRookCounts (Cell SameAcross SameDown IsRookPlacement rookCount)

instance {n : ℕ} (W : Finset (Cell n)) : DecidableRel (SameAcross W) :=
  fun c d => by unfold SameAcross; infer_instance

instance {n : ℕ} (W : Finset (Cell n)) : DecidableRel (SameDown W) :=
  fun c d => by unfold SameDown; infer_instance

/-- The permutation grid of `w`: black squares exactly at `(i, w i)`. -/
def permGrid {n : ℕ} (w : Equiv.Perm (Fin n)) : Finset (Cell n) :=
  Finset.univ.filter (fun c => w c.1 ≠ c.2)

/-- Lewis–Won, Conjecture 3.10. -/
def claim : Prop :=
  ∀ r : ℕ, 0 < r →
    ((∃ n : ℕ, ∃ w : Equiv.Perm (Fin n), rookCount (permGrid w) = r) ↔ (r ≠ 4 ∧ r ≠ 12 ∧ r % 4 ≠ 3))

/-- A finite list of possible cells for each across word, with a down-word label on every cell. -/
structure WordData (n : ℕ) (W : Finset (Cell n)) where
  across : List (Finset (Cell n))
  downId : Cell n → ℕ
  downIds : Finset ℕ
  word_subset : ∀ A ∈ across, A ⊆ W
  word_nonempty : ∀ A ∈ across, A.Nonempty
  word_unique : ∀ c ∈ W, ∃! A, A ∈ across ∧ c ∈ A
  across_iff : ∀ c ∈ W, ∀ d ∈ W,
    SameAcross W c d ↔ ∃ A ∈ across, c ∈ A ∧ d ∈ A
  down_iff : ∀ c ∈ W, ∀ d ∈ W,
    SameDown W c d ↔ downId c = downId d
  ids_eq : W.image downId = downIds

/-- A perfect matching of the across/down word intersection graph, represented by its cells. -/
def IsWordMatching {n : ℕ} {W : Finset (Cell n)} (D : WordData n W)
    (R : Finset (Cell n)) : Prop :=
  R ⊆ W ∧
  (∀ A ∈ D.across, ∃! c, c ∈ R ∧ c ∈ A) ∧
  (∀ c ∈ R, ∀ d ∈ R, c ≠ d → D.downId c ≠ D.downId d) ∧
  R.image D.downId = D.downIds

/-- Complete rook placements are exactly perfect matchings of the word graph. -/
theorem rookPlacement_iff_wordMatching {n : ℕ} {W : Finset (Cell n)}
    (D : WordData n W) (R : Finset (Cell n)) :
    IsRookPlacement W R ↔ IsWordMatching D R := by
  classical
  constructor
  · intro h
    rcases h with ⟨hsub, hpair, hcover⟩
    refine ⟨hsub, ?_, ?_, ?_⟩
    · intro A hA
      obtain ⟨c, hcA⟩ := D.word_nonempty A hA
      have hcW : c ∈ W := D.word_subset A hA hcA
      obtain ⟨d, hdR, hcd⟩ := (hcover c hcW).1
      obtain ⟨B, hB, hcB, hdB⟩ := (D.across_iff c hcW d (hsub hdR)).mp hcd
      obtain ⟨A0, _, huniq⟩ := D.word_unique c hcW
      have hBA : B = A :=
        (huniq B ⟨hB, hcB⟩).trans (huniq A ⟨hA, hcA⟩).symm
      have hdA : d ∈ A := hBA ▸ hdB
      refine ⟨d, ⟨hdR, hdA⟩, ?_⟩
      intro e he
      have hde : SameAcross W d e :=
        (D.across_iff d (hsub hdR) e (hsub he.1)).mpr ⟨A, hA, hdA, he.2⟩
      by_contra hne
      have hne' : d ≠ e := by intro h; exact hne h.symm
      exact (hpair d hdR e he.1 hne').1 hde
    · intro c hc d hd hne heq
      have hdown : SameDown W c d :=
        (D.down_iff c (hsub hc) d (hsub hd)).mpr heq
      exact (hpair c hc d hd hne).2 hdown
    · apply Finset.Subset.antisymm
      · rw [← D.ids_eq]
        exact Finset.image_subset_image hsub
      · intro k hk
        rw [← D.ids_eq] at hk
        obtain ⟨c, hcW, rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨d, hdR, hcd⟩ := (hcover c hcW).2
        exact Finset.mem_image.mpr ⟨d, hdR,
          (D.down_iff c hcW d (hsub hdR)).mp hcd |>.symm⟩
  · rintro ⟨hsub, hwords, hdown, hids⟩
    refine ⟨hsub, ?_, ?_⟩
    · intro c hc d hd hne
      constructor
      · intro h
        obtain ⟨A, hA, hcA, hdA⟩ :=
          (D.across_iff c (hsub hc) d (hsub hd)).mp h
        obtain ⟨e, he, huniq⟩ := hwords A hA
        exact hne ((huniq c ⟨hc, hcA⟩).trans (huniq d ⟨hd, hdA⟩).symm)
      · intro h
        exact hdown c hc d hd hne ((D.down_iff c (hsub hc) d (hsub hd)).mp h)
    · intro c hc
      obtain ⟨A, ⟨hA, hcA⟩, _⟩ := D.word_unique c hc
      obtain ⟨d, ⟨hdR, hdA⟩, _⟩ := hwords A hA
      constructor
      · exact ⟨d, hdR, (D.across_iff c hc d (hsub hdR)).mpr ⟨A, hA, hcA, hdA⟩⟩
      · have hkid : D.downId c ∈ D.downIds := by
          rw [← D.ids_eq]
          exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
        rw [← hids] at hkid
        obtain ⟨e, heR, heq⟩ := Finset.mem_image.mp hkid
        exact ⟨e, heR, (D.down_iff c hc e (hsub heR)).mpr heq.symm⟩

/-- Count complete matchings by branching on the next across word. -/
def matchingCount {α : Type*} (words : List (Finset α))
    (id : α → ℕ) (target used : Finset ℕ) : ℕ :=
  match words with
  | [] => if used = target then 1 else 0
  | A :: rest => ∑ c ∈ A,
      if id c ∈ used then 0
      else matchingCount rest id target (insert (id c) used)

/-- Cell sets generated by the same branching recurrence as `matchingCount`. -/
def matchingSets {α : Type*} [DecidableEq α] (words : List (Finset α))
    (id : α → ℕ) (target used : Finset ℕ) : Finset (Finset α) :=
  match words with
  | [] => if used = target then {∅} else ∅
  | A :: rest => A.biUnion fun c =>
      if id c ∈ used then ∅
      else (matchingSets rest id target (insert (id c) used)).image (insert c)

/-- Union of the cells in a list of word classes. -/
def wordUnion {α : Type*} [DecidableEq α] : List (Finset α) → Finset α
  | [] => ∅
  | A :: rest => A ∪ wordUnion rest

/-- Word classes do not overlap. -/
def DisjointWords {α : Type*} [DecidableEq α] : List (Finset α) → Prop
  | [] => True
  | A :: rest => Disjoint A (wordUnion rest) ∧ DisjointWords rest

/-- Intrinsic conditions on a partial matching after some down words have been used. -/
def SetMatchingSpec {α : Type*} [DecidableEq α] (words : List (Finset α))
    (id : α → ℕ) (target used : Finset ℕ) (R : Finset α) : Prop :=
  R ⊆ wordUnion words ∧
  (∀ A ∈ words, ∃! c, c ∈ R ∧ c ∈ A) ∧
  (∀ c ∈ R, ∀ d ∈ R, c ≠ d → id c ≠ id d) ∧
  (∀ c ∈ R, id c ∉ used) ∧
  R.image id ∪ used = target

theorem setMatchingSpec_cons_iff {α : Type*} [DecidableEq α]
    (A : Finset α) (rest : List (Finset α)) (id : α → ℕ)
    (target used : Finset ℕ) (R : Finset α)
    (hdis : Disjoint A (wordUnion rest)) :
    SetMatchingSpec (A :: rest) id target used R ↔
      ∃ c ∈ A, c ∈ R ∧ id c ∉ used ∧
        SetMatchingSpec rest id target (insert (id c) used) (R.erase c) := by
  classical
  have mem_tail (words : List (Finset α)) (c : α) :
      c ∈ wordUnion words ↔ ∃ B ∈ words, c ∈ B := by
    induction words with
    | nil => simp [wordUnion]
    | cons B tail ih =>
        simp only [wordUnion, Finset.mem_union, ih, List.mem_cons]
        constructor
        · rintro (hB | ⟨C, hC, hcC⟩)
          · exact ⟨B, Or.inl rfl, hB⟩
          · exact ⟨C, Or.inr hC, hcC⟩
        · rintro ⟨C, (rfl | hC), hcC⟩
          · exact Or.inl hcC
          · exact Or.inr ⟨C, hC, hcC⟩
  constructor
  · rintro ⟨hsub, hwords, hpair, hunused, hcover⟩
    obtain ⟨c, ⟨hcR, hcA⟩, huniq⟩ := hwords A (by simp)
    refine ⟨c, hcA, hcR, hunused c hcR, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxc, hxR⟩ := Finset.mem_erase.mp hx
      rcases Finset.mem_union.mp (hsub hxR) with hxA | hxT
      · exact False.elim (hxc (huniq x ⟨hxR, hxA⟩))
      · exact hxT
    · intro B hB
      obtain ⟨d, ⟨hdR, hdB⟩, huniqB⟩ := hwords B (by simp [hB])
      have hcB : c ∉ B := by
        intro h
        exact Finset.disjoint_left.mp hdis hcA
          ((mem_tail rest c).mpr ⟨B, hB, h⟩)
      have hdc : d ≠ c := by intro h; subst d; exact hcB hdB
      refine ⟨d, ⟨Finset.mem_erase.mpr ⟨hdc, hdR⟩, hdB⟩, ?_⟩
      intro e he
      exact huniqB e ⟨(Finset.mem_erase.mp he.1).2, he.2⟩
    · intro x hx y hy hxy
      exact hpair x (Finset.mem_erase.mp hx).2 y (Finset.mem_erase.mp hy).2 hxy
    · intro x hx hmem
      obtain ⟨hxc, hxR⟩ := Finset.mem_erase.mp hx
      rcases Finset.mem_insert.mp hmem with heq | hused
      · exact hpair x hxR c hcR hxc heq
      · exact hunused x hxR hused
    · have hR : R = insert c (R.erase c) := (Finset.insert_erase hcR).symm
      rw [hR] at hcover
      simpa [Finset.image_insert, Finset.union_insert,
        Finset.insert_union] using hcover
  · rintro ⟨c, hcA, hcR, hcUnused, htail⟩
    obtain ⟨hsub, hwords, hpair, hunused, hcover⟩ := htail
    have hR : R = insert c (R.erase c) := (Finset.insert_erase hcR).symm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hR]
      exact Finset.insert_subset_iff.mpr
        ⟨Finset.mem_union_left _ hcA, hsub.trans Finset.subset_union_right⟩
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · refine ⟨c, ⟨hcR, hcA⟩, ?_⟩
        intro x hx
        by_contra hxc
        have hxT : x ∈ R.erase c := Finset.mem_erase.mpr ⟨hxc, hx.1⟩
        exact Finset.disjoint_left.mp hdis hx.2 (hsub hxT)
      · obtain ⟨d, ⟨hdT, hdB⟩, huniq⟩ := hwords B hB
        refine ⟨d, ⟨(Finset.mem_erase.mp hdT).2, hdB⟩, ?_⟩
        intro x hx
        have hcB : c ∉ B := by
          intro h
          exact Finset.disjoint_left.mp hdis hcA
            ((mem_tail rest c).mpr ⟨B, hB, h⟩)
        have hxc : x ≠ c := by intro h; subst x; exact hcB hx.2
        exact huniq x ⟨Finset.mem_erase.mpr ⟨hxc, hx.1⟩, hx.2⟩
    · intro x hx y hy hxy heq
      rcases Finset.mem_insert.mp (hR ▸ hx) with rfl | hxT
      · rcases Finset.mem_insert.mp (hR ▸ hy) with h | hyT
        · exact hxy h.symm
        · exact hunused y hyT (Finset.mem_insert.mpr (Or.inl heq.symm))
      · rcases Finset.mem_insert.mp (hR ▸ hy) with rfl | hyT
        · exact hunused x hxT (Finset.mem_insert.mpr (Or.inl heq))
        · exact hpair x hxT y hyT hxy heq
    · intro x hx hused
      rcases Finset.mem_insert.mp (hR ▸ hx) with rfl | hxT
      · exact hcUnused hused
      · exact hunused x hxT (Finset.mem_insert.mpr (Or.inr hused))
    · rw [hR]
      simpa [Finset.image_insert, Finset.union_insert,
        Finset.insert_union] using hcover

theorem matchingSets_subset {α : Type*} [DecidableEq α]
    (words : List (Finset α)) (id : α → ℕ) (target used : Finset ℕ)
    (R : Finset α) (hR : R ∈ matchingSets words id target used) :
    R ⊆ wordUnion words := by
  classical
  induction words generalizing used R with
  | nil =>
      by_cases h : used = target
      · simp [matchingSets, h] at hR
        simp [hR, wordUnion]
      · simp [matchingSets, h] at hR
  | cons A rest ih =>
      obtain ⟨c, hc, hR⟩ := Finset.mem_biUnion.mp hR
      by_cases hused : id c ∈ used
      · simp [hused] at hR
      · have hR' : R ∈
            (matchingSets rest id target (insert (id c) used)).image (insert c) := by
          simpa [hused] using hR
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR'
        exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hc,
          (ih (insert (id c) used) S hS).trans (Finset.subset_union_right)⟩

/-- The numeric recurrence counts the generated cell sets when word classes are disjoint. -/
theorem matchingCount_eq_card_sets {α : Type*} [DecidableEq α]
    (words : List (Finset α)) (id : α → ℕ) (target used : Finset ℕ)
    (hdis : DisjointWords words) :
    matchingCount words id target used = (matchingSets words id target used).card := by
  classical
  induction words generalizing used with
  | nil =>
      by_cases h : used = target <;> simp [matchingCount, matchingSets, h]
  | cons A rest ih =>
      rcases hdis with ⟨hA, hrest⟩
      simp only [matchingCount, matchingSets]
      rw [Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro c hc
        by_cases hused : id c ∈ used
        · simp [hused]
        · simp only [hused, ↓reduceIte]
          rw [Finset.card_image_iff.mpr]
          · exact ih (insert (id c) used) hrest
          · intro S hS T hT heq
            have hcS : c ∉ S := by
              intro hcs
              exact Finset.disjoint_left.mp hA hc
                ((matchingSets_subset rest id target _ S hS) hcs)
            have hcT : c ∉ T := by
              intro hct
              exact Finset.disjoint_left.mp hA hc
                ((matchingSets_subset rest id target _ T hT) hct)
            have := congrArg (fun U : Finset α => U.erase c) heq
            simpa [Finset.erase_insert hcS, Finset.erase_insert hcT] using this
      · intro c hc d hd hne
        change Disjoint
          (if id c ∈ used then ∅ else
            (matchingSets rest id target (insert (id c) used)).image (insert c))
          (if id d ∈ used then ∅ else
            (matchingSets rest id target (insert (id d) used)).image (insert d))
        by_cases hcu : id c ∈ used
        · simp [hcu]
        by_cases hdu : id d ∈ used
        · simp [hdu]
        apply Finset.disjoint_left.mpr
        intro X hX hX'
        simp only [hcu, hdu, ↓reduceIte] at hX hX'
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨T, hT, heq⟩ := Finset.mem_image.mp hX'
        have hcT : c ∉ T := by
          intro hct
          exact Finset.disjoint_left.mp hA hc
            ((matchingSets_subset rest id target _ T hT) hct)
        have hcInsert : c ∈ insert d T := heq ▸ Finset.mem_insert_self c S
        rcases Finset.mem_insert.mp hcInsert with hcd | hct
        · exact hne hcd
        · exact hcT hct

/-- The generated sets are exactly the partial matchings specified by the word classes. -/
theorem matchingSets_iff_spec {α : Type*} [DecidableEq α]
    (words : List (Finset α)) (id : α → ℕ) (target used : Finset ℕ)
    (R : Finset α) (hdis : DisjointWords words) :
    R ∈ matchingSets words id target used ↔
      SetMatchingSpec words id target used R := by
  classical
  induction words generalizing used R with
  | nil =>
      constructor
      · intro h
        by_cases heq : used = target
        · have hR : R = ∅ := by simpa [matchingSets, heq] using h
          subst R
          simp [SetMatchingSpec, wordUnion, heq]
        · simp [matchingSets, heq] at h
      · rintro ⟨hsub, _, _, _, hcover⟩
        have hR : R = ∅ := Finset.subset_empty.mp hsub
        subst R
        have heq : used = target := by simpa using hcover
        simp [matchingSets, heq]
  | cons A rest ih =>
      obtain ⟨hA, hrest⟩ := hdis
      rw [setMatchingSpec_cons_iff A rest id target used R hA]
      constructor
      · intro h
        obtain ⟨c, hcA, hbranch⟩ := Finset.mem_biUnion.mp h
        by_cases hused : id c ∈ used
        · simp [hused] at hbranch
        · have hbranch' : R ∈
              (matchingSets rest id target (insert (id c) used)).image (insert c) := by
            simpa [hused] using hbranch
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hbranch'
          have hcS : c ∉ S := by
            intro hc
            exact Finset.disjoint_left.mp hA hcA
              ((matchingSets_subset rest id target _ S hS) hc)
          refine ⟨c, hcA, Finset.mem_insert_self _ _, hused, ?_⟩
          simpa [Finset.erase_insert hcS] using
            (ih (insert (id c) used) S hrest).mp hS
      · rintro ⟨c, hcA, hcR, hused, hspec⟩
        have hS := (ih (insert (id c) used) (R.erase c) hrest).mpr hspec
        apply Finset.mem_biUnion.mpr
        refine ⟨c, hcA, ?_⟩
        have hR : insert c (R.erase c) = R := Finset.insert_erase hcR
        simpa [hused] using
          (Finset.mem_image.mpr ⟨R.erase c, hS, hR⟩ :
            R ∈ (matchingSets rest id target (insert (id c) used)).image (insert c))

/-- The zero-indexed permutation `1,6,3,7,0,5,2,4`. -/
def witness : Equiv.Perm (Fin 8) where
  toFun := ![1, 6, 3, 7, 0, 5, 2, 4]
  invFun := ![4, 0, 6, 2, 7, 5, 1, 3]
  left_inv := by decide
  right_inv := by decide

/-- A row interval of the concrete grid. -/
def rowRun (i lo hi : ℕ) : Finset (Cell 8) :=
  Finset.univ.filter (fun c => c.1.val = i ∧ lo ≤ c.2.val ∧ c.2.val ≤ hi)

/-- The fourteen maximal across words of the concrete grid. -/
def witnessAcross : List (Finset (Cell 8)) :=
  [rowRun 0 0 0, rowRun 0 2 7,
   rowRun 1 0 5, rowRun 1 7 7,
   rowRun 2 0 2, rowRun 2 4 7,
   rowRun 3 0 6,
   rowRun 4 1 7,
   rowRun 5 0 4, rowRun 5 6 7,
   rowRun 6 0 1, rowRun 6 3 7,
   rowRun 7 0 3, rowRun 7 5 7]

/-- Labels of the fourteen maximal down words. -/
def witnessDownId (c : Cell 8) : ℕ :=
  match c.2.val with
  | 0 => if c.1.val ≤ 3 then 0 else 1
  | 1 => 2
  | 2 => if c.1.val ≤ 5 then 3 else 4
  | 3 => if c.1.val ≤ 1 then 5 else 6
  | 4 => 7
  | 5 => if c.1.val ≤ 4 then 8 else 9
  | 6 => if c.1.val = 0 then 10 else 11
  | _ => if c.1.val ≤ 2 then 12 else 13

/-- The finite matching checker returns 155 for the witness word graph. -/
theorem witness_matchingCount :
    matchingCount witnessAcross witnessDownId (Finset.range 14) ∅ = 155 := by
  decide

/-- A kernel-checked classification of every white cell and every pair of white cells. -/
def witnessData : WordData 8 (permGrid witness) where
  across := witnessAcross
  downId := witnessDownId
  downIds := Finset.range 14
  word_subset := by decide
  word_nonempty := by decide
  word_unique := by decide
  across_iff := by
    set_option maxRecDepth 4096 in decide
  down_iff := by
    set_option maxRecDepth 4096 in decide
  ids_eq := by decide

theorem result : ¬ claim := by
  intro h
  classical
  have mem_words (words : List (Finset (Cell 8))) (c : Cell 8) :
      c ∈ wordUnion words ↔ ∃ A ∈ words, c ∈ A := by
    induction words with
    | nil => simp [wordUnion]
    | cons A rest ih =>
        simp only [wordUnion, Finset.mem_union, ih, List.mem_cons]
        constructor
        · rintro (hA | ⟨B, hB, hcB⟩)
          · exact ⟨A, Or.inl rfl, hA⟩
          · exact ⟨B, Or.inr hB, hcB⟩
        · rintro ⟨B, (rfl | hB), hcB⟩
          · exact Or.inl hcB
          · exact Or.inr ⟨B, hB, hcB⟩
  have hunion : wordUnion witnessData.across = permGrid witness := by
    apply Finset.Subset.antisymm
    · intro c hc
      obtain ⟨A, hA, hcA⟩ := (mem_words witnessData.across c).mp hc
      exact witnessData.word_subset A hA hcA
    · intro c hc
      obtain ⟨A, ⟨hA, hcA⟩, _⟩ := witnessData.word_unique c hc
      exact (mem_words witnessData.across c).mpr ⟨A, hA, hcA⟩
  have hdis : DisjointWords witnessData.across := by
    simp only [witnessData, witnessAcross, DisjointWords,
      Finset.disjoint_iff_inter_eq_empty]
    set_option maxRecDepth 4096 in decide
  have hsets : matchingSets witnessData.across witnessData.downId witnessData.downIds ∅ =
      (permGrid witness).powerset.filter (IsRookPlacement (permGrid witness)) := by
    ext R
    rw [matchingSets_iff_spec witnessData.across witnessData.downId
      witnessData.downIds ∅ R hdis]
    simp only [Finset.mem_filter, Finset.mem_powerset]
    rw [rookPlacement_iff_wordMatching witnessData]
    simp [SetMatchingSpec, IsWordMatching, hunion]
  have hcount : rookCount (permGrid witness) = 155 := by
    calc
      rookCount (permGrid witness) =
          (matchingSets witnessData.across witnessData.downId witnessData.downIds ∅).card := by
        unfold rookCount
        exact congrArg Finset.card hsets.symm
      _ = matchingCount witnessData.across witnessData.downId witnessData.downIds ∅ :=
        (matchingCount_eq_card_sets witnessData.across witnessData.downId
          witnessData.downIds ∅ hdis).symm
      _ = 155 := witness_matchingCount
  have hex : ∃ n : ℕ, ∃ w : Equiv.Perm (Fin n),
      rookCount (permGrid w) = 155 := ⟨8, witness, hcount⟩
  have hmod := ((h 155 (by decide)).mp hex).2.2
  exact hmod (by decide)

#print axioms result

end D5.S3.Combinatorics.CrosswordPermutationGridRefutation

/- GID: D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration
   mirror-E: none(waiver:square-avoider-enumeration-generating-series-and-recurrence)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse]
   utility: none
   digest: Indecomposable counts, rational generating series, and order-seven recurrence. -/

import D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Exact counts of sum-indecomposable square-avoiders across all lengths, composition convolution,
    threshold of the conjectured recurrence, rational generating series over the integers, and the
    order-seven linear recurrence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration

open D5.S3.Combinatorics Nonnesting NonnestingBasicSum
open PermutationSquareDefs PermutationSquareStructure PermutationSquareCounting
open PermutationSquareFamilies PermutationSquareClassification
open scoped BigOperators

/-- Compositions of `n` into parts of size between `1` and `4` inclusive. -/
def boundedCompositions (n : ℕ) : Set (List ℕ) :=
  {parts | (∀ d ∈ parts, 1 ≤ d ∧ d ≤ 4) ∧ parts.sum = n}

/-- Number `c_n` of compositions of `n` into parts in `{1, 2, 3, 4}`. -/
noncomputable def c (n : ℕ) : ℕ := (boundedCompositions n).ncard

/-- Formal power series `B(X) = ∑_{n ≥ 0} b_n X^n` over `ℤ`. -/
noncomputable def seriesB : PowerSeries ℤ := PowerSeries.mk fun n => (b n : ℤ)

/-- Formal power series `A(X) = ∑_{n ≥ 1} a_n X^n` over `ℤ`. -/
noncomputable def seriesA : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℤ)

private theorem avoiders_finite (n : ℕ) : (avoiders n).Finite :=
  (List.finite_toSet (List.range' 1 n).permutations).subset fun _ hp =>
    List.mem_permutations.mpr hp.1

private theorem indecomposableAvoiders_finite (n : ℕ) : (indecomposableAvoiders n).Finite :=
  (avoiders_finite n).subset fun _ hp => hp.2.1

private theorem sublist_len3_of_len4 {u v w x₀ x₁ x₂ x₃ : ℕ}
    (h : [u, v, w].Sublist [x₀, x₁, x₂, x₃]) :
    [u, v, w] = [x₁, x₂, x₃] ∨ [u, v, w] = [x₀, x₂, x₃] ∨
      [u, v, w] = [x₀, x₁, x₃] ∨ [u, v, w] = [x₀, x₁, x₂] := by
  cases h with
  | cons _ h1 => exact Or.inl (h1.eq_of_length rfl)
  | cons_cons _ h1 =>
    cases h1 with
    | cons _ h2 => exact Or.inr (Or.inl (by rw [h2.eq_of_length rfl]))
    | cons_cons _ h2 =>
      cases h2 with
      | cons _ h3 => exact Or.inr (Or.inr (Or.inl (by rw [h3.eq_of_length rfl])))
      | cons_cons _ _ => exact Or.inr (Or.inr (Or.inr rfl))

private theorem b_one : b 1 = 1 := by
  have hset : indecomposableAvoiders 1 = {[1]} := by
    ext p
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hp
      have hlen : p.length = 1 := by simpa using hp.2.1.1.length_eq
      rcases p with _ | ⟨x, _ | _⟩
      · simp at hlen
      · have hx : x ∈ ([1] : List ℕ) := by simpa using hp.2.1.1.mem_iff.mp (by simp)
        simp only [List.mem_singleton] at hx
        rw [hx]
      · simp at hlen
    · rintro rfl
      refine ⟨by simp, ⟨List.Perm.refl _, ?_, ?_, ?_⟩, by unfold sumIndecomposable; decide⟩
      · rintro ⟨_, _, _, hsub, _⟩; have hle := hsub.length_le; simp at hle
      · rintro ⟨_, _, _, hsub, _⟩; have hle := hsub.length_le; simp at hle
      · rintro ⟨_, _, _, hsub, _⟩; have hle := hsub.length_le; simp [square] at hle
  simp [b, hset]

private theorem b_two : b 2 = 1 := by
  have hset : indecomposableAvoiders 2 = {[2, 1]} := by
    ext p
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hp
      have hlen : p.length = 2 := by simpa using hp.2.1.1.length_eq
      have hend : p.getD 1 0 = 1 :=
        (indecomposable_shape_and_prefix_iff.2.2.2.2 2 (by omega) p hp).1.1
      rcases p with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
      · simp at hlen
      · simp at hlen
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at hend
        subst hend
        have h2 : 2 ∈ [x, 1] := hp.2.1.1.mem_iff.mpr (by decide)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with h2 | h2
        · rw [← h2]
        · omega
      · simp at hlen
    · rintro rfl
      have hI2 : familyI 2 = [2, 1] := by decide
      simpa [hI2] using seven_families_admissible_and_distinct.1 2 (by omega)
  simp [b, hset]

private theorem b_three : b 3 = 2 := by
  have h321 : [3, 2, 1] ∈ indecomposableAvoiders 3 := by
    refine ⟨by simp, ⟨by decide, ?_, ?_, ?_⟩, by unfold sumIndecomposable; decide⟩
    · rintro ⟨v, hmono, _, hsub, _⟩
      have heq := hsub.eq_of_length (by simp)
      simp only [List.map, List.cons.injEq] at heq
      have h12 : v 1 < v 2 := hmono 1 (by omega) (by change 1 < 3; omega)
      omega
    · rintro ⟨_, _, _, hsub, _⟩; have hle := hsub.length_le; simp at hle
    · have hsq : square [3, 2, 1] = [1, 2, 3] := by decide
      rw [hsq]
      rintro ⟨v, hmono, _, hsub, _⟩
      have heq := hsub.eq_of_length (by simp)
      simp only [List.map, List.cons.injEq] at heq
      have h23 : v 2 < v 3 := hmono 2 (by omega) (by change 2 < 3; omega)
      omega
  have hset : indecomposableAvoiders 3 = {[2, 3, 1], [3, 2, 1]} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hp
      have hlen : p.length = 3 := by simpa using hp.2.1.1.length_eq
      have hend : p.getD 2 0 = 1 :=
        (indecomposable_shape_and_prefix_iff.2.2.2.2 3 (by omega) p hp).1.1
      rcases p with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩
      · simp at hlen
      · simp at hlen
      · simp at hlen
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at hend
        subst hend
        have hnd : ([x, y, 1] : List ℕ).Nodup := hp.2.1.1.nodup_iff.mpr (List.nodup_range' 1)
        have h2 : 2 ∈ [x, y, 1] := hp.2.1.1.mem_iff.mpr (by decide)
        have h3 : 3 ∈ [x, y, 1] := hp.2.1.1.mem_iff.mpr (by decide)
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
          not_false_eq_true, List.nodup_nil, and_true, or_false] at hnd h2 h3
        rcases (by omega : (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp at hlen
    · rintro (rfl | rfl)
      · have hI3 : familyI 3 = [2, 3, 1] := by decide
        simpa [hI3] using seven_families_admissible_and_distinct.1 3 (by omega)
      · exact h321
  rw [b, hset, Set.ncard_pair (by decide)]

private theorem b_four : b 4 = 3 := by
  have h3241 : [3, 2, 4, 1] ∈ indecomposableAvoiders 4 := by
    refine ⟨by simp, ⟨by decide, ?_, ?_, ?_⟩, by unfold sumIndecomposable; decide⟩
    · rintro ⟨v, hmono, _, hsub, _⟩
      have h12 : v 1 < v 2 := hmono 1 (by omega) (by change 1 < 3; omega)
      have h23 : v 2 < v 3 := hmono 2 (by omega) (by change 2 < 3; omega)
      simp only [List.map] at hsub
      rcases sublist_len3_of_len4 hsub with h | h | h | h <;>
        simp only [List.cons.injEq] at h <;> omega
    · rintro ⟨_, _, _, hsub, _⟩; have hle := hsub.length_le; simp at hle
    · have hsq : square [3, 2, 4, 1] = [4, 2, 1, 3] := by decide
      rw [hsq]
      rintro ⟨v, hmono, _, hsub, _⟩
      have h12 : v 1 < v 2 := hmono 1 (by omega) (by change 1 < 3; omega)
      have h23 : v 2 < v 3 := hmono 2 (by omega) (by change 2 < 3; omega)
      simp only [List.map] at hsub
      rcases sublist_len3_of_len4 hsub with h | h | h | h <;>
        simp only [List.cons.injEq] at h <;> omega
  have hnot3421 : [3, 4, 2, 1] ∉ indecomposableAvoiders 4 := by
    intro hp
    apply hp.2.1.2.2.2
    have hsq : square [3, 4, 2, 1] = [2, 1, 4, 3] := by decide
    rw [hsq]
    let vals : ℕ → ℕ := fun r => if r = 1 then 1 else if r = 2 then 3 else 4
    refine ⟨vals, ?_, ?_, by decide, by simp⟩
    · intro r hr1 hr2
      change r < 3 at hr2
      rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl <;> simp [vals]
    · intro r hr1 hr2
      change r ≤ 3 at hr2
      rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;> simp [vals]
  have hset : indecomposableAvoiders 4 = {[2, 3, 4, 1], [3, 2, 4, 1], [4, 3, 2, 1]} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hp
      have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 4 (by omega) p hp
      have hbnd : 2 ≤ p.getD 0 0 ∧ p.getD 0 0 ≤ 4 := ⟨hsh.2.1.1, hsh.2.1.2.1⟩
      rcases (by omega : p.getD 0 0 = 2 ∨ p.getD 0 0 = 3 ∨ p.getD 0 0 = 4) with h2 | h3 | h4
      · rcases (first_entry_two_and_three_classification.1 4 (by omega)).1 p |>.mp ⟨hp, h2⟩ with
          rfl | ⟨h5, _⟩ | ⟨h6, _⟩
        · exact Or.inl (by decide)
        · omega
        · omega
      · have hlen : p.length = 4 := by simpa using hp.2.1.1.length_eq
        have hend : p.getD 3 0 = 1 := hsh.1.1
        rcases p with _ | ⟨w, _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩⟩
        · simp at hlen
        · simp at hlen
        · simp at hlen
        · simp at hlen
        · simp only [List.getD_cons_zero] at h3
          simp only [List.getD_cons_succ, List.getD_cons_zero] at hend
          subst h3; subst hend
          have hnd : ([3, x, y, 1] : List ℕ).Nodup := hp.2.1.1.nodup_iff.mpr (List.nodup_range' 1)
          have hm2 : 2 ∈ [3, x, y, 1] := hp.2.1.1.mem_iff.mpr (by decide)
          have hm4 : 4 ∈ [3, x, y, 1] := hp.2.1.1.mem_iff.mpr (by decide)
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            not_false_eq_true, List.nodup_nil, and_true, or_false] at hnd hm2 hm4
          rcases (by omega : (x = 2 ∧ y = 4) ∨ (x = 4 ∧ y = 2)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inl rfl)
          · exact False.elim (hnot3421 hp)
        · simp at hlen
      · rcases (first_entry_four_classification 4 (by omega)).1 p |>.mp ⟨hp, h4⟩ with
          rfl | ⟨h6, _⟩ | ⟨h7, _⟩ | ⟨h9, _⟩
        · exact Or.inr (Or.inr (by decide))
        · omega
        · omega
        · omega
    · rintro (rfl | rfl | rfl)
      · have hI4 : familyI 4 = [2, 3, 4, 1] := by decide
        simpa [hI4] using seven_families_admissible_and_distinct.1 4 (by omega)
      · exact h3241
      · have hc4 : familyC 4 = [4, 3, 2, 1] := by decide
        simpa [hc4] using seven_families_admissible_and_distinct.2.2.2.2.2.1 4 (by omega)
  rw [b, hset, Set.ncard_insert_of_notMem (by simp), Set.ncard_pair (by decide)]

private theorem b_ge_five (n : ℕ) (hn : 5 ≤ n) :
    b n = n / 2 + (if n ≤ 5 then 1 else if n = 6 then 2 else if n ≤ 8 then 3 else 4) := by
  let S2 : Set (List ℕ) := {p ∈ indecomposableAvoiders n | p.getD 0 0 = 2}
  let S4 : Set (List ℕ) := {p ∈ indecomposableAvoiders n | p.getD 0 0 = 4}
  have hunion : indecomposableAvoiders n = S2 ∪ S4 := by
    ext p
    change p ∈ indecomposableAvoiders n ↔
      (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 2) ∨
      (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 4)
    constructor
    · intro hp
      have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p hp
      have hbnd : 2 ≤ p.getD 0 0 ∧ p.getD 0 0 ≤ 4 := ⟨hsh.2.1.1, hsh.2.1.2.1⟩
      have hne3 := first_entry_two_and_three_classification.2 n hn p hp
      rcases (by omega : p.getD 0 0 = 2 ∨ p.getD 0 0 = 4) with h2 | h4
      · exact Or.inl ⟨hp, h2⟩
      · exact Or.inr ⟨hp, h4⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint S2 S4 := Set.disjoint_left.mpr fun _ h1 h2 => by
    change _ ∧ _ = 2 at h1; change _ ∧ _ = 4 at h2; omega
  have hf2 : S2.Finite := (indecomposableAvoiders_finite n).subset fun _ h => h.1
  have hf4 : S4.Finite := (indecomposableAvoiders_finite n).subset fun _ h => h.1
  rw [b, hunion, Set.ncard_union_eq hdisj hf2 hf4]
  have hc2 := (first_entry_two_and_three_classification.1 n (by omega)).2
  have hc4 := (first_entry_four_classification n (by omega)).2
  change S2.ncard = _ at hc2
  change S4.ncard = _ at hc4
  rw [hc2, hc4]
  have hne4 : n ≠ 4 := by omega
  simp only [hne4, ↓reduceIte]
  split_ifs <;> rfl

private theorem b_formula (n : ℕ) :
    b n = if n = 0 then 0 else if n ≤ 2 then 1 else if n = 3 then 2 else
      if n ≤ 5 then 3 else if n = 6 then 5 else if n = 7 then 6 else
      if n = 8 then 7 else n / 2 + 4 := by
  by_cases h5 : 5 ≤ n
  · rw [b_ge_five n h5]
    by_cases h9 : 9 ≤ n
    · have : ¬ n = 0 ∧ ¬ n ≤ 2 ∧ ¬ n = 3 ∧ ¬ n ≤ 5 ∧ ¬ n = 6 ∧ ¬ n = 7 ∧ ¬ n = 8 ∧ ¬ n ≤ 8 := by
        omega
      simp only [this, ↓reduceIte]
    · rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) with rfl | rfl | rfl | rfl <;> simp
  · rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl
    · simp [indecomposable_shape_and_prefix_iff.1]
    · simp [b_one]
    · simp [b_two]
    · simp [b_three]
    · simp [b_four]

private theorem boundedCompositions_zero : boundedCompositions 0 = {[]} := by
  ext parts
  change ((∀ d ∈ parts, 1 ≤ d ∧ d ≤ 4) ∧ parts.sum = 0) ↔ parts = []
  constructor
  · rintro ⟨hb, hs⟩
    cases parts with
    | nil => rfl
    | cons d rest => have := (hb d (by simp)).1; simp at hs; omega
  · rintro rfl; simp

private theorem c_zero : c 0 = 1 := by simp [c, boundedCompositions_zero]

private theorem boundedCompositions_finite : ∀ m : ℕ, (boundedCompositions m).Finite := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [boundedCompositions_zero]; exact Set.finite_singleton []
    · have hfin : (⋃ d ∈ (Finset.Icc 1 (min 4 m) : Set ℕ),
          (List.cons d) '' boundedCompositions (m - d)).Finite :=
        (Finset.finite_toSet _).biUnion fun d hd => by
          simp only [Finset.mem_coe, Finset.mem_Icc] at hd
          exact (ih (m - d) (by omega)).image _
      refine hfin.subset ?_
      rintro parts ⟨hb, hs⟩
      cases parts with
      | nil => simp at hs; omega
      | cons d rest =>
        have hd := hb d (by simp)
        simp only [List.sum_cons] at hs
        refine Set.mem_iUnion₂.mpr
          ⟨d, ?_, rest, ⟨fun x hx => hb x (by simp [hx]), by omega⟩, rfl⟩
        simp only [Finset.mem_coe, Finset.mem_Icc]; omega

private theorem c_pos (m : ℕ) (hm : 1 ≤ m) :
    c m = ∑ d ∈ Finset.Icc 1 (min 4 m), c (m - d) := by
  classical
  let Dom := Σ d : Finset.Icc 1 (min 4 m), boundedCompositions (m - d.val)
  let build : Dom → boundedCompositions m := fun entry =>
    ⟨entry.1.val :: entry.2.val, by
      have hd := Finset.mem_Icc.mp entry.1.property
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact entry.2.property.1 x hx
      · simp only [List.sum_cons, entry.2.property.2]; omega⟩
  have hinj : Function.Injective build := by
    rintro ⟨d1, r1⟩ ⟨d2, r2⟩ heq
    have hcons := List.cons.inj (congrArg Subtype.val heq)
    have hd : d1 = d2 := Subtype.ext hcons.1
    subst hd
    exact congrArg (Sigma.mk d1) (Subtype.ext hcons.2)
  have hsurj : Function.Surjective build := by
    rintro ⟨parts, hb, hs⟩
    cases parts with
    | nil => simp at hs; omega
    | cons d rest =>
      have hd := hb d (by simp)
      simp only [List.sum_cons] at hs
      have hrsum : rest.sum = m - d := by omega
      refine ⟨⟨⟨d, Finset.mem_Icc.mpr (by omega)⟩,
        ⟨rest, fun x hx => hb x (by simp [hx]), hrsum⟩⟩, rfl⟩
  let (d : Finset.Icc 1 (min 4 m)) : Finite (boundedCompositions (m - d.val)) :=
    (boundedCompositions_finite _).to_subtype
  let : Finite (boundedCompositions m) := (boundedCompositions_finite m).to_subtype
  have hcard := Nat.card_congr (Equiv.ofBijective build ⟨hinj, hsurj⟩)
  rw [Nat.card_sigma] at hcard
  simp only [Nat.card_coe_set_eq] at hcard
  change c m = _
  unfold c
  exact hcard.symm.trans ((Finset.Icc 1 (min 4 m)).sum_attach fun d =>
    (boundedCompositions (m - d)).ncard)

private theorem c_small : c 1 = 1 ∧ c 2 = 2 ∧ c 3 = 4 := by
  have hc1 : c 1 = 1 := by
    rw [c_pos 1 (by omega)]
    change ∑ d ∈ Finset.Icc 1 1, c (1 - d) = 1
    simp [c_zero]
  have hc2 : c 2 = 2 := by
    rw [c_pos 2 (by omega)]
    change ∑ d ∈ Finset.Icc 1 2, c (2 - d) = 2
    rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
    simp [hc1, c_zero]
  have hc3 : c 3 = 4 := by
    rw [c_pos 3 (by omega)]
    change ∑ d ∈ Finset.Icc 1 3, c (3 - d) = 4
    rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
    simp [hc2, hc1, c_zero]
  exact ⟨hc1, hc2, hc3⟩

private theorem assemble_length :
    ∀ parts : List (List ℕ),
      (FishburnTenThirteen.FishburnBasicComponents.assemble parts).length =
        (parts.map List.length).sum
  | [] => by simp [FishburnTenThirteen.FishburnBasicComponents.assemble]
  | block :: rest => by
    simp [FishburnTenThirteen.FishburnBasicComponents.assemble, directSum, shift,
      assemble_length rest]

private theorem dec_block_props (d : ℕ) (hd : 1 ≤ d) :
    let blk := (List.range' 1 d).reverse
    blk ≠ [] ∧ blk.length = d ∧ blk.Perm (List.range' 1 blk.length) ∧
      sumIndecomposable blk := by
  intro blk
  have hne : blk ≠ [] := by simp [blk]; omega
  have hlen : blk.length = d := by simp [blk]
  have hperm : blk.Perm (List.range' 1 blk.length) := by
    rw [hlen]; exact List.reverse_perm _
  have hend : blk.getLast? = some 1 := by
    cases d with
    | zero => omega
    | succ m => rw [show blk = (List.range' 1 (m + 1)).reverse from rfl, List.getLast?_reverse]; rfl
  have hind : sumIndecomposable blk :=
    indecomposable_shape_and_prefix_iff.2.2.2.1 d blk hd (by simpa [hlen] using hperm) hend
  exact ⟨hne, hlen, hperm, hind⟩

private theorem a_convolution (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ k ∈ Finset.Icc 1 n, b k * c (n - k) := by
  classical
  let assemble := FishburnTenThirteen.FishburnBasicComponents.assemble
  let dec (d : ℕ) : List ℕ := (List.range' 1 d).reverse
  let Dom := Σ k : Finset.Icc 1 n, indecomposableAvoiders k.val × boundedCompositions (n - k.val)
  have hmap_len (parts : List ℕ) : ((parts.map dec).map List.length) = parts := by
    induction parts with
    | nil => rfl
    | cons d rest ih => simp [dec, ih]
  have hrecover : ∀ L : List (List ℕ),
      (∀ blk ∈ L, blk = (List.range' 1 blk.length).reverse) →
      (L.map List.length).map dec = L := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons blk rest ih =>
      intro hL
      have hb := hL blk (by simp)
      simp only [List.map_cons, dec, ← hb,
        ih (fun item hi => hL item (List.mem_cons_of_mem blk hi))]
  let build : Dom → avoiders n := fun entry =>
    let first := entry.2.1.val
    let parts := entry.2.2.val
    let tail := parts.map dec
    ⟨assemble (first :: tail), by
      have hk := Finset.mem_Icc.mp entry.1.property
      have hflen : first.length = entry.1.val := by simpa using entry.2.1.property.2.1.1.length_eq
      have hfav : first ∈ avoiders first.length := by
        simpa [hflen] using entry.2.1.property.2.1
      have htail : ∀ blk ∈ tail, blk ≠ [] ∧ blk = (List.range' 1 blk.length).reverse ∧
          blk.length ≤ 4 := by
        intro blk hblk
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hblk
        have hdb := entry.2.2.property.1 d hd
        simp [dec, hdb.2, Nat.ne_of_gt hdb.1]
      have hadm := admissible_layered_tail first tail entry.2.1.property.1 hfav htail
      change assemble (first :: tail) ∈ avoiders (assemble (first :: tail)).length at hadm
      have htot : (assemble (first :: tail)).length = n := by
        rw [assemble_length]
        dsimp only [tail, parts]
        rw [List.map_cons, List.sum_cons, hflen, hmap_len, entry.2.2.property.2]
        omega
      rwa [htot] at hadm⟩
  have hblocks_ok (k : Finset.Icc 1 n) (f : indecomposableAvoiders k.val)
      (p : boundedCompositions (n - k.val)) :
      ∀ blk ∈ (f.val :: p.val.map dec),
        blk ≠ [] ∧ blk.Perm (List.range' 1 blk.length) ∧ sumIndecomposable blk := by
    intro blk hblk
    rcases List.mem_cons.mp hblk with rfl | hmem
    · have hflen : f.val.length = k.val := by simpa using f.property.2.1.1.length_eq
      exact ⟨f.property.1, by simpa [hflen] using f.property.2.1.1, f.property.2.2⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem
      have hpr := dec_block_props d (p.property.1 d hd).1
      exact ⟨hpr.1, hpr.2.2.1, hpr.2.2.2⟩
  have hinj : Function.Injective build := by
    rintro ⟨k1, f1, p1⟩ ⟨k2, f2, p2⟩ heq
    have hval := congrArg Subtype.val heq
    let w := (build ⟨k1, f1, p1⟩).val
    have hw : w.Perm (List.range' 1 n) := (build ⟨k1, f1, p1⟩).property.1
    have hwlen : w.length = n := by simpa using hw.length_eq
    have huc := FishburnTenThirteen.FishburnBasicComponents.unique_sum_components n w hw []
      (by simp)
    obtain ⟨u, _, huniq⟩ := huc.1
    let L1 := f1.val :: p1.val.map dec
    let L2 := f2.val :: p2.val.map dec
    have hb1 := hblocks_ok k1 f1 p1
    have hb2 := hblocks_ok k2 f2 p2
    have hiff1 := huc.2.1 L1 hb1
    have hiff2 := huc.2.1 L2 hb2
    change FishburnTenThirteen.FishburnBasicComponents.assemble L1 =
      FishburnTenThirteen.FishburnBasicComponents.assemble L2 at hval
    have ha1 : FishburnTenThirteen.FishburnBasicComponents.assemble L1 = w := rfl
    have ha2 : FishburnTenThirteen.FishburnBasicComponents.assemble L2 = w := hval.symm
    rw [ha1, hwlen] at hiff1
    rw [ha2, hwlen] at hiff2
    have hu1 : L1 = u := huniq L1 ⟨ha1, hb1, hiff1⟩
    have hu2 : L2 = u := huniq L2 ⟨ha2, hb2, hiff2⟩
    have hL : L1 = L2 := hu1.trans hu2.symm
    have hcons := List.cons.inj hL
    have hf_eq : f1.val = f2.val := hcons.1
    have hk_eq : k1 = k2 := by
      apply Subtype.ext
      have hl1 : f1.val.length = k1.val := by simpa using f1.property.2.1.1.length_eq
      have hl2 : f2.val.length = k2.val := by simpa using f2.property.2.1.1.length_eq
      rw [← hl1, ← hl2, hf_eq]
    subst hk_eq
    have hp_eq : p1.val = p2.val := by
      have hm := congrArg (List.map List.length) hcons.2
      simpa [hmap_len] using hm
    exact congrArg (Sigma.mk k1) (Prod.ext (Subtype.ext hf_eq) (Subtype.ext hp_eq))
  have hsurj : Function.Surjective build := by
    rintro ⟨w, hw⟩
    obtain ⟨first, tail, hweq, hfne, hfav, hfind, htail⟩ :=
      avoider_layered_tail n w (by omega) hw
    have hwlen : w.length = n := by simpa using hw.1.length_eq
    have hsum : first.length + (tail.map List.length).sum = n := by
      have hl := congrArg List.length hweq
      rw [hwlen] at hl
      have hal := assemble_length (first :: tail)
      simp only [FishburnTenThirteen.FishburnBasicComponents.assemble,
        List.map_cons, List.sum_cons] at hal
      omega
    have hpos : 1 ≤ first.length := List.length_pos_iff.mpr hfne
    let k : Finset.Icc 1 n := ⟨first.length, Finset.mem_Icc.mpr ⟨hpos, by omega⟩⟩
    let f : indecomposableAvoiders k.val := ⟨first, hfne, hfav, hfind⟩
    let p : boundedCompositions (n - k.val) := ⟨tail.map List.length, by
      refine ⟨?_, by dsimp [k]; omega⟩
      intro d hd
      obtain ⟨blk, hblk, rfl⟩ := List.mem_map.mp hd
      have hb := htail blk hblk
      exact ⟨List.length_pos_iff.mpr hb.1, hb.2.2⟩⟩
    refine ⟨⟨k, f, p⟩, Subtype.ext ?_⟩
    change assemble (first :: (tail.map List.length).map dec) = w
    rw [hrecover tail (fun blk hblk => (htail blk hblk).2.1)]
    exact hweq.symm
  let (k : Finset.Icc 1 n) : Finite (indecomposableAvoiders k.val) :=
    (indecomposableAvoiders_finite _).to_subtype
  let (k : Finset.Icc 1 n) : Finite (boundedCompositions (n - k.val)) :=
    (boundedCompositions_finite _).to_subtype
  let : Finite (avoiders n) := (avoiders_finite n).to_subtype
  have hcard := Nat.card_congr (Equiv.ofBijective build ⟨hinj, hsurj⟩)
  rw [Nat.card_sigma] at hcard
  simp only [Nat.card_prod, Nat.card_coe_set_eq] at hcard
  change a n = _
  unfold a b c
  exact hcard.symm.trans ((Finset.Icc 1 n).sum_attach fun k =>
    (indecomposableAvoiders k).ncard * (boundedCompositions (n - k)).ncard)

private theorem a_small : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 5 ∧ a 4 = 11 := by
  obtain ⟨hc1, hc2, hc3⟩ := c_small
  have ha1 : a 1 = 1 := by
    rw [a_convolution 1 (by omega)]
    simp [b_one, c_zero]
  have ha2 : a 2 = 2 := by
    rw [a_convolution 2 (by omega), show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
    simp [b_one, b_two, hc1, c_zero]
  have ha3 : a 3 = 5 := by
    rw [a_convolution 3 (by omega), show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
    simp [b_one, b_two, b_three, hc2, hc1, c_zero]
  have ha4 : a 4 = 11 := by
    rw [a_convolution 4 (by omega), show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
    simp [b_one, b_two, b_three, b_four, hc3, hc2, hc1, c_zero]
  exact ⟨ha1, ha2, ha3, ha4⟩

section CountBoundary
attribute [local instance 2000] Classical.propDecidable

/-- Closed-form counts `b_n` of indecomposable square-avoiders, the composition convolution for
    `a_n`, and the exact validity threshold `6 ≤ n ≤ 10` of the conjectured recurrence. -/
theorem indecomposable_count_and_recurrence_boundary :
    (∀ n : ℕ, b n = if n = 0 then 0 else if n ≤ 2 then 1 else if n = 3 then 2 else
      if n ≤ 5 then 3 else if n = 6 then 5 else if n = 7 then 6 else
      if n = 8 then 7 else n / 2 + 4) ∧
    b 1 = 1 ∧ b 2 = 1 ∧ b 3 = 2 ∧ b 4 = 3 ∧ b 5 = 3 ∧ b 6 = 5 ∧ b 7 = 6 ∧ b 8 = 7 ∧
    (∀ n : ℕ, 9 ≤ n → b n = n / 2 + 4) ∧
    c 0 = 1 ∧ (∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Icc 1 n, b k * c (n - k)) ∧
    (∀ n : ℕ, 6 ≤ n →
      (a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + (n - 1) ↔ n ≤ 10)) ∧
    (∀ n : ℕ, 11 ≤ n →
      a n < a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + (n - 1)) ∧
    (∀ n : ℕ, 5 ≤ n → a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + b n) ∧
    (∀ n : ℕ, 6 ≤ n →
      (a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + (n - 1) ↔ b n = n - 1)) ∧
    (∀ n : ℕ, 6 ≤ n → n ≤ 10 → b n = n - 1) ∧
    (∀ n : ℕ, 11 ≤ n → b n < n - 1) := by
  classical
  have hb5 : b 5 = 3 := by rw [b_formula]; norm_num
  have hb6 : b 6 = 5 := by rw [b_formula]; norm_num
  have hb7 : b 7 = 6 := by rw [b_formula]; norm_num
  have hb8 : b 8 = 7 := by rw [b_formula]; norm_num
  have hb9 : ∀ n : ℕ, 9 ≤ n → b n = n / 2 + 4 := by
    intro n hn
    rw [b_formula]
    have : ¬ n = 0 ∧ ¬ n ≤ 2 ∧ ¬ n = 3 ∧ ¬ n ≤ 5 ∧ ¬ n = 6 ∧ ¬ n = 7 ∧ ¬ n = 8 := by omega
    simp [this]
  have hrec_b : ∀ n : ℕ, 5 ≤ n →
      a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + b n := by
    intro n hn
    rw [count_recurrence n hn, ← (indecomposable_shape_and_prefix_iff.2.1 n (by omega)).2]
  refine ⟨fun n => by rw [b_formula n]; split_ifs <;> rfl, b_one, b_two, b_three, b_four, hb5,
    hb6, hb7, hb8, hb9, c_zero, a_convolution, ?_, ?_, hrec_b, ?_, ?_, ?_⟩
  · intro n hn
    rw [hrec_b n (by omega)]
    by_cases h9 : 9 ≤ n
    · rw [hb9 n h9]; omega
    · rcases (by omega : n = 6 ∨ n = 7 ∨ n = 8) with rfl | rfl | rfl <;>
        simp [hb6, hb7, hb8]
  · intro n hn
    rw [hrec_b n (by omega), hb9 n (by omega)]
    omega
  · intro n hn
    rw [hrec_b n (by omega)]
    omega
  · intro n hn6 hn10
    by_cases h9 : 9 ≤ n
    · rw [hb9 n h9]; omega
    · rcases (by omega : n = 6 ∨ n = 7 ∨ n = 8) with rfl | rfl | rfl <;>
        simp [hb6, hb7, hb8]
  · intro n hn
    rw [hb9 n (by omega)]
    omega

end CountBoundary

private theorem coeff_mul_X_eq (f : PowerSeries ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (f * PowerSeries.X) =
      if 1 ≤ n then (PowerSeries.coeff (n - 1)) f else 0 := by
  simpa using PowerSeries.coeff_mul_X_pow' f 1 n

/-- Rational generating series for `b_n` and `a_n` over `ℤ[[X]]` and the resulting order-seven
    linear recurrence for `a_n` when `n ≥ 12`. -/
theorem generating_series_and_order_seven_recurrence :
    let num : PowerSeries ℤ := PowerSeries.X + PowerSeries.X ^ 4 - PowerSeries.X ^ 5 +
      PowerSeries.X ^ 6 + PowerSeries.X ^ 7 - PowerSeries.X ^ 8 - PowerSeries.X ^ 11
    let denB : PowerSeries ℤ := (1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2)
    let denC : PowerSeries ℤ :=
      1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4
    let denA : PowerSeries ℤ := denB * denC
    PowerSeries.constantCoeff seriesB = 0 ∧ PowerSeries.constantCoeff seriesA = 0 ∧
    IsUnit denB ∧ IsUnit denC ∧ IsUnit denA ∧
    seriesA * denC = seriesB ∧ seriesA = seriesB * Ring.inverse denC ∧
    seriesB * denB = num ∧ seriesB = num * Ring.inverse denB ∧
    seriesA * denA = num ∧ seriesA = num * Ring.inverse denA ∧
    denA = (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 5 - PowerSeries.X ^ 7 : PowerSeries ℤ) ∧
    (∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) -
      2 * (a (n - 3) : ℤ) - (a (n - 5) : ℤ) + (a (n - 7) : ℤ)) := by
  intro num denB denC denA
  obtain ⟨ha1, ha2, ha3, ha4⟩ := a_small
  have hb0 : b 0 = 0 := indecomposable_shape_and_prefix_iff.1
  have hb9 : ∀ m : ℕ, 9 ≤ m → b m = m / 2 + 4 :=
    indecomposable_count_and_recurrence_boundary.2.2.2.2.2.2.2.2.2.1
  have hrecA : ∀ n : ℕ, 5 ≤ n →
      a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + b n := by
    intro n hn
    rw [count_recurrence n hn, ← (indecomposable_shape_and_prefix_iff.2.1 n (by omega)).2]
  have hcB : PowerSeries.constantCoeff seriesB = 0 := by simp [seriesB, hb0]
  have hcA : PowerSeries.constantCoeff seriesA = 0 := by simp [seriesA]
  have huB : IsUnit denB := by rw [PowerSeries.isUnit_iff_constantCoeff]; simp [denB]
  have huC : IsUnit denC := by rw [PowerSeries.isUnit_iff_constantCoeff]; simp [denC]
  have huA : IsUnit denA := by rw [PowerSeries.isUnit_iff_constantCoeff]; simp [denA, denB, denC]
  have hAC : seriesA * denC = seriesB := by
    apply PowerSeries.ext; intro n
    rw [show seriesA * denC = seriesA - seriesA * PowerSeries.X - seriesA * PowerSeries.X ^ 2 -
      seriesA * PowerSeries.X ^ 3 - seriesA * PowerSeries.X ^ 4 by dsimp only [denC]; ring]
    simp only [map_sub, coeff_mul_X_eq, PowerSeries.coeff_mul_X_pow', seriesA, seriesB,
      PowerSeries.coeff_mk]
    by_cases h5 : 5 ≤ n
    · have hr := hrecA n h5
      have h0 : n ≠ 0 := by omega
      have h1 : 1 ≤ n ∧ n - 1 ≠ 0 := by omega
      have h2 : 2 ≤ n ∧ n - 2 ≠ 0 := by omega
      have h3 : 3 ≤ n ∧ n - 3 ≠ 0 := by omega
      have h4 : 4 ≤ n ∧ n - 4 ≠ 0 := by omega
      simp only [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, ↓reduceIte]
      omega
    · rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with
        rfl | rfl | rfl | rfl | rfl <;>
        simp [b_formula, ha1, ha2, ha3, ha4]
  have hBB : seriesB * denB = num := by
    apply PowerSeries.ext; intro n
    rw [show seriesB * denB = seriesB - seriesB * PowerSeries.X - seriesB * PowerSeries.X ^ 2 +
      seriesB * PowerSeries.X ^ 3 by dsimp only [denB]; ring]
    simp only [num, map_add, map_sub, coeff_mul_X_eq, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X, PowerSeries.coeff_X_pow, seriesB, PowerSeries.coeff_mk]
    by_cases h12 : 12 ≤ n
    · rw [hb9 n (by omega), hb9 (n - 1) (by omega), hb9 (n - 2) (by omega), hb9 (n - 3) (by omega)]
      omega
    · rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
        n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [b_formula]
  have hBinv : seriesB = num * Ring.inverse denB := by
    rw [← hBB, mul_assoc, Ring.mul_inverse_cancel _ huB, mul_one]
  have hAA : seriesA * denA = num := by
    calc seriesA * denA = (seriesA * denC) * denB := by dsimp only [denA]; ring
      _ = seriesB * denB := by rw [hAC]
      _ = num := hBB
  have hAinv : seriesA = num * Ring.inverse denA := by
    rw [← hAA, mul_assoc, Ring.mul_inverse_cancel _ huA, mul_one]
  have hdenA : denA = 1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 5 - PowerSeries.X ^ 7 := by dsimp only [denA, denB, denC]; ring
  have hrec7 : ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) -
      2 * (a (n - 3) : ℤ) - (a (n - 5) : ℤ) + (a (n - 7) : ℤ) := by
    intro n hn
    have hc := congrArg (PowerSeries.coeff n) hAA
    rw [hdenA, show seriesA * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 5 - PowerSeries.X ^ 7) = seriesA - seriesA * PowerSeries.X -
      seriesA * PowerSeries.X - seriesA * PowerSeries.X ^ 2 + seriesA * PowerSeries.X ^ 3 +
      seriesA * PowerSeries.X ^ 3 + seriesA * PowerSeries.X ^ 5 -
      seriesA * PowerSeries.X ^ 7 by ring] at hc
    simp only [num, map_add, map_sub, coeff_mul_X_eq, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X, PowerSeries.coeff_X_pow, seriesA, PowerSeries.coeff_mk] at hc
    omega
  have hACinv : seriesA = seriesB * Ring.inverse denC := by
    rw [← hAC, mul_assoc, Ring.mul_inverse_cancel _ huC, mul_one]
  exact ⟨hcB, hcA, huB, huC, huA, hAC, hACinv, hBB, hBinv, hAA, hAinv, hdenA, hrec7⟩

end D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration

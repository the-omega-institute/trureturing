/- GID: D5/S0/Computability/Coding/PrefixFreeCode
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/PrefixFreeCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prefix-free codes are uniquely decodable, giving Kraft's inequality for prefix codes. -/

import D5.S0.Computability.KraftInequality

/-!
# Prefix-free codes

## Audit trail and scope

`D5/S0/Computability/KraftInequality` deposits the Kraft-McMillan inequality for finite
binary *uniquely decodable* codes as a thin wrapper over pinned mathlib, and its blueprint
commentary records the missing step: "the bridge from prefix freedom to unique decodability.
Those stronger steps are outside this deposited partial closure."  This module supplies that
bridge.  The hypothesis matters because unique decodability quantifies over all pairs of
codeword lists and is not a checkable property of a finite code, whereas prefix-freedom is a
finite pairwise condition; Kraft's original 1949 statement is the prefix-code one.

Both `IsPrefixFree` and the suffix-free companion are new: pinned mathlib
(`Mathlib/InformationTheory/Coding/`) contains only `UniquelyDecodable` and
`kraft_mcmillan_inequality`, with no notion of a prefix code anywhere in the library.

Not covered here: the converse construction (given lengths with Kraft sum at most one, build
a prefix code realizing them), infinite codes, and the halting-set clause of the source.

## Search receipt (2026-08-15)

Searched pinned mathlib for `prefixfree`, `prefix_free`, `prefix code`, `IsPrefixCode`,
`instantaneous code`, `self-delimiting`, `PrefixCode`: zero hits across the whole library.
Searched `D5` and `Blueprint` for the same plus `suffixfree`: zero hits.  Hits used below are
core's `List.prefix_or_prefix_of_prefix`, `List.prefix_append`, `List.append_cancel_left`,
`List.reverse_prefix`, `List.reverse_flatten`, and mathlib's `List.map_injective_iff`,
`InformationTheory.UniquelyDecodable`.
-/

namespace D5.S0.Computability.Coding.PrefixFreeCode

open InformationTheory

variable {α : Type*}

/-- A set of codewords is prefix-free when no codeword is a prefix of another. -/
def IsPrefixFree (S : Set (List α)) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u <+: v → u = v

/-- A set of codewords is suffix-free when no codeword is a suffix of another. -/
def IsSuffixFree (S : Set (List α)) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u <:+ v → u = v

/-- A prefix-free code containing the empty word is the singleton `{[]}`; this is why
excluding the empty word is the right side condition rather than an extra restriction. -/
theorem IsPrefixFree.eq_singleton_nil {S : Set (List α)} (hpf : IsPrefixFree S)
    (hnil : [] ∈ S) : S = {[]} := by
  ext v
  exact ⟨fun hv => (hpf hnil hv List.nil_prefix).symm, fun hv => hv ▸ hnil⟩

/-- The greedy decoding step: in a prefix-free code the first codeword of a concatenation is
determined, together with the remaining tail. -/
theorem IsPrefixFree.first_codeword {S : Set (List α)} (hpf : IsPrefixFree S)
    {u v x y : List α} (hu : u ∈ S) (hv : v ∈ S) (h : u ++ x = v ++ y) :
    u = v ∧ x = y := by
  have hup : u <+: v ++ y := h ▸ List.prefix_append u x
  have hvp : v <+: v ++ y := List.prefix_append v y
  have huv : u = v := by
    rcases List.prefix_or_prefix_of_prefix hup hvp with hh | hh
    · exact hpf hu hv hh
    · exact (hpf hv hu hh).symm
  subst huv
  exact ⟨rfl, List.append_cancel_left h⟩

/-- **Prefix-free codes are uniquely decodable.** -/
theorem uniquelyDecodable_of_isPrefixFree {S : Set (List α)}
    (hpf : IsPrefixFree S) (hnil : [] ∉ S) : UniquelyDecodable S := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ _ h₂ hflat
    cases L₂ with
    | nil => rfl
    | cons v s =>
      exfalso
      have hz : v ++ s.flatten = [] := by simpa using hflat.symm
      exact hnil ((List.append_eq_nil_iff.mp hz).1 ▸ h₂ v (by simp))
  | cons w t ih =>
    intro L₂ h₁ h₂ hflat
    cases L₂ with
    | nil =>
      exfalso
      have hz : w ++ t.flatten = [] := by simpa using hflat
      exact hnil ((List.append_eq_nil_iff.mp hz).1 ▸ h₁ w (by simp))
    | cons v s =>
      simp only [List.flatten_cons] at hflat
      obtain ⟨hwv, hrest⟩ :=
        hpf.first_codeword (h₁ w (by simp)) (h₂ v (by simp)) hflat
      subst hwv
      rw [ih s (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) hrest]

/-- Reversal turns a suffix-free code into a prefix-free one. -/
theorem IsSuffixFree.isPrefixFree_reverse_image {S : Set (List α)}
    (hsf : IsSuffixFree S) : IsPrefixFree (List.reverse '' S) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ h
  exact congrArg List.reverse (hsf hu hv (List.reverse_prefix.mp h))

/-- **Suffix-free codes are uniquely decodable**, by transport along reversal. -/
theorem uniquelyDecodable_of_isSuffixFree {S : Set (List α)}
    (hsf : IsSuffixFree S) (hnil : [] ∉ S) : UniquelyDecodable S := by
  have hnil' : [] ∉ List.reverse '' S := by
    rintro ⟨u, hu, h⟩
    exact hnil (List.reverse_eq_nil_iff.mp h ▸ hu)
  have hUD := uniquelyDecodable_of_isPrefixFree hsf.isPrefixFree_reverse_image hnil'
  have hmem : ∀ L : List (List α), (∀ w ∈ L, w ∈ S) →
      ∀ w ∈ (L.map List.reverse).reverse, w ∈ List.reverse '' S := by
    intro L hL w hw
    simp only [List.mem_reverse, List.mem_map] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨x, hL x hx, rfl⟩
  intro L₁ L₂ h₁ h₂ hflat
  have hrev : ((L₁.map List.reverse).reverse).flatten
      = ((L₂.map List.reverse).reverse).flatten := by
    rw [← List.reverse_flatten, ← List.reverse_flatten, hflat]
  have hkey := hUD _ _ (hmem L₁ h₁) (hmem L₂ h₂) hrev
  have hmaps : L₁.map List.reverse = L₂.map List.reverse := by
    simpa using congrArg List.reverse hkey
  exact List.map_injective_iff.mpr List.reverse_injective hmaps

/-- **Kraft's inequality for finite binary prefix codes**: the deposited uniquely-decodable
form now applies under a finite, checkable hypothesis. -/
theorem kraft_inequality_of_isPrefixFree {S : Finset (List (Fin 2))}
    (hpf : IsPrefixFree (S : Set (List (Fin 2)))) (hnil : [] ∉ S) :
    ∑ w ∈ S, (1 / Fintype.card (Fin 2) : ℝ) ^ w.length ≤ 1 :=
  D5.S0.Computability.KraftInequality.finite_binary_kraft_inequality
    (uniquelyDecodable_of_isPrefixFree hpf (by simpa using hnil))

/-- Prefix-freedom is strictly stronger than unique decodability: the binary code
`{[0], [0,1]}` is suffix-free, hence uniquely decodable, but not prefix-free. -/
theorem exists_uniquelyDecodable_not_isPrefixFree :
    ∃ S : Set (List (Fin 2)), UniquelyDecodable S ∧ ¬IsPrefixFree S := by
  refine ⟨{[0], [0, 1]}, uniquelyDecodable_of_isSuffixFree ?_ ?_, ?_⟩
  · rintro u (rfl | rfl) v (rfl | rfl) h <;> first
      | rfl
      | (exfalso; revert h; decide)
  · rintro (h | h) <;> exact absurd h (by decide)
  · intro hpf
    have h0 : ([0] : List (Fin 2)) ∈ ({[0], [0, 1]} : Set (List (Fin 2))) := by simp
    have h1 : ([0, 1] : List (Fin 2)) ∈ ({[0], [0, 1]} : Set (List (Fin 2))) := by simp
    have hsub : ([0] : List (Fin 2)) <+: ([0, 1] : List (Fin 2)) := by decide
    exact absurd (hpf h0 h1 hsub) (by decide)

#print axioms IsPrefixFree.eq_singleton_nil
#print axioms IsPrefixFree.first_codeword
#print axioms uniquelyDecodable_of_isPrefixFree
#print axioms IsSuffixFree.isPrefixFree_reverse_image
#print axioms uniquelyDecodable_of_isSuffixFree
#print axioms kraft_inequality_of_isPrefixFree
#print axioms exists_uniquelyDecodable_not_isPrefixFree

end D5.S0.Computability.Coding.PrefixFreeCode

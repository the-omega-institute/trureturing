/- GID: D5/S0/Computability/Coding/LengthProfileSeparation
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/LengthProfileSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal codeword lengths can hide an arbitrarily large immutable-extension gap. -/

import D5.S0.Computability.Coding.ImmutableExtension

/-!
# Length-profile separation for immutable extensions

This module supplies the paper's quantified negative client for the residual-capacity profile.
For every `d` and every positive padding length `r`, it constructs two binary prefix codes with
the same complete length multiset and Kraft mass.  Their shortest possible extension lengths are
nevertheless `d + 1` and `1`, so the gap is unbounded while all traditional length data agree.

## Search receipt (2026-09-06)

Searched pinned mathlib and `D5` for spread/packed prefix-code families, equal length-multiset
extension gaps, fixed-length vector images, image cardinalities, list replication and prefix
cancellation, constant finset sums, and powers of one half.  No matching separation theorem or
construction was found.  Exact hits used below are `Finset.card_image_of_injective`,
`Multiset.eq_replicate_card`, `List.prefix_iff_eq_take`, `List.replicate_succ`,
`List.append_cancel_left`, `List.IsPrefix.eq_of_length`, and `card_vector`; the residual slot
predicate is imported from `ImmutableExtension`.
-/

namespace D5.S0.Computability.Coding.LengthProfileSeparation

open D5.S0.Computability.Coding.PrefixFreeCode
open D5.S0.Computability.Coding.ImmutableExtension
open scoped BigOperators

/-- The all-zero binary word of a specified length. -/
private def zeros (n : ℕ) : Word 2 := List.replicate n 0

/-- A spread word retains an arbitrary `d`-bit prefix and appends `r` zeroes. -/
private def spreadWord {d : ℕ} (r : ℕ) (u : List.Vector (Fin 2) d) : Word 2 :=
  u.1 ++ zeros r

/-- A packed word places `r` common leading zeroes before an arbitrary `d`-bit suffix. -/
private def packedWord {d : ℕ} (r : ℕ) (u : List.Vector (Fin 2) d) : Word 2 :=
  zeros r ++ u.1

/-- The spread code `{u ++ 0^r | |u| = d}`. -/
def spreadCode (d r : ℕ) : Finset (Word 2) :=
  (Finset.univ : Finset (List.Vector (Fin 2) d)).image (spreadWord r)

/-- The packed code `{0^r ++ u | |u| = d}`. -/
def packedCode (d r : ℕ) : Finset (Word 2) :=
  (Finset.univ : Finset (List.Vector (Fin 2) d)).image (packedWord r)

/-- Every spread word has length `d + r`. -/
private theorem spreadWord_length {d r : ℕ} (u : List.Vector (Fin 2) d) :
    (spreadWord r u).length = d + r := by simp [spreadWord, zeros, u.2]

/-- Every packed word has length `d + r`. -/
private theorem packedWord_length {d r : ℕ} (u : List.Vector (Fin 2) d) :
    (packedWord r u).length = d + r := by simp [packedWord, zeros, u.2, Nat.add_comm]

/-- The spread family is prefix-free because all its words have equal length. -/
private theorem spread_prefixFree (d r : ℕ) :
    IsPrefixFree (spreadCode d r : Set (Word 2)) := by
  intro x hx y hy hxy
  simp only [spreadCode, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
    true_and] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact hxy.eq_of_length (by rw [spreadWord_length, spreadWord_length])

/-- The packed family is prefix-free because all its words have equal length. -/
private theorem packed_prefixFree (d r : ℕ) :
    IsPrefixFree (packedCode d r : Set (Word 2)) := by
  intro x hx y hy hxy
  simp only [packedCode, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
    true_and] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact hxy.eq_of_length (by rw [packedWord_length, packedWord_length])

/-- A depth-`n` witness escaping the spread family when `d < n`. -/
private def spreadCandidate (d n : ℕ) : Word 2 :=
  zeros d ++ (1 : Fin 2) :: zeros (n - d - 1)

/-- A depth-`n` witness escaping every packed family at positive depth. -/
private def packedCandidate (n : ℕ) : Word 2 :=
  (1 : Fin 2) :: zeros (n - 1)

/-- The spread escape witness has the requested length. -/
private theorem spreadCandidate_length {d n : ℕ} (hdn : d < n) :
    (spreadCandidate d n).length = n := by
  simp [spreadCandidate, zeros]
  omega

/-- The packed escape witness has the requested positive length. -/
private theorem packedCandidate_length {n : ℕ} (hn : 0 < n) :
    (packedCandidate n).length = n := by
  simp [packedCandidate, zeros]
  omega

/-- The spread escape witness is prefix-incomparable with every spread codeword. -/
private theorem spreadCandidate_compatible {d r n : ℕ} (hr : 0 < r) (hdn : d < n) :
    Compatible (spreadCode d r) (spreadCandidate d n) := by
  intro frozen hfrozen
  simp only [spreadCode, Finset.mem_image, Finset.mem_univ, true_and] at hfrozen
  obtain ⟨u, rfl⟩ := hfrozen
  have htakeSpread : (spreadWord r u).take d = u.1 := by
    simp [spreadWord, u.2]
  have htakeCandidate : (spreadCandidate d n).take d = zeros d := by
    simp [spreadCandidate, zeros]
  constructor
  · intro hprefix
    have heq := List.prefix_iff_eq_take.mp hprefix
    have ht := congrArg (List.take d) heq
    simp [List.take_take, spreadWord_length, spreadCandidate_length hdn,
      htakeSpread, htakeCandidate, Nat.min_eq_left (Nat.le_of_lt hdn)] at ht
    have hu : u.1 = zeros d := ht
    have htail : zeros r <+: (1 : Fin 2) :: zeros (n - d - 1) := by
      simpa [spreadWord, spreadCandidate, hu] using hprefix
    cases r with
    | zero => omega
    | succ r => simpa [zeros, List.replicate_succ] using htail
  · intro hprefix
    have heq := List.prefix_iff_eq_take.mp hprefix
    have ht := congrArg (List.take d) heq
    simp [List.take_take, spreadWord_length, spreadCandidate_length hdn,
      htakeSpread, htakeCandidate, Nat.min_eq_left (Nat.le_of_lt hdn)] at ht
    have hu : u.1 = zeros d := ht.symm
    have htail : (1 : Fin 2) :: zeros (n - d - 1) <+: zeros r := by
      simpa [spreadWord, spreadCandidate, hu] using hprefix
    cases r with
    | zero => omega
    | succ r => simpa [zeros, List.replicate_succ] using htail

/-- The packed escape witness differs from every packed codeword in its first bit. -/
private theorem packedCandidate_compatible {d r n : ℕ} (hr : 0 < r) (_hn : 0 < n) :
    Compatible (packedCode d r) (packedCandidate n) := by
  intro frozen hfrozen
  simp only [packedCode, Finset.mem_image, Finset.mem_univ, true_and] at hfrozen
  obtain ⟨u, rfl⟩ := hfrozen
  constructor <;> intro hprefix <;> cases r with
  | zero => omega
  | succ r => simpa [packedWord, packedCandidate, zeros, List.replicate_succ] using hprefix

/-- The spread code has a free depth-`n` slot exactly above depth `d`. -/
private theorem spread_freeAt_nonempty_iff {d r n : ℕ} (hr : 0 < r) :
    (freeAt (spreadCode d r) n).Nonempty ↔ d < n := by
  classical
  constructor
  · intro hfree
    by_contra hdn
    have hnd : n ≤ d := Nat.le_of_not_gt hdn
    obtain ⟨v, hvfree⟩ := hfree
    have hvcomp : Compatible (spreadCode d r) v.1 := by
      simpa [freeAt] using hvfree
    let u : List.Vector (Fin 2) d :=
      ⟨v.1 ++ zeros (d - n), by simp [zeros, v.2, Nat.add_sub_of_le hnd]⟩
    have hword : spreadWord r u ∈ spreadCode d r := by
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    apply (hvcomp (spreadWord r u) hword).2
    refine ⟨zeros (d - n) ++ zeros r, ?_⟩
    simp [spreadWord, u, List.append_assoc]
  · intro hdn
    let v : List.Vector (Fin 2) n := ⟨spreadCandidate d n, spreadCandidate_length hdn⟩
    refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact spreadCandidate_compatible (n := n) hr hdn

/-- The packed code has a free slot at every and only positive depth. -/
private theorem packed_freeAt_nonempty_iff {d r n : ℕ} (hr : 0 < r) :
    (freeAt (packedCode d r) n).Nonempty ↔ 0 < n := by
  classical
  constructor
  · intro hfree
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    obtain ⟨v, hvfree⟩ := hfree
    have hvcomp : Compatible (packedCode d r) v.1 := by
      simpa [freeAt] using hvfree
    let u : List.Vector (Fin 2) d := ⟨zeros d, by simp [zeros]⟩
    have hword : packedWord r u ∈ packedCode d r := by
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    apply (hvcomp (packedWord r u) hword).2
    have hvnil : v.1 = [] := List.eq_nil_of_length_eq_zero v.2
    rw [hvnil]
    exact List.nil_prefix
  · intro hn
    let v : List.Vector (Fin 2) n := ⟨packedCandidate n, packedCandidate_length hn⟩
    refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact packedCandidate_compatible (d := d) (r := r) hr hn

/-- Appending fixed zero padding is injective on the variable prefix. -/
private theorem spreadWord_injective {d r : ℕ} :
    Function.Injective (spreadWord (d := d) r) := by
  intro u v huv
  apply Subtype.ext
  have ht := congrArg (List.take d) huv
  simpa [spreadWord, u.2, v.2] using ht

/-- Prepending fixed zero padding is injective on the variable suffix. -/
private theorem packedWord_injective {d r : ℕ} :
    Function.Injective (packedWord (d := d) r) := by
  intro u v huv
  apply Subtype.ext
  exact List.append_cancel_left huv

/-- The spread family contains all `2^d` possible variable prefixes. -/
private theorem spreadCode_card (d r : ℕ) : (spreadCode d r).card = 2 ^ d := by
  rw [spreadCode, Finset.card_image_of_injective _ spreadWord_injective]
  simp [card_vector]

/-- The packed family contains all `2^d` possible variable suffixes. -/
private theorem packedCode_card (d r : ℕ) : (packedCode d r).card = 2 ^ d := by
  rw [packedCode, Finset.card_image_of_injective _ packedWord_injective]
  simp [card_vector]

/-- The two families have identical complete codeword-length multisets. -/
private theorem equal_length_multisets (d r : ℕ) :
    (spreadCode d r).val.map List.length =
      (packedCode d r).val.map List.length := by
  have hs : (spreadCode d r).val.map List.length =
      Multiset.replicate
        ((spreadCode d r).val.map List.length).card (d + r) := by
    apply Multiset.eq_replicate_card.mpr
    intro k hk
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hk
    simp only [Finset.mem_val] at hw
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hw
    exact spreadWord_length u
  have hp : (packedCode d r).val.map List.length =
      Multiset.replicate
        ((packedCode d r).val.map List.length).card (d + r) := by
    apply Multiset.eq_replicate_card.mpr
    intro k hk
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hk
    simp only [Finset.mem_val] at hw
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hw
    exact packedWord_length u
  rw [hs, hp]
  simp [spreadCode_card, packedCode_card]

/-- The Kraft mass of the spread family is exactly `2^-r`. -/
private theorem spreadCode_mass (d r : ℕ) :
    (∑ w ∈ spreadCode d r, (1 / 2 : ℝ) ^ w.length) = (1 / 2 : ℝ) ^ r := by
  have hlength : ∀ w ∈ spreadCode d r, w.length = d + r := by
    intro w hw
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hw
    exact spreadWord_length u
  calc
    (∑ w ∈ spreadCode d r, (1 / 2 : ℝ) ^ w.length) =
        ∑ _w ∈ spreadCode d r, (1 / 2 : ℝ) ^ (d + r) := by
      exact Finset.sum_congr rfl fun w hw => by rw [hlength w hw]
    _ = (spreadCode d r).card * (1 / 2 : ℝ) ^ (d + r) := by simp
    _ = (1 / 2 : ℝ) ^ r := by
      rw [spreadCode_card]
      norm_num [pow_add]
      rw [← mul_assoc, ← mul_pow]
      norm_num

/-- **Equal length profiles hide an unbounded immutable-extension gap.**  The spread and packed
binary codes have the same full length multiset and Kraft mass `2^-r`, but their free-slot
thresholds are respectively `d < n` and `0 < n`.  Hence their shortest extension lengths differ
by `d`, which is arbitrarily large even with `r` fixed and positive. -/
theorem equal_lengths_unbounded_extension_gap (d r : ℕ) (hr : 0 < r) :
    IsPrefixFree (spreadCode d r : Set (Word 2)) ∧
    IsPrefixFree (packedCode d r : Set (Word 2)) ∧
    (spreadCode d r).val.map List.length =
      (packedCode d r).val.map List.length ∧
    (∑ w ∈ spreadCode d r, (1 / 2 : ℝ) ^ w.length) =
      (1 / 2 : ℝ) ^ r ∧
    (∀ n, (freeAt (spreadCode d r) n).Nonempty ↔ d < n) ∧
    (∀ n, (freeAt (packedCode d r) n).Nonempty ↔ 0 < n) := by
  exact ⟨spread_prefixFree d r, packed_prefixFree d r,
    equal_length_multisets d r, spreadCode_mass d r,
    fun n => spread_freeAt_nonempty_iff hr,
    fun n => packed_freeAt_nonempty_iff hr⟩

end D5.S0.Computability.Coding.LengthProfileSeparation

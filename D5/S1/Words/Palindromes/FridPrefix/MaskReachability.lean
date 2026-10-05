/- GID: D5/S1/Words/Palindromes/FridPrefix/MaskReachability
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/MaskReachability
   mirror-E: none(waiver:paired-digit-language-semantics)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity.palindrome_endpoint; instance=D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointMasks
   digest: Mask propagation reconstructs actual paths through the paired-digit relation. -/

/-
proof_shape: content (mask_path).
escape_witness: induction reconstructing an actual path from each retained bit.
admission_basis: escape-witness.
Direct frozen dependencies: none; remaining dependencies are pinned Mathlib or this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Computability.NFA

namespace D5.S1.Words.FridPrefix.Language

def maskStep (rows : List (List ℕ)) (mask symbol : ℕ) : ℕ :=
  (List.range rows.length).foldl
    (fun result q => if mask.testBit q then result ||| (rows[q]!).getD symbol 0 else result) 0

/-- The transition relation reads a set bit in the source's transition mask. -/
def maskNFA (rows : List (List ℕ)) (start : ℕ) : NFA ℕ ℕ where
  start := {s | start.testBit s = true}
  accept := Set.univ
  step := fun s a => {t | s < rows.length ∧ ((rows[s]!).getD a 0).testBit t = true}

/-- A bit retained by any finite mask run has an actual NFA path. -/
theorem mask_path (rows : List (List ℕ)) (w : List ℕ) (start q : ℕ)
    (h : (w.foldl (maskStep rows) start).testBit q = true) :
    ∃ s, start.testBit s = true ∧
      Nonempty ((maskNFA rows start).Path s q w) := by
  let M := maskNFA rows start
  have one (l : List ℕ) (mask symbol acc q : ℕ)
      (h : (l.foldl (fun result s => if mask.testBit s then
        result ||| (rows[s]!).getD symbol 0 else result) acc).testBit q = true) :
      acc.testBit q = true ∨ ∃ s ∈ l, mask.testBit s = true ∧
        ((rows[s]!).getD symbol 0).testBit q = true := by
    induction l generalizing acc with
    | nil => exact Or.inl h
    | cons s l ih =>
      simp only [List.foldl_cons] at h
      rcases ih _ h with h | ⟨t,ht,hb,he⟩
      · by_cases hs : mask.testBit s = true
        · simp only [hs, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨s,by simp,hs,h⟩
        · simp only [hs, ↓reduceIte] at h
          exact Or.inl h
      · exact Or.inr ⟨t,List.mem_cons_of_mem _ ht,hb,he⟩
  have step_exists (mask symbol q : ℕ) (h : (maskStep rows mask symbol).testBit q = true) :
      ∃ s, mask.testBit s = true ∧ s < rows.length ∧
        ((rows[s]!).getD symbol 0).testBit q = true := by
    rcases one (List.range rows.length) mask symbol 0 q h with h | ⟨s,hs,hb,he⟩
    · simp at h
    · exact ⟨s,hb,List.mem_range.mp hs,he⟩
  have join {s t : ℕ} {v : List ℕ} (hp : M.Path s t v)
      {q a : ℕ} (ht : q ∈ M.step t a) : M.Path s q (v++[a]) := by
    induction hp with
    | nil => exact NFA.Path.cons _ _ _ _ _ ht (NFA.Path.nil _)
    | cons t s u b v hm hp ih => exact NFA.Path.cons _ _ _ _ _ hm (ih ht)
  have aux (v : List ℕ) (mask q : ℕ)
      (h : (v.foldl (maskStep rows) mask).testBit q = true) :
      ∃ s, mask.testBit s = true ∧ Nonempty (M.Path s q v) := by
    induction v using List.reverseRecOn generalizing q with
    | nil => exact ⟨q,h,⟨NFA.Path.nil _⟩⟩
    | append_singleton v a ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      obtain ⟨t,ht,hlen,htrans⟩ := step_exists _ _ _ h
      obtain ⟨s,hs,⟨hpath⟩⟩ := ih t ht
      exact ⟨s,hs,⟨join hpath (by exact ⟨hlen,htrans⟩)⟩⟩
  exact aux w start q h

end D5.S1.Words.FridPrefix.Language

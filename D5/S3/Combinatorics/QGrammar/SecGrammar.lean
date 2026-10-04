/- GID: D5/S3/Combinatorics/QGrammar/SecGrammar
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QGrammar/SecGrammar
   mirror-E: none(waiver:sec-grammar-conjecture-resolution)
   anchors: []
   utility: none
   digest: The exact support region and its count prove Conjecture III.7 for all positive n. -/

import D5.S3.Combinatorics.QGrammar.SecGrammarCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QGrammar.SecGrammar

open SecGrammarDefs

/-- Han, Ji and Xiong, Conjecture III.7, with the fixed polynomial derivative statement. -/
theorem result : SecGrammarDefs.claim := by
  classical
  intro n hn
  have admissible (f : Bool) (j a b : ℕ) (h : (f, j, a, b) ∈ region n) :
      if f then 1 ≤ a else 1 ≤ j := by
    have hp := (Finset.mem_filter.mp h).2
    cases f
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
      rcases hp with he | ⟨hj, _⟩ <;> omega
    · simp only [↓reduceIte] at hp ⊢
      rcases hp with he | ⟨r, hr, ht, ha, _⟩ <;> omega
  have hy (f : Bool) (j a b : ℕ) :
      (encode f j a b).filter (fun v => v.1) = [(true, j)] := by
    cases f <;> simp [encode, List.filter_append]
  have inj : Set.InjOn (fun q : Bool × ℕ × ℕ × ℕ =>
      encode q.1 q.2.1 q.2.2.1 q.2.2.2) ↑(region n) := by
    rintro ⟨f, j, a, b⟩ hp ⟨g, k, c, d⟩ hq he
    have hj : j = k := by
      have hh := congrArg (List.filter (fun v : Var => v.1)) he
      rw [hy, hy] at hh
      simpa using hh
    subst k
    have hs : encode f j a b ∈
        (deriv^[n] (Finsupp.single [(true, 0)] 1)).support := by
      rw [reachable_region n hn]
      exact Finset.mem_image.mpr ⟨(f, j, a, b), hp, rfl⟩
    obtain ⟨hw, _, hwidth, hz⟩ := word_invariants n _ hs
    have hmem : (true, j) ∈ encode f j a b := by
      cases f <;> simp [encode]
    have hx : ∀ v ∈ encode f j a b, j - 1 ≤ v.2 ∧ v.2 ≤ j + 1 := by
      intro v hv
      have hl := hwidth (true, j) hmem v hv
      have hr := hwidth v hv (true, j) hmem
      dsimp at hl hr
      omega
    have hzero : 1 ≤ j ∨ (false, j + 1) ∈ encode f j a b :=
      hz hn (true, j) hmem rfl
    obtain ⟨q, _, unique⟩ := normal_form (encode f j a b) j hw (hy f j a b)
      hx hwidth hzero
    have hleft := unique (f, a, b) ⟨admissible f j a b hp, rfl⟩
    have hright := unique (g, c, d) ⟨admissible g j c d hq, he.symm⟩
    have heq := hleft.trans hright.symm
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj heq
    rfl
  rw [reachable_region n hn, Finset.card_image_iff.mpr inj, region_count n hn]

end D5.S3.Combinatorics.QGrammar.SecGrammar

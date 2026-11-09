/- GID: D5/S3/Combinatorics/Orthogonality/BinaryLineGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/BinaryLineGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero binary vectors are exactly the actual one-dimensional subspace vertices. -/

import D5.S3.Combinatorics.Orthogonality.NikandishClique

/-! The source's line graph is the induced graph on all actual one-dimensional
Submodules. Over F2 each such space has precisely one nonzero vector. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Orthogonality.BinaryLineGraph

open Module
open NikandishClique
open D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality

abbrev VectorVertex (n : ℕ) := {v : Fin n → ZMod 2 // v ≠ 0}
abbrev LineVertex (n : ℕ) := {U : Vertex n // finrank (ZMod 2) U.1 = 1}

def vectorGraph (n : ℕ) : SimpleGraph (VectorVertex n) where
  Adj v w := v ≠ w ∧ dotProduct v.1 w.1 = 0
  symm := ⟨fun v w h => ⟨h.1.symm, (dotProduct_comm w.1 v.1).trans h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def lineGraph (n : ℕ) : SimpleGraph (LineVertex n) :=
  (orthogonalityGraph n).induce {U : Vertex n | finrank (ZMod 2) U.1 = 1}

def spanVertex (n : ℕ) (v : VectorVertex n) : LineVertex n :=
  ⟨⟨(ZMod 2) ∙ v.1, by simpa using v.2⟩, finrank_span_singleton v.2⟩

private theorem span_injective (n : ℕ) : Function.Injective (spanVertex n) := by
  intro v w h
  have hs : (ZMod 2) ∙ v.1 = (ZMod 2) ∙ w.1 :=
    congrArg (fun U : LineVertex n => U.1.1) h
  have hv : v.1 ∈ (ZMod 2) ∙ w.1 := by
    rw [← hs]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have hcases : c = 0 ∨ c = 1 := by
    fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hcases with rfl | rfl
  · exact (v.2 (by simpa using hc.symm)).elim
  · exact Subtype.ext (by simpa using hc.symm)

/-- Every line is present, not only the coordinate lines. -/
noncomputable def vertexEquiv (n : ℕ) : VectorVertex n ≃ LineVertex n :=
  Equiv.ofBijective (spanVertex n) ⟨span_injective n, by
    intro U
    obtain ⟨v, hv, hn⟩ := U.1.1.ne_bot_iff.mp U.1.2
    refine ⟨⟨v, hn⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (eq_span_singleton_of_mem_of_finrank_eq_one U.2 hv hn).symm⟩

/-- The all-dimensional vector/line correspondence preserves the actual
loopless orthogonality relation in both directions. -/
noncomputable def graphIso (n : ℕ) : vectorGraph n ≃g lineGraph n where
  toEquiv := vertexEquiv n
  map_rel_iff' := by
    intro v w
    change ((vertexEquiv n v).1 ≠ (vertexEquiv n w).1 ∧ _) ↔
      (v ≠ w ∧ dotProduct v.1 w.1 = 0)
    rw [Subtype.val_injective.ne_iff, (vertexEquiv n).injective.ne_iff]
    apply and_congr_right
    intro _
    constructor
    · intro h
      exact h v.1 (Submodule.mem_span_singleton_self _) w.1
        (Submodule.mem_span_singleton_self _)
    · intro h x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      change dotProduct (a • v.1) (b • w.1) = 0
      simp [dotProduct_smul, h]

#print axioms graphIso

end D5.S3.Combinatorics.Orthogonality.BinaryLineGraph

/- GID: D5/S3/Observer/Separation/BooleanCompanionMinimality
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/BooleanCompanionMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A binary effective-image map is surjective iff it has a surjective row or column. -/

set_option autoImplicit false

/-! Structural binary effective-image reduction for one companion. -/

namespace D5.S3.Observer.Separation.BooleanCompanionMinimality

/- A nonconstant binary companion cannot have both all rows and all columns
   non-surjective.  This is the structural reduction used before the width
   comparison in the source's one-companion clause. -/
private theorem binary_effective_image_has_surjective_slice
    {A B : Type} [Nonempty A] [Nonempty B]
    (ψ : A → B → Bool)
    (hψ : Function.Surjective (fun p : A × B => ψ p.1 p.2)) :
    (∃ b, Function.Surjective (fun a => ψ a b)) ∨
      (∃ a, Function.Surjective (fun b => ψ a b)) := by
  by_cases hrow : ∃ a, Function.Surjective (fun b => ψ a b)
  · exact Or.inr hrow
  · left
    by_cases hcol : ∃ b, Function.Surjective (fun a => ψ a b)
    · exact hcol
    · obtain ⟨p, hp⟩ := hψ false
      obtain ⟨q, hq⟩ := hψ true
      change ψ p.1 p.2 = false at hp
      change ψ q.1 q.2 = true at hq
      have row_constant (a : A) (b₁ b₂ : B) : ψ a b₁ = ψ a b₂ := by
        by_cases hne : ψ a b₁ = ψ a b₂
        · exact hne
        · have hsurj : Function.Surjective (fun b => ψ a b) := by
            intro z
            cases z with
            | false =>
              by_cases h₁ : ψ a b₁ = false
              · exact ⟨b₁, h₁⟩
              · have h₁' : ψ a b₁ = true := by
                  cases hval : ψ a b₁ with
                  | false => exact False.elim (h₁ hval)
                  | true => rfl
                have h₂ : ψ a b₂ = false := by
                  cases hb₂ : ψ a b₂ with
                  | false => rfl
                  | true => exact False.elim (hne (h₁'.trans hb₂.symm))
                exact ⟨b₂, h₂⟩
            | true =>
              by_cases h₁ : ψ a b₁ = true
              · exact ⟨b₁, h₁⟩
              · have h₁' : ψ a b₁ = false := by
                  cases hval : ψ a b₁ with
                  | false => rfl
                  | true => exact False.elim (h₁ hval)
                have h₂ : ψ a b₂ = true := by
                  cases hb₂ : ψ a b₂ with
                  | false => exact False.elim (hne (h₁'.trans hb₂.symm))
                  | true => rfl
                exact ⟨b₂, h₂⟩
          exact False.elim (hrow ⟨a, hsurj⟩)
      let b₀ : B := Classical.choice inferInstance
      have hcol₀ : Function.Surjective (fun a => ψ a b₀) := by
        intro z
        cases z with
        | false =>
          refine ⟨p.1, ?_⟩
          exact (row_constant p.1 p.2 b₀).symm.trans hp
        | true =>
          refine ⟨q.1, ?_⟩
          exact (row_constant q.1 q.2 b₀).symm.trans hq
      exact False.elim (hcol ⟨b₀, hcol₀⟩)

theorem binary_effective_image_surjective_iff
    {A B : Type} [Nonempty A] [Nonempty B]
    (ψ : A → B → Bool) :
    Function.Surjective (fun p : A × B => ψ p.1 p.2) ↔
      ((∃ b, Function.Surjective (fun a => ψ a b)) ∨
        (∃ a, Function.Surjective (fun b => ψ a b))) := by
  constructor
  · exact binary_effective_image_has_surjective_slice ψ
  · intro hslice z
    cases hslice with
    | inl hrow =>
        obtain ⟨b, hb⟩ := hrow
        obtain ⟨a, ha⟩ := hb z
        exact ⟨(a, b), ha⟩
    | inr hcol =>
        obtain ⟨a, ha⟩ := hcol
        obtain ⟨b, hb⟩ := ha z
        exact ⟨(a, b), hb⟩

#print axioms binary_effective_image_surjective_iff

end D5.S3.Observer.Separation.BooleanCompanionMinimality

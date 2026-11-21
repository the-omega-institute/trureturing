/- GID: D5/S0/Computability/Coding/PrefixGeneratorEnvelope
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/PrefixGeneratorEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact factorizations through at most n nonempty prefix-separated generators. -/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A prefix-generator envelope for arbitrary finite labelled word families. -/

public section

namespace D5.S0.Computability.Coding.PrefixGeneratorEnvelope

open scoped BigOperators

universe u

/-- Every finite labelled word family admits exact factorizations through a family of nonempty,
prefix-separated words with no more generators than the number of input labels. -/
theorem prefix_generator_envelope {α : Type u} {n : ℕ} (f : Fin n → List α) :
    ∃ m : ℕ, m ≤ n ∧ ∃ g : Fin m → List α,
      ∃ c : Fin n → List (Fin m),
        (∀ i, g i ≠ []) ∧
        (∀ i j, List.IsPrefix (g i) (g j) → i = j) ∧
        ∀ i, f i = (c i).flatMap g := by
  classical
  induction n with
  | zero =>
    refine ⟨0, le_rfl, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | succ n outer =>
    suffices ∀ k : ℕ, ∀ h : Fin (n + 1) → List α,
        (∑ i, (h i).length) = k →
        ∃ m : ℕ, m ≤ n + 1 ∧ ∃ g : Fin m → List α,
          ∃ c : Fin (n + 1) → List (Fin m),
            (∀ i, g i ≠ []) ∧
            (∀ i j, List.IsPrefix (g i) (g j) → i = j) ∧
            ∀ i, h i = (c i).flatMap g from
      this _ f rfl
    intro k
    induction k using Nat.strong_induction_on with
    | h k inner =>
      intro h hlen
      by_cases hz : ∃ z, h z = []
      · obtain ⟨z, hz⟩ := hz
        obtain ⟨m, hm, g, c, hne, hp, hc⟩ := outer (fun a => h (z.succAbove a))
        refine ⟨m, Nat.le_trans hm (Nat.le_succ n), g, Fin.insertNth z [] c,
          hne, hp, ?_⟩
        intro a
        refine Fin.succAboveCases z ?_ (fun b => ?_) a
        · simpa using hz
        · simpa using hc b
      · have hne : ∀ i, h i ≠ [] := by simpa using hz
        by_cases hp : ∀ i j, List.IsPrefix (h i) (h j) → i = j
        · refine ⟨n + 1, le_rfl, h, (fun i => [i]), hne, hp, ?_⟩
          intro i
          simp
        · have hpair : ∃ i j, List.IsPrefix (h i) (h j) ∧ i ≠ j := by
            simpa only [not_forall, not_imp, exists_prop] using hp
          obtain ⟨i, j, hij, hneij⟩ := hpair
          obtain ⟨r, hr⟩ := hij
          let q := Function.update h j r
          let σ : Fin (n + 1) → List (Fin (n + 1)) :=
            fun a => if a = j then [i, j] else [a]
          have hq : ∀ a, h a = (σ a).flatMap q := by
            intro a
            by_cases haj : a = j
            · subst a
              simpa [σ, q, hneij] using hr.symm
            · simp [σ, q, haj]
          have hshort : (∑ a, (q a).length) < k := by
            rw [← hlen]
            apply Finset.sum_lt_sum
            · intro a _
              by_cases haj : a = j
              · subst a
                simp only [q, Function.update_self]
                rw [← hr, List.length_append]
                omega
              · simp [q, haj]
            · refine ⟨j, Finset.mem_univ j, ?_⟩
              simp only [q, Function.update_self]
              have hi : 0 < (h i).length := List.length_pos_iff_ne_nil.mpr (hne i)
              rw [← hr, List.length_append]
              omega
          obtain ⟨m, hm, g, c, hgne, hgp, hc⟩ := inner _ hshort q rfl
          refine ⟨m, hm, g, (fun a => (σ a).flatMap c), hgne, hgp, ?_⟩
          intro a
          rw [hq a, List.flatMap_assoc]
          exact List.flatMap_congr (fun b _ => hc b)

end D5.S0.Computability.Coding.PrefixGeneratorEnvelope

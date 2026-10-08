/- GID: D5/S3/Combinatorics/TotalRoman/SupercriticalBasics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/SupercriticalBasics
   mirror-E: none(waiver:shared-domination-foundations)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset]
   utility: none
   digest: Attainment and lower bounds for total Roman domination weights. -/

import D5.S3.Combinatorics.TotalRoman.SupercriticalDefs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.SupercriticalBasics

open SupercriticalDefs

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem attained (hG : ∀ v, ∃ u, G.Adj v u) :
    ∃ f : V → ℕ, IsTRDF G f ∧ ∑ v, f v = gammaTR G := by
  have hone : IsTRDF G (fun _ => 1) := by
    refine ⟨fun _ => by simp, ?_, ?_⟩
    · intro v hv
      simp at hv
    · intro v _
      obtain ⟨u, hu⟩ := hG v
      exact ⟨u, hu, by simp⟩
  obtain ⟨f, hf, hw⟩ := Nat.sInf_mem
    (show {w | ∃ f : V → ℕ, IsTRDF G f ∧ w = ∑ v, f v}.Nonempty from
      ⟨∑ _ : V, 1, fun _ => 1, hone, rfl⟩)
  exact ⟨f, hf, hw.symm⟩

theorem le_weight {f : V → ℕ} (hf : IsTRDF G f) : gammaTR G ≤ ∑ v, f v :=
  Nat.sInf_le ⟨f, hf, rfl⟩

theorem weight_pair {f : V → ℕ} {u v : V} (huv : u ≠ v) :
    f u + f v ≤ ∑ x, f x := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f)
    (show ({u, v} : Finset V) ⊆ Finset.univ from fun _ _ => Finset.mem_univ _)
    (fun x _ _ => Nat.zero_le (f x))
  simpa [Finset.sum_pair huv] using h

theorem weight_two {f : V → ℕ} (hf : IsTRDF G f) (v : V) : 2 ≤ ∑ x, f x := by
  obtain ⟨u, hu⟩ : ∃ u, 0 < f u := by
    by_cases hv : f v = 0
    · obtain ⟨u, _, hu⟩ := hf.2.1 v hv
      exact ⟨u, by omega⟩
    · exact ⟨v, by omega⟩
  obtain ⟨w, huw, hw⟩ := hf.2.2 u hu
  have hp := weight_pair (f := f) (G.ne_of_adj huw)
  omega

theorem weight_three {f : V → ℕ} (hf : IsTRDF G f) (hcard : 3 ≤ Fintype.card V) :
    3 ≤ ∑ x, f x := by
  by_cases ht : ∃ v, f v = 2
  · obtain ⟨v, hv⟩ := ht
    obtain ⟨u, hu, hfu⟩ := hf.2.2 v (by omega)
    have hp := weight_pair (f := f) (G.ne_of_adj hu)
    omega
  · have hpos : ∀ v, 1 ≤ f v := by
      intro v
      by_contra hv
      obtain ⟨u, _, hu⟩ := hf.2.1 v (by omega)
      exact ht ⟨u, hu⟩
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpos v)
    have hc : (∑ _ : V, (1 : ℕ)) = Fintype.card V := by simp
    omega

theorem universal_bound (v w : V) (hvw : G.Adj v w)
    (hv : ∀ x, x ≠ v → G.Adj v x) : gammaTR G ≤ 3 := by
  classical
  have hvne : v ≠ w := G.ne_of_adj hvw
  let f : V → ℕ := fun x => if x = v then 2 else if x = w then 1 else 0
  have hf : IsTRDF G f := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      dsimp [f]
      split_ifs <;> omega
    · intro x hx
      have hxv : x ≠ v := by intro he; subst x; simp [f] at hx
      refine ⟨v, (hv x hxv).symm, by simp [f]⟩
    · intro x hx
      by_cases hxv : x = v
      · subst x
        exact ⟨w, hvw, by simp [f, hvne.symm]⟩
      · have hxw : x = w := by
          by_contra hxw
          simp [f, hxv, hxw] at hx
        subst x
        exact ⟨v, hvw.symm, by simp [f]⟩
  have hsum : (∑ x, f x) = 3 := by
    have heq : f = fun x => (if x = v then 2 else 0) + (if x = w then 1 else 0) := by
      funext x
      dsimp [f]
      split_ifs <;> simp_all
    rw [heq, Finset.sum_add_distrib]
    simp
  have hup := le_weight hf
  omega

end D5.S3.Combinatorics.TotalRoman.SupercriticalBasics

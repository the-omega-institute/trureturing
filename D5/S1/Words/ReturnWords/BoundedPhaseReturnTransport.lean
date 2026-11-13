/- GID: D5/S1/Words/ReturnWords/BoundedPhaseReturnTransport
   generality: G
   mirror-B: D5/B/S1/Words/ReturnWords/BoundedPhaseReturnTransport
   mirror-E: none(waiver:bounded-phase-return-transport)
   anchors: []
   utility: none
   digest: Bounded phases transport output letters along every actual path. -/

import D5.S1.Words.ReturnWords.CoherentReturnPathTemplates

namespace D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport

open Quiver D5.S1.Words.Powers
open CoherentReturnPathTemplates

universe u v w

/-- A bounded phase certificate determines the exact letter at every position
of every actual internal path. -/
theorem path_output_of_bounded_phases {V : Type u} [Quiver.{v} V] [Finite V]
    {α : Type w} (label : EdgeLabel V α) (S : StronglyConnectedComponent V)
    (hP : BoundedPhases label S) :
    ∃ p : Nat, 0 < p ∧ p ≤ Nat.card (Component S) ∧
      ∃ P : ZMod p → α, ∃ θ : Component S → ZMod p,
        (∀ {a b : Component S} (e : a ⟶ b),
          componentLabel label S e = P (θ a) ∧ θ b = θ a + 1) ∧
        ∀ {a b : Component S} (H : Path a b),
          θ b = θ a + (H.length : ZMod p) ∧
          ∀ (i : Nat), i < H.length →
            (output (componentLabel label S) H)[i]? =
              some (P (θ a + (i : ZMod p))) := by
  classical
  obtain ⟨p, hp, hbound, P, θ, hedge⟩ := hP
  let W := Component S
  let ℓ : EdgeLabel W α := componentLabel label S
  have outcons {a b c : W} (H : Path a b) (e : b ⟶ c) :
      output ℓ (H.cons e) = output ℓ H ++ [ℓ e] := by
    simp only [output, Path.weight_cons, FreeMonoid.toList_mul,
      FreeMonoid.of, FreeMonoid.toList_ofList]
  have outlen {a b : W} (H : Path a b) :
      (output ℓ H).length = H.length := by
    induction H with
    | nil => simp [output]
    | cons H e ih =>
        rw [outcons, List.length_append, List.length_singleton,
          Path.length_cons, ih]
  have pathlaw {a b : W} (H : Path a b) :
      θ b = θ a + (H.length : ZMod p) ∧
      ∀ i, i < H.length →
        (output ℓ H)[i]? = some (P (θ a + (i : ZMod p))) := by
    induction H with
    | nil => exact ⟨by simp, by simp⟩
    | @cons b c H e ih =>
        obtain ⟨he, hθ⟩ := hedge e
        refine ⟨?_, ?_⟩
        · rw [hθ, ih.1, Path.length_cons, Nat.cast_add, Nat.cast_one, add_assoc]
        · intro i hi
          rw [outcons]
          by_cases hiH : i < H.length
          · rw [List.getElem?_append_left (by rw [outlen]; exact hiH)]
            exact ih.2 i hiH
          · have hieq : i = H.length := by simp only [Path.length_cons] at hi; omega
            subst i
            rw [List.getElem?_append_right (by rw [outlen]), outlen, Nat.sub_self]
            change some (ℓ e) = _
            change ℓ e = P (θ b) at he
            rw [he, ih.1]
  refine ⟨p, hp, hbound, P, θ, hedge, ?_⟩
  exact fun H => pathlaw H

end D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport

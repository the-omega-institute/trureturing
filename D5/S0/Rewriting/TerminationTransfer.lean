/- GID: D5/S0/Rewriting/TerminationTransfer
   generality: G
   mirror-B: D5/B/S0/Rewriting/TerminationTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quasi-commuting terminating relations have a terminating union. -/

import Mathlib

namespace TerminationTransfer

/-- Bachmair-Dershowitz termination transfer for a quasi-commuting union. -/
theorem termination_union_of_quasi_commutation {α : Type*} (r s : α → α → Prop)
    (hr : WellFounded (Function.swap r)) (hs : WellFounded (Function.swap s))
    (hcomm : ∀ {a b c}, s a b → r b c → ∃ d, r a d ∧
      Relation.ReflTransGen (fun x y => r x y ∨ s x y) d c) :
    WellFounded (Function.swap (fun a b => r a b ∨ s a b)) := by
  let p : α → α → Prop := fun a b => r a b ∨ s a b
  let U : α → α → Prop := Function.swap p
  let R : α → α → Prop := Function.swap r
  let S : α → α → Prop := Function.swap s
  have acc_of_path : ∀ {a b}, Acc U a → Relation.ReflTransGen p a b → Acc U b := by
    intro a b ha hab
    induction hab with
    | refl => exact ha
    | tail hab hbc ih =>
        exact Acc.inv ih (show U _ _ from hbc)
  have outer : ∀ a, ∀ hsa : Acc S a, Acc U a := by
    intro a
    induction a using hr.induction with
    | h a ih =>
      intro hsa
      induction hsa with
      | intro a hacc ihs =>
          apply Acc.intro a
          intro b hab
          rcases hab with hab | hab
          · exact ih b hab (hs.apply b)
          · apply ihs b hab
            intro y hy
            obtain ⟨d, hd, hdy⟩ := hcomm hab hy
            intro _
            exact acc_of_path (ih d hd (hs.apply d)) hdy
  have result : WellFounded U := WellFounded.intro (fun a => outer a (hs.apply a))
  simpa [U, p] using result

example : WellFounded (Function.swap (fun a b : Nat => b < a ∨ b < a)) := by
  apply termination_union_of_quasi_commutation
    (r := fun a b : Nat => b < a) (s := fun a b : Nat => b < a)
  · exact Nat.lt_wfRel.wf
  · exact Nat.lt_wfRel.wf
  · intro a b c hsb hrc
    exact ⟨b, hsb, Relation.ReflTransGen.single (Or.inl hrc)⟩

end TerminationTransfer

/- GID: D5/S3/Combinatorics/Transportation/SupportedBooleanCycleEquivalence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/SupportedBooleanCycleEquivalence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Supported equal margins characterize bounded target-conformal Boolean cycle chains. -/

import D5.S3.Combinatorics.Transportation.SupportedBooleanCycles

/-! The necessary and sufficient endpoint conditions for the supported Boolean
cycle construction, on independently universed finite row and column carriers. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence

open SupportedBooleanCycles

universe u v
variable {R : Type u} {C : Type v} [Fintype R] [Fintype C]

/-- Bounded target-conformal chains exist exactly between supported tables with
the same individually labeled row and column margins. -/
theorem bounded_conformal_chain_iff (E : R → C → Prop) (A B : Table R C) :
    (∃ n : ℕ, Chain E B A n ∧ n ≤ distance A B / 4) ↔
      (Supported E A ∧ Supported E B ∧ SameMargins A B) := by
  constructor
  · rintro ⟨n, hchain, hbound⟩
    clear hbound
    induction hchain with
    | done hs =>
        exact ⟨hs, hs, ⟨fun _ => rfl, fun _ => rfl⟩⟩
    | step hs hm _ _ _ ih =>
        exact ⟨hs, ih.2.1, hm⟩
  · rintro ⟨ha, hb, hm⟩
    exact bounded_conformal_chain E A B ha hb hm

end D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence

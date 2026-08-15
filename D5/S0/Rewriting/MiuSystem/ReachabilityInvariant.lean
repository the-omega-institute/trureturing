/- GID: D5/S0/Rewriting/MiuSystem/ReachabilityInvariant
   generality: I
   mirror-B: D5/B/S0/Rewriting/MiuSystem/ReachabilityInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: MIU derivability has I-count residues one and two modulo three and excludes MU. -/

import Archive.MiuLanguage.DecisionNec
import Mathlib.Tactic

/- Library-search audit trail (2026-08-15):
   * Pinned mathlib's `Archive.MiuLanguage.DecisionNec` contains the exact MIU alphabet, production
     system, invariant `Miu.count_equiv_one_or_two_mod3_of_derivable`, and theorem
     `Miu.not_derivable_mu`; this file imports and applies them rather than reproving them.
   * Repository search found only `GoldenShellRecurrence`, whose declaration covers the separate
     Hofstadter G recurrence and explicitly says that it does not cover the MIU invariant.
-/

namespace D5.S0.Rewriting.MiuSystem.ReachabilityInvariant

/-- The invariant clauses of observation 6.157, stated over pinned mathlib's MIU system: every
derivable word has nonzero `I`-count modulo three, the realized residues are exactly one and two,
and `MU` is not derivable. -/
theorem miu_observation_invariant_clauses :
    (∀ word : Miu.Miustr,
      Miu.Derivable word → List.count Miu.MiuAtom.I word % 3 ≠ 0) ∧
      (∀ residue : Nat,
        (∃ word : Miu.Miustr,
          Miu.Derivable word ∧ List.count Miu.MiuAtom.I word % 3 = residue) ↔
          residue = 1 ∨ residue = 2) ∧
      ¬ Miu.Derivable "MU" := by
  constructor
  · intro word derivable
    rcases Miu.count_equiv_one_or_two_mod3_of_derivable word derivable with h | h <;> omega
  constructor
  · intro residue
    constructor
    · rintro ⟨word, derivable, residueEquation⟩
      rcases Miu.count_equiv_one_or_two_mod3_of_derivable word derivable with h | h <;> omega
    · rintro (rfl | rfl)
      · exact ⟨"MI", Miu.Derivable.mk, by decide⟩
      · refine ⟨[Miu.MiuAtom.M, Miu.MiuAtom.I, Miu.MiuAtom.I], ?_, by decide⟩
        exact Miu.Derivable.r2 Miu.Derivable.mk
  · exact Miu.not_derivable_mu

#print axioms miu_observation_invariant_clauses

end D5.S0.Rewriting.MiuSystem.ReachabilityInvariant

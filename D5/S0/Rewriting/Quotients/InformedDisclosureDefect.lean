/- GID: D5/S0/Rewriting/Quotients/InformedDisclosureDefect
   generality: G
   mirror-B: D5/B/S0/Rewriting/Quotients/InformedDisclosureDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A disclosure collision blocks consequence-sensitive decisions and full recovery. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-20):
   * Exact pinned-Mathlib hit: `congrArg` transports a disclosure equality
     through every disclosure-only decision rule; it is applied below.
   * Pinned Mathlib's `Function.FactorsThrough` and
     `Function.factorsThrough_iff` give adjacent fiber semantics, but no
     library theorem packages the source's decision and recovery conclusions.
   * Repository searches for disclosure, informed choice, consequence
     recovery, and decision-rule indistinguishability found no exact theorem. -/

namespace D5.S0.Rewriting.Quotients.InformedDisclosureDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If two situations disclose the same information but have different true
consequences, every rule using only that disclosure treats the pair alike, and
the true consequence map cannot be recovered from the disclosure. -/
theorem informed_disclosure_defect
    {Z Disclosure Consequence Decision : Type*}
    (disclosure : Z → Disclosure) (consequence : Z → Consequence)
    {z z' : Z} (hsame : disclosure z = disclosure z')
    (hdifferent : consequence z ≠ consequence z') :
    (∀ rule : Disclosure → Decision,
      rule (disclosure z) = rule (disclosure z')) ∧
      ¬∃ recover : Disclosure → Consequence,
        consequence = recover ∘ disclosure := by
  constructor
  · intro rule
    exact congrArg rule hsame
  · rintro ⟨recover, hrecover⟩
    apply hdifferent
    calc
      consequence z = recover (disclosure z) := by
        simpa only [Function.comp_apply] using congrFun hrecover z
      _ = recover (disclosure z') := congrArg recover hsame
      _ = consequence z' := by
        simpa only [Function.comp_apply] using (congrFun hrecover z').symm

/-- The witness situation type is inhabited. -/
example : Bool := false

/-- Two Boolean situations with constant disclosure and distinct Boolean
consequences witness simultaneous satisfiability of the public premises. -/
example :
    (∀ rule : Unit → Bool, rule () = rule ()) ∧
      ¬∃ recover : Unit → Bool,
        (id : Bool → Bool) = recover ∘ (fun _ : Bool => ()) := by
  exact informed_disclosure_defect
    (Decision := Bool) (fun _ : Bool => ()) id
    (z := false) (z' := true) rfl Bool.false_ne_true

#print axioms informed_disclosure_defect

end D5.S0.Rewriting.Quotients.InformedDisclosureDefect

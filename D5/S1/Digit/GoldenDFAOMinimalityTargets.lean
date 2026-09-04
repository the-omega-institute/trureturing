/- GID: D5/S1/Digit/GoldenDFAOMinimalityTargets
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenDFAOMinimalityTargets
   mirror-E: none(waiver:open-problem-certificate-targets)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   digest: M07-M16 register exact finite-prefix LRAT targets for the golden-ratio DFAO controls and the base-4 state-exclusion ladder. -/

import D5.S1.Digit.GoldenBase4AutomataOracle
import D5.S0.Certificates.LRATDFAStateLowerBound

/- Library-search audit trail (2026-09-04):
   * `D5.S1.Digit.GoldenBase4AutomataOracle` already certifies the sparse
     base-four golden-ratio words and exact floor-difference digits; both are
     reused verbatim, no second digit oracle is introduced.
   * `D5.S0.Certificates.LRATDFAStateLowerBound` supplies the frozen
     prefix-refutation-to-minimality bridge that every target instantiates.
   * Repository and mathlib/Batteries searches found no registered CNF target
     family for golden-ratio DFAO state minimality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenDFAOMinimalityTargets

open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Certificates.DFAIdentificationCNF
open D5.S0.Certificates.LRATUnsatisfiable
open D5.S0.Certificates.LRATDFAStateLowerBound

/-- The exact sparse typed-DFAO problem for base-4 digits of the golden ratio. -/
noncomputable def base4Problem :
    SparseProblem (Fin 2) (Fin 4) BinaryZeckendorfState where
  base := binaryZeckendorfBase
  input := base4PowerWord
  target := base4GoldenDigit

/-- The registered base-4 problem uses exactly the canonical Zeckendorf words
and the exact floor-difference digits certified by the frozen oracle layer. -/
theorem base4_problem_semantics (index : Nat) :
    base4Problem.input index = zeckendorfMSDWord (4 ^ index) ∧
      ((base4Problem.target index).val : Int) =
        base4Floor (index + 1) - 4 * base4Floor index := by
  refine ⟨rfl, ?_⟩
  show ((base4GoldenDigit index).val : Int) =
    base4Floor (index + 1) - 4 * base4Floor index
  rw [base4GoldenDigit_val,
    Int.toNat_of_nonneg (base4DigitInt_bounds index).1]
  rfl

/-- Exact semantic data required before a published base-2 or base-3 control
automaton is admitted. This keeps transcribed machine tables separate from the
general LRAT reasoning. -/
structure PhiControlData (base states : Nat) where
  base_pos : 0 < base
  problem :
    SparseProblem (Fin 2) (Fin base) BinaryZeckendorfState
  input_spec :
    ∀ index, problem.input index = zeckendorfMSDWord (base ^ index)
  digit_spec :
    ∀ index,
      ((problem.target index).val : Int) =
        ⌊(((base ^ (index + 1) : Nat) : Real) *
            Real.goldenRatio)⌋ -
          (base : Int) *
            ⌊(((base ^ index : Nat) : Real) *
              Real.goldenRatio)⌋
  upper : problem.HasGlobalModel states

/-- M07. A seven-state finite-prefix refutation certifies exact eight-state
minimality for any fully transcribed base-2 control instance. -/
theorem m07_phi_base2_minimality_control
    (control : PhiControlData 2 8)
    (extent : Nat)
    (encoding :
      PrefixModelEncoding control.problem extent 7)
    (refutation : Refutation encoding.formula) :
    IsMinimalStateCount control.problem 8 :=
  minimal_state_count_of_prefix_refutation
    control.problem 8 extent control.upper encoding refutation

/-- M08. A twelve-state finite-prefix refutation certifies exact thirteen-state
minimality for any fully transcribed base-3 control instance. -/
theorem m08_phi_base3_minimality_control
    (control : PhiControlData 3 13)
    (extent : Nat)
    (encoding :
      PrefixModelEncoding control.problem extent 12)
    (refutation : Refutation encoding.formula) :
    IsMinimalStateCount control.problem 13 :=
  minimal_state_count_of_prefix_refutation
    control.problem 13 extent control.upper encoding refutation

/-- M09. Reproduce the published base-4 lower bound by refuting every machine
with at most fourteen states on one exact finite prefix. -/
theorem m09_phi_base4_exclude_at_most_fourteen
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 14)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 14 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 14 encoding refutation

/-- M10. First new base-4 target: exclude every machine with at most fifteen states. -/
theorem m10_phi_base4_exclude_at_most_fifteen
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 15)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 15 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 15 encoding refutation

/-- M11. Exclude every machine with at most sixteen states. -/
theorem m11_phi_base4_exclude_at_most_sixteen
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 16)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 16 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 16 encoding refutation

/-- M12. Exclude every machine with at most seventeen states. -/
theorem m12_phi_base4_exclude_at_most_seventeen
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 17)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 17 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 17 encoding refutation

/-- M13. Exclude every machine with at most eighteen states. -/
theorem m13_phi_base4_exclude_at_most_eighteen
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 18)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 18 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 18 encoding refutation

/-- M14. Exclude every machine with at most nineteen states. -/
theorem m14_phi_base4_exclude_at_most_nineteen
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 19)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 19 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 19 encoding refutation

/-- M15. Exclude every machine with at most twenty states. -/
theorem m15_phi_base4_exclude_at_most_twenty
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 20)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 20 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 20 encoding refutation

/-- M16. Exclude every machine with at most twenty-one states. -/
theorem m16_phi_base4_exclude_at_most_twenty_one
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 21)
    (refutation : Refutation encoding.formula) :
    ¬base4Problem.HasGlobalModelAtMost 21 :=
  no_global_model_at_most_of_prefix_refutation
    base4Problem extent 21 encoding refutation

/-- The terminal M-series theorem. Once the published twenty-two-state machine
has been independently verified and M16 carries an LRAT refutation, exact
typed minimality follows in the kernel. -/
theorem phi_base4_twenty_two_state_minimality
    (upper : base4Problem.HasGlobalModel 22)
    (extent : Nat)
    (encoding : PrefixModelEncoding base4Problem extent 21)
    (refutation : Refutation encoding.formula) :
    IsMinimalStateCount base4Problem 22 :=
  minimal_state_count_of_prefix_refutation
    base4Problem 22 extent upper encoding refutation

#print axioms base4_problem_semantics
#print axioms m09_phi_base4_exclude_at_most_fourteen
#print axioms m16_phi_base4_exclude_at_most_twenty_one
#print axioms phi_base4_twenty_two_state_minimality

end D5.S1.Digit.GoldenDFAOMinimalityTargets

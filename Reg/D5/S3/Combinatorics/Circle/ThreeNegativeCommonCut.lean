import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
import Reg.Support.DependentFamily

/-! The source-equivalence bridge retains the complete native telescope and the
literal joint candidate. The law is an existential constructor; a lawful enrolled
readout, whole-family variation/sensitivity, sourceSelection and current binding
remain unresolved under issue #22063. This is not a Contract.Registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut

structure Source where
  a : ℕ
  c : ℕ

def length (q : Source) : ℕ := 2 * q.a + q.c

def seed (q : Source) : ℕ := 1 + 2 ^ q.a + 2 ^ (2 * q.a)

def Assumptions (q : Source) : Prop := 2 ≤ q.c ∧ q.c < q.a

def candidate (q : Source) (w : List (Fin (length q)) × ℕ) : Prop :=
  w.2 ≤ length q ∧ OriginalOrder (length q) (seed q) w.1 ∧
    OriginalOrder (length q + 1) (2 * seed q) (earWord (length q) w.1 w.2)

abbrev signature : Signature where
  Params := Source
  State q := List (Fin (length q)) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q w => candidate q w) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Source, Assumptions q → ∃ w, R.readout () q w

abbrev sourceScope := type_of% (@native_three_negative_common_cut)

theorem bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h q hq
    obtain ⟨sigma, j, hj, ho, hn⟩ := h q.a q.c hq.1 hq.2
    exact ⟨(sigma, j), hj, ho, hn⟩
  · intro h a c hc hca
    obtain ⟨⟨sigma, j⟩, hj, ho, hn⟩ := h ⟨a, c⟩ ⟨hc, hca⟩
    exact ⟨sigma, j, hj, ho, hn⟩

theorem actual_law : arena.Law actual :=
  bridge.mp (@native_three_negative_common_cut)

#print axioms bridge
#print axioms actual_law

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut

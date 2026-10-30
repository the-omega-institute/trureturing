import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
import Reg.Support.DependentFamily

/-! The source-equivalence bridge retains the complete native telescope and the
literal joint candidate. The law is an existential constructor; a lawful enrolled
readout selection and current source binding remain unresolved under issue
#22063. The semantic variation, sensitivity and dependence are retained below. This is not a Contract.Registration. -/

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

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, hw⟩ := h ⟨3, 2⟩ ⟨by decide, by decide⟩
  exact hw

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let q : Source := ⟨3, 2⟩
  obtain ⟨w, hw⟩ := actual_law q ⟨by decide, by decide⟩
  refine ⟨q, w, (w.1, length q + 1), ?_⟩
  change candidate q w ≠ candidate q (w.1, length q + 1)
  intro he
  have hbad : candidate q (w.1, length q + 1) := he ▸ hw
  have hh := hbad.1
  omega

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

#print axioms bridge
#print axioms actual_law
#print axioms source_registration

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut

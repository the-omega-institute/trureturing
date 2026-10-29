import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.IsolatedSmallSource
import Reg.Support.DependentFamily

/-! The source and readout retain the finite carrier, permutation and every
hypothesis. Lawful source selection, whole-family intervention sensitivity and
observational dependence remain unresolved under issue #22063. The bridge is
not a completed four-slot Contract.Registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.IsolatedSmallSource

namespace Reg.D5.S3.Combinatorics.Circle.IsolatedSmallSource

structure Source where
  carrier : Type u
  finite : Fintype carrier
  inhabited : Nonempty carrier
  σ : Equiv.Perm carrier
  w : carrier → ℤ
  Q : ℤ

def Assumptions (q : Source.{u}) : Prop :=
  2 ≤ q.Q ∧
  (∀ i, -(2 * q.Q - 1) ≤ q.w i ∧ q.w i ≤ 2 * q.Q - 1) ∧
  (∀ i, q.w (q.σ i) = doubleStep (4 * q.Q - 1) (q.w i)) ∧
  ((∀ i, |q.w i| < q.Q → 0 ≤ q.w i) ∨
    (∀ i, |q.w i| < q.Q → q.w i ≤ 0)) ∧
  (∀ i, |q.w i| < q.Q → q.Q ≤ |q.w (q.σ i)|)

def candidate (q : Source.{u}) (L : List q.carrier) : Prop :=
  letI := q.finite
  L.Perm (Finset.univ.toList : List q.carrier) ∧
    InStrip q.w (2 * q.Q - 1) 0 L ∧ (L.map q.w).sum = 0

abbrev signature : Signature where
  Params := Source.{u}
  State q := List q.carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q L => candidate q L) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Source.{u}, Assumptions q → ∃ L, R.readout () q L

abbrev sourceScope := type_of% (@finite_isolated_small_completion.{u})

theorem bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h q hq
    letI := q.finite
    letI := q.inhabited
    obtain ⟨hQ, hb, hs, hsign, hi⟩ := hq
    exact h q.σ q.w q.Q hQ hb hs hsign hi
  · intro h α fi ni σ w Q hQ hb hs hsign hi
    exact h ⟨α, fi, ni, σ, w, Q⟩ ⟨hQ, hb, hs, hsign, hi⟩

theorem actual_law : arena.Law actual :=
  bridge.mp (@finite_isolated_small_completion.{u})

#print axioms bridge
#print axioms actual_law

end Reg.D5.S3.Combinatorics.Circle.IsolatedSmallSource

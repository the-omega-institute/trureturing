import Reg.Support.DependentFamily
import D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace

/-! # Source family for the odd cyclic inverse identities -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace

open _root_.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape

noncomputable section

def signature : DependentFamily.Signature where
  Params := ℕ
  State := fun m => Word (2 * m + 1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ m => Word (2 * m + 1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ m y => inverse m y) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ m : ℕ,
    Function.LeftInverse (R.readout () m) chi ∧ Function.RightInverse (R.readout () m) chi

abbrev sourceScope := type_of% (@inverse_spec)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp inverse_spec

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0).2 (fun _ => 1)
  have hz := congrFun hh 0
  change chi (0 : Word 1) 0 = (1 : ZMod 2) at hz
  simpa [chi] using hz

theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro _
  refine ⟨0, 0, (fun _ => 1), ?_⟩
  change inverse 0 (0 : Word 1) ≠ inverse 0 (fun _ => 1)
  intro h
  have hh := congrArg (@chi 1) h
  rw [(inverse_spec 0).2, (inverse_spec 0).2] at hh
  have hz := congrFun hh 0
  exact zero_ne_one hz

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

end
end Reg.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace

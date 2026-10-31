import D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The new legality predicate is observed with the complete physical source telescope. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := List (Fin (n + 7)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n seed => OriginalOrder (n + 7) seed) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 2 ≤ n) (_h8 : n % 8 = 0)
    (sigma : List (Fin (n + 6))) (cut : ℕ) (_hcut : cut ≤ n + 6)
    (_hold : OriginalOrder (n + 6) 85 sigma)
    (_hnew : R.readout () n 170 (earWord (n + 6) sigma cut)),
    ¬ ([n + 1, n + 3, n + 5, n - 1].Sublist (sigma.map Fin.val) ∨
      [n + 3, n + 5, n - 1, n + 1].Sublist (sigma.map Fin.val))

private theorem actual_law : arena.Law actual :=
  actual_source_cyclic_order_residue_obstruction

private def oldWord : List (Fin 14) := [0,1,2,3,6,9,8,11,5,10,13,4,12,7]

private theorem old_legal : OriginalOrder 14 85 oldWord := by
  have hs : InStrip (actualSource 14 85) (modulus 14 / 2) 0 oldWord := by
    norm_num [oldWord, InStrip, actualSource, centered, modulus]
  refine ⟨by decide, ?_, ?_⟩
  · norm_num [oldWord, actualSource, centered, modulus]
  · intro r
    simpa only [zero_add, Set.mem_Icc] using inStrip_prefix hs r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 8 (by decide) (by decide) oldWord 0 (by decide) old_legal (by trivial)
  exact hh (Or.inl (by decide))

private def identityWord : List (Fin 15) := List.finRange 15
private theorem zero_legal : OriginalOrder 15 0 identityWord := by
  have hf : actualSource 15 0 = fun _ => (0 : ℤ) := by
    funext i
    norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, by simp [hf], ?_⟩
  intro r
  simp [hf, modulus]

private theorem two_illegal : ¬ OriginalOrder 15 2 identityWord := by
  intro h
  have hh := h.2.2 14
  norm_num [identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro side
  refine ⟨8, 0, 2, ?_⟩
  intro he
  have hh := congrFun he identityWord
  change OriginalOrder 15 0 identityWord = OriginalOrder 15 2 identityWord at hh
  exact two_illegal (hh.mp zero_legal)

def source_registration : Registration arena
    (type_of% (@actual_source_cyclic_order_residue_obstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction.actual_source_cyclic_order_residue_obstruction)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction.actual_source_cyclic_order_residue_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction

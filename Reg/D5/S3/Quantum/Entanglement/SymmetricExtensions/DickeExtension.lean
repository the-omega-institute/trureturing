import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
import Reg.Support.SingleDependentReadout

/-! The full Dicke cone telescope, observed through its actual star-extension predicate. -/

namespace Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure Parameters where
  n : ℕ
  r : ℕ
  hn : 1 ≤ n
  hr : 2 ≤ r
  Y : Fin n → Fin n → ℝ
  hY : ∀ i j, i ≤ j → 0 ≤ Y i j

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Matrix (Fin p.r → Fin p.n) (Fin p.r → Fin p.n) ℂ)
    (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ p E =>
    StarExtension (⟨0,by have := p.hr; omega⟩ : Fin p.r) (dickeOperator p.Y) E)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r)
    (Y : Fin n → Fin n → ℝ) (hY : ∀ i j, i ≤ j → 0 ≤ Y i j),
    (∃ E, R.readout () ⟨n,r,hn,hr,Y,hY⟩ E) ↔
      ∃ E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ,
        CompleteExtension (dickeOperator Y) E

private lemma zero_complete (n r : ℕ) :
    CompleteExtension (dickeOperator (fun _ _ : Fin n => (0 : ℝ)))
      (0 : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, by simp, ?_, ?_⟩
  · intro a b hab
    ext u v
    simp [edgeMarginal, _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
      dickeOperator]
  · intro S hS hp
    exact Matrix.PosSemidef.zero

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 1 2 (by omega) (by omega) (fun _ _ => 0) (by simp)).mpr
    ⟨0,zero_complete 1 2⟩
  obtain ⟨E,hE⟩ := hz
  exact hE

private def base : Parameters := ⟨1,2,by omega,by omega,fun _ _ => 0,by simp⟩

private lemma zero_star :
    StarExtension (⟨0,by decide⟩ : Fin 2)
      (dickeOperator (fun _ _ : Fin 1 => (0 : ℝ)))
      (0 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, by simp, ?_, ?_⟩
  · intro i hi
    ext u v
    simp [edgeMarginal, _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
      dickeOperator]
  · intro S hS hp
    exact Matrix.PosSemidef.zero

private lemma not_one_star :
    ¬ StarExtension (⟨0,by decide⟩ : Fin 2)
      (dickeOperator (fun _ _ : Fin 1 => (0 : ℝ)))
      (1 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ) := by
  intro h
  have hm := h.2.2.1 (⟨1,by decide⟩ : Fin 2) (by decide)
  have he := congrArg (fun A : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ =>
    A (0,0) (0,0)) hm
  have hone (x y : Fin 2 → Fin 1) :
      (1 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ) x y = 1 := by
    simp [Matrix.one_apply, Subsingleton.elim x y]
  norm_num [edgeMarginal,
    _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.submatrix_apply, hone, dickeOperator] at he

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨base,0,1,?_⟩
  intro h
  have h0 : actual.readout () base 0 := zero_star
  have h1 : actual.readout () base 1 := Eq.mp h h0
  exact not_one_star h1

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p E =>
    StarExtension (⟨0,by have := p.hr; omega⟩ : Fin p.r) (dickeOperator p.Y) E)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","arg","body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration


/-! A source-faithful dependent reconstruction of `same_matrix_core`. The four-slot escape
identity remains unestablished; this is an audit attempt, not declared validation. -/
namespace BoseCore
universe u v

structure Parameters where
  I : Type u
  L : Type v
  finiteI : Fintype I
  eqI : DecidableEq I
  finiteL : Fintype L
  eqL : DecidableEq L
  root : I
  rho : Matrix (L × L) (L × L) ℂ
  support : pairSymmetricProjector * rho * pairSymmetricProjector = rho

attribute [instance] Parameters.finiteI Parameters.eqI Parameters.finiteL Parameters.eqL

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Matrix (p.I → p.L) (p.I → p.L) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p E => StarExtensionCore p.root p.rho E) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {I : Type u} {L : Type v}
    [fi : Fintype I] [di : DecidableEq I] [fl : Fintype L] [dl : DecidableEq L]
    (root : I) (rho : Matrix (L × L) (L × L) ℂ)
    (support : pairSymmetricProjector * rho * pairSymmetricProjector = rho)
    (E : Matrix (I → L) (I → L) ℂ),
    R.readout () ⟨I,L,fi,di,fl,dl,root,rho,support⟩ E ↔ CompleteExtensionCore rho E

private lemma zero_complete {I : Type u} {L : Type v}
    [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] :
    CompleteExtensionCore (0 : Matrix (L × L) (L × L) ℂ)
      (0 : Matrix (I → L) (I → L) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, by simp, ?_⟩
  · intro a b hab
    ext x y
    simp [edgeMarginal,
      _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight]

private def base : Parameters.{u,v} := {
  I := ULift.{u} (Fin 2)
  L := ULift.{v} (Fin 1)
  finiteI := inferInstance
  eqI := inferInstance
  finiteL := inferInstance
  eqL := inferInstance
  root := ⟨0⟩
  rho := 0
  support := by simp }

private lemma rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hz := (h (I := (base.{u,v}).I) (L := (base.{u,v}).L)
    (base.{u,v}).root (base.{u,v}).rho (base.{u,v}).support 0).mpr
      (zero_complete (I := (base.{u,v}).I) (L := (base.{u,v}).L))
  exact hz

private lemma dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  change Unit at i
  cases i
  refine ⟨base.{u,v},0,-1,?_⟩
  intro h
  have h0 : actual.readout () base 0 :=
    ( same_matrix_core base.root base.rho base.support 0).mpr zero_complete
  have hneg : StarExtensionCore base.root base.rho (-1) := Eq.mp h h0
  have hd := hneg.1.diag_nonneg (i := fun _ => ⟨0⟩)
  have hr := (RCLike.nonneg_iff.mp hd).1
  norm_num [Matrix.neg_apply, Matrix.one_apply, base] at hr

def source_registration : Registration arena.{u,v}
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.same_matrix_core.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.same_matrix_core,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.same_matrix_core.{u,v})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.BoseCore.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.BoseCore.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p E => StarExtensionCore p.root p.rho E)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end BoseCore


/-! A source-faithful dependent reconstruction of `same_matrix`. The four-slot escape
identity remains unestablished; this is an audit attempt, not declared validation. -/
namespace BosePPT
universe u v

structure Parameters where
  I : Type u
  L : Type v
  finiteI : Fintype I
  eqI : DecidableEq I
  finiteL : Fintype L
  eqL : DecidableEq L
  root : I
  rho : Matrix (L × L) (L × L) ℂ
  support : pairSymmetricProjector * rho * pairSymmetricProjector = rho

attribute [instance] Parameters.finiteI Parameters.eqI Parameters.finiteL Parameters.eqL

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Matrix (p.I → p.L) (p.I → p.L) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p E => StarExtension p.root p.rho E) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {I : Type u} {L : Type v}
    [fi : Fintype I] [di : DecidableEq I] [fl : Fintype L] [dl : DecidableEq L]
    (root : I) (rho : Matrix (L × L) (L × L) ℂ)
    (support : pairSymmetricProjector * rho * pairSymmetricProjector = rho)
    (E : Matrix (I → L) (I → L) ℂ),
    R.readout () ⟨I,L,fi,di,fl,dl,root,rho,support⟩ E ↔ CompleteExtension rho E

private lemma zero_complete {I : Type u} {L : Type v}
    [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] :
    CompleteExtension (0 : Matrix (L × L) (L × L) ℂ)
      (0 : Matrix (I → L) (I → L) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, by simp, ?_, ?_⟩
  · intro a b hab
    ext x y
    simp [edgeMarginal,
      _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight]
  · intro S hS hp
    exact Matrix.PosSemidef.zero

private def base : Parameters.{u,v} := {
  I := ULift.{u} (Fin 2)
  L := ULift.{v} (Fin 1)
  finiteI := inferInstance
  eqI := inferInstance
  finiteL := inferInstance
  eqL := inferInstance
  root := ⟨0⟩
  rho := 0
  support := by simp }

private lemma rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hz := (h (I := (base.{u,v}).I) (L := (base.{u,v}).L)
    (base.{u,v}).root (base.{u,v}).rho (base.{u,v}).support 0).mpr
      (zero_complete (I := (base.{u,v}).I) (L := (base.{u,v}).L))
  exact hz

private lemma dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  change Unit at i
  cases i
  refine ⟨base.{u,v},0,-1,?_⟩
  intro h
  have h0 : actual.readout () base 0 :=
    ( same_matrix base.root base.rho base.support 0).mpr zero_complete
  have hneg : StarExtension base.root base.rho (-1) := Eq.mp h h0
  have hd := hneg.1.diag_nonneg (i := fun _ => ⟨0⟩)
  have hr := (RCLike.nonneg_iff.mp hd).1
  norm_num [Matrix.neg_apply, Matrix.one_apply, base] at hr

def source_registration : Registration arena.{u,v}
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.same_matrix.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.same_matrix,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.same_matrix.{u,v})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.BosePPT.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.BosePPT.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p E => StarExtension p.root p.rho E)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end BosePPT


namespace BoseSupport
universe u v
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor

abbrev signature : Signature where
  Params := BoseCore.Parameters.{u,v}
  State p := Matrix (p.I → p.L) (p.I → p.L) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.I → p.L) (p.I → p.L) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p E => P p.I p.L * E * P p.I p.L) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ E => E + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {I : Type u} {L : Type v}
    [fi : Fintype I] [di : DecidableEq I] [fl : Fintype L] [dl : DecidableEq L]
    (root : I) (rho : Matrix (L × L) (L × L) ℂ)
    (support : pairSymmetricProjector * rho * pairSymmetricProjector = rho)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hm : ∀ i (hi : root ≠ i), edgeMarginal root i hi E = rho),
    R.readout () ⟨I,L,fi,di,fl,dl,root,rho,support⟩ E = E ∧
      ∀ a b (hab : a ≠ b), edgeMarginal a b hab E = rho

private def base : BoseCore.Parameters.{u,v} := {
  I := ULift.{u} (Fin 2)
  L := ULift.{v} (Fin 1)
  finiteI := inferInstance
  eqI := inferInstance
  finiteL := inferInstance
  eqL := inferInstance
  root := ⟨0⟩
  rho := 0
  support := by simp }

private lemma zero_marginals :
    ∀ i (hi : base.root ≠ i), edgeMarginal base.root i hi 0 = base.rho := by
  intro i hi
  ext x y
  simp [base, edgeMarginal,
    _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight]

private lemma rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hz := (h (I := (base.{u,v}).I) (L := (base.{u,v}).L)
    (base.{u,v}).root (base.{u,v}).rho (base.{u,v}).support 0
      Matrix.PosSemidef.zero zero_marginals).1
  have hd := congrArg (fun M => M (fun _ => ⟨0⟩) (fun _ => ⟨0⟩)) hz
  norm_num [rejected, realize, base, Matrix.one_apply, Matrix.zero_apply] at hd

private lemma dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  change Unit at i
  cases i
  refine ⟨base.{u,v},0,1,?_⟩
  intro h
  have hp : P base.I base.L *ᵥ (fun _ => (1 : ℂ)) = fun _ => 1 :=
    P_mulVec_of_symmetric _ (by intro sigma x; rfl)
  have hm : (0 : Matrix (base.I → base.L) (base.I → base.L) ℂ) = P base.I base.L := by
    simpa only [actual, realize, mul_zero, zero_mul, mul_one, P_idempotent] using h
  have hd := congrArg (fun M => (M *ᵥ (fun _ => (1 : ℂ))) (fun _ => ⟨0⟩)) hm
  rw [Matrix.zero_mulVec, hp] at hd
  norm_num [Pi.zero_apply] at hd

def source_registration : Registration arena.{u,v}
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.support_of_bose_root_marginals.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.support_of_bose_root_marginals,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.support_of_bose_root_marginals.{u,v})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.BoseSupport.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.BoseSupport.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p E => P p.I p.L * E * P p.I p.L)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,10,11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end BoseSupport

end
end Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

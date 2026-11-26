import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary

/-! Audit the actual twist operator, including a one-chord nonconstant fixture. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open _root_.D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State E := E → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := (E → K) →ₗ[K] (E → K)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ t => twistDiagonal t) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} (t : E → Bool) (z : E → K) (e : E),
    R.readout () E t z e = if t e then z e else 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (fun _ : ULift.{u} Unit => true) (fun _ => 1) ⟨()⟩
  change (0 : K) = (if true = true then 1 else 0) at hh
  simp at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨ULift.{u} Unit,(fun _ => true),(fun _ => false),?_⟩
  intro h
  change twistDiagonal (fun _ : ULift.{u} Unit => true) =
    twistDiagonal (fun _ : ULift.{u} Unit => false) at h
  have hh := congrArg (fun f : (ULift.{u} Unit → K) →ₗ[K] (ULift.{u} Unit → K) =>
    f (fun _ => 1) ⟨()⟩) h
  simp [twistDiagonal_apply] at hh

def source_registration : Registration arena.{u} (type_of% @twistDiagonal_apply.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@twistDiagonal_apply.{u},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@twistDiagonal_apply.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.twistDiagonal_apply.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ t => twistDiagonal t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace BoundaryRank
open _root_.D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank

private abbrev BoundaryParams :=
  Sigma fun n : ℕ => Sigma fun E : Type u =>
    Sigma fun _ : E → D n => E → D n

private abbrev boundarySignature : Signature where
  Params := BoundaryParams.{u}
  State p := p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def circles (_ : Unit) (p : BoundaryParams.{u}) (t : p.2.1 → Bool) : ℕ :=
  Nat.card (Quotient (boundarySetoid p.2.2.1 p.2.2.2 t))

private def boundaryActual : Realization boundarySignature.{u} :=
  realize boundarySignature circles (fun e => nomatch e)

private def boundaryRejected : Realization boundarySignature.{u} :=
  realize boundarySignature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev boundaryArena : Arena where
  signature := boundarySignature.{u}
  Law R := ∀ {n : ℕ} {E : Type u} [g : Fintype E] (a b : E → D n) (t : E → Bool)
    (_ha : Function.Injective a) (_hb : Function.Injective b) (_hd : ∀ i j, a i ≠ b j)
    (_hord : ∀ e, (a e).val < (b e).val),
    R.readout () ⟨n,E,a,b⟩ t +
      Module.finrank K (interlacementMap a b + twistDiagonal t).range = 1+Fintype.card E

private abbrev U := ULift.{u} Unit
private def a₀ : U.{u} → D 1 := fun _ => 0
private def b₀ : U.{u} → D 1 := fun _ => 1
private theorem ha₀ : Function.Injective a₀.{u} := fun _ _ _ => Subsingleton.elim _ _
private theorem hb₀ : Function.Injective b₀.{u} := fun _ _ _ => Subsingleton.elim _ _
private theorem hd₀ : ∀ i j : U.{u}, a₀ i ≠ b₀ j := by intro i j; change (0 : Fin 2) ≠ 1; decide
private theorem hord₀ : ∀ i : U.{u}, (a₀ i).val < (b₀ i).val := by intro i; change (0 : ℕ) < 1; decide

private theorem emptyInterlace : interlacementMap a₀.{u} b₀=0 := by
  apply LinearMap.ext
  intro z
  funext e
  change (interlacementMap a₀ b₀) z e = 0
  rw [interlacementMap_apply]
  have he : e = (default : U) := Subsingleton.elim _ _
  simp [interlaces,a₀,b₀,he]

private theorem noTwist : twistDiagonal (fun _ : U.{u} => false)=0 := by
  ext z e
  simp [twistDiagonal_apply]

private theorem fullTwist : twistDiagonal (fun _ : U.{u} => true)=LinearMap.id := by
  ext z e
  simp [twistDiagonal_apply]

private abbrev sample : BoundaryParams.{u} := ⟨1,U.{u},a₀,b₀⟩

private theorem sampleUntwisted : circles () sample.{u} (fun _=>false)=2 := by
  have h := signed_flag_boundary_plus_rank a₀.{u} b₀ (fun _=>false) ha₀ hb₀ hd₀ hord₀
  rw [emptyInterlace,noTwist,zero_add,LinearMap.range_zero,finrank_bot] at h
  simpa [circles,sample] using h

private theorem sampleTwisted : circles () sample.{u} (fun _=>true)=1 := by
  have h := signed_flag_boundary_plus_rank a₀.{u} b₀ (fun _=>true) ha₀ hb₀ hd₀ hord₀
  rw [emptyInterlace,fullTwist,zero_add,LinearMap.range_id,finrank_top] at h
  simp [Module.finrank_pi] at h
  simpa only [circles,sample] using (show Nat.card (Quotient (boundarySetoid a₀ b₀ (fun _=>true)))=1 by omega)

private theorem boundaryReject : ¬ boundaryArena.{u}.Law boundaryRejected := by
  intro h
  have hh := h a₀.{u} b₀ (fun _=>false) ha₀ hb₀ hd₀ hord₀
  rw [emptyInterlace,noTwist,zero_add,LinearMap.range_zero,finrank_bot] at hh
  simp [boundaryRejected,realize] at hh

private theorem boundaryDependence : ObservationalDependence boundarySignature.{u} boundaryActual := by
  intro i; cases i
  refine ⟨sample,(fun _=>false),(fun _=>true),?_⟩
  change circles () sample.{u} (fun _=>false) ≠ circles () sample.{u} (fun _=>true)
  rw [sampleUntwisted,sampleTwisted]
  decide

def boundarySource : Registration boundaryArena.{u} (type_of% @signed_flag_boundary_plus_rank.{u}) where
  actual := boundaryActual
  bridge := Iff.rfl
  variation := ⟨@signed_flag_boundary_plus_rank.{u},boundaryRejected,boundaryReject⟩
  sensitivity := ⟨fun i => ⟨boundaryRejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,boundaryReject⟩,fun e => nomatch e⟩
  dependence := boundaryDependence

def boundaryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signed_flag_boundary_plus_rank.{u}) (Realization boundarySignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.signed_flag_boundary_plus_rank.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.BoundaryRank.boundarySource
  realizationSource := none
  generated := false
  arena := .source ⟨boundaryArena⟩
  objectArena := .source ⟨boundaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundaryArena ⟨boundarySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundarySignature circles (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
    definition := none
    coordinates := #[0,1,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "fn","arg","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms boundaryRegistration
end BoundaryRank

#print axioms registration
end
end Reg.D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary

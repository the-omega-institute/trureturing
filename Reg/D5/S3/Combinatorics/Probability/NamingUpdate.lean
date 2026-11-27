import D5.S3.Combinatorics.Probability.NamingUpdate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Newly assigned values are removed from the remaining name set. -/

open LeanInformationAudit
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S3.Combinatorics.Probability.NamingUpdate
open _root_.D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Probability.NamingUpdate

noncomputable section
universe u v

private abbrev NameSignature : Signature where
  Params := Σ V : Type u, Σ N : Type v, Σ (_ : Finset V), Finset N
  State p := p.2.2.1 ↪ p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def remainingNames : Realization NameSignature.{u,v} :=
  realize NameSignature (fun _ p expanded => unused p.2.2.2 p.2.2.1 expanded)
    (fun e => nomatch e)

private def noNames : Realization NameSignature.{u,v} :=
  realize NameSignature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev NameArena : Arena where
  signature := NameSignature.{u,v}
  Law R := ∀ {V : Type u} {N : Type v} [DecidableEq V] [Finite V] [Finite N]
    {K L : Finset V} (hKL : K ⊆ L)
    (A : Finset N) (known : K ↪ N) (expanded : L ↪ N)
    (_hOld : ∀ x : K, expanded ⟨x.1, hKL x.2⟩ = known x)
    (_hNew : ∀ x : L, x.1 ∉ K → expanded x ∈ A)
    (h : Nonempty {f : Candidates K A known // agrees expanded f.1}),
    let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A known) := h.map Subtype.val
    let μ := uniformPmf (Candidates K A known)
    let observed : Set (Candidates K A known) := {f | agrees expanded f.1}
    let remaining := R.readout () ⟨V, N, L, A⟩ expanded
    let New := Candidates L remaining expanded
    ∃ equivalence : {f : Candidates K A known // agrees expanded f.1} ≃ New,
      (∀ f, (equivalence f).1 = f.1.1) ∧
      let _ : Fintype New := Fintype.ofFinite _
      let _ : Nonempty New := h.map equivalence
      ∀ hr : ∃ r ∈ observed, r ∈ μ.support,
        ((μ.filter observed hr).map (fun f => f.1)) = (uniformPmf New).map Subtype.val

private theorem noNames_invalid : ¬ NameArena.{u,v}.Law noNames := by
  classical
  intro h
  let V := ULift.{u} Unit
  let N := ULift.{v} Unit
  let vertex : V := ⟨()⟩
  let name : N := ⟨()⟩
  let K : Finset V := ∅
  let A : Finset N := {name}
  let known : K ↪ N :=
    ⟨fun _ => name, fun x _ _ => (Finset.notMem_empty x.1 x.2).elim⟩
  let complete : V ↪ N := ⟨fun _ => name, fun _ _ _ => Subsingleton.elim _ _⟩
  let candidate : Candidates K A known :=
    ⟨complete, fun _ => rfl, fun _ => Finset.mem_singleton_self _⟩
  have hAgree : agrees known candidate.1 := fun _ => rfl
  have hNew (x : K) (_ : x.1 ∉ K) : known x ∈ A := Finset.mem_singleton_self _
  obtain ⟨e, _⟩ := h (show K ⊆ K from Finset.Subset.refl K) A known known
    (fun _ => rfl) hNew ⟨⟨candidate, hAgree⟩⟩
  have hOutside : vertex ∉ K := Finset.notMem_empty _
  have hAvailable := (e ⟨candidate, hAgree⟩).2.2 ⟨vertex, hOutside⟩
  exact Finset.notMem_empty _ hAvailable

private theorem remainingNames_varies : ObservationalDependence NameSignature.{u,v} remainingNames := by
  classical
  intro _
  let V := ULift.{u} Unit
  let N := ULift.{v} Bool
  let vertex : V := ⟨()⟩
  let name : N := ⟨false⟩
  let alternative : N := ⟨true⟩
  let _ : DecidableEq N := Classical.decEq N
  let L : Finset V := {vertex}
  let A : Finset N := {name}
  let f : L ↪ N := ⟨fun _ => name, fun _ _ _ => Subsingleton.elim _ _⟩
  let g : L ↪ N := ⟨fun _ => alternative, fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨⟨V, N, L, A⟩, f, g, ?_⟩
  change unused A L f ≠ unused A L g
  have hUsed : name ∈ L.attach.image f :=
    Finset.mem_image.mpr ⟨⟨vertex, Finset.mem_singleton_self _⟩, Finset.mem_attach _ _, rfl⟩
  have hStillFree : name ∈ unused A L g := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self _, ?_⟩
    intro hIn
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hIn
    exact Bool.false_ne_true (congrArg ULift.down hy).symm
  intro he
  have hFreeAtF : name ∈ unused A L f := he ▸ hStillFree
  exact (Finset.mem_sdiff.mp hFreeAtF).2 hUsed

def evidence : Registration NameArena.{u,v} (type_of% (@uniform_after_reveal.{u,v})) where
  actual := remainingNames
  bridge := Iff.rfl
  variation := ⟨@uniform_after_reveal.{u,v}, noNames, noNames_invalid⟩
  sensitivity := ⟨fun i => ⟨noNames, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, noNames_invalid⟩, fun e => nomatch e⟩
  dependence := remainingNames_varies

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@uniform_after_reveal.{u,v}) (Realization NameSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Probability.NamingUpdate.uniform_after_reveal
  realizationName := `Reg.D5.S3.Combinatorics.Probability.NamingUpdate.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨NameArena.{u,v}⟩
  objectArena := .source ⟨NameArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source NameArena.{u,v} ⟨evidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize NameSignature
    (fun _ p expanded => unused p.2.2.2 p.2.2.1 expanded) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Probability.NamingUpdate
    definition := none
    coordinates := #[0, 1, 6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Probability.NamingUpdate

import D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed
import Reg.Support.DependentFamily

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.DependencyTopology
open LegalLedgerFixedSet SupportFamilyNotIntersectionClosed

namespace Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed

noncomputable section

abbrev signature : Signature where
  Params := Σ _P : Type, Σ _Proof : Type, Σ _Ax : Type, Type
  State p := KernelData p.1 p.2.1 p.2.2.1 p.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (Set p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => supportFamily k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ¬ (∀ (P Proof Ax Model : Type) (k : KernelData P Proof Ax Model), SourceLaws k →
    IntersectionClosed (R.readout () ⟨P, Proof, Ax, Model⟩ k) ∨
      ∃ edge : P → P → Prop, supportFamily k = graphFamily edge)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro P Proof Ax Model k laws
  exact Or.inl (fun _ _ _ _ => Set.mem_univ _)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let none : KernelData Unit Unit Unit Unit :=
    (fun _ _ => false, fun _ => ∅, fun _ => ∅, ∅, id, fun _ _ => True, fun _ _ => True)
  let some : KernelData Unit Unit Unit Unit :=
    (fun _ _ => true, fun _ => ∅, fun _ => ∅, ∅, id, fun _ _ => True, fun _ _ => True)
  refine ⟨⟨Unit, Unit, Unit, Unit⟩, none, some, ?_⟩
  intro heq
  have good : ({()} : Set Unit) ∈ supportFamily some := by
    refine ⟨⟨⟨{()}, fun _ => ()⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p; rfl
    · intro p ax h; exact Finset.notMem_empty ax h
    · intro p q h; exact (Finset.notMem_empty q h).elim
    · intro p h
      have impossible : Relation.TransGen (fun _ _ : Unit => False) p p :=
        Relation.TransGen.mono (by rintro _ _ ⟨_, h⟩; exact Finset.notMem_empty _ h) p p h
      simpa only [Relation.transGen_eq_self] using impossible
    · simp [CertifiedNodes.nodes]
  have bad : ({()} : Set Unit) ∉ supportFamily none := by
    rintro ⟨C, hC⟩
    have hp : () ∈ C.nodes := by
      change () ∈ (↑C.nodes : Set Unit)
      rw [hC]
      exact Set.mem_singleton ()
    have h := C.property.1 ⟨(), hp⟩
    exact Bool.false_ne_true h
  change supportFamily none = supportFamily some at heq
  exact bad (heq ▸ good)

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i
      cases j
      exact False.elim (h rfl)
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem
  _root_.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.result in arena
  readout via (realize signature (fun _ _ k => supportFamily k) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed
    «definition» := some {
      owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed
      name := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.claim
      path := #["arg"] }
    coordinates := #[0, 1, 2, 3]
    readouts := #[
      { path := #["arg", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
        stateBinder := 4 }] })
  escape continues (open)

end

end Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed

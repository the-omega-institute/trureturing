import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.UnreachableProofs

abbrev familyArena : StructuralArena := ⟨Finset Nat⟩

def kernels (index : Nat) : StructuralKernel (Finset Nat) := {
  relation := fun x y => decide (index ∈ x) = decide (index ∈ y)
  equivalence := eq_equivalence.comap fun x => decide (index ∈ x) }

def familyLaw (family : Nat → StructuralKernel (Finset Nat)) : Prop :=
  ∀ i x, (family i).relation x x

theorem familyReflexive : familyLaw kernels := fun _ _ => rfl

theorem infiniteObligation : InfinitePrimitiveObligation ``familyReflexive
    familyArena Nat familyLaw kernels (familyLaw kernels) where
  infinite := inferInstance
  equivalence := Iff.rfl
  noFiniteSubfamily := by
    intro selected
    obtain ⟨i, outside⟩ := selected.exists_notMem
    refine ⟨∅, {i}, ?_, ?_⟩
    · intro j member
      have different : j ≠ i := fun same => outside (same ▸ member)
      simp [kernels, different]
    · intro allAgree
      have impossible := allAgree i
      simpa [kernels] using impossible

def noBundle : UnreachableElaborationEvidence (familyLaw kernels) where
  reason := .noFinitePrimitiveBundle
  candidateArena := some ``familyArena
  explanation := "The proposed primitive signature is indexed by Nat."
  failedObligation := some ``infiniteObligation

theorem boundedParity : ∀ n : Nat, n % 2 < 2 := Evidence.structuralTheorem

def identityReadouts : StructuralPrimitiveRealization Evidence.infiniteArena
    Evidence.structuralLawArena.signature := ⟨fun _ n => n⟩

theorem unfaithfulObligation : UnfaithfulPrimitiveObligation ``boundedParity
    Evidence.structuralLawArena identityReadouts (∀ n : Nat, n % 2 < 2) := by
  constructor
  intro bridge
  have impossible := bridge.mp boundedParity 2
  exact Nat.lt_irrefl 2 impossible

def noRealization : UnreachableElaborationEvidence (∀ n : Nat, n % 2 < 2) where
  reason := .noFaithfulPrimitiveRealization
  candidateArena := some ``Evidence.infiniteArena
  explanation := "Identity readouts violate the proposed law at state 2."
  failedObligation := some ``unfaithfulObligation

def inventory : DispositionInventory := ⟨"reasons", #[
  ⟨⟨``Evidence.closedNumerical, "1"⟩,
    .unreachable ⟨.noCanonicalObjectCarrier, ``Evidence.noCarrier⟩⟩,
  ⟨⟨``familyReflexive, "2"⟩, .unreachable ⟨.noFinitePrimitiveBundle, ``noBundle⟩⟩,
  ⟨⟨``boundedParity, "3"⟩,
    .unreachable ⟨.noFaithfulPrimitiveRealization, ``noRealization⟩⟩]⟩

/-- info: all-reasons-validated -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule inventory
  logInfo "all-reasons-validated"

/-- info: (3, 1, 1, 1, 3) -/
#guard_msgs in
#eval let c := count inventory
  (c.unreachable, c.noCanonicalObjectCarrier, c.noFinitePrimitiveBundle,
    c.noFaithfulPrimitiveRealization,
    c.noCanonicalObjectCarrier + c.noFinitePrimitiveBundle + c.noFaithfulPrimitiveRealization)

theorem otherParity : ∀ n : Nat, n % 2 < 2 := boundedParity

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.UnreachableProofs.otherParity class=unreachable invalid=evidence.theorem -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule ⟨"reasons", #[
    ⟨⟨``otherParity, "other"⟩,
      .unreachable ⟨.noFaithfulPrimitiveRealization, ``noRealization⟩⟩]⟩

#print axioms infiniteObligation
#print axioms unfaithfulObligation

end LeanInformationAudit.Tests.Census.UnreachableProofs

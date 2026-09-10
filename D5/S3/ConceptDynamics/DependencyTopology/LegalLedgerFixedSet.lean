/- GID: D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed membership of legal proof ledgers under witness-preserving extensions. -/

import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sum.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet

open DependencyReachabilityOrder (AcyclicEdge)

universe u v w x

/-- The source kernel, finite readouts, permitted axioms and model semantics. -/
def KernelData (P : Type u) (Proof : Type v) (Ax : Type w) (Model : Type x) :=
  (Proof → P → Bool) × (Proof → Finset Ax) × (Proof → Finset P) × Set Ax ×
    (P → P) × (Model → Set Ax → Prop) × (Model → P → Prop)

variable {P : Type u} {Proof : Type v} {Ax : Type w} {Model : Type x}

def KernelData.accept (k : KernelData P Proof Ax Model) : Proof → P → Bool := k.1
def KernelData.axioms (k : KernelData P Proof Ax Model) : Proof → Finset Ax := k.2.1
def KernelData.refs (k : KernelData P Proof Ax Model) : Proof → Finset P := k.2.2.1
def KernelData.permitted (k : KernelData P Proof Ax Model) : Set Ax := k.2.2.2.1
def KernelData.neg (k : KernelData P Proof Ax Model) : P → P := k.2.2.2.2.1
def KernelData.models (k : KernelData P Proof Ax Model) : Model → Set Ax → Prop :=
  k.2.2.2.2.2.1
def KernelData.holds (k : KernelData P Proof Ax Model) : Model → P → Prop :=
  k.2.2.2.2.2.2

variable (k : KernelData P Proof Ax Model)

/-- A permitted proof is accepted and uses only permitted axioms. -/
def Proved (p : P) : Prop :=
  ∃ π : Proof, k.accept π p = true ∧ ∀ a ∈ k.axioms π, a ∈ k.permitted

/-- A finite core with exact dependent witnesses and their acyclic reference graph. -/
def CertifiedNodes :=
  {data : (Σ nodes : Finset P, {p // p ∈ nodes} → Proof) //
    (∀ p, k.accept (data.2 p) p.val = true) ∧
    (∀ p, ∀ a ∈ k.axioms (data.2 p), a ∈ k.permitted) ∧
    (∀ p, ∀ q ∈ k.refs (data.2 p), q ∈ data.1) ∧
    AcyclicEdge (fun q p => ∃ hp : p ∈ data.1, q ∈ k.refs (data.2 ⟨p, hp⟩))}

variable {k}

def CertifiedNodes.nodes (C : CertifiedNodes k) : Finset P := C.val.1
def CertifiedNodes.witness (C : CertifiedNodes k) : {p // p ∈ C.nodes} → Proof :=
  C.val.2

/-- Edges are the actual references of the selected witnesses. -/
def CertifiedNodes.edge (C : CertifiedNodes k) (q p : P) : Prop :=
  ∃ hp : p ∈ C.nodes, q ∈ k.refs (C.witness ⟨p, hp⟩)

/-- A certificate contains its certified proposition. -/
def Certificate (k : KernelData P Proof Ax Model) (p : P) :=
  {C : CertifiedNodes k // p ∈ C.nodes}

/-- A legal ledger has a certified core and an arbitrary disjoint registered frontier. -/
def LegalLedger (k : KernelData P Proof Ax Model) :=
  {data : CertifiedNodes k × Set P // ∀ p ∈ data.2, p ∉ data.1.nodes}

def LegalLedger.core (L : LegalLedger k) : CertifiedNodes k := L.val.1
def LegalLedger.frontier (L : LegalLedger k) : Set P := L.val.2

/-- The source assumptions are premises, including soundness and consistency. -/
def SourceLaws (k : KernelData P Proof Ax Model) : Prop :=
  (∀ p, Proved k p → ∀ M, k.models M k.permitted → k.holds M p) ∧
  (∀ p, Proved k p → Nonempty (Certificate k p)) ∧
  (∀ p, ¬ (Proved k p ∧ Proved k (k.neg p)))

def Frozen (L : LegalLedger k) : Set P := {p | p ∈ L.core.nodes}

/-- Extensions retain nodes, derived edges, and the exact old witness at every old node. -/
def Extends (L L' : LegalLedger k) : Prop :=
  (∀ p, p ∈ L.core.nodes → p ∈ L'.core.nodes) ∧
  (∀ q p, L.core.edge q p → L'.core.edge q p) ∧
  (∀ p (h : p ∈ L.core.nodes) (h' : p ∈ L'.core.nodes),
    L'.core.witness ⟨p, h'⟩ = L.core.witness ⟨p, h⟩)

/-- Admissibility is required on every legal input to a total transformation. -/
def Admissible (T : LegalLedger k → LegalLedger k) : Prop := ∀ L, Extends L (T L)

def Fix (L : LegalLedger k) : Set P :=
  {p | ∀ T : LegalLedger k → LegalLedger k, Admissible T →
    (p ∈ Frozen L ↔ p ∈ Frozen (T L))}

private noncomputable def chosenWitness (A C : CertifiedNodes k) (p : P)
    (h : p ∈ A.nodes ∨ p ∈ C.nodes) : Proof := by
  classical
  exact if hp : p ∈ A.nodes then A.witness ⟨p, hp⟩
    else C.witness ⟨p, h.resolve_left hp⟩

private theorem chosen_acyclic (A C : CertifiedNodes k) :
    AcyclicEdge (fun q p => ∃ h : p ∈ A.nodes ∨ p ∈ C.nodes,
      q ∈ k.refs (chosenWitness A C p h)) := by
  classical
  let tag : P → P ⊕ P := fun p => if p ∈ A.nodes then Sum.inl p else Sum.inr p
  let r : (P ⊕ P) → (P ⊕ P) → Prop :=
    Sum.Lex (Relation.TransGen A.edge) (Relation.TransGen C.edge)
  let : Std.Irrefl (Relation.TransGen A.edge) := ⟨A.property.2.2.2⟩
  let : Std.Irrefl (Relation.TransGen C.edge) := ⟨C.property.2.2.2⟩
  have liftEdge : ∀ q p, (∃ h : p ∈ A.nodes ∨ p ∈ C.nodes,
      q ∈ k.refs (chosenWitness A C p h)) → r (tag q) (tag p) := by
    rintro q p ⟨h, href⟩
    by_cases hp : p ∈ A.nodes
    · have hrefA : q ∈ k.refs (A.witness ⟨p, hp⟩) := by
        simpa only [chosenWitness, dif_pos hp] using href
      have hq : q ∈ A.nodes := A.property.2.2.1 ⟨p, hp⟩ q hrefA
      simp only [tag, if_pos hp, if_pos hq]
      exact Sum.Lex.inl (Relation.TransGen.single ⟨hp, hrefA⟩)
    · have hrefC : q ∈ k.refs (C.witness ⟨p, h.resolve_left hp⟩) := by
        simpa only [chosenWitness, dif_neg hp] using href
      by_cases hq : q ∈ A.nodes
      · simp only [tag, if_neg hp, if_pos hq]
        exact Sum.Lex.sep q p
      · simp only [tag, if_neg hp, if_neg hq]
        exact Sum.Lex.inr (Relation.TransGen.single ⟨h.resolve_left hp, hrefC⟩)
  intro p hcycle
  have hc : Relation.TransGen r (tag p) (tag p) :=
    Relation.TransGen.lift tag liftEdge p p hcycle
  have hc' : r (tag p) (tag p) := by
    simpa only [Relation.transGen_eq_self] using hc
  exact irrefl (tag p) hc'

private noncomputable def appendCore (A C : CertifiedNodes k) : CertifiedNodes k := by
  classical
  refine ⟨⟨A.nodes ∪ C.nodes,
    fun p => chosenWitness A C p.val (Finset.mem_union.mp p.property)⟩,
    ?_, ?_, ?_, ?_⟩
  · intro p
    by_cases hp : p.val ∈ A.nodes
    · simp only [chosenWitness, dif_pos hp]
      exact A.property.1 ⟨p.val, hp⟩
    · simp only [chosenWitness, dif_neg hp]
      exact C.property.1 ⟨p.val, (Finset.mem_union.mp p.property).resolve_left hp⟩
  · intro p a ha
    by_cases hp : p.val ∈ A.nodes
    · simp only [chosenWitness, dif_pos hp] at ha
      exact A.property.2.1 ⟨p.val, hp⟩ a ha
    · simp only [chosenWitness, dif_neg hp] at ha
      exact C.property.2.1 ⟨p.val, (Finset.mem_union.mp p.property).resolve_left hp⟩ a ha
  · intro p q hq
    by_cases hp : p.val ∈ A.nodes
    · simp only [chosenWitness, dif_pos hp] at hq
      exact Finset.mem_union_left _ (A.property.2.2.1 ⟨p.val, hp⟩ q hq)
    · simp only [chosenWitness, dif_neg hp] at hq
      exact Finset.mem_union_right _
        (C.property.2.2.1 ⟨p.val, (Finset.mem_union.mp p.property).resolve_left hp⟩ q hq)
  · intro p hcycle
    apply chosen_acyclic A C p
    apply Relation.TransGen.mono ?_ p p hcycle
    rintro q p ⟨hp, hq⟩
    exact ⟨Finset.mem_union.mp hp, hq⟩

/-- Append the certificate, preserving old witnesses on every overlap. -/
noncomputable def appendCertificate (L : LegalLedger k) (C : CertifiedNodes k) :
    LegalLedger k :=
  ⟨⟨appendCore L.core C, L.frontier \ {p | p ∈ C.nodes}⟩, by
    classical
    rintro p ⟨hp, hC⟩ hmem
    rcases Finset.mem_union.mp hmem with hA | hC'
    · exact L.property p hp hA
    · exact hC hC'⟩

private theorem appendCertificate_extends (L : LegalLedger k) (C : CertifiedNodes k) :
    Extends L (appendCertificate L C) := by
  classical
  refine ⟨fun p hp => Finset.mem_union_left _ hp, ?_, ?_⟩
  · rintro q p ⟨hp, hq⟩
    refine ⟨Finset.mem_union_left _ hp, ?_⟩
    change q ∈ k.refs (chosenWitness L.core C p (Or.inl hp))
    simpa only [chosenWitness, dif_pos hp] using hq
  · intro p hp hp'
    change chosenWitness L.core C p (Finset.mem_union.mp hp') = L.core.witness ⟨p, hp⟩
    simp only [chosenWitness, dif_pos hp]

/-- A total map: use the identity on inputs already containing the proposition. -/
noncomputable def addWithCertificate (p : P) (C : Certificate k p)
    (L : LegalLedger k) : LegalLedger k := by
  classical
  exact if p ∈ Frozen L then L else appendCertificate L C.val

/-- The concrete certificate map retains every old node, edge and witness. -/
theorem addWithCertificate_admissible (p : P) (C : Certificate k p) :
    Admissible (addWithCertificate p C) := by
  classical
  intro L
  by_cases hp : p ∈ Frozen L
  · simp only [addWithCertificate, if_pos hp]
    exact ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩
  · simpa only [addWithCertificate, if_neg hp] using appendCertificate_extends L C.val

private theorem frozen_proved (L : LegalLedger k) {p : P} (hp : p ∈ Frozen L) :
    Proved k p :=
  ⟨L.core.witness ⟨p, hp⟩, L.core.property.1 ⟨p, hp⟩, L.core.property.2.1 ⟨p, hp⟩⟩

/-- Under the source laws, fixed membership is exactly frozen or unprovable membership. -/
theorem fixed_eq_frozen_union_unprovable (laws : SourceLaws k) (L : LegalLedger k) :
    Fix L = Frozen L ∪ {p | ¬ Proved k p} := by
  classical
  ext p
  constructor
  · intro hfix
    by_cases hp : p ∈ Frozen L
    · exact Or.inl hp
    · right
      intro hproved
      obtain ⟨C⟩ := laws.2.1 p hproved
      have hmem : p ∈ Frozen (addWithCertificate p C L) := by
        change p ∈ Frozen (if p ∈ Frozen L then L else appendCertificate L C.val)
        rw [if_neg hp]
        exact Finset.mem_union_right _ C.property
      exact hp ((hfix _ (addWithCertificate_admissible p C)).mpr hmem)
  · rintro (hf | hu) T hT
    · exact ⟨fun _ => (hT L).1 p hf, fun _ => hf⟩
    · exact ⟨fun h => (hu (frozen_proved L h)).elim,
        fun h => (hu (frozen_proved (T L) h)).elim⟩

end D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet

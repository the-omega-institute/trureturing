/- GID: D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=atom:bc98f9a0480352eec7d4271cad8a27cb6d68310623fd783b041767e79cb76792; result=D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.result; claim=D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.claim
   digest: Dependency emptiness varies between kernels with the same provable image. -/

import D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization

/-! A shared-carrier pair with lawful certificates and different accepted-proof fibers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.KernelRelativeDependencyEmptiness

open LegalLedgerFixedSet FiniteSupportPatternRealization
open DagSemantics.StrictDependencyCoordinate

/-- Acceptance together with permission for every axiom read by this proof. -/
def Qualified {P Proof Ax Model : Type*} (k : KernelData P Proof Ax Model)
    (π : Proof) (p : P) : Prop :=
  k.accept π p = true ∧ ∀ a ∈ k.axioms π, a ∈ k.permitted

/-- Every qualified proof has a reference or an axiom dependency. -/
def DependencyEmpty {P Proof Ax Model : Type*} (k : KernelData P Proof Ax Model)
    (p : P) : Prop :=
  ∀ π, Qualified k π p → k.refs π ≠ ∅ ∨ k.axioms π ≠ ∅

/-- All kernel data other than the acceptance function agree. -/
def SharedData {P Proof Ax Model : Type*} (k₁ k₂ : KernelData P Proof Ax Model) : Prop :=
  k₁.axioms = k₂.axioms ∧ k₁.refs = k₂.refs ∧ k₁.permitted = k₂.permitted ∧
    k₁.neg = k₂.neg ∧ k₁.models = k₂.models ∧ k₁.holds = k₂.holds

/-- The assertion that the shared data and provable image determine dependency emptiness. -/
def claim : Prop :=
  ∀ (P Proof Ax Model : Type) (k₁ k₂ : KernelData P Proof Ax Model),
    SharedData k₁ k₂ → SourceLaws k₁ → SourceLaws k₂ →
    (∃ M, k₁.models M k₁.permitted) →
    (∀ p, Proved k₁ p ↔ Proved k₂ p) →
    ∀ p, Proved k₁ p → (DependencyEmpty k₁ p ↔ DependencyEmpty k₂ p)

/-- Exactly the three proof symbols used by the two kernels. -/
inductive ProofSymbol where
  | alpha
  | beta
  | delta
  deriving DecidableEq

/-- In implication/falsity syntax, this is p or not p, namely not p implies not p. -/
def Q : Formula := .imp (Formula.neg (.atom 0)) (Formula.neg (.atom 0))

/-- The syntactically distinct tautology p implies p. -/
def P : Formula := .imp (.atom 0) (.atom 0)

/-- The Boolean parameter adds only the accepted pair (delta,P). -/
def kernel (extra : Bool) : KernelData Formula ProofSymbol Unit (Nat → Bool) :=
  (fun π p => match π with
    | .alpha => decide (p = Q)
    | .beta => decide (p = P)
    | .delta => extra && decide (p = P),
   fun _ => ∅,
   fun π => match π with
    | .beta => {Q}
    | _ => ∅,
   ∅, Formula.neg, fun _ _ => True, fun v p => p.eval v = true)

private theorem qualified_iff (extra : Bool) (π : ProofSymbol) (p : Formula) :
    Qualified (kernel extra) π p ↔
      match π with
      | .alpha => p = Q
      | .beta => p = P
      | .delta => extra = true ∧ p = P := by
  cases π <;> simp [Qualified, kernel, KernelData.accept, KernelData.axioms]

private theorem proved_iff (extra : Bool) (p : Formula) :
    Proved (kernel extra) p ↔ p = Q ∨ p = P := by
  constructor
  · rintro ⟨π, hπ⟩
    change Qualified (kernel extra) π p at hπ
    rw [qualified_iff] at hπ
    cases π with
    | alpha => exact Or.inl hπ
    | beta => exact Or.inr hπ
    | delta => exact Or.inr hπ.2
  · rintro (rfl | rfl)
    · exact ⟨.alpha, (qualified_iff extra .alpha Q).mpr rfl⟩
    · exact ⟨.beta, (qualified_iff extra .beta P).mpr rfl⟩

/-- The proof fibers are different even though their entire images agree. -/
private theorem qualified_fiber (extra : Bool) :
    {π | Qualified (kernel extra) π P} =
      if extra then ({.beta, .delta} : Set ProofSymbol) else {.beta} := by
  ext π
  cases extra <;> cases π <;> simp [qualified_iff, P, Q, Formula.neg]

private def rootCore (extra : Bool) : CertifiedNodes (kernel extra) := by
  refine ⟨⟨{Q}, fun _ => .alpha⟩, ?_, ?_, ?_, ?_⟩
  · intro p
    have hp : p.val = Q := Finset.mem_singleton.mp p.property
    simp [kernel, KernelData.accept, hp]
  · intro p a ha
    exact Finset.notMem_empty a ha
  · intro p q hq
    exact (Finset.notMem_empty q hq).elim
  · apply acyclic_of_strictCoordinate (coordinate := fun _ : Formula => (0 : Nat))
    rintro q p ⟨_, hq⟩
    exact (Finset.notMem_empty q hq).elim

private def pairCore (extra : Bool) : CertifiedNodes (kernel extra) := by
  let nodes : Finset Formula := {Q, P}
  let w : {p // p ∈ nodes} → ProofSymbol :=
    fun p => if p.val = Q then .alpha else .beta
  have cases_node : ∀ p ∈ nodes, p = Q ∨ p = P := by
    intro p hp
    simpa [nodes] using hp
  refine ⟨⟨nodes, w⟩, ?_, ?_, ?_, ?_⟩
  · intro p
    rcases cases_node p.val p.property with hp | hp
    · simp [w, hp, kernel, KernelData.accept]
    · simp [w, hp, kernel, KernelData.accept, P, Q, Formula.neg]
  · intro p a ha
    exact Finset.notMem_empty a ha
  · intro p q hq
    by_cases hp : p.val = Q
    · simp [w, hp, kernel, KernelData.refs] at hq
    · have hqQ : q = Q := by
        simpa [w, hp, kernel, KernelData.refs] using hq
      simp [nodes, hqQ]
  · apply acyclic_of_strictCoordinate
      (coordinate := fun p : Formula => if p = P then (1 : Nat) else 0)
    rintro q p ⟨hp, hq⟩
    by_cases hpQ : p = Q
    · simp [w, hpQ, kernel, KernelData.refs] at hq
    · have hpP : p = P := (cases_node p hp).resolve_left hpQ
      have hqQ : q = Q := by
        simpa [w, hpQ, kernel, KernelData.refs] using hq
      simp [hpP, hqQ, P, Q, Formula.neg]

private theorem sound (extra : Bool) (p : Formula) (hp : Proved (kernel extra) p)
    (v : Nat → Bool) : p.eval v = true := by
  rcases (proved_iff extra p).mp hp with rfl | rfl
  · cases hv : v 0 <;> simp [Q, Formula.neg, Formula.eval, hv]
  · cases hv : v 0 <;> simp [P, Formula.eval, hv]

private theorem source_laws (extra : Bool) : SourceLaws (kernel extra) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp v _
    exact sound extra p hp v
  · intro p hp
    rcases (proved_iff extra p).mp hp with rfl | rfl
    · exact ⟨⟨rootCore extra, Finset.mem_singleton_self Q⟩⟩
    · exact ⟨⟨pairCore extra, by simp [pairCore, CertifiedNodes.nodes]⟩⟩
  · rintro p ⟨hp, hn⟩
    have ht := sound extra p hp (fun _ => false)
    have hf := sound extra ((kernel extra).neg p) hn (fun _ => false)
    change (!(p.eval (fun _ => false)) || false) = true at hf
    simp [ht] at hf

private theorem emptiness_separates :
    DependencyEmpty (kernel false) P ∧ ¬ DependencyEmpty (kernel true) P := by
  constructor
  · intro π hπ
    have hm : π ∈ {ρ | Qualified (kernel false) ρ P} := hπ
    rw [qualified_fiber] at hm
    have he : π = .beta := hm
    subst π
    left
    simp [kernel, KernelData.refs]
  · intro h
    have hm : ProofSymbol.delta ∈ {ρ | Qualified (kernel true) ρ P} := by
      rw [qualified_fiber]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hd := h .delta hm
    simp [kernel, KernelData.refs, KernelData.axioms] at hd

/-- Two lawful kernels have equal provable images but different dependency-emptiness values. -/
theorem result : ¬ claim := by
  intro universal
  have shared : SharedData (kernel false) (kernel true) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have equal_image : ∀ p, Proved (kernel false) p ↔ Proved (kernel true) p :=
    fun p => (proved_iff false p).trans (proved_iff true p).symm
  have model : ∃ v, (kernel false).models v (kernel false).permitted :=
    ⟨fun _ => false, trivial⟩
  have provedP : Proved (kernel false) P := (proved_iff false P).mpr (Or.inr rfl)
  have forced := universal Formula ProofSymbol Unit (Nat → Bool)
    (kernel false) (kernel true) shared (source_laws false) (source_laws true)
    model equal_image P provedP
  exact emptiness_separates.2 (forced.mp emptiness_separates.1)

#print axioms result

end D5.S3.ConceptDynamics.DependencyTopology.KernelRelativeDependencyEmptiness

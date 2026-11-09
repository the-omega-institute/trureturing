import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S1.Dynamics.Shadowing.NorthSouthSelector

/-! Observe actual membership in the target neighborhood in the inverse compact
uniformity clause. The other three clauses and all source parameters are retained. -/

noncomputable section
open Set Filter Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing.PointwiseNorthSouth

namespace Reg.D5.S1.Dynamics.Shadowing.PointwiseNorthSouth
universe u

abbrev membershipSignature : Signature where
  Params := Σ X : Type u, Set X
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization membershipSignature.{u} :=
  realize membershipSignature (fun _ p x => x ∈ p.2) (fun e => nomatch e)

def rejected : Realization membershipSignature.{u} :=
  realize membershipSignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := membershipSignature.{u}
  Law A := ∀ {M : Type u} [MetricSpace M] [CompactSpace M] {f : M ≃ₜ M} {N S : M},
    Pointwise f N S →
    Stable f S ∧ Stable f.symm N ∧
    (∀ C : Set M, IsCompact C → N ∉ C → ∀ O ∈ 𝓝 S,
      ∃ T : ℕ, ∀ n ≥ T, (f ^ n) '' C ⊆ O) ∧
    (∀ C : Set M, IsCompact C → S ∉ C → ∀ O ∈ 𝓝 N,
      ∃ T : ℕ, ∀ n ≥ T, ∀ p ∈ (f.symm ^ n) '' C, A.readout () ⟨M, O⟩ p)

theorem actual_law : arena.{u}.Law actual := by
  simpa only [arena, actual, realize, Set.subset_def] using
    (@stability_and_compact_uniformity.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  have h := (hh NorthSouthSelector.twoDynamics).2.2.2
  have hSN : NorthSouthSelector.south ≠ (NorthSouthSelector.north : NorthSouthSelector.Two.{u}) := by
    intro he
    have := congrArg (fun p : NorthSouthSelector.Two => p.down.val) he
    norm_num [NorthSouthSelector.north, NorthSouthSelector.south] at this
  obtain ⟨T, hT⟩ := h {NorthSouthSelector.north} isCompact_singleton
    (by simpa only [mem_singleton_iff] using hSN) univ univ_mem
  exact hT T le_rfl _ ⟨NorthSouthSelector.north, mem_singleton _, rfl⟩

def familyRegistration : Registration arena.{u} (type_of% (@stability_and_compact_uniformity.{u})) where
  actual := actual
  bridge := by simp only [arena, actual, realize, Set.subset_def]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨NorthSouthSelector.Two.{u}, {NorthSouthSelector.north}⟩,
      NorthSouthSelector.north, NorthSouthSelector.south, ?_⟩
    simp [actual, realize, NorthSouthSelector.north, NorthSouthSelector.south]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stability_and_compact_uniformity.{u}) (Realization membershipSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.PointwiseNorthSouth.compactUniformity
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.PointwiseNorthSouth.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize membershipSignature.{u} (fun _ p x => x ∈ p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Shadowing.PointwiseNorthSouth

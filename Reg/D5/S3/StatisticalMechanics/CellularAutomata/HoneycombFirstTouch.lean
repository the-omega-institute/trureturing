import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
import Reg.Support.SingleDependentReadout
import Reg.Support.HoneycombTouchEvents

/-! Source registrations for HoneycombFirstTouch. -/

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination (Vertex honeycombGraph)
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch


set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [local instance] repositoryAdjacency

namespace DomainMembership

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Finset Vertex)

def actual : Realization signature :=
  realize signature (fun _ _ a => domain a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a K : ℕ} {v : Vertex},
    v ∈ R.readout () () a K ↔ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧ heightSum v < a ∧ g v < K

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm := (h (a := 1) (K := 1) (v := A 0 0)).mpr
    (mem_domain.mp (seed_mem (by decide) (by decide)))
  simp [rejected, realize] at hm

def family : Registration arena (type_of% @mem_domain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_domain, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro eq
    have h := seed_mem (a := 1) (K := 1) (by decide) (by decide)
    change domain 0 = domain 1 at eq
    have h' : A 0 0 ∈ domain 0 1 := by rw [eq]; exact h
    have hh := (mem_domain.mp h').2.2.1
    norm_num [heightSum, A] at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@mem_domain) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.DomainMembership.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.DomainMembership.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => domain a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DomainMembership

namespace DomainHeightMonotonicity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Finset Vertex)

def actual : Realization signature :=
  realize signature (fun _ _ a => domain a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => {A 0 0}) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m N K : ℕ}, m ≤ N → R.readout () () m K ⊆ domain N K

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm : A 0 0 ∈ domain 0 1 := (h (m := 0) (N := 0) (K := 1) (by decide))
    (Finset.mem_singleton_self _)
  have hh := (mem_domain.mp hm).2.2.1
  norm_num [heightSum, A] at hh

def family : Registration arena (type_of% @domain_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@domain_mono, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro eq
    have h := seed_mem (a := 1) (K := 1) (by decide) (by decide)
    change domain 0 = domain 1 at eq
    have h' : A 0 0 ∈ domain 0 1 := by rw [eq]; exact h
    have hh := (mem_domain.mp h').2.2.1
    norm_num [heightSum, A] at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@domain_mono) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.DomainHeightMonotonicity.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.DomainHeightMonotonicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => domain a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DomainHeightMonotonicity

namespace SeedMembership

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Finset Vertex)

def actual : Realization signature :=
  realize signature (fun _ _ a => domain a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a K : ℕ}, 0 < a → 0 < K → A 0 0 ∈ R.readout () () a K

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm := h (a := 1) (K := 1) (by decide) (by decide)
  simp [rejected, realize] at hm

def family : Registration arena (type_of% @seed_mem) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@seed_mem, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro eq
    have h := seed_mem (a := 1) (K := 1) (by decide) (by decide)
    change domain 0 = domain 1 at eq
    have h' : A 0 0 ∈ domain 0 1 := by rw [eq]; exact h
    have hh := (mem_domain.mp h').2.2.1
    norm_num [heightSum, A] at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@seed_mem) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.SeedMembership.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.SeedMembership.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => domain a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SeedMembership

namespace DomainCutMonotonicity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Finset Vertex)

def actual : Realization signature :=
  realize signature (fun _ _ a => domain a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a K K' : ℕ}, K ≤ K' → domain a K ⊆ R.readout () () a K'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm := (h (a := 1) (K := 1) (K' := 1) (by decide))
    (seed_mem (by decide) (by decide))
  simp [rejected, realize] at hm

def family : Registration arena (type_of% @domain_cut_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@domain_cut_mono, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro eq
    have h := seed_mem (a := 1) (K := 1) (by decide) (by decide)
    change domain 0 = domain 1 at eq
    have h' : A 0 0 ∈ domain 0 1 := by rw [eq]; exact h
    have hh := (mem_domain.mp h').2.2.1
    norm_num [heightSum, A] at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@domain_cut_mono) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.DomainCutMonotonicity.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.DomainCutMonotonicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => domain a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DomainCutMonotonicity

namespace NeighborsA

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (SimpleGraph Vertex) (fun _ => Vertex) (fun _ => Vertex → Prop)

def actual : Realization signature :=
  realize signature (fun _ G v => G.Adj v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : SimpleGraph Vertex}, NeighborLaws G →
    ∀ (x y : ℤ) (w : Vertex), R.readout () G (A x y) w ↔
      w = B x y ∨ w = B (x - 1) y ∨ w = B x (y - 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h repositoryNeighborLaws 0 0 (B 0 0)).mpr (Or.inl rfl)

def family : Registration arena (type_of% @neighbors_A) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neighbors_A, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨honeycombGraph, A 0 0, A 2 0, ?_⟩
    intro eq
    have hadj := (neighbors_A repositoryNeighborLaws 0 0 (B 0 0)).mpr (Or.inl rfl)
    change honeycombGraph.Adj (A 0 0) = honeycombGraph.Adj (A 2 0) at eq
    have hbad : honeycombGraph.Adj (A 2 0) (B 0 0) := by rw [← eq]; exact hadj
    rcases (neighbors_A repositoryNeighborLaws 2 0 (B 0 0)).mp hbad with h | h | h <;>
      simp [B] at h

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@neighbors_A) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.NeighborsA.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.NeighborsA.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ G v => G.Adj v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NeighborsA

namespace NeighborsB

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (SimpleGraph Vertex) (fun _ => Vertex) (fun _ => Vertex → Prop)

def actual : Realization signature :=
  realize signature (fun _ G v => G.Adj v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : SimpleGraph Vertex}, NeighborLaws G →
    ∀ (x y : ℤ) (w : Vertex), R.readout () G (B x y) w ↔
      w = A x y ∨ w = A (x + 1) y ∨ w = A x (y + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h repositoryNeighborLaws 0 0 (A 0 0)).mpr (Or.inl rfl)

def family : Registration arena (type_of% @neighbors_B) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neighbors_B, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨honeycombGraph, A 0 0, A 2 0, ?_⟩
    intro eq
    have hadj := (neighbors_A repositoryNeighborLaws 0 0 (B 0 0)).mpr (Or.inl rfl)
    change honeycombGraph.Adj (A 0 0) = honeycombGraph.Adj (A 2 0) at eq
    have hbad : honeycombGraph.Adj (A 2 0) (B 0 0) := by rw [← eq]; exact hadj
    rcases (neighbors_A repositoryNeighborLaws 2 0 (B 0 0)).mp hbad with h | h | h <;>
      simp [B] at h

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@neighbors_B) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.NeighborsB.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.NeighborsB.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ G v => G.Adj v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NeighborsB

namespace EarliestBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Vertex) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ v => earliest v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : SimpleGraph Vertex} [DecidableRel G.Adj],
    NeighborLaws G → ∀ {D : Finset Vertex} {t μ : ℕ} {v : Vertex},
      Touch G D (A 0 0) t v μ → R.readout () () v ≤ t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have touch : Touch honeycombGraph {A 0 0} (A 0 0) 0 (A 0 0) 1 :=
    touch_zero_iff.mpr ⟨Finset.mem_singleton_self _, rfl, rfl⟩
  have bad : 1 ≤ 0 := h repositoryNeighborLaws touch
  omega

def family : Registration arena (type_of% @earliest_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@earliest_bound, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), A 0 0, B 0 0, ?_⟩
    change earliest (A 0 0) ≠ earliest (B 0 0)
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@earliest_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.EarliestBound.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.EarliestBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => earliest v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EarliestBound

abbrev ClippedParams :=
  Σ G : SimpleGraph Vertex, Σ _ : DecidableRel G.Adj, Σ _ : ℕ, ℕ
namespace ClippedTouch

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ClippedParams (fun _ => ℕ) (fun _ => Vertex → Prop)

def actual : Realization signature :=
  realize signature (fun _ p t => @Born Vertex _ p.1 p.2.1 (domain p.2.2.1 p.2.2.2) (A 0 0) t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : SimpleGraph Vertex} [i : DecidableRel G.Adj], NeighborLaws G →
    ∀ {b m N K : ℕ}, 0 < m → m < N → 1 ≤ K → K ≤ 2 * m →
    2 ^ b ∣ m → EarliestBirths G (domain N K) → ∀ t : ℕ,
    (∀ v ∈ domain m K, t < horizon (2 ^ b) v → ∀ μ, 0 < μ →
      (Touch G (domain m K) (A 0 0) t v μ ↔ Touch G (domain N K) (A 0 0) t v μ)) ∧
    (∀ v ∈ domain N K, v ∉ domain m K → t < horizon (2 ^ b) v →
      ¬ R.readout () ⟨G, i, N, K⟩ t v)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have first : EarliestBirths honeycombGraph (domain 2 2) := by
    intro v hv hparity
    exact (earliestBirthIff_of_neighborLaws repositoryNeighborLaws 2 2
      (by decide) (by decide) v hv).mpr hparity
  exact (h repositoryNeighborLaws (b := 0) (m := 1) (N := 2) (K := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) first 0).2
    (A 0 1) (by decide) (by decide) (by decide) trivial

def family : Registration arena (type_of% @clipped_first_touch) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clipped_first_touch, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨⟨honeycombGraph, repositoryAdjacency, 2, 2⟩, 0, 1, ?_⟩
    change Born honeycombGraph (domain 2 2) (A 0 0) 0 ≠
      Born honeycombGraph (domain 2 2) (A 0 0) 1
    intro eq
    have seed : Born honeycombGraph (domain 2 2) (A 0 0) 0 (A 0 0) :=
      touch_zero_iff.mpr ⟨by decide, rfl, rfl⟩
    have later : Born honeycombGraph (domain 2 2) (A 0 0) 1 (A 0 0) := by
      rw [← eq]
      exact seed
    have impossible := (touch_unique seed later).1
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@clipped_first_touch) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.ClippedTouch.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.ClippedTouch.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => @Born Vertex _ p.1 p.2.1 (domain p.2.2.1 p.2.2.2) (A 0 0) t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ClippedTouch



end

end Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.AlmostDisjoint.ConvergentBranches

namespace Reg.D5.S3.Topology.AlmostDisjoint.ConvergentBranches

open Set Filter
open scoped _root_.Topology

universe u v
open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open _root_.D5.S3.ConceptDynamics.InformationEscape

/-- The complete branch statement with the actual limit function as observation state. -/
def branchCertificate (n : ℕ) (L : Branch → unitInterval) : Prop :=
  (∀ x : Branch, (wordValue (wordPrefix x n) : ℝ) =
    ∑ i ∈ Finset.range (n + 1),
      (finTwoEquiv.symm (x i).1 : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹) ∧
  (∀ x : Branch, (branchSet x).Infinite) ∧
  (∀ x y : Branch, x ≠ y → (branchSet x ∩ branchSet y).Finite) ∧
  (∀ x : Branch, ConvergesOn wordValue (branchSet x) (L x)) ∧
  Continuous L ∧ Function.Surjective L ∧
  (∀ r : unitInterval, Cardinal.mk {x : Branch // L x = r} = Cardinal.continuum)

def branchSignature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => Branch → unitInterval
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def branchActual : DependentFamily.Realization branchSignature :=
  DependentFamily.realize branchSignature (fun _ n L => branchCertificate n L)
    (fun a => Empty.elim a)

def branchArena : DependentFamily.Arena where
  signature := branchSignature
  Law := fun R => ∀ n, R.readout () n limitValue

abbrev branchSourceScope := type_of% (@branch_system)

theorem branch_source_bridge : branchSourceScope ↔ branchArena.Law branchActual := Iff.rfl

theorem branch_actual_positive : branchArena.Law branchActual :=
  branch_source_bridge.mp branch_system

def branchRejected : DependentFamily.Realization branchSignature :=
  DependentFamily.realize branchSignature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem branch_rejected_law : ¬ branchArena.Law branchRejected := fun h => h (0 : ℕ)

theorem constant_limit_invalid : ¬ branchCertificate 0 (fun _ => 0) := by
  intro h
  obtain ⟨x, hx⟩ := h.2.2.2.2.2.1 1
  norm_num at hx

def branchFamilyRegistration : DependentFamily.Registration branchArena branchSourceScope where
  actual := branchActual
  bridge := branch_source_bridge
  variation := ⟨branch_actual_positive, branchRejected, branch_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨branchRejected, ?_, rfl, branch_rejected_law⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    refine ⟨(0 : ℕ), limitValue, (fun _ => 0), ?_⟩
    intro h
    change branchCertificate 0 limitValue = branchCertificate 0 (fun _ => 0) at h
    exact constant_limit_invalid (h ▸ branch_actual_positive (0 : ℕ))

/-- Full source telescope, including both carrier universes and the topology. -/
structure RangeParams where
  Carrier : Type u
  Target : Type v
  topology : TopologicalSpace Target
  sequence : ℕ → Carrier
  value : Carrier → Target
  point : Target
  tends : letI := topology; Tendsto (value ∘ sequence) atTop (𝓝 point)

def rangeSignature : DependentFamily.Signature where
  Params := RangeParams.{u, v}
  State := fun p => Set p.Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def rangeCertificate (p : RangeParams.{u, v}) (A : Set p.Carrier) : Prop :=
  letI := p.topology
  ConvergesOn p.value A p.point

def rangeActual : DependentFamily.Realization rangeSignature.{u, v} :=
  DependentFamily.realize rangeSignature.{u, v} (fun _ p A => rangeCertificate.{u, v} p A)
    (fun a => Empty.elim a)

def rangeArena : DependentFamily.Arena where
  signature := rangeSignature.{u, v}
  Law := fun R => ∀ p, R.readout () p (range p.sequence)

abbrev rangeSourceScope := type_of% (@convergesOn_range.{u, v})

theorem range_source_bridge : rangeSourceScope.{u, v} ↔ rangeArena.{u, v}.Law rangeActual.{u, v} := by
  constructor
  · intro h p
    letI := p.topology
    exact h p.sequence p.value p.point p.tends
  · intro h α Y t f u r ht
    exact h ⟨α, Y, t, f, u, r, ht⟩

theorem range_actual_positive : rangeArena.{u, v}.Law rangeActual.{u, v} :=
  range_source_bridge.{u, v}.mp (@convergesOn_range.{u, v})

def rangeRejected : DependentFamily.Realization rangeSignature.{u, v} :=
  DependentFamily.realize rangeSignature.{u, v} (fun _ _ _ => False) (fun a => Empty.elim a)

def witnessParams : RangeParams.{u, v} where
  Carrier := ULift.{u} ℕ
  Target := ULift.{v} Bool
  topology := inferInstance
  sequence := fun _ => ⟨0⟩
  value := fun n => if n.down = 0 then ⟨false⟩ else ⟨true⟩
  point := ⟨false⟩
  tends := by
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (⟨false⟩ : ULift.{v} Bool)) atTop (𝓝 ⟨false⟩))

theorem range_rejected_law : ¬ rangeArena.{u, v}.Law rangeRejected.{u, v} := fun h => h witnessParams.{u, v}

theorem empty_range_valid : rangeCertificate.{u, v} witnessParams.{u, v} ∅ := by
  dsimp [rangeCertificate]
  intro V hV
  exact finite_empty.subset sdiff_subset

theorem whole_range_invalid : ¬ rangeCertificate.{u, v} witnessParams.{u, v} univ := by
  dsimp [rangeCertificate]
  intro h
  have hV : ({⟨false⟩} : Set (ULift.{v} Bool)) ∈ 𝓝 ⟨false⟩ := by
    exact IsOpen.mem_nhds (isOpen_discrete _) rfl
  have hf := h {⟨false⟩} hV
  have hi : (univ \ {⟨0⟩} : Set (ULift.{u} ℕ)).Infinite :=
    (infinite_univ : (univ : Set (ULift.{u} ℕ)).Infinite).sdiff (finite_singleton (⟨0⟩ : ULift.{u} ℕ))
  apply hi (hf.subset ?_)
  intro n hn
  have hn0 : n.down ≠ 0 := by
    intro hz
    exact hn.2 (mem_singleton_iff.mpr (ULift.ext hz))
  refine ⟨mem_univ n, ?_⟩
  change (if n.down = 0 then (⟨false⟩ : ULift.{v} Bool) else ⟨true⟩) ≠ ⟨false⟩
  rw [if_neg hn0]
  intro he
  cases congrArg (fun b : ULift.{v} Bool => b.down) he

def rangeFamilyRegistration : DependentFamily.Registration rangeArena.{u, v} rangeSourceScope.{u, v} where
  actual := rangeActual.{u, v}
  bridge := range_source_bridge.{u, v}
  variation := ⟨range_actual_positive.{u, v}, rangeRejected.{u, v}, range_rejected_law.{u, v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rangeRejected.{u, v}, ?_, rfl, range_rejected_law.{u, v}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    refine ⟨witnessParams.{u, v}, (∅ : Set (ULift.{u} ℕ)),
      (univ : Set (ULift.{u} ℕ)), ?_⟩
    intro h
    change rangeCertificate.{u, v} witnessParams.{u, v} ∅ = rangeCertificate.{u, v} witnessParams.{u, v} univ at h
    exact whole_range_invalid.{u, v} (h ▸ empty_range_valid.{u, v})

/-- Source occurrence reconstruction is not asserted by either audit attempt. -/
noncomputable def branchRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@branch_system) (DependentFamily.Realization branchSignature) Type Unit where
  unitName := `D5.S3.Topology.AlmostDisjoint.ConvergentBranches.branch_system.__information_unit
  realizationName := `Reg.D5.S3.Topology.AlmostDisjoint.ConvergentBranches.branchFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨branchArena⟩
  objectArena := .source ⟨branchArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source branchArena ⟨branchFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize branchSignature
    (fun _ n L => branchCertificate n L) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (Branch → unitInterval)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def rangeRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@convergesOn_range.{u, v}) (DependentFamily.Realization rangeSignature.{u, v})
      (Type (u + 1)) Unit where
  unitName := `D5.S3.Topology.AlmostDisjoint.ConvergentBranches.convergesOn_range.__information_unit
  realizationName := `Reg.D5.S3.Topology.AlmostDisjoint.ConvergentBranches.rangeFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rangeArena.{u, v}⟩
  objectArena := .source ⟨rangeArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rangeArena.{u, v} ⟨rangeFamilyRegistration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize rangeSignature.{u, v}
    (fun _ p A => rangeCertificate.{u, v} p A) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (Type u)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.AlmostDisjoint.ConvergentBranches

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic

/-! Source-bound whole-family observations with explicit open residuals. -/

set_option autoImplicit false
open Matrix Finset
open scoped Classical
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
attribute [local instance] _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.subgroupFintype

abbrev integerSignature : Signature where
  Params := Unit
  State _ := Multiset ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def integerActual : Realization integerSignature :=
  realize integerSignature (fun _ _ s => IntegralSpectrum s) (fun e => nomatch e)
def rejectedTrue : Realization integerSignature :=
  realize integerSignature (fun _ _ _ => True) (fun e => nomatch e)
def rejectedFalse : Realization integerSignature :=
  realize integerSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem integerDependence : ObservationalDependence integerSignature integerActual := by
  intro i
  refine ⟨(),{0},{(1/2 : ℝ)},?_⟩
  intro he
  have h0 : IntegralSpectrum ({0} : Multiset ℝ) := by
    intro x hx
    simp only [Multiset.mem_singleton] at hx
    exact ⟨0,by simpa using hx⟩
  change IntegralSpectrum ({0} : Multiset ℝ) = IntegralSpectrum ({(1/2 : ℝ)} : Multiset ℝ) at he
  have hbad : IntegralSpectrum ({(1/2 : ℝ)} : Multiset ℝ) := he ▸ h0
  obtain ⟨z,hz⟩ := hbad (1/2) (by simp)
  have hh : (2 : ℝ)*(z : ℝ) = 1 := by linarith
  have hh' : (2 : ℤ)*z = 1 := by exact_mod_cast hh
  omega
private theorem S3_nonabelian : ∃ a b : Equiv.Perm (Fin 3), a*b ≠ b*a := by
  refine ⟨Equiv.swap 0 1,Equiv.swap 1 2,?_⟩
  intro he
  have hh := congrArg (fun p => p 0) he
  norm_num [Equiv.Perm.mul_apply,Equiv.swap_apply_def] at hh

namespace adjacency_not_integralAudit
abbrev arena : Arena where
  signature := integerSignature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (hG : 1 < Fintype.card G), ¬ R.readout () () (graphSpectrum (sgbGraph G) .adjacency)
private theorem rejected_law : ¬ arena.Law rejectedTrue := by
  intro h
  have hh := @h (Multiplicative (ZMod 2)) inferInstance inferInstance (by norm_num)
  exact hh True.intro
def family : Registration arena (type_of% (@adjacency_not_integral)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨@adjacency_not_integral,rejectedTrue,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedTrue,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := integerDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjacency_not_integral) (Realization integerSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.adjacency_not_integral.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.adjacency_not_integralAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integerSignature integerActual.readout integerActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end adjacency_not_integralAudit

namespace other_spectra_integralAudit
abbrev arena : Arena where
  signature := integerSignature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (kind : MatrixKind) (hk : kind ≠ .adjacency), R.readout () () (graphSpectrum (sgbGraph G) kind)
private theorem rejected_law : ¬ arena.Law rejectedFalse := by
  intro h
  have hh := @h PUnit inferInstance inferInstance .laplacian (by intro he; cases he)
  exact hh
def family : Registration arena (type_of% (@other_spectra_integral)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨@other_spectra_integral,rejectedFalse,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedFalse,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := integerDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@other_spectra_integral) (Realization integerSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.other_spectra_integral.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.other_spectra_integralAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integerSignature integerActual.readout integerActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end other_spectra_integralAudit

namespace resultAudit
abbrev arena : Arena where
  signature := integerSignature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (hn : ∃ a b : G, a*b ≠ b*a), ¬ R.readout () () (graphSpectrum (sgbGraph G) .adjacency) ∧
    IntegralSpectrum (graphSpectrum (sgbGraph G) .laplacian) ∧
    IntegralSpectrum (graphSpectrum (sgbGraph G) .signless) ∧
    IntegralSpectrum (graphSpectrum (sgbGraph G) .commonNeighbour) ∧
    graphEnergy (sgbGraph G) .adjacency < (Fintype.card (Vertex G) : ℝ) ∧
    graphEnergy (sgbGraph G) .adjacency ≤ 2*((Fintype.card (Vertex G) : ℝ)-1) ∧
    graphEnergy (sgbGraph G) .laplacian ≤ 2*((Fintype.card (Vertex G) : ℝ)-1) ∧
    graphEnergy (sgbGraph G) .signless ≤ 2*((Fintype.card (Vertex G) : ℝ)-1) ∧
    graphEnergy (sgbGraph G) .commonNeighbour ≤
      2*((Fintype.card (Vertex G) : ℝ)-1)*((Fintype.card (Vertex G) : ℝ)-2) ∧
    graphEnergy (sgbGraph G) .adjacency ≤ graphEnergy (sgbGraph G) .laplacian
private theorem rejected_law : ¬ arena.Law rejectedTrue := by
  intro h
  have hh := @h (Equiv.Perm (Fin 3)) inferInstance inferInstance S3_nonabelian
  exact hh.1 True.intro
def family : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.result)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.result,rejectedTrue,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedTrue,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := integerDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.result) (Realization integerSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.resultAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integerSignature integerActual.readout integerActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end resultAudit

namespace sgb_energyAudit
abbrev signature : Signature where
  Params := Σ G : Type, Group G × Fintype G
  State _ := MatrixKind
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p kind => by
    letI := p.2.1
    letI := p.2.2
    exact graphEnergy (sgbGraph p.1) kind) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], R.readout () ⟨G,inferInstance,inferInstance⟩ .adjacency = 2 * ∑ H : Subgroup G, Real.sqrt (pairCount H) ∧
    graphEnergy (sgbGraph G) .commonNeighbour =
      2 * ((Fintype.card G : ℝ)^2 - (positiveFibers (G := G)).card) ∧
    graphEnergy (sgbGraph G) .laplacian =
      Fintype.card (Subgroup G) * averageDegree (sgbGraph G) +
      ((Fintype.card G : ℝ)^2 - (positiveFibers (G := G)).card) * |1-averageDegree (sgbGraph G)| +
      (Fintype.card G : ℝ)^2 + (positiveFibers (G := G)).card -
      (positiveFibers (G := G)).card * averageDegree (sgbGraph G) ∧
    graphEnergy (sgbGraph G) .signless = graphEnergy (sgbGraph G) .laplacian
private theorem PUnit_count (H : Subgroup PUnit) : pairCount H = 1 := by
  have hh : H = ⊥ := Subsingleton.elim _ _
  rw [hh,pairCount_bot]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (@h PUnit inferInstance inferInstance).1
  norm_num [rejected,realize,PUnit_count] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨PUnit,inferInstance,inferInstance⟩,.adjacency,.commonNeighbour,?_⟩
  intro he
  change graphEnergy (sgbGraph PUnit) .adjacency = graphEnergy (sgbGraph PUnit) .commonNeighbour at he
  rw [(sgb_energy (G := PUnit)).1,(sgb_energy (G := PUnit)).2.1] at he
  have ht : (positiveFibers (G := PUnit)).card = 1 := by simp [positiveFibers,PUnit_count]
  norm_num [PUnit_count,ht] at he

def family : Registration arena (type_of% (@sgb_energy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sgb_energy,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sgb_energy) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.sgb_energy.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds.sgb_energyAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sgb_energyAudit

end Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds

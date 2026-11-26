import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150
import Reg.Support.SingleDependentReadout

/-! Native dependent observations for Bojić's Rule 150 local semisimple parts. -/

noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150
open LeanInformationAudit Polynomial

private abbrev LocalParameters := Σ _ : ℕ, Σ _ : ℕ, P

private theorem order_witness :
    ∃ f ∈ factors 7, orderOf (semisimplePart 3 0 f) ≠ 1 := by
  classical
  by_contra! h
  have hseven : (nontrivialFactors 7).lcm (fun f => orderOf (semisimplePart 3 0 f)) = 7 :=
    semisimpleOrder_lcm 3 0 (by decide)
  have hdiv : (nontrivialFactors 7).lcm (fun f => orderOf (semisimplePart 3 0 f)) ∣ 1 := by
    apply Finset.lcm_dvd_iff.mpr
    intro f hf
    have hf' : f ∈ factors 7 := Finset.mem_of_mem_erase hf
    rw [h f hf']
  rw [hseven] at hdiv
  exact (by decide : ¬ 7 ∣ (1 : ℕ)) hdiv

namespace LocalLCM

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
    (fun _ => P → ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p F => (nontrivialFactors (2 ^ p.1 - 1)).lcm F) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ), ¬ 3 ∣ 2 ^ k - 1 →
    R.readout () ⟨k, m⟩ (fun f => orderOf (semisimplePart k m f)) = 2 ^ k - 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : (0 : ℕ) = 1 := h 1 0 (by decide)
  exact Nat.zero_ne_one hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3, 0⟩, (fun f => orderOf (semisimplePart 3 0 f)), (fun _ => 1), ?_⟩
  change (nontrivialFactors 7).lcm _ ≠ (nontrivialFactors 7).lcm (fun _ => 1)
  have hactual : (nontrivialFactors 7).lcm (fun f => orderOf (semisimplePart 3 0 f)) = 7 :=
    semisimpleOrder_lcm 3 0 (by decide)
  have hvar : (nontrivialFactors 7).lcm (fun _ => 1) = 1 := by
    apply Nat.dvd_antisymm
    · exact Finset.lcm_dvd_iff.mpr (fun _ _ => dvd_rfl)
    · exact one_dvd _
  rw [hactual, hvar]
  exact (by decide : (7 : ℕ) ≠ 1)

def evidence : Registration arena (type_of% @semisimpleOrder_lcm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@semisimpleOrder_lcm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

end LocalLCM

namespace LocalLCM

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@semisimpleOrder_lcm)
    (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150.LocalLCM.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150.LocalLCM.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LocalLCM

namespace LocalOrder

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature LocalParameters
    (fun p => Local p.2.2 p.2.1) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ s => orderOf s) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ), ¬ 3 ∣ 2 ^ k - 1 → ∀ {f : P},
    f ∈ factors (2 ^ k - 1) →
      R.readout () ⟨k, m, f⟩ (semisimplePart k m f) =
        orderOf (project f (multiplier (2 ^ m * (2 ^ k - 1))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, hf, horder⟩ := order_witness
  have hactual := @semisimplePart_order 3 0 (by decide) f hf
  have hbad := @h 3 0 (by decide) f hf
  change (1 : ℕ) = _ at hbad
  exact horder (hactual.trans hbad.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨f, _, horder⟩ := order_witness
  refine ⟨⟨3, 0, f⟩, semisimplePart 3 0 f, 1, ?_⟩
  change orderOf (semisimplePart 3 0 f) ≠ orderOf (1 : Local f 0)
  rwa [orderOf_one]

def evidence : Registration arena (type_of% @semisimplePart_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@semisimplePart_order, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

end LocalOrder

namespace LocalOrder

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@semisimplePart_order)
    (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150.LocalOrder.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150.LocalOrder.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LocalOrder

namespace LocalSpec

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature LocalParameters
    (fun p => Local p.2.2 p.2.1) (fun p => Local p.2.2 p.2.1 → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ g => IsSemisimplePart g) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ), ¬ 3 ∣ 2 ^ k - 1 → ∀ {f : P},
    f ∈ factors (2 ^ k - 1) →
      R.readout () ⟨k, m, f⟩ (localMultiplier (2 ^ m * (2 ^ k - 1)) f m)
          (semisimplePart k m f) ∧
        ∀ s, IsSemisimplePart (f := f) (m := m)
          (localMultiplier (2 ^ m * (2 ^ k - 1)) f m) s → s = semisimplePart k m f

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, hf, _⟩ := order_witness
  exact (@h 3 0 (by decide) f hf).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨f, hf, horder⟩ := order_witness
  let g : Local f 0 := localMultiplier 7 f 0
  let s : Local f 0 := semisimplePart 3 0 f
  have hs : IsSemisimplePart (f := f) (m := 0) g s :=
    (@semisimplePart_spec 3 0 (by decide) f hf).1
  have hne : s ≠ 1 := by
    intro h
    exact horder (by simp [← show s = semisimplePart 3 0 f from rfl, h])
  let : Nontrivial (Local f 0) := ⟨⟨s, 1, hne⟩⟩
  refine ⟨⟨3, 0, f⟩, g, 0, ?_⟩
  change IsSemisimplePart (f := f) (m := 0) g ≠ IsSemisimplePart (f := f) (m := 0) 0
  intro heq
  have hzero : IsSemisimplePart (f := f) (m := 0) 0 s := congrFun heq s ▸ hs
  obtain ⟨hu, _, ν, _, hnil, hg⟩ := hzero
  exact not_isUnit_zero (hg ▸ hu.mul hnil.isUnit_one_add)

def evidence : Registration arena (type_of% @semisimplePart_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@semisimplePart_spec, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

end LocalSpec

namespace LocalSpec

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@semisimplePart_spec)
    (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150.LocalSpec.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150.LocalSpec.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LocalSpec

end Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150

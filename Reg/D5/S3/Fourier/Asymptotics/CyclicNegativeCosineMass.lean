import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass

/-! Dependence of the limiting negative-cosine mass on the deficit parameter. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass

open Filter Finset
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 3 * x / 8) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lam : ℝ), 0 ≤ lam →
    ∀ (v : (k : ℕ) → ZMod k.succ → ℝ),
    (∀ᶠ k in atTop,
      v k ∈ feasible k.succ (1 - lam / (k.succ : ℝ) ^ 2) ∧
        IsMinOn energy (feasible k.succ (1 - lam / (k.succ : ℝ) ^ 2)) (v k)) →
    let limitValue := fun x : ℝ => R.readout () () x
    let readout (k : ℕ) (i : ZMod k.succ) := Real.cos (2 * Real.pi * (i.val : ℝ) / k.succ)
    let negative (k : ℕ) := (univ : Finset (ZMod k.succ)).filter (fun i => readout k i < 0)
    Tendsto (fun k : ℕ => (k.succ : ℝ) ^ 2 * ∑ i ∈ negative k, v k i)
      atTop (𝓝 (limitValue lam)) ∧
    Tendsto (fun k : ℕ => ∑ i ∈ negative k,
      (k.succ : ℝ) ^ 2 * (1 + readout k i) * v k i) atTop (𝓝 0)

private theorem exists_minimum_at_one (k : ℕ) :
    ∃ v ∈ feasible k.succ 1, IsMinOn energy (feasible k.succ 1) v := by
  have hq : 2 * latticeSupportRadius 1 (0 / (8 * Real.pi ^ 2)) < k.succ := by
    simp [latticeSupportRadius]
  obtain ⟨_, _, _, _, _, v, hv, hm, _, _, _⟩ :=
    cyclic_to_lattice_comparison k.succ 1 (by decide) 0 hq (by norm_num) (by norm_num)
  exact ⟨v, by simpa using hv, by simpa using hm⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let v (k : ℕ) := Classical.choose (exists_minimum_at_one k)
  have hv : ∀ᶠ k : ℕ in atTop,
      v k ∈ feasible k.succ (1 - 0 / (k.succ : ℝ) ^ 2) ∧
        IsMinOn energy (feasible k.succ (1 - 0 / (k.succ : ℝ) ^ 2)) (v k) :=
    Eventually.of_forall fun k => by simpa using Classical.choose_spec (exists_minimum_at_one k)
  have h := tendsto_nhds_unique (cyclic_negative_cosine_mass_limit 0 le_rfl v hv).1
    (law 0 le_rfl v hv).1
  change (3 * 0 / 8 : ℝ) = 1 at h
  norm_num at h

def evidence : Registration arena (type_of% @cyclic_negative_cosine_mass_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_negative_cosine_mass_limit, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_negative_cosine_mass_limit) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass

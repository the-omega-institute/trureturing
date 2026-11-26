import D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap

open _root_.D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open _root_.D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap.RTOverlap

private noncomputable def deterministicSingleton : LocalColumns (Fin 1) (Fin 1) (Fin 1) where
  entry := fun _ _ _ => 1
  gram := by intro a b; simp [Subsingleton.elim a b]

private noncomputable def singletonExperiment : CapExperiment :=
  ⟨1,1,1,1,fun _ => 1,deterministicSingleton,deterministicSingleton⟩

private theorem singleton_measured (n : ℕ) :
    measuredCap n singletonExperiment = 1/((n:ℝ)+1) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have h : (↑n + 1 : ℝ)⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_one (by linarith)).2 (by linarith)
  change (∑ i : Fin 1, min (1/((n:ℝ)+1))
    ((lnorm (bornVector deterministicSingleton deterministicSingleton
    (fun _ => (Real.sqrt 1 : ℂ)) i i))^2)) = _
  simp [lnorm,lsquare,bornVector,deterministicSingleton, Complex.sq_norm, h]

private theorem constant_zero_invalid : ¬ UniformCapLaw 0 (fun _ => 0) := by
  intro h
  obtain ⟨A,hA⟩ := (h 1 (fun _ => 1) (by simp) (by simp)).2
  norm_num [_root_.D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap.RTCriticalOverlap.spectralScore] at hA

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => CapExperiment → ℝ)

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => measuredCap n) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, let observed := R.readout () () n; UniformCapLaw n observed

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact constant_zero_invalid (h 0)

private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 1 := by
  intro h
  have he := congrFun h singletonExperiment
  change measuredCap 0 singletonExperiment = measuredCap 1 singletonExperiment at he
  rw [singleton_measured, singleton_measured] at he
  norm_num at he

noncomputable def family : Registration arena (type_of% @uniform_matched_overlap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_matched_overlap,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(),0,1,actual_dependence⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@uniform_matched_overlap) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap.uniform_matched_overlap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap.family
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
    owner := `D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap

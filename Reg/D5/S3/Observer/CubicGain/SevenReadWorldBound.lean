import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.SevenReadWorldBound
import Reg.Support.SingleDependentReadout

/-! The complete original world family with both literal sixth actions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.SevenReadWorldBound
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.SevenReadWorldBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Bool × OriginalWorld) (fun _ => Fin 7 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s i => sevenRead s.1 s.2 i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ![0,0,0,1,0,0,0]) (fun e => nomatch e)

def fiber (R : Realization signature) (e : Bool) (b A C z Y p v : ℝ) : Set OriginalWorld :=
  {W | FullWorldMeanSpan.FullWorld W ∧ W.2.1=b ∧
    ∀ i : Fin 7, R.readout () () (e,W) i = (![0,A,C,z,Y,p,v] : Fin 7 → ℝ) i}

abbrev arenaBound : Arena where
  signature := signature
  Law R := ∀ (e : Bool) (b A C z Y p v : ℝ), 0 < b → z ≠ A →
    (fiber R e b A C z Y p v).Finite ∧ (fiber R e b A C z Y p v).ncard ≤ 3

abbrev arenaRoots : Arena where
  signature := signature
  Law R := ∀ (e : Bool) (b A C z Y p v : ℝ), 0 < b → z ≠ A →
    ∀ S : Finset OriginalWorld, (∀ W ∈ S, W ∈ fiber R e b A C z Y p v) →
      S.val.map (fun W => W.2.2.1) ≤ (driftPolynomial e b A C z Y p v).roots

private def probeWorld (d : ℝ) : OriginalWorld := (1/2,1,d,![1,0,0,0])

private theorem rejected_mem (d : ℝ) :
    probeWorld d ∈ fiber rejected false 1 0 0 1 0 0 0 := by
  refine ⟨⟨by norm_num [probeWorld],by norm_num [probeWorld],
    by norm_num [probeWorld],?_⟩,rfl,?_⟩
  · norm_num [originalPolynomial,probeWorld,Polynomial.ofFn_eq_sum_monomial,
      Fin.sum_univ_four]
  · intro i
    fin_cases i <;> norm_num [rejected,realize]

private theorem rejected_bound : ¬ arenaBound.Law rejected := by
  classical
  intro h
  obtain ⟨hfin,hbound⟩ := h false 1 0 0 1 0 0 0 (by norm_num) (by norm_num)
  let S : Finset OriginalWorld := {probeWorld 0,probeWorld 1,probeWorld 2,probeWorld 3}
  have hS : (S : Set OriginalWorld) ⊆ fiber rejected false 1 0 0 1 0 0 0 := by
    intro W hw
    simp only [S,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> exact rejected_mem _
  have hc : S.card=4 := by norm_num [S,probeWorld]
  have hh := Set.ncard_le_ncard hS hfin
  rw [Set.ncard_coe_finset,hc] at hh
  omega

private theorem rejected_roots : ¬ arenaRoots.Law rejected := by
  classical
  intro h
  have hh := h false 1 0 0 1 0 0 0 (by norm_num) (by norm_num) {probeWorld 1}
    (by intro W hw; rcases Finset.mem_singleton.mp hw with rfl; exact rejected_mem 1)
  have hm : (1 : ℝ) ∈ (driftPolynomial false 1 0 0 1 0 0 0).roots :=
    Multiset.mem_of_le hh (by simp [probeWorld])
  have he := (Polynomial.mem_roots (by
    intro hz
    have hc := congrArg (fun P : Polynomial ℝ => P.eval 1) hz
    norm_num [driftPolynomial,oddNumerators,evenNumerators,sixthIndex] at hc)).mp hm
  norm_num [Polynomial.IsRoot,driftPolynomial,oddNumerators,evenNumerators,sixthIndex] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),(false,probeWorld 0),(false,probeWorld 1),?_⟩
  intro h
  have h0 := congrFun h 0
  norm_num [actual,realize,sevenRead,probeWorld] at h0

def bound_source_registration : Registration arenaBound (type_of% @seven_read_world_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨seven_read_world_bound,rejected,rejected_bound⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arenaBound.Law actual rejected
    rejected_bound
  dependence := dependence

def roots_source_registration : Registration arenaRoots (type_of% @native_drift_multiset_le_roots) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_drift_multiset_le_roots,rejected,rejected_roots⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arenaRoots.Law actual rejected
    rejected_roots
  dependence := dependence

private def selection : LeanInformationAudit.Contract.SourceSelection where
  owner := `D5.S3.Observer.CubicGain.SevenReadWorldBound
  definition := none
  coordinates := #[]
  readouts := #[]

def bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@seven_read_world_bound) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.SevenReadWorldBound.seven_read_world_bound.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.SevenReadWorldBound.bound_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arenaBound⟩
  objectArena := .source ⟨arenaBound⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arenaBound ⟨bound_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s i => sevenRead s.1 s.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[] }

def roots_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@native_drift_multiset_le_roots) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.SevenReadWorldBound.native_drift_multiset_le_roots.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.SevenReadWorldBound.roots_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arenaRoots⟩
  objectArena := .source ⟨arenaRoots⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arenaRoots ⟨roots_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s i => sevenRead s.1 s.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms bound_source_registration
#print axioms roots_source_registration
end Reg.D5.S3.Observer.CubicGain.SevenReadWorldBound

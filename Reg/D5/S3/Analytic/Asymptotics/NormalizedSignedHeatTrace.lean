import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace

open Finset Set LeanInformationAudit
open _root_.D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f b => StrictMonoOn f (Ioc 0 b)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (g z : ℕ → ℝ) (B dB : ℝ → ℝ) (b : ℝ)
    (hprefix : ∀ k ≤ n, (∑ i ∈ range k, g i) ≤ 0)
    (htotal : (∑ i ∈ range n, g i) < 0)
    (hz : ∀ i, 0 ≤ z i) (horder : Monotone z)
    (hB : ∀ x ∈ Ioc 0 b, B x < 0)
    (hderiv : ∀ x ∈ Ioc 0 b, HasDerivAt B (dB x) x)
    (hgap : ∀ x ∈ Ioc 0 b, B x < x * dB x),
    R.readout () () (fun x => (x^2 * ∑ i ∈ range n, g i * Real.exp (-(z i / x))) / B x) b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (fun _ => -1) (fun _ => 0) (fun _ => -1) (fun _ => 0) 1
    (fun _ _ => sum_nonpos (fun _ _ => by norm_num)) (by norm_num)
    (fun _ => le_rfl) (fun _ _ _ => le_rfl) (by intros; norm_num)
    (fun x _ => hasDerivAt_const x (-1 : ℝ)) (by intros; norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun x => x), (fun _ => 0), ?_⟩
  intro h
  have hi : StrictMonoOn (fun x : ℝ => x) (Set.Ioc 0 1) :=
    fun _ _ _ _ hxy => hxy
  have hc : StrictMonoOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioc 0 1) :=
    Eq.mp (congrFun h 1) hi
  have contradiction := hc (a := (1/2 : ℝ)) (b := 1)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) contradiction

def family : Registration arena (type_of% @normalized_cutoff_heat_strictMono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_cutoff_heat_strictMono, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_cutoff_heat_strictMono) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace.normalized_cutoff_heat_strictMono.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace

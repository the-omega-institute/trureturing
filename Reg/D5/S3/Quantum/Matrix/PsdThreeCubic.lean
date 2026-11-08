import D5.S3.Quantum.Matrix.PsdThreeCubic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound scalar observations retain each original telescope.
The source-selection reconstruction and escape coordinate are unfinished. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.PsdThreeCubic
open _root_.D5.S3.Quantum.Matrix.PsdThreeCubic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.PsdThreeCubic
noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

namespace negative_pair_bound
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (a b c d e f x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hgram : ∀ u v w : ℝ, 0 ≤ d*u^2+e*v^2+f*w^2-
      2*(x*u*v+y*v*w+z*w*u)), F.readout () () (allowance a b c * (x*y*z), pairEnergy a b c d e f x y z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0 0 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro u v w; norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_pair_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_pair_bound, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_pair_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_pair_bound.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_pair_bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end negative_pair_bound

namespace allowance_of_p396
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (a b c k : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hs : 0 < a+b+c)
    (hcert : (a+b+c)*k^2 ≤ 4*(a+b+c)*(a*b+b*c+c*a)+396*a*b*c), F.readout () () (k, allowance a b c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.allowance_of_p396)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.allowance_of_p396, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.allowance_of_p396) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubic.allowance_of_p396.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubic.allowance_of_p396.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end allowance_of_p396

end
end Reg.D5.S3.Quantum.Matrix.PsdThreeCubic

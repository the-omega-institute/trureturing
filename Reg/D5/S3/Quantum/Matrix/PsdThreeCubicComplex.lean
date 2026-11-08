import D5.S3.Quantum.Matrix.PsdThreeCubicComplex
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

namespace Reg.D5.S3.Quantum.Matrix.PsdThreeCubicComplex
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

namespace negative_cycle_gram
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (S : Mat) (hS : S.PosSemidef) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y)
    (ha : Complex.normSq (S 0 1) = x^2)
    (hb : Complex.normSq (S 1 2) = y^2)
    (hcycle : (cycle S).re = -(x*y*z)), ∀ u v w : ℝ, F.readout () () (0, (S 0 0).re*u^2+(S 1 1).re*v^2+(S 2 2).re*w^2- 2*(x*u*v+y*v*w+z*w*u))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ)) (fun _ => 1)) (by simpa using Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 3 => (1 : ℂ))) 1 1 (-1) (by norm_num) (by norm_num) (by norm_num [Matrix.vecMulVec, Complex.normSq_apply]) (by norm_num [Matrix.vecMulVec, Complex.normSq_apply]) (by norm_num [cycle, Matrix.vecMulVec]) 0 0 0

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_cycle_gram)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_cycle_gram, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.negative_cycle_gram) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubicComplex.negative_cycle_gram.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubicComplex.negative_cycle_gram.family
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
end negative_cycle_gram

namespace cubic_nonneg
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (S : Mat) (hS : S.PosSemidef) (a b c k : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hcoeff : k ≤ allowance a b c), F.readout () () (0, cubic a b c k S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 Matrix.PosSemidef.zero 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [allowance, root3])

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.cubic_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.cubic_nonneg, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.PsdThreeCubic.cubic_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubicComplex.cubic_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PsdThreeCubicComplex.cubic_nonneg.family
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
end cubic_nonneg

end
end Reg.D5.S3.Quantum.Matrix.PsdThreeCubicComplex

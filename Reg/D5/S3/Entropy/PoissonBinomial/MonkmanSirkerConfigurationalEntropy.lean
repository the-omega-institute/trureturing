import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep
import D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
open _root_.D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open _root_.Reg.D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep
open LeanInformationAudit

namespace Reg.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
noncomputable section
set_option autoImplicit false
namespace result
abbrev signature := orderSignature
def actual : Realization signature := orderActual
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : ℕ) (c d : Fin M → ℝ),
    (∀ i, c i ∈ Set.Icc 0 1) → (∀ i, d i ∈ Set.Icc 0 1) →
    moreMixed d c → R.readout () () (F c) (F d)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    (by constructor <;> simp [moreMixed,desc,prefixSum])

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := order_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.result.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
    definition := some { owner := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy, name := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.claim, path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end result
end
end Reg.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy

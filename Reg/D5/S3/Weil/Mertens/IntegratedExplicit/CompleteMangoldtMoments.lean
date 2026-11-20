import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory LeanInformationAudit
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent (transform)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
  (signature actual shifted)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments

def arena : Arena where
  signature := signature
  Law V :=
    let Φ := V.readout () ()
    ∀ k : ℕ, ∀ {s : ℂ}, 1 < s.re →
    IntegrableOn (fun u : ℝ => (-(u : ℂ)) ^ k *
      (Complex.exp (-s * u) * (U (Real.exp u) : ℂ))) (Ioi 0) ∧
    iteratedDeriv k Φ s =
      ∫ u : ℝ in Ioi 0, (-(u : ℂ)) ^ k * (Complex.exp (-s * u) * (U (Real.exp u) : ℂ))

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hs : 1 < (2 : ℂ).re := by norm_num
  have he := (h 0 hs).2.trans (iterated_derivative_moment 0 hs).2.symm
  change transform 2 + 1 = transform 2 at he
  exact one_ne_zero (by linear_combination he : (1 : ℂ) = 0)

def evidence : Registration arena (type_of% @iterated_derivative_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨iterated_derivative_moment, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual shifted shifted_fails
  dependence := _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent.evidence.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@iterated_derivative_moment) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments.iterated_derivative_moment.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => transform) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments

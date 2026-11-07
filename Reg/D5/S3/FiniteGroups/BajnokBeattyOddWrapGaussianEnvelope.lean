import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful full-domain registration attempt for
`actual_gaussian_envelope`.

The original telescope consists of integers p,t with 3<=p, Odd p,
2<=t and t<=p. The parameter subtype retains exactly the p constraints;
the dependent state subtype retains exactly the t constraints. Both
roles read the complete `original_return_pair p t`, at source length
(p*(6*t-1)).toNat. No comparison, binomial estimate, count formula,
positive denominator or exponential bound is added as a hypothesis.

The Law is the original real inequality
  exp(s)+exp(-9s) < 2*W19/W33,
where s=4*p^2/(p*(6*t-1)+1). Each role can separately be replaced
by zero. At the admissible state p=5,t=2 this makes the real quotient
zero, while the sum of exponentials is strictly positive. Each
intervention preserves the other role and the empty anchor family.

Actual observational dependence fixes p=5 and uses t=2,3; both belong
to the full original state domain. The exact existing original count
formulas at lengths 55 and 85 establish dependence for both roles.

sourceSelection and familyRecord remain none. Checked binding to the
original component readout occurrences remains unfinished, tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
No declared_validated source binding is claimed.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev gaussianEnvelopeSignature : Signature where
  Params := {p : ℤ // 3 ≤ p ∧ Odd p}
  State p := {t : ℤ // 2 ≤ t ∧ t ≤ p.1}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def gaussianEnvelopeActual : Realization gaussianEnvelopeSignature :=
  realize gaussianEnvelopeSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 t.1).1
      else (original_return_pair p.1 t.1).2)
    (fun e => nomatch e)

noncomputable def gaussianEnvelopeRejected (i : Fin 2) :
    Realization gaussianEnvelopeSignature :=
  realize gaussianEnvelopeSignature
    (fun j p t => if j = i then 0 else gaussianEnvelopeActual.readout j p t)
    (fun e => nomatch e)

abbrev gaussianEnvelopeArena : Arena where
  signature := gaussianEnvelopeSignature
  Law R := ∀ (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p)
      (ht2 : 2 ≤ t) (htp : t ≤ p),
    let pp : gaussianEnvelopeSignature.Params := ⟨p,hp3,hpo⟩
    let tt : gaussianEnvelopeSignature.State pp := ⟨t,ht2,htp⟩
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    Real.exp s+Real.exp (-9*s) <
      2*(R.readout 0 pp tt : ℝ)/(R.readout 1 pp tt : ℝ)

private theorem gaussianEnvelope_actual_law :
    gaussianEnvelopeArena.Law gaussianEnvelopeActual := by
  exact actual_gaussian_envelope

private theorem gaussianEnvelope_rejected_law (i : Fin 2) :
    ¬ gaussianEnvelopeArena.Law (gaussianEnvelopeRejected i) := by
  intro h
  have hh := h 5 2 (by norm_num) (by decide) (by norm_num) (by norm_num)
  let s : ℝ := 4*(5 : ℝ)^2/((5 : ℝ)*(6*(2 : ℝ)-1)+1)
  have hpos : 0 < Real.exp s+Real.exp (-9*s) := by positivity
  have hneg : Real.exp s+Real.exp (-9*s) < 0 := by
    fin_cases i <;>
      simpa [gaussianEnvelopeRejected, gaussianEnvelopeActual, realize, s] using hh
  linarith only [hneg,hpos]

set_option maxRecDepth 10000 in
private theorem gaussianEnvelope_actual_dependence :
    ObservationalDependence gaussianEnvelopeSignature gaussianEnvelopeActual := by
  intro i
  let p : gaussianEnvelopeSignature.Params := ⟨5,by decide⟩
  refine ⟨p, ⟨2,by decide⟩, ⟨3,by decide⟩, ?_⟩
  have h55 := actual_odd_wrap_counts 5 2 (by norm_num) (by decide) (by norm_num)
  have h85 := actual_odd_wrap_counts 5 3 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change returns19 5 2 55 ≠ returns19 5 3 85
    have hc55 : returns19 5 2 55 =
        2*(Nat.choose 55 30+Nat.choose 55 50) := h55.1
    have hc85 : returns19 5 3 85 =
        2*(Nat.choose 85 45+Nat.choose 85 65) := h85.1
    rw [hc55,hc85]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 45 ≤ 85),
      Nat.choose_eq_factorial_div_factorial (by decide : 65 ≤ 85), Nat.factorial]
  · change returns33 5 2 55 ≠ returns33 5 3 85
    have hc55 : returns33 5 2 55 = 4*Nat.choose 55 35 := h55.2
    have hc85 : returns33 5 3 85 = 4*Nat.choose 85 50 := h85.2
    rw [hc55,hc85]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 35 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 85), Nat.factorial]

noncomputable def gaussianEnvelopeSource : Registration gaussianEnvelopeArena
    (type_of% actual_gaussian_envelope) where
  actual := gaussianEnvelopeActual
  bridge := Iff.rfl
  variation := ⟨gaussianEnvelope_actual_law,
    gaussianEnvelopeRejected 0, gaussianEnvelope_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨gaussianEnvelopeRejected i, ?_, rfl, gaussianEnvelope_rejected_law i⟩
      intro j hj
      funext p t
      simp [gaussianEnvelopeRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := gaussianEnvelope_actual_dependence

noncomputable def gaussianEnvelopeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_gaussian_envelope)
      (Realization gaussianEnvelopeSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope.actual_gaussian_envelope.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope.gaussianEnvelopeSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianEnvelopeArena⟩
  objectArena := .source ⟨gaussianEnvelopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianEnvelopeArena ⟨gaussianEnvelopeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianEnvelopeSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 t.1).1
      else (original_return_pair p.1 t.1).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope

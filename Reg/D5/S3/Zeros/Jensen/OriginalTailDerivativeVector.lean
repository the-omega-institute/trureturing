import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open _root_.D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
open _root_.D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
open _root_.D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open _root_.D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
open _root_.D5.S3.Zeros.Jensen
open private originalCoefficient from D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
open LeanInformationAudit MeasureTheory Set Real Polynomial

noncomputable section
namespace Reg.D5.S3.Zeros.Jensen.OriginalTailDerivativeVector

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
      0<fullZ ∧ (∫ x:ℝ,sourceThetaDensity x)=1 ∧
      ∀ a:ℝ,0<a → ∃ C:ℝ,0<C ∧
        ∀ N n:ℕ,1≤N → 1≤n → ∀ t:ℝ,0<t → t/(2*(n:ℝ))≤a →
          let A:=modeScale (N+1)
          let I:=∫ x in Ioi (0:ℝ),originalB n t x*originalTail N x
          let H:=∫ x in Ioi (0:ℝ),originalB n t x*originalHead N x
          0<originalFlux N ∧
          IntegrableOn (fun x:ℝ =>originalB n t x*originalTail N x) (Ioi 0) ∧
          IntegrableOn (fun x:ℝ =>originalB n t x*originalHead N x) (Ioi 0) ∧
          Integrable (fun x:ℝ =>originalB n t x*sourceThetaDensity x) ∧
          originalJ n t=(sourceP n).eval (-t) ∧ originalJ n t=(2/fullZ)*(H+I) ∧
          (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=(originalJ n t:ℂ) ∧
          sourceJensenPolynomial n=normalizedJensen sourceThetaCoefficient n ∧
          ((sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0 ↔ originalJ n t=0) ∧
          |t*I/originalFlux N-1|≤C*((N:ℝ)+1)^4/t ∧
          (∀ x:ℝ,HasDerivAt (fun u:ℝ =>originalB n u x) (originalb n t x) t) ∧
          (∀ x:ℝ,originalb n 0 x= -x^2/2) ∧
          (
        IntegrableOn (fun x =>originalb n t x*originalTail N x) (Ioi 0) ∧
        IntegrableOn (fun x =>x^2*originalB n t x*originalTail N x) (Ioi 0) ∧
        IntegrableOn (fun x =>originalb n t x*originalHead N x) (Ioi 0) ∧
        IntegrableOn (fun x =>x^2*originalB n t x*originalHead N x) (Ioi 0) ∧
        Integrable (fun x:ℝ =>originalb n t x*sourceThetaDensity x) ∧
        Integrable (fun x:ℝ =>x^2*originalB n t x*sourceThetaDensity x) ∧
        HasDerivAt (fun u =>∫ x in Ioi (0:ℝ),originalB n u x*originalTail N x)
          (rawD n t (originalTail N)) t ∧
        HasDerivAt (fun u =>∫ x in Ioi (0:ℝ),originalB n u x*originalHead N x)
          (rawD n t (originalHead N)) t ∧
        HasDerivAt (originalJ n) (fullD n t) t ∧
        fullD n t= -(sourceP n).derivative.eval (-t) ∧
        fullD n t=(2/fullZ)*(rawD n t (originalHead N)+rawD n t (originalTail N)) ∧
        fullM2 n t=(2/fullZ)*(rawM2 n t (originalHead N)+rawM2 n t (originalTail N)) ∧
        fullG n t=(2/fullZ)*(rawG n t (originalHead N)+rawG n t (originalTail N)) ∧
        rawG n t (originalTail N)=
          -∑ k∈Finset.range (n+1),originalCoefficient n 1 k*t^k*
            (∫ x in Ioi (0:ℝ),x^(2*(k+1))*originalTail N x)/(2*(2*(k:ℝ)+1)) ∧
        rawG n t (originalHead N)=
          -∑ k∈Finset.range (n+1),originalCoefficient n 1 k*t^k*
            (∫ x in Ioi (0:ℝ),x^(2*(k+1))*originalHead N x)/(2*(2*(k:ℝ)+1))) ∧ (
        fullG n t= -∑ k∈Finset.range (n+1),
          (-1:ℝ)^k*(n.descFactorial k:ℝ)/(n:ℝ)^k*((k:ℝ)+1)*sourceThetaCoefficient (k+1)*t^k ∧
        HasDerivAt (originalJ (n+1)) (fullG n t) (((n+1:ℕ):ℝ)/(n:ℝ)*t)) ∧ (
        let α:=t/(2*(n:ℝ))
        let S:=4*A^2
        let Λ:=S+t
        let Q:=originalTail N
        let R:=tailResidual N A α
        let R₂:=tailSecondResidual N A α
        let I:=∫ x in Ioi (0:ℝ),originalB n t x*Q x
        let U:=∫ x in Ioi (0:ℝ),originalB n t x*R x
        Λ*I=originalFlux N+U ∧
        (Λ-2*α)*rawD n t Q= -I+rawD n t R ∧
        (Λ+2*α)*rawM2 n t Q=2*I+8*t*rawD n t Q+rawM2 n t R ∧
        (Λ-2*α)*rawD n t R= -U+rawD n t R₂ ∧
        (Λ+2*α)*rawM2 n t R=2*U+8*t*rawD n t R+rawM2 n t R₂) ∧
          (max 64 a≤A → (
        IntegrableOn (fun x:ℝ => exp (a*x^2/2)*|tailResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) (Ioi 0) ∧
        (∫ x in Ioi (0:ℝ),exp (a*x^2/2)*|tailResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) ≤
          64*originalFlux N/modeScale (N+1)) ∧ (
        IntegrableOn (fun x:ℝ => x^2*exp (a*x^2/2)*
          |tailSecondResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) (Ioi 0) ∧
        (∫ x in Ioi (0:ℝ),x^2*exp (a*x^2/2)*
          |tailSecondResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) ≤1100*originalFlux N/modeScale (N+1)) ∧ (
        let A:=modeScale (N+1)
        let S:=4*A^2
        let Λ:=S+t
        let κ:=originalFlux N
        let I:=∫ x in Ioi (0:ℝ),originalB n t x*originalTail N x
        let D:=rawD n t (originalTail N)
        let M:=rawM2 n t (originalTail N)
        let G:=rawG n t (originalTail N)
        let c:=((2*(n:ℝ)+1)*S+(2*(n:ℝ)-3)*t)/((2*(n:ℝ)+1)*Λ)
        R.readout () () (Λ*I/κ-1)≤64/A ∧ |Λ^2*D/κ+1|≤2600/A ∧
        |Λ^3*M/(2*κ)-(S-3*t)|≤16000*Λ/A ∧
        |Λ^2*G/κ+c|≤(5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A) ∧
        (5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A)≤21200/(3*A))) ∧
          (max 72000 a≤A → (
        rawD n t (originalTail N)≤-originalFlux N/(2*(4*(modeScale (N+1))^2+t)^2) ∧
        rawG n t (originalTail N)≤-originalFlux N/(10*(4*(modeScale (N+1))^2+t)^2) ∧
        (originalFlux N)^2/(20*(4*(modeScale (N+1))^2+t)^4)≤rawD n t (originalTail N)*rawG n t (originalTail N) ∧
        0<(originalFlux N)^2/(20*(4*(modeScale (N+1))^2+t)^4) ∧
        (2/fullZ)*rawD n t (originalTail N)≤-originalFlux N/(fullZ*(4*(modeScale (N+1))^2+t)^2) ∧
        (2/fullZ)*rawG n t (originalTail N)≤-originalFlux N/(5*fullZ*(4*(modeScale (N+1))^2+t)^2) ∧
        (originalFlux N)^2/(5*fullZ^2*(4*(modeScale (N+1))^2+t)^4)≤
          ((2/fullZ)*rawD n t (originalTail N))*((2/fullZ)*rawG n t (originalTail N)) ∧
        0<(originalFlux N)^2/(5*fullZ^2*(4*(modeScale (N+1))^2+t)^4))) ∧
          (originalJ n t=0 → (
        let δ:ℝ:=(n:ℝ)/((n+1:ℕ):ℝ)
        let ξ:=δ/t
        let q:=sourceQ (n+1)
        0<ξ ∧ q.derivative.eval ξ=0 ∧
        ((n+1:ℕ):ℝ)*q.eval ξ=ξ^n*fullG n t ∧
        ξ^2*q.derivative.derivative.eval ξ= -(n:ℝ)*ξ^n*fullD n t ∧
        q.eval ξ*q.derivative.derivative.eval ξ=
          -((n:ℝ)/((n+1:ℕ):ℝ))*ξ^(2*n-2)*fullD n t*fullG n t ∧
        (fullD n t≠0 ↔ q.derivative.derivative.eval ξ≠0) ∧
        (fullD n t≠0 →
          SourceJensenPositiveExtension.sourceCoupling (n+1) ξ=
            (ξ^2/(n:ℝ))*(fullG n t/fullD n t) ∧
          (0≤SourceJensenPositiveExtension.sourceCoupling (n+1) ξ ↔
            0≤fullD n t*fullG n t)))) ∧
          fullD n t*fullG n t=(4/fullZ^2)*(
            rawD n t (originalHead N)*rawG n t (originalHead N)+
            rawD n t (originalHead N)*rawG n t (originalTail N)+
            rawD n t (originalTail N)*rawG n t (originalHead N)+
            rawD n t (originalTail N)*rawG n t (originalTail N))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C,hC,hCn⟩:=h.2.2 1 (by norm_num)
  rcases hCn 5 1 (by omega) (by omega) 1 (by norm_num) (by norm_num) with
    ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hQuant,_⟩
  have hA:max (64:ℝ) 1≤modeScale (5+1) := by
    norm_num [modeScale]
    nlinarith [pi_gt_three]
  have hread:=(hQuant hA).2.2.1
  change (1:ℝ)≤64/modeScale (5+1) at hread
  have hpos:0<modeScale (5+1) := by dsimp [modeScale]; positivity
  have hh:=(le_div_iff₀ hpos).mp hread
  norm_num [modeScale] at hh
  nlinarith [pi_gt_three]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change |(0:ℝ)|≠|(1:ℝ)|
  norm_num

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_tail_derivative_vector,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Zeros.Jensen.OriginalTailDerivativeVector.original_tail_derivative_vector)
    (type_of% (realize signature (fun _ _ x => |x|) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.Jensen.OriginalTailDerivativeVector.derivative_vector_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.OriginalTailDerivativeVector.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration_1
end Reg.D5.S3.Zeros.Jensen.OriginalTailDerivativeVector

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open _root_.D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
open _root_.D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open _root_.D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
open LeanInformationAudit MeasureTheory Set Real

noncomputable section
namespace Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    0 < fullZ ∧ (∫ x:ℝ, sourceThetaDensity x) = 1 ∧
      ∃ K:ℝ, 0<K ∧ ∀ a:ℝ, 0<a → ∃ C:ℝ, 0<C ∧
        ∀ N n:ℕ, 1≤N → 1≤n → ∀ t:ℝ, 0<t → t/(2*(n:ℝ))≤a →
          let A := modeScale (N+1)
          let I := ∫ x in Set.Ioi (0:ℝ), originalB n t x*originalTail N x
          let H := ∫ x in Set.Ioi (0:ℝ), originalB n t x*originalHead N x
          0<originalFlux N ∧
          MeasureTheory.IntegrableOn (fun x:ℝ => originalB n t x*originalTail N x) (Set.Ioi 0) ∧
          MeasureTheory.IntegrableOn (fun x:ℝ => originalB n t x*originalHead N x) (Set.Ioi 0) ∧
          MeasureTheory.Integrable (fun x:ℝ => originalB n t x*sourceThetaDensity x) ∧
          originalJ n t = (sourceP n).eval (-t) ∧
          originalJ n t = (2/fullZ)*(H+I) ∧
          (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ)) = (originalJ n t:ℂ) ∧
          sourceJensenPolynomial n = normalizedJensen sourceThetaCoefficient n ∧
          ((sourceJensenPolynomial n).eval (((-t:ℝ):ℂ)) = 0 ↔ originalJ n t = 0) ∧
          R.readout () () (t*I/originalFlux N-1) ≤ C*((N:ℝ)+1)^4/t ∧
          (2*C*((N:ℝ)+1)^4 ≤ t →
            (originalJ n t=0 ∨ (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0) →
            (2/fullZ)*H ≤ -originalFlux N/(fullZ*t)) ∧
          (max 12 a ≤ A → |(t+4*A^2)*I/originalFlux N-1| ≤ K/A) ∧
          (max (max 12 a) (2*K) ≤ A →
            originalFlux N/(2*(t+4*A^2)) ≤ I ∧
            0<originalFlux N/(2*(t+4*A^2)) ∧
            ((originalJ n t=0 ∨ (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0) →
              (2/fullZ)*H ≤ -originalFlux N/(fullZ*(t+4*A^2)) ∧
              -originalFlux N/(fullZ*(t+4*A^2))<0))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K,_,hall⟩ := h.2.2
  obtain ⟨C,hC,hCn⟩ := hall 1 (by norm_num)
  let t := 32*C+1
  have ht : 0<t := by dsimp [t]; linarith
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have hn1 : 1≤n := by exact_mod_cast (show (1:ℝ)≤n by dsimp [t] at hn; linarith)
  have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hα : t/(2*(n:ℝ))≤1 := by
    apply (div_le_iff₀ (by positivity : 0<2*(n:ℝ))).mpr
    linarith
  rcases hCn 1 n (by omega) hn1 t ht hα with ⟨_,_,_,_,_,_,_,_,_,hP,_⟩
  simp only [rejected,realize,Nat.cast_one] at hP
  have h := (le_div_iff₀ ht).mp hP
  norm_num at h
  dsimp [t] at h
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change |(0:ℝ)|≠|(1:ℝ)|
  norm_num

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_primal_tail_response,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Zeros.Jensen.OriginalPrimalTailResponse.original_primal_tail_response)
    (type_of% (realize signature (fun _ _ x => |x|) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailResponse.absolute_response_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailResponse.evidence
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
    owner := `D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[ "arg", "arg", "arg", "body", "arg", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg" ]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration_1
end Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

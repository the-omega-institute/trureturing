import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.LeeYang.FiolDoubleHubPhysical
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Zeros.LeeYang.FiolDoubleHubPhysical
open _root_.D5.S3.Zeros.LeeYang.FiolDoubleHub
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => ℂ) (fun _ => ℝ)

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- All source binders and all conjuncts are retained. The selected observation
is the norm of the same complex zero, not an assumed unit-circle predicate. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (m cutoff : ℕ) (hm : 1 ≤ m) (hc : 3 ≤ cutoff),
    let p := (spinCoefficient m cutoff).map Complex.ofRealHom
    p.natDegree = 4*m+6 ∧ p ≠ 0 ∧
    ∃ theta : Fin (N (m+1)) → ℝ, StrictMono theta ∧
      (∀ j, 0 < theta j ∧ theta j < Real.pi) ∧
      p.roots = Multiset.replicate (h (m+1)) 1 +
        Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) +
        Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) ∧
      Polynomial.rootMultiplicity 1 p = (if Even m then 2*m+2 else 2*m) ∧
      (∀ z : ℂ, p.IsRoot z → z ≠ 1 →
        Polynomial.rootMultiplicity z p = 1 ∧ R.readout () (m, cutoff) z = 1) ∧
      (p.roots.filter (fun z => z ≠ 1)).card = (if Even m then 2*m+4 else 2*m+6) ∧
      ¬ p.IsRoot (-1) ∧
      (p.IsRoot Complex.I ↔ m % 4 = 1) ∧
      (p.IsRoot (-Complex.I) ↔ m % 4 = 1) ∧
      (m % 4 = 1 → Polynomial.rootMultiplicity Complex.I p = 1 ∧
        Polynomial.rootMultiplicity (-Complex.I) p = 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 1 3 (by decide) (by decide)
  dsimp only at hx
  obtain ⟨_, _, theta, _, _, _, _, hzero, _, _, hi, _, _⟩ := hx
  have hz := hzero Complex.I (hi.mpr (by decide)) (by norm_num [Complex.ext_iff])
  have he := hz.2
  change (2 : ℝ) = 1 at he
  norm_num at he

noncomputable def evidence : Registration arena (type_of% (@physical_root_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_root_classification, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(1,3), (0:ℂ), (1:ℂ), ?_⟩
    change ‖(0:ℂ)‖ ≠ ‖(1:ℂ)‖
    norm_num

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_root_classification)
    (type_of% (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)))
    Type Unit := {
  unitName := `Reg.D5.S3.Zeros.LeeYang.FiolDoubleHubPhysical.physical_unit
  realizationName := `Reg.D5.S3.Zeros.LeeYang.FiolDoubleHubPhysical.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Zeros.LeeYang.FiolDoubleHubPhysical
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg",
        "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body",
        "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Zeros.LeeYang.FiolDoubleHubPhysical

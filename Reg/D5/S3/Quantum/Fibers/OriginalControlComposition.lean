import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalControlComposition
import Reg.Support.DependentFamily

open D5.S3.Quantum.Fibers.FiniteRectangleTransport
open D5.S3.Quantum.Fibers.OriginalControlComposition
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory
namespace Reg.D5.S3.Quantum.Fibers.OriginalControlComposition
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

def signature : Signature where
  Params := ℝ × (ℝ → ℝ)
  State := fun _ => ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p chi => concatenate chi p.2 p.1) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => (0 : ℝ → ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (b : Base) (T S : ℝ) (k chi K C : ℝ → ℝ)
    (_hc : OriginalControl b T k chi) (_hd : OriginalControl b S K C)
    (_hjoin : k T=K 0),
    OriginalControl b (T+S) (concatenate k K T) ((R.readout () (T,C) chi)) ∧
    EqOn (concatenate k K T) k (Icc (0:ℝ) T) ∧
    EqOn ((R.readout () (T,C) chi)) chi (Icc (0:ℝ) T) ∧
    (∀ s ∈ Icc (0:ℝ) S, concatenate k K T (T+s)=K s ∧
      (R.readout () (T,C) chi) (T+s)=chi T+C s-C 0) ∧
    (R.readout () (T,C) chi) (T+S)-(R.readout () (T,C) chi) 0=
      (chi T-chi 0)+(C S-C 0) ∧
    (∀ F : ℝ → ℝ, ContinuousOn F (Ioo (lower b) (upper b)) →
      (∫ t in (0:ℝ)..(T+S), F (concatenate k K T t)*deriv ((R.readout () (T,C) chi)) t)=
        (∫ t in (0:ℝ)..T, F (k t)*deriv chi t)+
        (∫ t in (0:ℝ)..S, F (K t)*deriv C t))

private theorem constant_control (c : ℝ) :
    OriginalControl ((2/5:ℝ),2/5,1/5) 0 (fun _ => 1/5) (fun _ => c) := by
  refine ⟨le_rfl,continuousOn_const,continuousOn_const,?_,?_,Or.inl ⟨?_,?_⟩⟩
  · intro t ht; norm_num [lower,upper]
  · exact (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval.boundedVariationOn
  · exact (LipschitzWith.const (1/5:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  · exact (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hp := (h ((2/5:ℝ),2/5,1/5) 0 0 (fun _ => 1/5) (fun _ => 1)
    (fun _ => 1/5) (fun _ => 0) (constant_control 1) (constant_control 0) rfl).2.2.1
  have he := hp (show (0:ℝ) ∈ Icc (0:ℝ) 0 from ⟨le_rfl,le_rfl⟩)
  norm_num [rejected,realize] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨concatenate_original,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(0,fun _ => 0),(fun _ => 0),(fun _ => 1),?_⟩
    intro he
    have hx := congrFun he 0
    norm_num [actual,realize,concatenate] at hx

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@D5.S3.Quantum.Fibers.OriginalControlComposition.concatenate_original)
    (type_of% (realize signature (fun _ p chi => concatenate chi p.2 p.1)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalControlComposition.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalControlComposition.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p chi => concatenate chi p.2 p.1)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := (`D5.S3.Quantum.Fibers.OriginalControlComposition),
    definition := none,
    coordinates := #[1,6],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "fn","arg","arg"],
      stateBinder := 4,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end
end Reg.D5.S3.Quantum.Fibers.OriginalControlComposition

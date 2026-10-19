import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.FiniteRectangleTransport
import Reg.Support.DependentFamily

open D5.S3.Quantum.Fibers.FiniteRectangleTransport
open D5.S3.Quantum.Fibers.InteriorProbabilityPhaseFiber
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

def signature : Signature where
  Params := List (ℝ × ℝ)
  State := fun _ => ℝ → State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Vec
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ data q => (q (4*data.length)).2.2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (0 : Vec)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (b : Base) (_hb : ValidBase b) (k0 : ℝ)
    (_hk0 : k0 ∈ Set.Ioo (lower b) (upper b)) (data : List (ℝ × ℝ))
    (_hdata : ∀ ka ∈ data, ka.1 ∈ Set.Ioo (lower b) (upper b)),
    ∃ q : ℝ → State,
      Admissible b (4*data.length) q ∧
      q 0 = (k0,0,0) ∧
      (q (4*data.length)).1 = k0 ∧ (q (4*data.length)).2.1 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (4*data.length),
        ∃ p : InteriorProbability 4, p.weight = probability b (q t).1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (4*data.length), Compatible (q t)) ∧
      R.readout () data q = residual (phaseWeight b) k0 data

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, _, _, _, _, _, _, he⟩ := h ((2/5 : ℝ),2/5,1/5)
    (by norm_num [ValidBase]) (1/5) (by norm_num [lower,upper]) [(1/10,1)]
    (by intro ka hka; simp only [List.mem_singleton] at hka; subst ka
        norm_num [lower,upper])
  have hc := congrFun he 0
  norm_num [rejected, realize,
    D5.S3.Quantum.Fibers.FiniteRectangleTransport.residual,
    phaseWeight, information, probability, direction,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at hc

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_rectangles_realize,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨[],(fun _ => (0,0,(0 : Vec))),(fun _ => (0,0,(1 : Vec))),?_⟩
    intro he
    have hc := congrFun he 0
    norm_num [actual,realize] at hc

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@D5.S3.Quantum.Fibers.FiniteRectangleTransport.finite_rectangles_realize)
    (type_of% (realize signature (fun _ data q => (q (4*data.length)).2.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ data q => (q (4*data.length)).2.2)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := (`D5.S3.Quantum.Fibers.FiniteRectangleTransport),
    definition := none,
    coordinates := #[4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"],
      stateBinder := 6,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport

namespace Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.WeightCompatibility

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

def signature : Signature where
  Params := Base
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Vec
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ b k => phaseWeight b k) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (0 : Vec)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (b : Base) (_hb : ValidBase b) (k : ℝ)
    (_hk : k ∈ Set.Ioo (lower b) (upper b)),
    R.readout () b k 2 = 0 ∧
      R.readout () b k 0 - R.readout () b k 1 -
      R.readout () b k 3 + R.readout () b k 4 = 1

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have he := (h ((2/5 : ℝ),2/5,1/5) (by norm_num [ValidBase])
    (1/5) (by norm_num [lower,upper])).2
  norm_num [rejected, realize] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weight_compatible,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨((2/5 : ℝ),2/5,1/5),(1/5 : ℝ),(1/10 : ℝ),?_⟩
    intro he
    have hc := congrFun he 0
    norm_num [actual,realize,phaseWeight,information,probability,direction,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at hc

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@D5.S3.Quantum.Fibers.FiniteRectangleTransport.weight_compatible)
    (type_of% (realize signature (fun _ b k => phaseWeight b k)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.WeightCompatibility.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.WeightCompatibility.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ b k => phaseWeight b k)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := (`D5.S3.Quantum.Fibers.FiniteRectangleTransport),
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.WeightCompatibility

namespace Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.Polygon
noncomputable section
open Set
set_option autoImplicit false
set_option relaxedAutoImplicit false

def signature : Signature where
  Params := State
  State := fun _ => List State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List State
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ x xs => x :: xs) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => ([] : List State)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (b : Base) (x : State) (xs : List State)
    (_hx : x.1 ∈ Ioo (lower b) (upper b))
    (_h : List.IsChain (LawfulLeg (phaseWeight b) (lower b) (upper b)) (x :: xs)),
    Admissible b xs.length (polygon (R.readout () x xs))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hx : (1/5:ℝ) ∈ Ioo (lower ((2/5:ℝ),2/5,1/5))
      (upper ((2/5:ℝ),2/5,1/5)) := by norm_num [lower,upper]
  have hh := h ((2/5:ℝ),2/5,1/5) (1/5,0,0) [] hx (by simp)
  have hi := hh.2.1 0 (by simp)
  norm_num [rejected,realize,lower,polygon] at hi

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨polygon_admissible,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(0:State),[],[(1:State)],?_⟩
    intro he
    have hi := congrArg List.length he
    norm_num [actual,realize] at hi

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@D5.S3.Quantum.Fibers.FiniteRectangleTransport.polygon_admissible)
    (type_of% (realize signature (fun _ x xs => x :: xs)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.Polygon.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.Polygon.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ x xs => x :: xs)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.FiniteRectangleTransport,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["body","body","body","body","body","arg","arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end
end Reg.D5.S3.Quantum.Fibers.FiniteRectangleTransport.Polygon

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℝ × ℝ × ℝ) (fun _ => Mode) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ p s => law starEnds 0 1 2 ![p.1,p.2.1,p.2.2] s) (fun e => nomatch e)

def zero : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def negative : Realization signature := realize signature
  (fun _ _ s => if s = .ab ∨ s = .bc then 1 else 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0,0,0),Mode.separate,Mode.all,?_⟩
  change law starEnds 0 1 2 ![0,0,0] .separate ≠ law starEnds 0 1 2 ![0,0,0] .all
  rw [star_law]
  norm_num

abbrev formula (A B C : ℝ) (s : Mode) : ℝ := match s with
  | .separate => 1-A*B-A*C-B*C+2*A*B*C
  | .ab => A*B*(1-C)
  | .bc => (1-A)*B*C
  | .all => A*B*C
  | .ac => A*(1-B)*C

abbrev lawArena : Arena where
  signature := signature
  Law R := ∀ A B C : ℝ, R.readout () (A,B,C) = formula A B C

private theorem zero_rejected : ¬ lawArena.Law zero := by
  intro h
  have hh := congrFun (h 0 0 0) .separate
  norm_num [zero,realize,formula] at hh

def lawRegistration : Registration lawArena (type_of% @star_law) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨star_law,zero,zero_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity lawArena.Law actual zero zero_rejected
  dependence := dependence

abbrev determinantArena : Arena where
  signature := signature
  Law R := ∀ A B C : ℝ, delta (R.readout () (A,B,C)) =
    B*(1-A*C)*law starEnds 0 1 2 ![A,B,C] .ac

private theorem determinant_rejected : ¬ determinantArena.Law zero := by
  intro h
  have hh := h (1/2) (1/2) (1/2)
  rw [star_law] at hh
  norm_num [zero,realize,delta] at hh

def determinantRegistration : Registration determinantArena (type_of% @star_determinant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨star_determinant,zero,determinant_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity determinantArena.Law actual zero
    determinant_rejected
  dependence := dependence

abbrev boundArena : Arena where
  signature := signature
  Law R := ∀ A B C : ℝ, A ∈ Set.Icc 0 1 → B ∈ Set.Icc 0 1 → C ∈ Set.Icc 0 1 →
    0 ≤ delta (R.readout () (A,B,C)) ∧
    delta (law starEnds 0 1 2 ![A,B,C]) ≤ law starEnds 0 1 2 ![A,B,C] .ac

private theorem bound_rejected : ¬ boundArena.Law negative := by
  intro h
  have hh := (h 0 0 0 (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [negative,realize,delta] at hh

def boundRegistration : Registration boundArena (type_of% @star_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨star_bound,negative,bound_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity boundArena.Law actual negative
    bound_rejected
  dependence := dependence

def register_star_law :
    Contract.Registration (@_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.star_law)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.register_star_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.lawRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨lawArena⟩
  objectArena := .source ⟨lawArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source lawArena ⟨lawRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => law starEnds 0 1 2 ![p.1,p.2.1,p.2.2] s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_star_determinant :
    Contract.Registration (@_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.star_determinant)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.register_star_determinant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.determinantRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨determinantArena⟩
  objectArena := .source ⟨determinantArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source determinantArena ⟨determinantRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => law starEnds 0 1 2 ![p.1,p.2.1,p.2.2] s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_star_bound :
    Contract.Registration (@_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.star_bound)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.register_star_bound
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.boundRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source boundArena ⟨boundRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => law starEnds 0 1 2 ![p.1,p.2.1,p.2.2] s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def lawAnalysisSource : Analysis.Source (@star_law) :=
  Analysis.Source.ofRegistration _ lawRegistration .exact {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }

/-- The probability-mass operation is the source observation. No finite
presentation or raw binding is acquired here. The native Fibonacci continuation
adapter requires additional reader and reply evidence. -/
def lawAnalysis : AuricFib.Contract.Application (@star_law) where
  evidence := .typed {
    source := lawAnalysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable "Finite presentation and raw binding unacquired; native Fibonacci reader/reply bridge absent" }

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Sharpness
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Fin 3 → ℝ) (fun _ => Mode) (fun _ => ℝ)
def actual : Realization signature := realize _
  (fun _ θ => law starEnds 0 1 2 θ) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ θ : Fin 3 → ℝ,
    (openGraph starEnds (fun _ => true)).IsTree ∧
    (∀ e, 0 < θ e ∧ θ e < 1) ∧
    (∀ s, 0 ≤ R.readout () θ s) ∧ (∑ s, R.readout () θ s) = 1 ∧
    0 < R.readout () θ .ac ∧ (1-ε)*R.readout () θ .ac < delta (R.readout () θ)
private theorem rejected : ¬ arena.Law bad := by
  intro h
  obtain ⟨θ,_,_,hp,_⟩ := h 1 (by norm_num)
  have hh := hp .separate
  norm_num [bad,realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨![0,0,0],.separate,.all,?_⟩
  change law starEnds 0 1 2 ![0,0,0] .separate ≠ law starEnds 0 1 2 ![0,0,0] .all
  rw [star_law]
  norm_num
def registration : Registration arena (type_of% @star_sharpness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨star_sharpness,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence
def register_star_sharpness : Contract.Registration (@star_sharpness)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Sharpness.register_star_sharpness
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Sharpness.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ θ => law starEnds 0 1 2 θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Sharpness

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.WeightSum
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
noncomputable section
structure Parameters where
  Edges : Type u
  finiteEdges : Fintype Edges
  decidableEdges : DecidableEq Edges
  rate : Edges → ℝ
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Edges → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize _
  (fun _ p => @weight p.Edges p.finiteEdges p.rate) (fun e => nomatch e)
def zero : Realization signature.{u} := realize _ (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [hE : Fintype E] [hD : DecidableEq E] (θ : E → ℝ),
    ∑ ω : E → Bool, R.readout () ⟨E,hE,hD,θ⟩ ω = 1
private theorem rejected : ¬ arena.{u}.Law zero := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance (fun _ => 0)
  norm_num [zero,realize] at hh
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit,inferInstance,inferInstance,fun _ => 0⟩,
    (fun _ => false),(fun _ => true),?_⟩
  change weight (fun _ : PUnit.{u+1} => (0:ℝ)) (fun _ => false) ≠
    weight (fun _ : PUnit.{u+1} => (0:ℝ)) (fun _ => true)
  simp [weight]
def registration : Registration arena.{u} (type_of% @weight_sum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weight_sum,zero,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zero,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence
def register_weight_sum : Contract.Registration (@weight_sum.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.WeightSum.register_weight_sum
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.WeightSum.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => @weight p.Edges p.finiteEdges p.rate) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.WeightSum

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Cube
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev Parameters := (n : ℕ) × ((Fin (n+1) → Bool) → ℝ)
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters (fun p => Fin (p.1+1) → Bool) (fun _ => ℝ)
def actual : Realization signature := realize _ (fun _ p => p.2) (fun e => nomatch e)
def zero : Realization signature := realize _ (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ),
    (∑ ω, R.readout () ⟨n,f⟩ ω) = ∑ x : Bool, ∑ ω : Fin n → Bool, f (Fin.cons x ω)
private theorem rejected : ¬ arena.Law zero := by
  intro h
  have hh := h 0 (fun _ => 1)
  norm_num [zero,realize,Fintype.sum_bool] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,fun ω => if ω 0 then 1 else 0⟩,(fun _ => true),(fun _ => false),?_⟩
  norm_num [actual,realize]
def registration : Registration arena (type_of% @sum_cube_succ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_cube_succ,zero,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual zero rejected
  dependence := dependence
def register_sum_cube_succ : Contract.Registration (@sum_cube_succ)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Cube.register_sum_cube_succ
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Cube.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","fn","arg","arg","body","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Cube

open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.register_star_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_star_law
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.register_star_determinant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_star_determinant
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.register_star_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_star_bound
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Sharpness
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Sharpness.register_star_sharpness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_star_sharpness
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.WeightSum
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.WeightSum.register_weight_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_weight_sum
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Cube
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Cube.register_sum_cube_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_sum_cube_succ

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Probability
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
universe u v
noncomputable section
structure Parameters where
  Vertices : Type u
  Edges : Type v
  finiteVertices : Fintype Vertices
  decidableVertices : DecidableEq Vertices
  finiteEdges : Fintype Edges
  decidableEdges : DecidableEq Edges
  ends : Edges → Vertices × Vertices
  a : Vertices
  b : Vertices
  c : Vertices
  rate : Edges → ℝ
abbrev signature : Signature where
  Params := Parameters.{u,v}
  State _ := Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u,v} := realize _
  (fun _ p => by
    letI := p.finiteVertices
    letI := p.decidableVertices
    letI := p.finiteEdges
    letI := p.decidableEdges
    exact law p.ends p.a p.b p.c p.rate) (fun e => nomatch e)
def bad : Realization signature.{u,v} := realize _ (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {V : Type u} {E : Type v} [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] [dE : DecidableEq E] (ends : E → V × V) (a b c : V)
    (θ : E → ℝ) (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    (∀ s, 0 ≤ R.readout () ⟨V,E,hV,dV,hE,dE,ends,a,b,c,θ⟩ s) ∧
      ∑ s, R.readout () ⟨V,E,hV,dV,hE,dE,ends,a,b,c,θ⟩ s = 1
private theorem rejected : ¬ arena.{u,v}.Law bad := by
  intro h
  have hh := (h (fun x : PEmpty.{v+1} => (nomatch x : PUnit.{u+1} × PUnit.{u+1}))
    PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) (by intro x; exact nomatch x)).2
  norm_num [bad,realize] at hh
private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  classical
  intro i
  let e : PEmpty.{v+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  refine ⟨⟨PUnit,PEmpty,inferInstance,inferInstance,inferInstance,inferInstance,
    e,PUnit.unit,PUnit.unit,PUnit.unit,fun _ => 0⟩,.all,.separate,?_⟩
  have hp (ω : PEmpty.{v+1} → Bool) :
      partition e PUnit.unit PUnit.unit PUnit.unit ω = .all := by
    simp [partition,connected]
  change law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all ≠
    law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .separate
  simp [law,hp,weight]
def registration : Registration arena.{u,v} (type_of% @law_probability.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨law_probability,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence
def register_law_probability : Contract.Registration (@law_probability.{u,v})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Probability.register_law_probability
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Probability.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => by
    letI := p.finiteVertices
    letI := p.decidableVertices
    letI := p.finiteEdges
    letI := p.decidableEdges
    exact law p.ends p.a p.b p.c p.rate) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Probability.register_law_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_law_probability
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Probability

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeLast
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Bool × (Fin 2 → Bool)) (fun _ => Fin 3) (fun _ => Bool)
def actual : Realization signature := realize _
  (fun _ p s => (Fin.cons p.1 p.2 : Fin 3 → Bool) s) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : Bool) (ω : Fin 2 → Bool), R.readout () (x,ω) 2 = ω 1
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h false (fun _ => true)
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(false,fun _ => true),0,2,?_⟩
  change (Fin.cons false (fun _ : Fin 2 => true) : Fin 3 → Bool) 0 ≠
    (Fin.cons false (fun _ : Fin 2 => true) : Fin 3 → Bool) 2
  decide +kernel
def registration : Registration arena (type_of% @cons_three_last) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cons_three_last,bad,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected
  dependence := dependence
def register_cons_three_last : Contract.Registration (@cons_three_last)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeLast.register_cons_three_last
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeLast.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => (Fin.cons p.1 p.2 : Fin 3 → Bool) s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeLast.register_cons_three_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cons_three_last
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeLast

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeMid
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Bool × (Fin 2 → Bool)) (fun _ => Fin 3) (fun _ => Bool)
def actual : Realization signature := realize _
  (fun _ p s => (Fin.cons p.1 p.2 : Fin 3 → Bool) s) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : Bool) (ω : Fin 2 → Bool), R.readout () (x,ω) 1 = ω 0
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h false (fun _ => true)
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(false,fun _ => true),0,1,?_⟩
  change (Fin.cons false (fun _ : Fin 2 => true) : Fin 3 → Bool) 0 ≠
    (Fin.cons false (fun _ : Fin 2 => true) : Fin 3 → Bool) 1
  decide +kernel
def registration : Registration arena (type_of% @cons_three_mid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cons_three_mid,bad,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected
  dependence := dependence
def register_cons_three_mid : Contract.Registration (@cons_three_mid)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeMid.register_cons_three_mid
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeMid.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => (Fin.cons p.1 p.2 : Fin 3 → Bool) s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeMid.register_cons_three_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cons_three_mid
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsThreeMid

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsTwoLast
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Bool × (Fin 1 → Bool)) (fun _ => Fin 2) (fun _ => Bool)
def actual : Realization signature := realize _
  (fun _ p s => (Fin.cons p.1 p.2 : Fin 2 → Bool) s) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : Bool) (ω : Fin 1 → Bool), R.readout () (x,ω) 1 = ω 0
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h false (fun _ => true)
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(false,fun _ => true),0,1,?_⟩
  change (Fin.cons false (fun _ : Fin 1 => true) : Fin 2 → Bool) 0 ≠
    (Fin.cons false (fun _ : Fin 1 => true) : Fin 2 → Bool) 1
  decide +kernel
def registration : Registration arena (type_of% @cons_two_last) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cons_two_last,bad,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected
  dependence := dependence
def register_cons_two_last : Contract.Registration (@cons_two_last)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsTwoLast.register_cons_two_last
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsTwoLast.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => (Fin.cons p.1 p.2 : Fin 2 → Bool) s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsTwoLast.register_cons_two_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cons_two_last
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.ConsTwoLast

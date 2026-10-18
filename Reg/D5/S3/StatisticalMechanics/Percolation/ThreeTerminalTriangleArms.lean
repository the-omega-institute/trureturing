import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Complete rate-family audit attempts for the actual central triangle and arms. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev Parameters := (u : ℝ) × (v : ℝ) × (s : ℝ) × (A : ℝ) × (B : ℝ) × ℝ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters (fun _ => Mode) (fun _ => ℝ)
def actual : Realization signature := realize _
  (fun _ p => law triangleArmsEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2])
  (fun e => nomatch e)
def zero : Realization signature := realize _ (fun _ _ _ => 0) (fun e => nomatch e)
def negative : Realization signature := realize _
  (fun _ _ s => if s = .ab ∨ s = .bc then 1 else 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0,0,0,0,0⟩,.separate,.all,?_⟩
  change law triangleArmsEnds 0 1 2 ![0,0,0,0,0,0] .separate ≠
    law triangleArmsEnds 0 1 2 ![0,0,0,0,0,0] .all
  rw [triangle_arms_law]
  norm_num
abbrev formula (u v s A B C : ℝ) (mode : Mode) : ℝ :=
  let U := u+(1-u)*s*v
  let V := v+(1-v)*u*s
  let W := s+(1-s)*u*v
  let K := u*v+u*s+v*s-2*u*v*s
  match mode with
  | .separate => 1-A*B*U-B*C*V-A*C*W+2*A*B*C*K
  | .ab => A*B*U-A*B*C*K
  | .bc => B*C*V-A*B*C*K
  | .all => A*B*C*K
  | .ac => A*C*W-A*B*C*K
abbrev lawArena : Arena where
  signature := signature
  Law R := ∀ u v s A B C : ℝ,
    R.readout () ⟨u,v,s,A,B,C⟩ = formula u v s A B C
private theorem law_rejected : ¬ lawArena.Law zero := by
  intro h
  have hh := congrFun (h 0 0 0 0 0 0) .separate
  norm_num [zero,realize,formula] at hh
def lawRegistration : Registration lawArena (type_of% @triangle_arms_law) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨triangle_arms_law,zero,law_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual zero law_rejected
  dependence := dependence
abbrev factorArena : Arena where
  signature := signature
  Law R := ∀ u v s A B C : ℝ,
    let K := u*v+u*s+v*s-2*u*v*s
    let L := (1-s)*(u+v-u*v)
    let Z₀ := s*(1-u)*(1-v)
    let S := A*C
    R.readout () ⟨u,v,s,A,B,C⟩ .ac = S*(Z₀+(1-B)*K) ∧
    delta (law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C]) =
      B^2*S*Z₀*(L+(1-S)*K)+B*(1-B)*S*K*(1-S*(Z₀+K))
private theorem factor_rejected : ¬ factorArena.Law zero := by
  intro h
  have hh := (h 0 0 1 1 0 1).1
  norm_num [zero,realize] at hh
def factorRegistration : Registration factorArena (type_of% @triangle_arms_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨triangle_arms_factorization,zero,factor_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual zero factor_rejected
  dependence := dependence
abbrev boundArena : Arena where
  signature := signature
  Law R := ∀ u v s A B C : ℝ,
    u ∈ Set.Icc 0 1 → v ∈ Set.Icc 0 1 → s ∈ Set.Icc 0 1 →
    A ∈ Set.Icc 0 1 → B ∈ Set.Icc 0 1 → C ∈ Set.Icc 0 1 →
    0 ≤ delta (R.readout () ⟨u,v,s,A,B,C⟩) ∧
    delta (law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C]) ≤
      2*law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C] .ac
private theorem bound_rejected : ¬ boundArena.Law negative := by
  intro h
  have hh := (h 0 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [negative,realize,delta] at hh
def boundRegistration : Registration boundArena (type_of% @triangle_arms_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨triangle_arms_bound,negative,bound_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual negative bound_rejected
  dependence := dependence

def register_triangle_arms_law : Contract.Registration (@triangle_arms_law) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.register_triangle_arms_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.lawRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨lawArena⟩
  objectArena := .source ⟨lawArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source lawArena ⟨lawRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => law triangleArmsEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2])
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_triangle_arms_factorization : Contract.Registration (@triangle_arms_factorization) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.register_triangle_arms_factorization
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.factorRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨factorArena⟩
  objectArena := .source ⟨factorArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source factorArena ⟨factorRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => law triangleArmsEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2])
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_triangle_arms_bound : Contract.Registration (@triangle_arms_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.register_triangle_arms_bound
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.boundRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source boundArena ⟨boundRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => law triangleArmsEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2])
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Configurations
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Fin 6 → Bool) (fun _ => Mode)
def actual : Realization signature := realize _
  (fun _ _ ω => partition triangleArmsEnds 0 1 2 ω) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => .all) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ω : Fin 6 → Bool, R.readout () () ω =
    if ω 3 && ω 4 && (ω 0 || (ω 2 && ω 1)) then
      (if ω 4 && ω 5 && (ω 1 || (ω 0 && ω 2)) then .all else .ab)
    else if ω 4 && ω 5 && (ω 1 || (ω 0 && ω 2)) then .bc
    else if ω 3 && ω 5 && (ω 2 || (ω 0 && ω 1)) then .ac else .separate
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h (fun _ => false)
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),(fun _ => false),(fun _ => true),?_⟩
  change partition triangleArmsEnds 0 1 2 (fun _ => false) ≠
    partition triangleArmsEnds 0 1 2 (fun _ => true)
  decide +kernel

def registration : Registration arena (type_of% @arms_partition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨arms_partition,bad,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad rejected
  dependence := dependence

def register_arms_partition : Contract.Registration (@arms_partition)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.Configurations.register_arms_partition
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.Configurations.registration
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
    (fun _ _ ω => partition triangleArmsEnds 0 1 2 ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Configurations

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms

open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.register_triangle_arms_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_triangle_arms_law
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.register_triangle_arms_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_triangle_arms_factorization
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.register_triangle_arms_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_triangle_arms_bound

open Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.Configurations in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.Configurations.register_arms_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_arms_partition

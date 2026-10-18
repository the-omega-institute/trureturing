import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Actual source-law registrations for the full four-edge independent rate family. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℝ × ℝ × ℝ × ℝ) (fun _ => Mode) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ p => law pendantEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2]) (fun e => nomatch e)
def zero : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def negative : Realization signature := realize signature
  (fun _ _ s => if s = .ab ∨ s = .bc then 1 else 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0,0,0,0),Mode.separate,Mode.all,?_⟩
  change law pendantEnds 0 1 2 ![0,0,0,0] .separate ≠
    law pendantEnds 0 1 2 ![0,0,0,0] .all
  rw [pendant_law]
  norm_num

abbrev formula (u v s A : ℝ) (mode : Mode) : ℝ := match mode with
  | .separate => (1-A)*(1-v)*(1-u*s)+A*(1-u)*(1-v)*(1-s)
  | .ab => A*u*(1-v)*(1-s)
  | .bc => (1-A)*(v+u*s-v*u*s)+A*v*(1-u)*(1-s)
  | .all => A*(u*v+u*s+v*s-2*u*v*s)
  | .ac => A*s*(1-u)*(1-v)

abbrev lawArena : Arena where
  signature := signature
  Law R := ∀ u v s A : ℝ, R.readout () (u,v,s,A) = formula u v s A

private theorem law_rejected : ¬ lawArena.Law zero := by
  intro h
  have hh := congrFun (h 0 0 0 0) .separate
  norm_num [zero,realize,formula] at hh

def lawRegistration : Registration lawArena (type_of% @pendant_law) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pendant_law,zero,law_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual zero law_rejected
  dependence := dependence

abbrev determinantArena : Arena where
  signature := signature
  Law R := ∀ u v s A : ℝ, delta (R.readout () (u,v,s,A)) =
    law pendantEnds 0 1 2 ![u,v,s,A] .ac *
      ((1-s)*(u+v-u*v)+(1-A)*(u*v+u*s+v*s-2*u*v*s))

private theorem determinant_rejected : ¬ determinantArena.Law zero := by
  intro h
  have hh := h (1/2) (1/2) (1/2) (1/2)
  rw [pendant_law] at hh
  norm_num [zero,realize,delta] at hh

def determinantRegistration : Registration determinantArena (type_of% @pendant_determinant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pendant_determinant,zero,determinant_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual zero determinant_rejected
  dependence := dependence

abbrev boundArena : Arena where
  signature := signature
  Law R := ∀ u v s A : ℝ, u ∈ Set.Icc 0 1 → v ∈ Set.Icc 0 1 →
    s ∈ Set.Icc 0 1 → A ∈ Set.Icc 0 1 →
    0 ≤ delta (R.readout () (u,v,s,A)) ∧
    delta (law pendantEnds 0 1 2 ![u,v,s,A]) ≤ 2*law pendantEnds 0 1 2 ![u,v,s,A] .ac

private theorem bound_rejected : ¬ boundArena.Law negative := by
  intro h
  have hh := (h 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [negative,realize,delta] at hh

def boundRegistration : Registration boundArena (type_of% @pendant_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pendant_bound,negative,bound_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual negative bound_rejected
  dependence := dependence

abbrev sharpFormulaArena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, R.readout () (1-t,1-t,t,t) .ac = t^4 ∧
    delta (law pendantEnds 0 1 2 ![1-t,1-t,t,t]) = t^4*(2-4*t+4*t^2-4*t^3+2*t^4)

private theorem formula_rejected : ¬ sharpFormulaArena.Law zero := by
  intro h
  have hh := (h 1).1
  norm_num [zero,realize] at hh

def sharpFormulaRegistration : Registration sharpFormulaArena (type_of% @pendant_sharp_formula) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pendant_sharp_formula,zero,formula_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual zero formula_rejected
  dependence := dependence

def register_pendant_law : Contract.Registration (@pendant_law) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.register_pendant_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.lawRegistration
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
    (fun _ p => law pendantEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_pendant_determinant : Contract.Registration (@pendant_determinant) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.register_pendant_determinant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.determinantRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨determinantArena⟩
  objectArena := .source ⟨determinantArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source determinantArena ⟨determinantRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => law pendantEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_pendant_bound : Contract.Registration (@pendant_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.register_pendant_bound
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.boundRegistration
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
    (fun _ p => law pendantEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_pendant_sharp_formula : Contract.Registration (@pendant_sharp_formula) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.register_pendant_sharp_formula
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.sharpFormulaRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sharpFormulaArena⟩
  objectArena := .source ⟨sharpFormulaArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source sharpFormulaArena ⟨sharpFormulaRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => law pendantEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Sharpness
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Fin 4 → ℝ) (fun _ => Mode) (fun _ => ℝ)
def actual : Realization signature := realize _
  (fun _ θ => law pendantEnds 0 1 2 θ) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ θ : Fin 4 → ℝ,
    (openGraph pendantEnds (fun _ => true)).Connected ∧
    IsCactus (openGraph pendantEnds (fun _ => true)) ∧
    (∀ e, 0 < θ e ∧ θ e < 1) ∧
    0 < R.readout () θ .ac ∧ (2-ε)*R.readout () θ .ac < delta (R.readout () θ)
private theorem rejected : ¬ arena.Law bad := by
  intro h
  obtain ⟨θ,_,_,_,hp,_⟩ := h 1 (by norm_num)
  norm_num [bad,realize] at hp
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨![0,0,0,0],.separate,.all,?_⟩
  change law pendantEnds 0 1 2 ![0,0,0,0] .separate ≠ law pendantEnds 0 1 2 ![0,0,0,0] .all
  rw [pendant_law]
  norm_num
def registration : Registration arena (type_of% @pendant_sharpness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pendant_sharpness,bad,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad rejected
  dependence := dependence
def register_pendant_sharpness : Contract.Registration (@pendant_sharpness)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Sharpness.register_pendant_sharpness
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Sharpness.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ θ => law pendantEnds 0 1 2 θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Sharpness

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Topology
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit
noncomputable section
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => SimpleGraph (Fin 4)) (fun _ => Bool)
def actual : Realization signature := realize _
  (fun _ _ G => @decide (IsCactus G) (Classical.propDecidable _)) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (openGraph pendantEnds (fun _ => true)) = true
private def p : (⊤ : SimpleGraph (Fin 4)).Walk 0 0 :=
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 0 1)
    (.cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 1 2) (.cons (by decide) .nil))
private def q : (⊤ : SimpleGraph (Fin 4)).Walk 0 0 :=
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 0 1)
    (.cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 1 3) (.cons (by decide) .nil))
private theorem not_cactus_top : ¬ IsCactus (⊤ : SimpleGraph (Fin 4)) := by
  intro h
  have hp : p.IsCycle := by norm_num [Walk.isCycle_def,Walk.isTrail_def,p,Sym2.eq_iff]
  have hq : q.IsCycle := by norm_num [Walk.isCycle_def,Walk.isTrail_def,q,Sym2.eq_iff]
  have hne : p.edges.toFinset ≠ q.edges.toFinset := by decide
  have hh := h 0 0 p q hp hq hne
  norm_num [p,q] at hh
private theorem rejected : ¬ arena.Law bad := by simp [arena,bad,realize]
private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨(),openGraph pendantEnds (fun _ => true),⊤,?_⟩
  change decide (IsCactus (openGraph pendantEnds (fun _ => true))) ≠
    decide (IsCactus (⊤ : SimpleGraph (Fin 4)))
  simp [pendant_cactus,not_cactus_top]
def registration : Registration arena (type_of% @pendant_cactus) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [actual,realize,decide_eq_true_eq] using pendant_cactus,bad,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad rejected
  dependence := dependence
def register_pendant_cactus : Contract.Registration (@pendant_cactus)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Topology.register_pendant_cactus
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Topology.registration
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
    (fun _ _ G => @decide (IsCactus G) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.Topology

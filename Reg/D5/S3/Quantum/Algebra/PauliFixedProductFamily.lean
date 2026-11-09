import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.PauliFixedProductFamily
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily

open scoped TensorProduct InnerProductSpace
noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ t => reportSquared t) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ t : ℝ, A.readout () () t=288*t^2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected,realize] at hh

def family : Registration arena (type_of% (@full_report)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_report,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual,realize,full_report]

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@full_report) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.PauliFixedProductFamily.full_report.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => reportSquared t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PauliFixedProductFamily
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration


namespace Scaling
abbrev signature : Signature where
  Params := ℝ × V × V
  State _ := V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p Y => E p.1 p.2.1 p.2.2 Y) (fun a => nomatch a)
def rejected : Realization signature := realize signature
  (fun _ _ _ => e 0 ⊗ₜ[ℝ] e 0) (fun a => nomatch a)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (t : ℝ) (H X Y : V), A.readout () (t,H,X) Y=t • E 1 H X Y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : e 0 ⊗ₜ[ℝ] e 0=(0 : V) := by
    simpa [rejected,realize] using h 0 0 0 0
  have hh := congrArg (fun v : V => ‖v‖) hz
  simp only [TensorProduct.norm_tmul,norm_zero] at hh
  have he : ‖e (0 : Fin 4)‖=1 := by simp [e]
  rw [he] at hh
  norm_num at hh

private theorem actual_nonzero : ∃ H X Y : V, E 1 H X Y≠0 := by
  by_contra! hn
  have hz : reportSquared 1=0 := by simp [reportSquared,hn]
  have hh := full_report 1
  rw [hz] at hh
  norm_num at hh

def family : Registration arena (type_of% (@residual_scaling)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨residual_scaling,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    obtain ⟨H,X,Y,hY⟩ := actual_nonzero
    refine ⟨(1,H,X),0,Y,?_⟩
    have hz : E 1 H X 0=0 := by simp [E]
    simpa [actual,realize,hz] using Ne.symm hY

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@residual_scaling) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.PauliFixedProductFamily.residual_scaling.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily.Scaling.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p Y => E p.1 p.2.1 p.2.2 Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PauliFixedProductFamily
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Scaling

namespace CompleteContract
abbrev arena : Arena where
  signature := signature
  Law A := ∀ t : ℝ,
    Module.finrank ℝ J=4 ∧ Module.finrank ℝ V=16 ∧
    (∀ i : Fin 4, localBasis i=e i) ∧
    (∀ i j : Fin 4, jointBasis (i,j)=e i ⊗ₜ e j) ∧
    (∀ a b : J, S a b=S b a) ∧ (∀ a : J, S (e 0) a=a) ∧
    (∀ a b c : J, inner ℝ (S a b) c=inner ℝ a (S b c)) ∧
    (∀ a b c : J, D t a (S b c)=S (D t a b) c+S b (D t a c)) ∧
    D t (e 1) (e 2)=e 3 ∧
    (∀ X Y : V, M X Y=M Y X) ∧
    (∀ X : V, M (e 0 ⊗ₜ e 0) X=X) ∧
    (∀ X Y Z : V, inner ℝ (M X Y) Z=inner ℝ X (M Y Z)) ∧
    (∀ X : V, 0 ≤ inner ℝ X X ∧ (inner ℝ X X=0 ↔ X=0)) ∧
    (∀ a b c d : J,
      M (a ⊗ₜ e 0) (c ⊗ₜ d)=S a c ⊗ₜ d ∧
      M (e 0 ⊗ₜ b) (c ⊗ₜ d)=c ⊗ₜ S b d ∧
      Gamma t (a ⊗ₜ b) (c ⊗ₜ e 0)=D t a c ⊗ₜ b ∧
      Gamma t (a ⊗ₜ b) (e 0 ⊗ₜ d)=a ⊗ₜ D t b d) ∧
    A.readout () () t=288*t^2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases h 0 with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hr⟩
  norm_num [rejected,realize] at hr

def family : Registration arena (type_of% (@family_contract)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨family_contract,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual,realize,full_report]

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@family_contract) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.PauliFixedProductFamily.family_contract.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily.CompleteContract.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => reportSquared t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PauliFixedProductFamily
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CompleteContract
end Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily

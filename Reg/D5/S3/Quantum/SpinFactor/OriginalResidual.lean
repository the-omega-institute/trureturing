import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.SpinFactor.OriginalResidual

/-! Source-equivalent equality readouts for the residual statements.

Factories retain every original premise. Their relation witness is an explicit
parameter, not a closed original-P2/PB instance. `sourceSelection = none` carries
no raw source-selector binding evidence. These terms supply no validation claim.
-/

noncomputable section

open _root_.D5.S3.Quantum.SpinFactor.OriginalDContract
open _root_.D5.S3.Quantum.SpinFactor.OriginalResidual
open _root_.D5.S3.Geometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.SpinFactor.OriginalResidual

private abbrev eqSignature (α : Type) : Signature where
  Params := Unit
  State _ := α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := α → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual (α : Type) : Realization (eqSignature α) :=
  realize (eqSignature α) (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected (α : Type) : Realization (eqSignature α) :=
  realize (eqSignature α) (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem eqSensitivity (α : Type)
    (law : Realization (eqSignature α) → Prop) (hbad : ¬ law (rejected α)) :
    Sensitivity ⟨eqSignature α, law⟩ (actual α) := by
  refine ⟨fun i => ⟨rejected α, ?_, rfl, hbad⟩, fun e => nomatch e⟩
  intro j hji
  exact (hji (Subsingleton.elim j i)).elim

private theorem eqDependence (α : Type) (x y : α) (hxy : x ≠ y) :
    ObservationalDependence (eqSignature α) (actual α) := by
  intro i
  refine ⟨(), x, y, ?_⟩
  intro h
  have hyx : y = x := Eq.mp (congrFun h x) rfl
  exact hxy hyx.symm

private theorem element_ne : (0 : E) ≠ unit := by
  intro h
  have hs := congrArg Prod.fst h
  norm_num [unit] at hs

private def x₀ : Vec := ![1, 0, 0]
private def y₀ : Vec := ![0, 1, 0]

namespace Cayley

abbrev arena : Arena where
  signature := eqSignature E
  Law O := ∀ (D : E → E → E) (_ : P2 D) (_ : PB D)
    (e : ℝ) (_ : e = 1 ∨ e = -1)
    (_ : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (s t : ℝ) (x y q : Vec), dot q x = t → dot q y = -s →
      O.readout () () (residual D e s t x y)
        (residual D e s t (-cayleyImage e q x) (-cayleyImage e q y))

private theorem rejected_law (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (e₀ : ℝ) (he₀ : e₀ = 1 ∨ e₀ = -1)
    (hpure₀ : ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e₀ • cross x y)) :
    ¬ arena.Law (rejected E) := by
  intro h
  exact h D₀ hP₀ hPB₀ e₀ he₀ hpure₀ 0 0 0 0 0 (by simp [dot]) (by simp [dot])

def family (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (e₀ : ℝ) (he₀ : e₀ = 1 ∨ e₀ = -1)
    (hpure₀ : ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e₀ • cross x y)) :
    Registration arena (type_of% (@cayley_residual)) where
  actual := actual E
  bridge := Iff.rfl
  variation := ⟨@cayley_residual, rejected E, rejected_law D₀ hP₀ hPB₀ e₀ he₀ hpure₀⟩
  sensitivity := eqSensitivity E arena.Law (rejected_law D₀ hP₀ hPB₀ e₀ he₀ hpure₀)
  dependence := eqDependence E 0 unit element_ne

def registration (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (e₀ : ℝ) (he₀ : e₀ = 1 ∨ e₀ = -1)
    (hpure₀ : ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e₀ • cross x y)) :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@cayley_residual) (Realization (eqSignature E)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalResidual.cayley_residual.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalResidual.Cayley.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family D₀ hP₀ hPB₀ e₀ he₀ hpure₀⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (eqSignature E) (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some E
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cayley

namespace FullCircle

abbrev arena : Arena where
  signature := eqSignature E
  Law O := ∀ (D : E → E → E) (_ : P2 D) (_ : PB D)
    (e : ℝ) (_ : e = 1 ∨ e = -1)
    (_ : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (s t : ℝ) (x y : Vec), cross x y ≠ 0 →
      ∀ (R : TwoAxisFiniteRotation.Orthogonal),
        R ∈ TwoAxisFiniteRotation.axisCircle
          (WithLp.toLp 2 (s • x + t • y + e • cross x y)) →
        O.readout () () (residual D e s t (rotate R x) (rotate R y))
          (residual D e s t x y)

private theorem rejected_law (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (e₀ : ℝ) (he₀ : e₀ = 1 ∨ e₀ = -1)
    (hpure₀ : ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e₀ • cross x y)) :
    ¬ arena.Law (rejected E) := by
  intro h
  apply h D₀ hP₀ hPB₀ e₀ he₀ hpure₀ 0 0 x₀ y₀ _ 1
    (TwoAxisFiniteRotation.axisCircle _).one_mem
  intro hh
  have hi := congrFun hh 2
  norm_num [x₀, y₀, cross] at hi

def family (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (e₀ : ℝ) (he₀ : e₀ = 1 ∨ e₀ = -1)
    (hpure₀ : ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e₀ • cross x y)) :
    Registration arena (type_of% (@local_full_circle)) where
  actual := actual E
  bridge := Iff.rfl
  variation := ⟨@local_full_circle, rejected E, rejected_law D₀ hP₀ hPB₀ e₀ he₀ hpure₀⟩
  sensitivity := eqSensitivity E arena.Law (rejected_law D₀ hP₀ hPB₀ e₀ he₀ hpure₀)
  dependence := eqDependence E 0 unit element_ne

def registration (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (e₀ : ℝ) (he₀ : e₀ = 1 ∨ e₀ = -1)
    (hpure₀ : ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e₀ • cross x y)) :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@local_full_circle) (Realization (eqSignature E)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalResidual.local_full_circle.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalResidual.FullCircle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family D₀ hP₀ hPB₀ e₀ he₀ hpure₀⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (eqSignature E) (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some E
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end FullCircle

namespace SaturatedSupport

abbrev arena : Arena where
  signature := eqSignature ℝ
  Law O := ∀ (e δ Z : ℝ), (e = 1 ∨ e = -1) → 0 ≤ Z →
    ∀ (w p : Vec), w ≠ 0 → dot w p = 0 →
      (∀ n : Vec, dot n n = 1 → |δ + e * dot n w| + Z ≤ vnorm (w + cross n p)) →
      O.readout () () δ 0 ∧ O.readout () () Z 0

private theorem rejected_law : ¬ arena.Law (rejected ℝ) := by
  intro h
  have hx : x₀ ≠ 0 := by
    intro hz
    have hi := congrFun hz 0
    norm_num [x₀] at hi
  have hb (n : Vec) (hn : dot n n = 1) :
      |(0 : ℝ) + 1 * dot n x₀| + 0 ≤ vnorm (x₀ + cross n 0) := by
    simp [x₀, dot, cross, vnorm, dotProduct, Fin.sum_univ_three]
    apply abs_le.mpr
    simp only [dot, dotProduct, Fin.sum_univ_three] at hn
    constructor <;> nlinarith [sq_nonneg (n 1), sq_nonneg (n 2)]
  exact (h 1 0 0 (Or.inl rfl) (le_refl 0) x₀ 0 hx (by simp [dot]) hb).1

def family : Registration arena (type_of% (@saturated_support_zero)) where
  actual := actual ℝ
  bridge := Iff.rfl
  variation := ⟨@saturated_support_zero, rejected ℝ, rejected_law⟩
  sensitivity := eqSensitivity ℝ arena.Law rejected_law
  dependence := eqDependence ℝ 0 1 (by norm_num)

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@saturated_support_zero) (Realization (eqSignature ℝ)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalResidual.saturated_support_zero.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalResidual.SaturatedSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (eqSignature ℝ) (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end SaturatedSupport

namespace AllInputs

abbrev arena : Arena where
  signature := eqSignature E
  Law O := ∀ (D : E → E → E) (_ : P2 D) (_ : PB D),
    (∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y)) →
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ (s t : ℝ) (x y : Vec),
      O.readout () () (D (s, x) (t, y)) (0, e • cross x y)

private theorem rejected_law (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (hpure₀ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e • cross x y)) :
    ¬ arena.Law (rejected E) := by
  intro h
  obtain ⟨e, he, hf⟩ := h D₀ hP₀ hPB₀ hpure₀
  exact hf 0 0 0 0

def family (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (hpure₀ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e • cross x y)) :
    Registration arena (type_of% (@all_inputs_of_pure)) where
  actual := actual E
  bridge := Iff.rfl
  variation := ⟨@all_inputs_of_pure, rejected E, rejected_law D₀ hP₀ hPB₀ hpure₀⟩
  sensitivity := eqSensitivity E arena.Law (rejected_law D₀ hP₀ hPB₀ hpure₀)
  dependence := eqDependence E 0 unit element_ne

def registration (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀)
    (hpure₀ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ x y : Vec, D₀ (0, x) (0, y) = (0, e • cross x y)) :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@all_inputs_of_pure) (Realization (eqSignature E)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalResidual.all_inputs_of_pure.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalResidual.AllInputs.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family D₀ hP₀ hPB₀ hpure₀⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (eqSignature E) (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some E
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end AllInputs

end Reg.D5.S3.Quantum.SpinFactor.OriginalResidual

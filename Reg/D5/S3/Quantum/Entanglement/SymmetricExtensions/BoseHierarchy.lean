import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy
import Reg.Support.SingleDependentReadout

/-! The full GNP telescope with its actual Parrilo-polar readout, including
zero and negative one-dimensional intervention states. -/

namespace Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy

open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy
open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS
open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI
open _root_.D5.S3.QuadraticForms.ParriloHierarchy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix MvPolynomial
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure Parameters where
  r : ℕ
  n : ℕ
  root : Fin r
  leaf : Fin r
  distinct : root ≠ leaf

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Matrix (Fin p.n) (Fin p.n) ℝ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ p P => parriloPolar (p.r-2) P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n r : ℕ} (root leaf : Fin r) (hne : root ≠ leaf)
    (P : Matrix (Fin n) (Fin n) ℝ), P.IsSymm →
    (ldui P ∈ adaptedDPS root leaf hne ↔ R.readout () ⟨r,n,root,leaf,hne⟩ P)

private lemma zero_polar : parriloPolar 0 (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro M hM
  simp

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (gnp_characterization (0 : Fin 2) 1 (by decide)
    (0 : Matrix (Fin 1) (Fin 1) ℝ) (by simp)).mpr zero_polar
  exact (h (0 : Fin 2) 1 (by decide) 0 (by simp)).mp hzero

private lemma negative_not_polar :
    ¬ parriloPolar 0 (-1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro h
  have hone : (1 : Matrix (Fin 1) (Fin 1) ℝ) ∈ K 0 := by
    constructor
    · simp
    · change IsSumSq (polynomial 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
      have he : polynomial 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) =
          (X 0 * X 0) * (X 0 * X 0) := by
        simp [polynomial,liftedForm,pow_two]
      rw [he]
      exact IsSumSq.mul_self _
  have hp := h 1 hone
  norm_num at hp

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2,1,0,1,by decide⟩,0,-1,?_⟩
  intro he
  exact negative_not_polar (Eq.mp he zero_polar)

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy.gnp_characterization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy.gnp_characterization,
    rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy.gnp_characterization)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p P => parriloPolar (p.r-2) P)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg[1]"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy

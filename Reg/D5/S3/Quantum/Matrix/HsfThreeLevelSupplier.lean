import D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope source-binding attempts for the three-level supplier and
PD Sylvester rigidity. Source selection and escape evidence are unfinished:
https://github.com/the-omega-institute/trureturing/issues/23103.
These registrations do not assert declared_validated. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
noncomputable section
universe u

namespace Supplier

private abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ), (∀ i, 0 < p i) →
    ∀ (S : Matrix n n ℂ), S.PosSemidef →
    ∀ (Z : Matrix n n ℂ), Z.IsHermitian →
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P^3 + t • (CFC.rpow P (3/2 : ℝ) * S *
        CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    W.readout () () (0 ≤ (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z^2 -
      (5/48 : ℝ) • (B 1)^3).trace.re)

private theorem bridge :
    (type_of% (@actual_threeLevel_supplier.{u})) ↔ arena.Law actual := by
  rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (ULift.{u} (Fin 0)) (fun i => nomatch i.down)
    (fun _ => 1) (by intro i; norm_num) 0 (by simp) 0 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  simp [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@actual_threeLevel_supplier.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@actual_threeLevel_supplier.{u}), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration
    (@actual_threeLevel_supplier.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelSupplier.Supplier.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelSupplier.Supplier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Supplier

namespace PDSylvester

private abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W :=     ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (S : Matrix n n ℂ) (hS : S.PosDef),
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let X : Matrix n n ℂ := fun i j =>
      (HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level j)) : ℂ)*S i j
    let Q : Matrix n n ℂ := fun i j => ∑ k,
      (((2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level k))*
        HsfLocalSpectrumSupplier.spectralTau (p (level k)) (p (level j))+
        3*HsfLocalSpectrumSupplier.spectralKernel (p (level i)) (p (level j))
          (p (level k)) : ℝ) : ℂ)*S i k*S k j
    let D := Q-X^2
    W.readout () () (X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      0 ≤ 4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re ∧
      ((4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re = 0) ↔ P*S = S*P))

private theorem bridge :
    (type_of% (@actual_threeLevel_PD_sylvester.{u})) ↔ arena.Law actual := by
  rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (ULift.{u} (Fin 0)) (fun i => nomatch i.down)
    (fun _ => 1) (by intro i; norm_num) 0 (by simp) 

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  simp [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@actual_threeLevel_PD_sylvester.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@actual_threeLevel_PD_sylvester.{u}), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration
    (@actual_threeLevel_PD_sylvester.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelSupplier.PDSylvester.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelSupplier.PDSylvester.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end PDSylvester

end Reg.D5.S3.Quantum.Matrix.HsfThreeLevelSupplier

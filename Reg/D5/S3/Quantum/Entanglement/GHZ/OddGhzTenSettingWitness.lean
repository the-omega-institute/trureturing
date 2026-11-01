import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations of public statements in the mirrored owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v
open _root_.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open scoped MatrixOrder ComplexOrder

namespace Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Ensemble
/-- Read the total weight of the finite ensemble. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun m => Fin m → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ m p => ∑ i : Fin m, p i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (ρ : DensityState ι),
    ∃ (m : ℕ) (p : Fin m → ℝ) (ψ : Fin m → ι → ℂ),
      (∀ i, 0 ≤ p i) ∧ R.readout () m p = 1 ∧
      (∀ i, star (ψ i) ⬝ᵥ ψ i = 1) ∧
      CStarMatrix.ofMatrix.symm ρ.1 =
        ∑ i, (p i : ℂ) • Matrix.vecMulVec (ψ i) (star (ψ i))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let ρ : DensityState (ULift.{u} Unit) := ⟨1, zero_le_one, by
    change Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 1
    simp [Matrix.trace]⟩
  obtain ⟨m, p, ψ, hp, ht, hψ, hr⟩ := h ρ
  change (0 : ℝ) = 1 at ht
  exact zero_ne_one ht
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @density_ensemble) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@density_ensemble, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@density_ensemble) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Ensemble.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Ensemble.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m p => ∑ i : Fin m, p i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print density_ensemble
#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Ensemble

namespace Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Quadratic
/-- Read the real part of the scaled quadratic value. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ z => z.re + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (g : ι → ℂ) (r : ℝ) (A : Matrix ι ι ℂ),
    R.readout () () (star g ⬝ᵥ (((r : ℂ) • A) *ᵥ g)) =
      r * (star g ⬝ᵥ (A *ᵥ g)).re
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (ι := ULift.{u} Unit) 0 0 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @quadratic_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quadratic_smul, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quadratic_smul) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Quadratic.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Quadratic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print quadratic_smul
#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Quadratic

namespace Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Overlap
/-- Read the squared modulus of the complex overlap. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ z => Complex.normSq z + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (f g : ι → ℂ),
    R.readout () () (star f ⬝ᵥ g) = Complex.normSq (star g ⬝ᵥ f)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (ι := ULift.{u} Unit) 0 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @normSq_overlap_comm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normSq_overlap_comm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normSq_overlap_comm) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Overlap.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Overlap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print normSq_overlap_comm
#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.Overlap

namespace Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.GhzOverlap
/-- Read the squared modulus of the GHZ overlap. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ z => Complex.normSq z + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (v : Fin d × Fin d × Fin d → ℂ),
    R.readout () () (star (ghz d) ⬝ᵥ v) =
      (1 / (d : ℝ)) * Complex.normSq (∑ i, v (i, i, i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d := 0) 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @ghz_overlap_normSq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ghz_overlap_normSq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ghz_overlap_normSq) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.GhzOverlap.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.GhzOverlap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print ghz_overlap_normSq
#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.GhzOverlap

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.DiamondSpinBounds
import Reg.Support.DependentFamily

/-! Source-bound observation of the native pair-order coefficient. -/

namespace Reg.D5.S3.Quantum.SpinChains.DiamondSpinBounds

open _root_.D5.S3.Quantum.SpinChains.DiamondSpinBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jz)
open _root_.D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation (siteOperator)
open _root_.D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (raising_entry)
open Matrix
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => (S : ℂ)^2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep all native relations and every original telescope unchanged. -/
abbrev arena : Arena where
  signature := signature
  Law R := (∀ (S : ℕ) (hS : 1 ≤ S) (i j : Fin 4) (hij : i ≠ j),
    (R.readout () () S • (1 : Operator S) - dot S i j).PosSemidef) ∧
  (∀ (S : ℕ) (x : Configuration S),
    0 < binomialProductReal S x) ∧
  (∀ (S : ℕ) (x : Configuration S),
    binomialProduct S x = (binomialProductReal S x : ℂ)) ∧
  (∀ {S : ℕ} (Q A B : Operator S),
    Q * (A * B) - (A * B) * Q = (Q * A - A * Q) * B + A * (Q * B - B * Q)) ∧
  (∀ (S : ℕ),
    hamiltonian S = ∑ e ∈ edges,
      (raising S e.1 * lowering S e.2 + lowering S e.1 * raising S e.2)) ∧
  (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (lowering S i *ᵥ binomialProduct S) x =
      ((x i).val : ℂ) * binomialProduct S x) ∧
  (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * raising S i - raising S i * totalLowering S =
      (-2 : ℂ) • z S i) ∧
  (∀ (n : ℕ),
    (Jplus n)ᴴ * Jplus n = diagonal (fun i : Fin (n + 1) =>
      (((i.val : ℝ) * ((n : ℝ) + 1 - i.val) : ℝ) : ℂ))) ∧
  (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * z S i - z S i * totalLowering S = lowering S i) ∧
  (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (raising S i *ᵥ binomialProduct S) x =
      ((2 * S : ℂ) - (x i).val) * binomialProduct S x) ∧
  (∀ (n : ℕ),
    Jplus n * (Jplus n)ᴴ = diagonal (fun i : Fin (n + 1) =>
      ((((i.val : ℝ) + 1) * ((n : ℝ) - i.val) : ℝ) : ℂ))) ∧
  (∀ (S : ℕ),
    (restrictedHamiltonian S).IsHermitian) ∧
  (∀ (S : ℕ),
    singletSpace S ≤ zeroWeightSpace S) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S),
    expect v (hamiltonian S) = (4 / 3 : ℂ) * expect v (isotropic S)) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ) (v : Configuration S → ℂ) (x : Configuration S),
    (site S i A *ᵥ v) x = ∑ a : Weight S, A (x i) a * v (Function.update x i a)) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A + B) = site S i A + site S i B) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ),
    (site S i A)ᴴ = site S i Aᴴ) ∧
  (∀ (S : ℕ) (i j : Fin 4) (hij : i ≠ j)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i A * site S j B = site S j B * site S i A) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A * B) = site S i A * site S i B) ∧
  (∀ (S : ℕ) (i : Fin 4) (c : ℂ)
    (A : Matrix (Weight S) (Weight S) ℂ),
    site S i (c • A) = c • site S i A) ∧
  (∀ (S : ℕ) (i : Fin 4) (v : Configuration S → ℂ) (x : Configuration S),
    (z S i *ᵥ v) x = ((S : ℂ) - (x i).val) * v x) ∧
  (∀ (S : ℕ) (i : Fin 4),
    z S i = diagonal (fun x : Configuration S => (S : ℂ) - (x i).val)) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ),
    v ∈ zeroWeightSpace S ↔
      ∀ x : Configuration S, (∑ i : Fin 4, (x i).val) ≠ 4 * S → v x = 0) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S),
    hamiltonian S *ᵥ v ∈ zeroWeightSpace S)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.1 1 (by norm_num) 0 1 (by decide)
  have hd := hbad.diag_nonneg (i := fun _ => 0)
  norm_num [rejected, realize, dot, xy, zz, z, raising, lowering, site,
    siteOperator, Matrix.mul_apply, Fintype.sum_pi_type, Fin.sum_univ_succ,
    raising_entry, Jz, Matrix.conjTranspose_apply] at hd

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ)^2 ≠ (1 : ℂ)^2
  norm_num

def source_registration : Registration arena
  ((∀ (S : ℕ) (hS : 1 ≤ S) (i j : Fin 4) (hij : i ≠ j),
    ((S : ℂ)^2 • (1 : Operator S) - dot S i j).PosSemidef) ∧
  (∀ (S : ℕ) (x : Configuration S),
    0 < binomialProductReal S x) ∧
  (∀ (S : ℕ) (x : Configuration S),
    binomialProduct S x = (binomialProductReal S x : ℂ)) ∧
  (∀ {S : ℕ} (Q A B : Operator S),
    Q * (A * B) - (A * B) * Q = (Q * A - A * Q) * B + A * (Q * B - B * Q)) ∧
  (∀ (S : ℕ),
    hamiltonian S = ∑ e ∈ edges,
      (raising S e.1 * lowering S e.2 + lowering S e.1 * raising S e.2)) ∧
  (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (lowering S i *ᵥ binomialProduct S) x =
      ((x i).val : ℂ) * binomialProduct S x) ∧
  (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * raising S i - raising S i * totalLowering S =
      (-2 : ℂ) • z S i) ∧
  (∀ (n : ℕ),
    (Jplus n)ᴴ * Jplus n = diagonal (fun i : Fin (n + 1) =>
      (((i.val : ℝ) * ((n : ℝ) + 1 - i.val) : ℝ) : ℂ))) ∧
  (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * z S i - z S i * totalLowering S = lowering S i) ∧
  (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (raising S i *ᵥ binomialProduct S) x =
      ((2 * S : ℂ) - (x i).val) * binomialProduct S x) ∧
  (∀ (n : ℕ),
    Jplus n * (Jplus n)ᴴ = diagonal (fun i : Fin (n + 1) =>
      ((((i.val : ℝ) + 1) * ((n : ℝ) - i.val) : ℝ) : ℂ))) ∧
  (∀ (S : ℕ),
    (restrictedHamiltonian S).IsHermitian) ∧
  (∀ (S : ℕ),
    singletSpace S ≤ zeroWeightSpace S) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S),
    expect v (hamiltonian S) = (4 / 3 : ℂ) * expect v (isotropic S)) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ) (v : Configuration S → ℂ) (x : Configuration S),
    (site S i A *ᵥ v) x = ∑ a : Weight S, A (x i) a * v (Function.update x i a)) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A + B) = site S i A + site S i B) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ),
    (site S i A)ᴴ = site S i Aᴴ) ∧
  (∀ (S : ℕ) (i j : Fin 4) (hij : i ≠ j)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i A * site S j B = site S j B * site S i A) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A * B) = site S i A * site S i B) ∧
  (∀ (S : ℕ) (i : Fin 4) (c : ℂ)
    (A : Matrix (Weight S) (Weight S) ℂ),
    site S i (c • A) = c • site S i A) ∧
  (∀ (S : ℕ) (i : Fin 4) (v : Configuration S → ℂ) (x : Configuration S),
    (z S i *ᵥ v) x = ((S : ℂ) - (x i).val) * v x) ∧
  (∀ (S : ℕ) (i : Fin 4),
    z S i = diagonal (fun x : Configuration S => (S : ℂ) - (x i).val)) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ),
    v ∈ zeroWeightSpace S ↔
      ∀ x : Configuration S, (∑ i : Fin 4, (x i).val) ≠ 4 * S → v x = 0) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S),
    hamiltonian S *ᵥ v ∈ zeroWeightSpace S)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_relations, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.DiamondSpinBounds.native_relations)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.DiamondSpinBounds.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.DiamondSpinBounds.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => (S : ℂ)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.DiamondSpinBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.SpinChains.DiamondSpinBounds

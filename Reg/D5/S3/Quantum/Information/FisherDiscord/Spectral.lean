import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.FisherDiscord.Spectral
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source realizations for the spectral information formulas. -/

namespace Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral
open _root_.D5.S3.Quantum.Information.FisherDiscord.Spectral
open _root_.D5.S3.Quantum.Information.FisherDiscord.Defs
open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev kernelSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def kernelActual : Realization kernelSignature :=
  realize kernelSignature (fun _ a b => pairKernel a b) (fun e => nomatch e)

def kernelRejected : Realization kernelSignature :=
  realize kernelSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev kernelArena : Arena where
  signature := kernelSignature
  Law R := ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ R.readout () a b

private theorem kernelRejected_law : ¬ kernelArena.Law kernelRejected := by
  intro h
  have he := h 0 0 (by norm_num) (by norm_num)
  norm_num [kernelRejected, realize] at he

def kernelSource : Registration kernelArena (type_of% @pairKernel_nonneg) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨pairKernel_nonneg, kernelRejected, kernelRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    kernelArena.Law kernelActual kernelRejected kernelRejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 4, ?_⟩
    norm_num [kernelActual, realize, pairKernel]

def kernelAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pairKernel_nonneg) (Realization kernelSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.kernelAuditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.kernelSource
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ a b => pairKernel a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


universe u

structure MatrixContext where
  Index : Type u
  finite : Fintype Index
  decidable : DecidableEq Index
  rho : Matrix Index Index ℂ
  observable : Matrix Index Index ℂ

abbrev matrixSignature : Signature where
  Params := MatrixContext.{u}
  State p := Matrix p.Index p.Index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def fisherActual : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L) (fun e => nomatch e)

def skewActual : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ p L => @skewWY p.Index p.finite p.decidable p.rho L) (fun e => nomatch e)

def discordActual : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L - @skewWY p.Index p.finite p.decidable p.rho p.observable) (fun e => nomatch e)

def matrixRejected : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem fisherDependence : ObservationalDependence matrixSignature.{u} fisherActual := by
  intro i
  let p : MatrixContext.{u} := ⟨ULift.{u} (Fin 1), inferInstance, inferInstance,
    (fun _ _ => 1), 0⟩
  refine ⟨p, (fun _ _ => 0), (fun _ _ => 2), ?_⟩
  norm_num [p, fisherActual, realize, fisherSLD, Matrix.trace, Matrix.diag,
    Matrix.mul_apply]

private theorem discordDependence : ObservationalDependence matrixSignature.{u} discordActual := by
  intro i
  obtain ⟨p, L₀, L₁, h⟩ := fisherDependence.{u} i
  refine ⟨p, L₀, L₁, ?_⟩
  letI := p.finite
  letI := p.decidable
  change fisherSLD p.rho L₀ ≠ fisherSLD p.rho L₁ at h
  change fisherSLD p.rho L₀ - skewWY p.rho p.observable ≠
    fisherSLD p.rho L₁ - skewWY p.rho p.observable
  exact fun he => h (sub_left_injective he)

private theorem skewDependence : ObservationalDependence matrixSignature.{u} skewActual := by
  intro i
  let w : ULift.{u} (Fin 2) → ℝ := fun j => j.down.val
  let rho : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) ℂ :=
    diagonal (fun j => (w j : ℂ))
  let p : MatrixContext.{u} := ⟨ULift.{u} (Fin 2), inferInstance, inferInstance, rho, 0⟩
  have hw : ∀ j, 0 ≤ w j := fun _ => Nat.cast_nonneg _
  have hH : Matrix.IsHermitian (fun (_ _ : ULift.{u} (Fin 2)) => (1 : ℂ)) := by
    apply Matrix.IsHermitian.ext
    intros
    simp
  have hv := skewWY_diag w hw (fun _ _ => 1) hH
  have he : skewWY rho (fun _ _ => 1) = 1 := by
    rw [hv]
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))]
    simp_rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))]
    norm_num [w, Fin.sum_univ_two]
  refine ⟨p, 0, (fun _ _ => 1), ?_⟩
  change skewWY rho 0 ≠ skewWY rho (fun _ _ => 1)
  rw [he]
  norm_num [skewWY]

namespace fisherSLD_diag
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H L : Matrix n n ℂ)
    (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L),
    R.readout () ⟨n, inferInstance, inferInstance, (diagonal (fun i => (w i : ℂ))), H⟩ L =
      (1 / 2) * ∑ i, ∑ j, (w i - w j) ^ 2 / (w i + w j) * Complex.normSq (H i j)

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) (fun _ => 0) (by intro j; exact le_rfl) 0 0 (by simpa using hL)
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @fisherSLD_diag.{u}) where
  actual := fisherActual
  bridge := Iff.rfl
  variation := ⟨@fisherSLD_diag, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := fisherDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fisherSLD_diag.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.fisherSLD_diag.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.fisherSLD_diag.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end fisherSLD_diag

namespace skewWY_diag
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H : Matrix n n ℂ)
    (hH : H.IsHermitian),
    R.readout () ⟨n, inferInstance, inferInstance, (diagonal (fun i => (w i : ℂ))), H⟩ H =
      (1 / 2) * ∑ i, ∑ j, (Real.sqrt (w i) - Real.sqrt (w j)) ^ 2 *
        Complex.normSq (H i j)

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) (fun _ => 0) (by intro j; exact le_rfl) 0 (by exact Matrix.isHermitian_zero)
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @skewWY_diag.{u}) where
  actual := skewActual
  bridge := Iff.rfl
  variation := ⟨@skewWY_diag, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := skewDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@skewWY_diag.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.skewWY_diag.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.skewWY_diag.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @skewWY p.Index p.finite p.decidable p.rho L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end skewWY_diag

namespace discord_diag
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H L : Matrix n n ℂ)
    (hH : H.IsHermitian) (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L),
    R.readout () ⟨n, inferInstance, inferInstance, (diagonal (fun i => (w i : ℂ))), H⟩ L =
      (1 / 2) * ∑ i, ∑ j, pairKernel (w i) (w j) * Complex.normSq (H i j)

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) (fun _ => 0) (by intro j; exact le_rfl) 0 0 (by exact Matrix.isHermitian_zero) (by simpa using hL)
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @discord_diag.{u}) where
  actual := discordActual
  bridge := Iff.rfl
  variation := ⟨@discord_diag, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := discordDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@discord_diag.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_diag.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_diag.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L - @skewWY p.Index p.finite p.decidable p.rho p.observable) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end discord_diag

namespace discord_nonneg_diag
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H L : Matrix n n ℂ)
    (hH : H.IsHermitian) (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L),
    0 ≤ R.readout () ⟨n, inferInstance, inferInstance, (diagonal (fun i => (w i : ℂ))), H⟩ L

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) (fun _ => 0) (by intro j; exact le_rfl) 0 0 (by exact Matrix.isHermitian_zero) (by simpa using hL)
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @discord_nonneg_diag.{u}) where
  actual := discordActual
  bridge := Iff.rfl
  variation := ⟨@discord_nonneg_diag, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := discordDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@discord_nonneg_diag.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_nonneg_diag.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_nonneg_diag.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L - @skewWY p.Index p.finite p.decidable p.rho p.observable) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end discord_nonneg_diag

namespace fisherSLD_spectral
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (ρ H L : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hL : IsSLD ρ H L),
    R.readout () ⟨n, inferInstance, inferInstance, ρ, H⟩ L = (1 / 2) * ∑ i, ∑ j,
      (hρ.isHermitian.eigenvalues i - hρ.isHermitian.eigenvalues j) ^ 2 /
        (hρ.isHermitian.eigenvalues i + hρ.isHermitian.eigenvalues j) *
      Complex.normSq ((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * H *
        (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) 0 0 0 Matrix.PosSemidef.zero hL
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @fisherSLD_spectral.{u}) where
  actual := fisherActual
  bridge := Iff.rfl
  variation := ⟨@fisherSLD_spectral, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := fisherDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fisherSLD_spectral.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.fisherSLD_spectral.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.fisherSLD_spectral.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end fisherSLD_spectral

namespace skewWY_spectral
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (ρ H : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hH : H.IsHermitian),
    R.readout () ⟨n, inferInstance, inferInstance, ρ, H⟩ H = (1 / 2) * ∑ i, ∑ j,
      (Real.sqrt (hρ.isHermitian.eigenvalues i) -
        Real.sqrt (hρ.isHermitian.eigenvalues j)) ^ 2 *
      Complex.normSq ((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * H *
        (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) 0 0 Matrix.PosSemidef.zero (by exact Matrix.isHermitian_zero)
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @skewWY_spectral.{u}) where
  actual := skewActual
  bridge := Iff.rfl
  variation := ⟨@skewWY_spectral, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := skewDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@skewWY_spectral.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.skewWY_spectral.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.skewWY_spectral.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @skewWY p.Index p.finite p.decidable p.rho L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end skewWY_spectral

namespace discord_spectral
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (ρ H L : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hH : H.IsHermitian) (hL : IsSLD ρ H L),
    R.readout () ⟨n, inferInstance, inferInstance, ρ, H⟩ L = (1 / 2) * ∑ i, ∑ j,
      pairKernel (hρ.isHermitian.eigenvalues i) (hρ.isHermitian.eigenvalues j) *
      Complex.normSq ((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * H *
        (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) 0 0 0 Matrix.PosSemidef.zero (by exact Matrix.isHermitian_zero) (by simpa using hL)
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @discord_spectral.{u}) where
  actual := discordActual
  bridge := Iff.rfl
  variation := ⟨@discord_spectral, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := discordDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@discord_spectral.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_spectral.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_spectral.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L - @skewWY p.Index p.finite p.decidable p.rho p.observable) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end discord_spectral

namespace discord_nonneg
abbrev arena : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (ρ H L : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hH : H.IsHermitian) (hL : IsSLD ρ H L),
    0 ≤ R.readout () ⟨n, inferInstance, inferInstance, ρ, H⟩ L

private theorem rejected_law : ¬ arena.{u}.Law matrixRejected := by
  intro h
  have hL : IsSLD (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) 0 0 := by
    constructor <;> simp [Matrix.IsHermitian]
  have he := h (n := ULift.{u} (Fin 1)) 0 0 0 Matrix.PosSemidef.zero (by exact Matrix.isHermitian_zero) (by simpa using hL)
  norm_num [matrixRejected, realize] at he

def source : Registration arena.{u} (type_of% @discord_nonneg.{u}) where
  actual := discordActual
  bridge := Iff.rfl
  variation := ⟨@discord_nonneg, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := discordDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@discord_nonneg.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_nonneg.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.discord_nonneg.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p L => @fisherSLD p.Index p.finite p.rho L - @skewWY p.Index p.finite p.decidable p.rho p.observable) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end discord_nonneg

end
end Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O :=
    (∀ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        O.readout () () rho ≤ (7 / 121 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (7 / 121 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 5 =>
        if ij = (0, 0) then (3 / 22 : ℂ) else (1 / 22 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (7 / 121 : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, _, hd, ha, _⟩ := result.2.2
  have hb := h.1 rho hd ha
  change (1 : ℝ) ≤ 7 / 121 at hb
  norm_num at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]
def familyRegistration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

def resultRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.familyRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity,
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity,
      name := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

abbrev raySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _m : ℕ, ℕ)
    (fun p => Fin p.1 × Fin p.2 → ℂ)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ)
def rayActual : Realization raySignature :=
  realize raySignature (fun _ _ v => normalizedRay v) (fun e => nomatch e)
def rayRejected : Realization raySignature :=
  realize raySignature (fun _ _ _ => fun _ _ => (-1 : ℂ)) (fun e => nomatch e)
abbrev rayArena : Arena where
  signature := raySignature
  Law O := ∀ {m n : ℕ} (v : Fin m × Fin n → ℂ),
    star v ⬝ᵥ v = (1 : ℂ) →
      (O.readout () ⟨m,n⟩ v).PosSemidef ∧ (normalizedRay v).trace = 1 ∧
        APPT (normalizedRay v) ∧
        (normalizedRay v * normalizedRay v).trace.re =
          (((m*n : ℕ) : ℝ) + 8) / (((m*n : ℕ) : ℝ) + 2)^2
private theorem rayRejected_law : ¬ rayArena.Law rayRejected := by
  intro h
  let v : Fin 1 × Fin 1 → ℂ := fun _ => 1
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by simp [v, dotProduct]
  have hp : (0 : ℂ) ≤ rayRejected.readout () ⟨1,1⟩ v (0,0) (0,0) := (h v hv).1.diag_nonneg
  change (0 : ℂ) ≤ (-1 : ℂ) at hp
  have hp' : (0 : ℂ) ≤ ((-1 : ℝ) : ℂ) := by simpa using hp
  have hr := Complex.zero_le_real.mp hp'
  norm_num at hr
private theorem rayActual_dependence : ObservationalDependence raySignature rayActual := by
  intro i
  refine ⟨⟨1,1⟩, 0, (fun _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h (0,0)) (0,0)
  norm_num [rayActual, realize, normalizedRay, Matrix.smul_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply] at he
def rayFamilyRegistration : Registration rayArena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalized_ray) where
  actual := rayActual
  bridge := Iff.rfl
  variation := ⟨@normalized_ray, rayRejected, rayRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity rayArena.Law rayActual rayRejected rayRejected_law
  dependence := rayActual_dependence

def rayRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalized_ray)
    (Realization raySignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalized_ray.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.rayFamilyRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨rayArena⟩, objectArena := .source ⟨rayArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source rayArena ⟨rayFamilyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize raySignature (fun _ _ v => normalizedRay v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity,
    definition := none, coordinates := #[0,1],
    readouts := #[{
      path := #["body","body","body","body","fn","arg","arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

abbrev diagonalSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _m : ℕ, ℕ)
    (fun p => Fin p.1 × Fin p.2)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ)
def diagonalActual : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ a => normalizedRay (Pi.single a 1)) (fun e => nomatch e)
def diagonalRejected : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev diagonalArena : Arena where
  signature := diagonalSignature
  Law O := ∀ {m n : ℕ} (a : Fin m × Fin n),
    O.readout () ⟨m,n⟩ a = diagonal (fun i =>
      if i = a then (3 / (((m*n : ℕ) : ℂ) + 2) : ℂ)
      else (1 / (((m*n : ℕ) : ℂ) + 2) : ℂ))
private theorem diagonalRejected_law : ¬ diagonalArena.Law diagonalRejected := by
  intro h
  have he := congrFun (congrFun (h ((0,0) : Fin 1 × Fin 1)) (0,0)) (0,0)
  norm_num [diagonalRejected, realize, Matrix.diagonal_apply] at he
private theorem diagonalActual_dependence : ObservationalDependence diagonalSignature diagonalActual := by
  intro i
  refine ⟨⟨1,2⟩, (0,0), (0,1), ?_⟩
  intro h
  have he := congrFun (congrFun h (0,0)) (0,0)
  rw [show diagonalActual.readout () ⟨1,2⟩ (0,0) = normalizedRay (Pi.single ((0,0) : Fin 1 × Fin 2) 1) from rfl,
    show diagonalActual.readout () ⟨1,2⟩ (0,1) = normalizedRay (Pi.single ((0,1) : Fin 1 × Fin 2) 1) from rfl] at h
  rw [normalized_basis_diagonal, normalized_basis_diagonal] at h
  have hh := congrFun (congrFun h (0,0)) (0,0)
  norm_num [Matrix.diagonal_apply] at hh
def diagonalFamilyRegistration : Registration diagonalArena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalized_basis_diagonal) where
  actual := diagonalActual
  bridge := Iff.rfl
  variation := ⟨@normalized_basis_diagonal, diagonalRejected, diagonalRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity diagonalArena.Law diagonalActual diagonalRejected diagonalRejected_law
  dependence := diagonalActual_dependence

def diagonalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalized_basis_diagonal)
    (Realization diagonalSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalized_basis_diagonal.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.diagonalFamilyRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨diagonalArena⟩, objectArena := .source ⟨diagonalArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source diagonalArena ⟨diagonalFamilyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize diagonalSignature (fun _ _ a => normalizedRay (Pi.single a 1)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity,
    definition := none, coordinates := #[0,1],
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms familyRegistration
#print axioms rayFamilyRegistration
#print axioms diagonalFamilyRegistration
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.FiniteCorner
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder
noncomputable section

-- Retain the full telescope and both pencil constraints.
-- Use the natural-number relation directly in boundary proofs.

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _m : ℕ, ℕ)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    rho.PosSemidef → rho.trace = 1 → APPT rho →
      ∃ l : Fin (m*n) → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i = 1) ∧
        (K1 (_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.cornerBoundaryValues
          (m*n) (Nat.le_trans (by decide : 9 ≤ 3*3) (Nat.mul_le_mul hm hn)) l)).PosSemidef ∧
        (K2 (_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.cornerBoundaryValues
          (m*n) (Nat.le_trans (by decide : 9 ≤ 3*3) (Nat.mul_le_mul hm hn)) l)).PosSemidef ∧
        O.readout () ⟨m,n⟩ rho = ∑ i, (l i)^2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, _hdiag, hd, ha, _hp⟩ :=
    _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.result.2.2
  obtain ⟨l, _ho, _hn, _ht, _h1, _h2, hp⟩ := h (by decide) (by decide) rho hd.1 hd.2 ha
  have hs : (0 : ℝ) ≤ ∑ i, (l i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change (-1 : ℝ) = ∑ i, (l i)^2 at hp
  linarith
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩, 0, 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]
def registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.spectral_reduction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.spectral_reduction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.spectral_reduction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.spectral_reduction.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.FiniteCorner.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.FiniteCorner

-- Labelled-diagonal supplier registrations.
namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledNecessary
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder
noncomputable section

-- Both original pencils are independent roles.

/-- Role 0 observes K1 and role 1 observes K2 on the same original boundary data. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 9 → ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 3) (Fin 3) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun i _ b => if i = 0 then K1 b else K2 b) (fun e => nomatch e)
/-- Change exactly one pencil; every other role retains its actual readout. -/
def rejected (i : Fin 2) : Realization signature :=
  realize signature (fun j p b =>
    if j = i then -(1 : Matrix (Fin 3) (Fin 3) ℝ) else actual.readout j p b)
    (fun e => nomatch e)
/-- Keep all original binders and the complete conjunction of pencil inequalities. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m*n)) (l : Fin (m*n) → ℝ)
    (hdiag : APPT (diagonal (fun p => (l (e p) : ℂ)))),
    (O.readout 0 () (cornerBoundaryValues (m*n)
      (Nat.le_trans (by decide : 9 ≤ 3*3) (Nat.mul_le_mul hm hn)) l)).PosSemidef ∧
    (O.readout 1 () (cornerBoundaryValues (m*n)
      (Nat.le_trans (by decide : 9 ≤ 3*3) (Nat.mul_le_mul hm hn)) l)).PosSemidef
private theorem rejected_law (i : Fin 2) : ¬ arena.Law (rejected i) := by
  intro h
  let e : (Fin 3 × Fin 3) ≃ Fin (3*3) := finProdFinEquiv
  have ha : APPT (diagonal (fun p => ((0 : Fin (3*3) → ℝ) (e p) : ℂ))) := by
    intro U
    have hzero :
        _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
          (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) = 0 := by
      ext p q
      rfl
    simpa [hzero, Pi.zero_apply] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ).PosSemidef)
  have hb := h (by decide : 3 ≤ 3) (by decide : 3 ≤ 3) e 0 ha
  have hp : (0 : ℝ) ≤ (-(1 : Matrix (Fin 3) (Fin 3) ℝ)) 0 0 := by
    fin_cases i
    · exact hb.1.diag_nonneg
    · exact hb.2.diag_nonneg
  norm_num at hp
/-- Each pencil alone can falsify the full law while the other stays actual. -/
private theorem actual_sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected i, ?_, ?_, rejected_law i⟩
    · intro j hji
      funext p b
      simp [rejected, realize, hji]
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun q => if q = 8 then 1 else 0), ?_⟩
  intro heq
  have he := congrFun (congrFun heq 0) 0
  fin_cases i <;> norm_num [actual, realize, K1, K2, Pi.zero_apply] at he
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.diagonal_necessary_both)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.diagonal_necessary_both, rejected 0, rejected_law 0⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

/-- Source-bound supplier registration. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.diagonal_necessary_both) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledNecessary.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledNecessary.family
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
    (fun i _ b => if i = 0 then K1 b else K2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledNecessary

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledSpectrum
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _m : ℕ, ℕ)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
/-- Every dimension, including zero, and every conclusion clause remain in scope. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {m n : ℕ} (e : (Fin m × Fin n) ≃ Fin (m*n))
    (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho),
    ∃ l : Fin (m*n) → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i = 1) ∧
      APPT (diagonal (fun p => (l (e p) : ℂ))) ∧
      O.readout () ⟨m,n⟩ rho = ∑ i, (l i)^2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, _hdiag, hd, ha, _hp⟩ :=
    _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.result.2.2
  obtain ⟨l, _ho, _hn, _ht, _ha, hp⟩ :=
    h (m := 4) (n := 5) finProdFinEquiv rho hd.1 hd.2 ha
  have hs : (0 : ℝ) ≤ ∑ i, (l i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change (-1 : ℝ) = ∑ i, (l i)^2 at hp
  linarith
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩, 0, 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.diagonal_spectral_reduction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.diagonal_spectral_reduction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- Source-bound supplier registration. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.diagonal_spectral_reduction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledSpectrum.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.LabelledSpectrum

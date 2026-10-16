import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder
noncomputable section

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
        (K1 (_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner.boundaryValues
          (m*n) (le_trans (by decide : 9 ≤ 3*3) (Nat.mul_le_mul hm hn)) l)).PosSemidef ∧
        (K2 (_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner.boundaryValues
          (m*n) (le_trans (by decide : 9 ≤ 3*3) (Nat.mul_le_mul hm hn)) l)).PosSemidef ∧
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
def registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner.spectral_reduction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner.spectral_reduction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner.spectral_reduction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner.spectral_reduction.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner.registration,
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner

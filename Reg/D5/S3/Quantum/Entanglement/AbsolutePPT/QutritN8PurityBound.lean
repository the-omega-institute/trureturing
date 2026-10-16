import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 24 → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ l : Fin 24 → ℝ, Antitone l → 0 ≤ l 23 → (∑ i, l i = 1) →
    (K1 (boundaryValues 5 l)).PosSemidef → (K2 (boundaryValues 5 l)).PosSemidef →
      O.readout () () l ≤ (32 : ℝ)/26^2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let v : Fin 4 × Fin 6 → ℂ := Pi.single (0,0) 1
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    classical
    simp [v, dotProduct, Pi.single_apply]
  obtain ⟨hd, ht, ha, _hp⟩ :=
    _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalized_ray v hv
  obtain ⟨l, ho, hn, hmass, h1, h2, _hp⟩ :=
    _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.spectral_reduction
      (by decide : 3 ≤ 4) (by decide : 3 ≤ 6) _ hd ht ha
  have hb : _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.cornerBoundaryValues 24 (by decide) l =
      boundaryValues 5 l := rfl
  rw [hb] at h1 h2
  have hh := h l ho (hn 23) hmass h1 h2
  change (1 : ℝ) ≤ (32 : ℝ)/26^2 at hh
  norm_num at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, (fun _ => 1), ?_⟩
  change (∑ i : Fin 24, (0 : ℝ)^2) ≠ ∑ i : Fin 24, (1 : ℝ)^2
  norm_num
def registration : Registration arena (type_of% @certificate_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨certificate_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound.certificate_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound.certificate_bound.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

/-! The squared reading difference in the reflected Gram bound. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints (reflected_contrast_sq_le)
open LeanInformationAudit

set_option autoImplicit false

universe u

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : Type u} (k : M → M → ℚ) (tri : M → M → M → M)
    (_ : ∀ a, k a a = 1) (_ : ∀ a b, k a b = k b a)
    (_ : ∀ a b, tri a a b = b) (_ : ∀ a b, tri a b b = a)
    (_ : ∀ a b c d, k (tri a b c) (tri a b d) = k c d)
    (_ : ∀ a b c d, k (tri a c d) (tri b c d) = k a b)
    (_ : ∀ (p : Fin 4 → M) (c : Fin 4 → ℚ),
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j))
    (x y z : M), R.readout () () (k x z - k y z) ≤ (1 - k x y) * (1 - k z (tri x z y))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let point : ULift.{u} Unit := ⟨()⟩
  let k : ULift.{u} Unit → ULift.{u} Unit → ℚ := fun _ _ => 1
  let tri : ULift.{u} Unit → ULift.{u} Unit → ULift.{u} Unit → ULift.{u} Unit :=
    fun a _ _ => a
  have hgram (p : Fin 4 → ULift.{u} Unit) (c : Fin 4 → ℚ) :
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j) := by
    simp only [k, mul_one, ← Finset.mul_sum, ← Finset.sum_mul, ← sq]
    exact sq_nonneg _
  have hbad := h k tri (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Subsingleton.elim _ _)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hgram point point point
  change (1 : ℚ) ≤ (1 - 1) * (1 - 1) at hbad
  norm_num at hbad

def family : Registration arena.{u} (type_of% @reflected_contrast_sq_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reflected_contrast_sq_le.{u}, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, by change (0 : ℚ) ^ 2 ≠ (1 : ℚ) ^ 2; norm_num⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reflected_contrast_sq_le.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

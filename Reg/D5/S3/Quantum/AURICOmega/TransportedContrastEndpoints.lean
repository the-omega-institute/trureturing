import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

/-! The absolute reading difference in the uniform heap contrast bound. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints (abs_contrast_le)
open LeanInformationAudit

set_option autoImplicit false

universe u

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ d => |d|) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : Type u} (k : M → M → ℚ) (tri : M → M → M → M)
    (_ : ∀ a, k a a = 1) (_ : ∀ a b, k a b = k b a)
    (_ : ∀ a b, 0 ≤ k a b)
    (_ : ∀ a b, tri a a b = b) (_ : ∀ a b, tri a b b = a)
    (_ : ∀ a b c d e, tri (tri a b c) d e = tri a b (tri c d e))
    (_ : ∀ a b c d, k (tri a b c) (tri a b d) = k c d)
    (_ : ∀ a b c d, k (tri a c d) (tri b c d) = k a b)
    (_ : ∀ (p : Fin 5 → M) (c : Fin 5 → ℚ),
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j))
    (x y z : M) (_ : k x y = 3 / 5), R.readout () () (k x z - k y z) ≤ 406 / 625

private def indicator (value point : Bool) : ℚ :=
  if point = value then 1 else 0

private def comparison (a b : Bool) : ℚ :=
  3 / 5 + 2 / 5 * (indicator true a * indicator true b +
    indicator false a * indicator false b)

private def ternary (a b c : Bool) : Bool := xor (xor a b) c

private theorem comparison_gram (p : Fin 5 → Bool) (c : Fin 5 → ℚ) :
    0 ≤ ∑ i, ∑ j, c i * c j * comparison (p i) (p j) := by
  have hsum (f g : Fin 5 → ℚ) (a : ℚ) :
      (∑ i, ∑ j, a * (f i * g j)) = a * (∑ i, f i) * (∑ j, g j) := by
    calc
      _ = ∑ i, (a * f i) * (∑ j, g j) := by simp only [Finset.mul_sum, mul_assoc]
      _ = (∑ i, a * f i) * (∑ j, g j) := by rw [Finset.sum_mul]
      _ = _ := by
        have h : a * (∑ i, f i) = ∑ i, a * f i := by simp only [Finset.mul_sum]
        exact congrArg (fun b => b * (∑ j, g j)) h.symm
  have hsplit (i j : Fin 5) :
      c i * c j * comparison (p i) (p j) =
        3 / 5 * (c i * c j) +
        2 / 5 * ((c i * indicator true (p i)) * (c j * indicator true (p j))) +
        2 / 5 * ((c i * indicator false (p i)) * (c j * indicator false (p j))) := by
    unfold comparison
    ring
  simp only [hsplit, Finset.sum_add_distrib, hsum]
  simpa only [mul_assoc, ← sq] using (show
    0 ≤ (3 / 5 : ℚ) * (∑ i, c i) ^ 2 +
      2 / 5 * (∑ i, c i * indicator true (p i)) ^ 2 +
      2 / 5 * (∑ i, c i * indicator false (p i)) ^ 2 by positivity)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let t : Bool → ULift.{u} Bool := ULift.up
  let k : ULift.{u} Bool → ULift.{u} Bool → ℚ := fun a b => comparison a.down b.down
  let tri : ULift.{u} Bool → ULift.{u} Bool → ULift.{u} Bool → ULift.{u} Bool :=
    fun a b c => t (ternary a.down b.down c.down)
  have hdiag : ∀ a, k a a = 1 := by
    rintro ⟨a⟩
    cases a <;> norm_num [k, comparison, indicator]
  have hsymm : ∀ a b, k a b = k b a := by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;> norm_num [k, comparison, indicator]
  have hnonneg : ∀ a b, 0 ≤ k a b := by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;> norm_num [k, comparison, indicator]
  have hcancelLeft : ∀ a b, tri a a b = b := by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;> rfl
  have hcancelRight : ∀ a b, tri a b b = a := by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;> rfl
  have hassoc : ∀ a b c d e, tri (tri a b c) d e = tri a b (tri c d e) := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩ ⟨e⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
  have hinvLeft : ∀ a b c d, k (tri a b c) (tri a b d) = k c d := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [k, tri, t, ternary, comparison, indicator]
  have hinvRight : ∀ a b c d, k (tri a c d) (tri b c d) = k a b := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [k, tri, t, ternary, comparison, indicator]
  have hgram (p : Fin 5 → ULift.{u} Bool) (c : Fin 5 → ℚ) :
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j) := comparison_gram (fun i => (p i).down) c
  have hbad := h k tri hdiag hsymm hnonneg hcancelLeft hcancelRight hassoc
    hinvLeft hinvRight hgram (t false) (t true) (t false)
    (by norm_num [k, t, comparison, indicator])
  change (1 : ℚ) ≤ 406 / 625 at hbad
  norm_num at hbad

def family : Registration arena.{u} (type_of% @abs_contrast_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abs_contrast_le.{u}, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, by change |(0 : ℚ)| ≠ |(1 : ℚ)|; norm_num⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_contrast_le.{u}) (Realization signature) Unit Unit where
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
  readout := some (realize signature (fun _ _ d => |d|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence
import Reg.Support.DependentFamily

/-! Source-bound registration for the compression/channel equivalence. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence

open _root_.D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence
open _root_.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

structure Parameters where
  d : ℕ
  n : ℕ
  X : Type
  instX : Fintype X
  Ω : X → Type
  instΩ : ∀ x, Fintype (Ω x)
  M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ

abbrev signature : Signature where
  Params := Parameters
  State p := MatrixMap (Fin p.d) (Fin p.n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (x : p.X) → p.Ω x → Matrix (Fin p.n) (Fin p.n) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p Φ x b => Φ (p.M x b)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (d n : ℕ), 1 ≤ n → n ≤ d →
      ∀ (X : Type) [Fintype X] (Ω : X → Type) [∀ x, Fintype (Ω x)]
        (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ),
        (∀ x, IsPOVM (M x)) →
        let p : Parameters := {
          d := d, n := n, X := X, instX := inferInstance, Ω := Ω,
          instΩ := inferInstance, M := M }
        (∀ V : Matrix (Fin d) (Fin n) ℂ, Vᴴ * V = 1 →
          FamilyJointlyMeasurable (fun x b => Vᴴ * M x b * V)) ↔
        (∀ Φ : MatrixMap (Fin d) (Fin n) ℂ, Φ.IsCompletelyPositive → Φ 1 = 1 →
          FamilyJointlyMeasurable (R.readout () p Φ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let M : (x : Unit) → Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 1
  have hM : ∀ x : Unit, IsPOVM (M x) := by
    intro x
    refine ⟨fun _ => Matrix.PosSemidef.one, ?_⟩
    simp [M]
  have hleft : ∀ V : Matrix (Fin 1) (Fin 1) ℂ, Vᴴ * V = 1 →
      FamilyJointlyMeasurable (fun (_ : Unit) (_ : Unit) => Vᴴ * M () () * V) := by
    intro V hV
    refine ⟨fun _ => 1, ?_, ?_⟩
    · refine ⟨fun _ => Matrix.PosSemidef.one, ?_⟩
      simp
    · intro x b
      simp only [M, Matrix.mul_one]
      rw [hV]
      simp
  have hzero : ¬ FamilyJointlyMeasurable
      (fun (_ : Unit) (_ : Unit) => (0 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    intro hz
    obtain ⟨G, hG, hMarginal⟩ := hz
    have hMarginal' : G (fun _ : Unit => ()) = 0 := by
      simpa [Fintype.sum_unique] using hMarginal () ()
    have hsum := hG.2
    change (∑ a : Unit → Unit, G a) = 1 at hsum
    rw [show (∑ a : Unit → Unit, G a) = G (fun _ : Unit => ()) by simp] at hsum
    rw [hMarginal'] at hsum
    norm_num at hsum
  have hiff := h 1 1 (by norm_num) (by norm_num) Unit (fun _ : Unit => Unit) M hM
  let I : MatrixMap (Fin 1) (Fin 1) ℂ :=
    MatrixMap.of_kraus (fun _ : Unit => 1) (fun _ : Unit => 1)
  have hIcp : I.IsCompletelyPositive := by
    exact MatrixMap.of_kraus_isCompletelyPositive (fun _ : Unit => 1)
  have hIu : I 1 = 1 := by
    change (MatrixMap.of_kraus (fun _ : Unit => 1) (fun _ : Unit => 1)) 1 = 1
    rw [MatrixMap.of_kraus, Fintype.sum_unique]
    simp
  have hz := (hiff.mp hleft) I hIcp hIu
  apply hzero
  change FamilyJointlyMeasurable
    (fun (_ : Unit) (_ : Unit) => (0 : Matrix (Fin 1) (Fin 1) ℂ)) at hz
  exact hz

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let p : Parameters := {
    d := 1, n := 1, X := Unit, instX := inferInstance,
    Ω := fun _ : Unit => Unit, instΩ := fun _ => inferInstance,
    M := fun _ _ => 1 }
  refine ⟨p, (0 : MatrixMap (Fin 1) (Fin 1) ℂ),
    (LinearMap.id : MatrixMap (Fin 1) (Fin 1) ℂ), ?_⟩
  intro he
  have he' := congrArg (fun f => f () ()) he
  have hentry := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) he'
  have hentry' : (0 : ℂ) = 1 := by
    simpa [p, actual, realize] using hentry
  norm_num at hentry'

theorem actual_law : arena.Law actual := by
  simpa [arena, claim, actual, realize] using result

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro h
      simpa [arena, claim, actual, realize] using h
    · intro h
      simpa [arena, claim, actual, realize] using h
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence.unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p Φ x b => Φ (p.M x b)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence
      name := `D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence.claim
      path := #[] }
    coordinates := #[0, 1, 4, 6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "body", "body", "fn", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence

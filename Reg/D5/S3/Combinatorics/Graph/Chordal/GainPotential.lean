import D5.S3.Combinatorics.Graph.Chordal.GainPotential
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! A source-bound whole-family audit of the original potential theorem. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.GainPotential
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev Params := Σ V : Type u, Σ H : Type v, Σ _ : Group H,
  Σ _ : SimpleGraph V, Σ _ : V → V → H, Σ _ : V → H, V

abbrev signature : Signature where
  Params := Params.{u, v}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def reader (p : Params.{u, v}) (j : p.1) : p.2.1 := by
  rcases p with ⟨V, H, inst, G, g, φ, i⟩
  letI : Group H := inst
  exact (φ i)⁻¹ * φ j

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p j => reader p j) (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p _ => by letI := p.2.2.1; exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {V : Type u} {H : Type v} [h : Group H] [Finite V]
    {G : SimpleGraph V} (_hG : G.IsChordal) (g : V → V → H)
    (_hrev : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹)
    (_htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      g i j * g j k = g i k),
    ∃ φ : V → H, ∀ i j, G.Adj i j →
      g i j = R.readout () ⟨V, H, h, G, g, φ, i⟩ j

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 2)
  let H := Equiv.Perm (ULift.{v} (Fin 2))
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  let t : H := Equiv.swap ⟨0⟩ ⟨1⟩
  let θ : V → H := fun i => if i = a then 1 else t
  let g : V → V → H := fun i j => (θ i)⁻¹ * θ j
  have hG : (⊤ : SimpleGraph V).IsChordal := by
    intro x c hc hlen
    have hcard := hc.support_nodup.length_le_card
    rw [List.length_tail, c.length_support] at hcard
    have hsize : Fintype.card V = 2 := by simp [V]
    rw [hsize] at hcard
    omega
  have hrev : ∀ i j, (⊤ : SimpleGraph V).Adj i j → g j i = (g i j)⁻¹ := by
    intro i j _
    dsimp only [g, H]
    simp
  have htri : ∀ i j k, (⊤ : SimpleGraph V).Adj i j →
      (⊤ : SimpleGraph V).Adj j k → (⊤ : SimpleGraph V).Adj i k →
      g i j * g j k = g i k := by
    intro i j k _ _ _
    dsimp only [g, H]
    simp [mul_assoc]
  obtain ⟨φ, hφ⟩ := h hG g hrev htri
  have hab_ne : a ≠ b := by
    intro heq
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down heq)
  have hab : (⊤ : SimpleGraph V).Adj a b := hab_ne
  have heq := hφ a b hab
  change (θ a)⁻¹ * θ b = 1 at heq
  have hθa : θ a = 1 := ite_eq_left rfl
  have hθb : θ b = t := ite_eq_right hab_ne.symm
  rw [hθa, hθb, inv_one, one_mul] at heq
  have hx := congrArg (fun p : H => (p ⟨0⟩).down) heq
  have hbad : (1 : Fin 2) = 0 := by
    dsimp only [H, t] at hx
    simpa only [one_mul, Equiv.swap_apply_left, Equiv.Perm.one_apply] using hx
  exact (by decide : (1 : Fin 2) ≠ 0) hbad

private theorem dependence : ObservationalDependence signature.{u, v} actual := by
  classical
  intro role
  let V := ULift.{u} (Fin 2)
  let H := Equiv.Perm (ULift.{v} (Fin 2))
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  let t : H := Equiv.swap ⟨0⟩ ⟨1⟩
  let φ : V → H := fun i => if i = a then 1 else t
  let p : Params.{u, v} := ⟨V, H, inferInstance, ⊤, (fun _ _ => 1), φ, a⟩
  refine ⟨p, a, b, ?_⟩
  intro heq
  change (φ a)⁻¹ * φ a = (φ a)⁻¹ * φ b at heq
  have hab_ne : a ≠ b := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)
  have hφa : φ a = 1 := ite_eq_left rfl
  have hφb : φ b = t := ite_eq_right hab_ne.symm
  rw [hφa, hφb, inv_one, one_mul] at heq
  have hx := congrArg (fun q : H => (q ⟨0⟩).down) heq
  have hbad : (0 : Fin 2) = 1 := by
    dsimp only [H, t] at hx
    simpa only [one_mul, Equiv.swap_apply_left, Equiv.Perm.one_apply] using hx
  exact (by decide : (0 : Fin 2) ≠ 1) hbad

def family : Registration arena.{u, v}
    (type_of% (@SimpleGraph.IsChordal.exists_gain_potential.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@SimpleGraph.IsChordal.exists_gain_potential.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SimpleGraph.IsChordal.exists_gain_potential.{u, v})
    (Realization signature.{u, v}) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.GainPotential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.GainPotential
    definition := none
    coordinates := #[0, 1, 4, 6, 9, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Chordal.GainPotential

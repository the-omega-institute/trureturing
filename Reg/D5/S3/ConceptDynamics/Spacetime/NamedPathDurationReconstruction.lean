import D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Full-telescope path readout family and a nonconstant one-loop witness. -/

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction

namespace Reg.D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction
universe u v

structure Params where
  V : Type u
  quiver : Quiver.{v} V
  d : ∀ {a b : V}, @Quiver.Hom V quiver a b → ℝ
  root : V

instance (p : Params) : Quiver p.V := p.quiver

abbrev signature : Signature where
  Params := Params.{u,v}
  State p := Σ b : p.V, Quiver.Path p.root b
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.V × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u,v} := realize signature
  (fun _ p => readout p.d p.root) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law q := ∀ p : Params.{u,v},
    (∀ {a b : p.V} (e : a ⟶ b), 0 < p.d e) →
    (∀ a b : p.V, Nonempty (Quiver.Path a b)) →
    (Function.Injective (q.readout () p) ↔
      ∀ a : p.V, Subsingleton (Σ b : p.V, a ⟶ b))

private def loopParams : Params.{u,v} where
  V := ULift.{u} Unit
  quiver := ⟨fun _ _ => ULift.{v} Unit⟩
  d := fun _ => 1
  root := ⟨()⟩

private theorem loop_positive : ∀ {a b : loopParams.{u,v}.V}
    (e : a ⟶ b), 0 < loopParams.d e := by
  intros
  exact zero_lt_one

private theorem loop_recurrent : ∀ a b : loopParams.{u,v}.V,
    Nonempty (Quiver.Path a b) := by
  intro a b
  have hab : a = b :=
    @Subsingleton.elim (ULift.{u} Unit) inferInstance a b
  subst b
  exact ⟨.nil⟩

private theorem loop_unique : ∀ a : loopParams.{u,v}.V,
    Subsingleton (Σ b : loopParams.V, a ⟶ b) := by
  intro a
  change Subsingleton (Σ _ : ULift.{u} Unit, ULift.{v} Unit)
  refine ⟨?_⟩
  rintro ⟨b, e⟩ ⟨c, f⟩
  have hbc : b = c := Subsingleton.elim _ _
  cases hbc
  have hef : e = f := Subsingleton.elim _ _
  cases hef
  rfl

private def emptyPath : signature.{u,v}.State loopParams := ⟨loopParams.root, .nil⟩
private def onePath : signature.{u,v}.State loopParams :=
  ⟨loopParams.root, Quiver.Path.cons .nil (ULift.up ())⟩

private theorem paths_distinct : emptyPath.{u,v} ≠ onePath := by
  intro h
  have hp := eq_of_heq (Sigma.mk.inj h).2
  have hl := congrArg Quiver.Path.length hp
  simp [Quiver.Path.length] at hl

private def rejected : Realization signature.{u,v} := realize signature
  (fun _ p _ => (p.root, 0)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hi := (h loopParams loop_positive loop_recurrent).mpr loop_unique
  exact paths_distinct (hi (a₁ := emptyPath) (a₂ := onePath) rfl)

def family : Registration arena.{u,v}
    (type_of% (@readout_injective_iff_no_branching.{u,v})) where
  actual := actual
  bridge := by
    constructor
    · intro h p hd hc
      exact h p.d hd p.root hc
    · intro h V q d hd r hc
      exact h ⟨V, q, d, r⟩ hd hc
  variation := ⟨fun p hd hc => readout_injective_iff_no_branching p.d hd p.root hc,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨loopParams, emptyPath, onePath, ?_⟩
    intro h
    have ht := congrArg Prod.snd h
    change (0 : ℝ) = 0 + 1 at ht
    norm_num at ht

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@readout_injective_iff_no_branching.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction.readout_injective_iff_no_branching.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction
    definition := none
    coordinates := #[0,1,2,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- The complete specified-arrow inventory, with only its readout operand varied. -/
abbrev inventoryArena : Arena where
  signature := signature.{u,v}
  Law q := ∀ c : Params.{u,v},
    (∀ x y : c.V, Nonempty (Quiver.Path x y)) →
    ∀ (z : c.V) (a b : Σ t : c.V, z ⟶ t), a ≠ b →
    ∃ (p : Quiver.Path c.root z) (A : Quiver.Path a.1 z) (B : Quiver.Path b.1 z),
      let U := a.2.toPath.comp A
      let W := b.2.toPath.comp B
      0 < U.length ∧ 0 < W.length ∧
      edgeWord U = ⟨z, a.1, a.2⟩ :: edgeWord A ∧
      edgeWord W = ⟨z, b.1, b.2⟩ :: edgeWord B ∧
      (⟨z, a.1, a.2⟩ : NamedEdge c.V) ≠ ⟨z, b.1, b.2⟩ ∧
      p.comp (U.comp W) ≠ p.comp (W.comp U) ∧
      duration c.d (p.comp (U.comp W)) =
        duration c.d p + duration c.d U + duration c.d W ∧
      duration c.d (p.comp (W.comp U)) =
        duration c.d p + duration c.d W + duration c.d U ∧
      q.readout () c ⟨z, p.comp (U.comp W)⟩ =
        q.readout () c ⟨z, p.comp (W.comp U)⟩ ∧
      ¬ Function.Injective (q.readout () c)

theorem inventory_bridge :
    (type_of% (@branching_collision_inventory.{u,v})) ↔ inventoryArena.{u,v}.Law actual := by
  constructor
  · intro h c hc z a b hab
    exact h c.d c.root hc z a b hab
  · intro h V q d r hc z a b hab
    exact h ⟨V, q, d, r⟩ hc z a b hab

theorem inventory_actual_law : inventoryArena.{u,v}.Law actual :=
  inventory_bridge.mp (@branching_collision_inventory.{u,v})

#print axioms inventory_bridge
#print axioms inventory_actual_law
#print axioms family
#print axioms registration
end Reg.D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction

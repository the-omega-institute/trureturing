import D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.ULift
import Reg.Support.DependentFamily

/-! Direct-source registrations for the typed crossed-module pasting laws. -/

set_option autoImplicit false
noncomputable section
universe u v t s o

namespace Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting

private abbrev oneRole (P : Type t) (S : P → Type s) (O : P → Type o) : Signature where
  Params := P
  State := S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := O
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem oneRoleSensitivity {P : Type t} {S : P → Type s} {O : P → Type o}
    (law : Realization (oneRole P S O) → Prop)
    (good bad : Realization (oneRole P S O)) (reject : ¬ law bad) :
    Sensitivity ⟨oneRole P S O, law⟩ good := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, reject⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

/-- A realization that samples one face per inhabited state fiber. -/
private def freeze {P : Type t} {S : P → Type s} {O : P → Type o}
    (good : Realization (oneRole P S O)) : Realization (oneRole P S O) :=
  realize (oneRole P S O)
    (fun i p x => good.readout i p (Classical.choice (show Nonempty (S p) from ⟨x⟩)))
    (fun e => nomatch e)

private abbrev Modules := Σ H : Type u, Σ G : Type v, Σ hH : Group H,
  Σ hG : Group G, @CrossedModule H G hH hG

private abbrev shellState (m : Modules.{u, v}) : Type _ := by
  rcases m with ⟨H, G, hH, hG, X⟩
  exact @Tetrahedron H G hH hG X

private abbrev Q := QuaternionGroup 2

private def liftId : CrossedModule (ULift.{u} Q) (ULift.{v} Q) where
  μ := {
    toFun := fun h => ⟨h.down⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  act := MulAut.conj.comp {
    toFun := fun g => ⟨g.down⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  equivariant := by intros; rfl
  peiffer := by intros; rfl

private def liftedA : ULift.{u} Q := ⟨.a 1⟩

private theorem liftedA_not_mem_center : liftedA.{u} ∉ Subgroup.center (ULift.{u} Q) := by
  intro h
  have he := Subgroup.mem_center_iff.mp h (⟨.xa 0⟩ : ULift.{u} Q)
  exact (by decide : (QuaternionGroup.xa 0 : Q) * .a 1 ≠ .a 1 * .xa 0)
    (congrArg ULift.down he)

private theorem liftedA_not_mem_ker : liftedA.{u} ∉ (liftId.{u, v}).μ.ker := by
  intro h
  have he := congrArg ULift.down (MonoidHom.mem_ker.mp h)
  exact (by decide : (QuaternionGroup.a 1 : Q) ≠ 1) he

private def outsider {H : Type u} [Group H] (K : Subgroup H) : H := by
  classical
  exact if h : ∃ a, a ∉ K then Classical.choose h else 1

private theorem outsider_not_mem {H : Type u} [Group H] (K : Subgroup H)
    (h : ∃ a, a ∉ K) : outsider K ∉ K := by
  classical
  simpa only [outsider, dite_eq_left h] using Classical.choose_spec h

private abbrev FlatH := ULift.{u} V4
private abbrev FlatG := ULift.{v} (PUnit.{1})

private def flat : CrossedModule FlatH.{u} FlatG.{v} where
  μ := 1
  act := 1
  equivariant := by intros; apply Subsingleton.elim
  peiffer := by
    intro h k
    change (1 : MulAut FlatH.{u}) k = h * k * h⁻¹
    rw [MulAut.one_apply, mul_comm h k, mul_assoc, mul_inv_cancel, mul_one]

private def mark : FlatH.{u} := ⟨Multiplicative.ofAdd ((1 : ZMod 2), 0)⟩

private theorem mark_ne_one : mark.{u} ≠ 1 := by
  intro h
  have he := congrArg (fun x : FlatH.{u} => x.down.toAdd.1) h
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) he

private def flatFace (a : FlatH.{u}) : Face flat.{u, v} 1 1 :=
  ⟨a, Subsingleton.elim _ _⟩

private def unitShell {H : Type u} {G : Type v} [Group H] [Group G]
    (X : CrossedModule H G) : Tetrahedron X where
  g01 := 1
  g02 := 1
  g03 := 1
  g12 := 1
  g13 := 1
  g23 := 1
  h012 := ⟨1, by simp⟩
  h013 := ⟨1, by simp⟩
  h023 := ⟨1, by simp⟩
  h123 := ⟨1, by simp⟩

private def flatShell (a : FlatH.{u}) : Tetrahedron flat.{u, v} :=
  { unitShell flat with h012 := ⟨a, Subsingleton.elim _ _⟩ }

private theorem flatShell_obstruction (a : FlatH.{u}) :
    (flatShell.{u, v} a).obstruction = a⁻¹ := by
  change ((1 * flat.{u, v}.act 1 1) * 1) * (a * 1)⁻¹ = a⁻¹
  simp only [map_one, one_mul, mul_one]

private theorem flatShell_distinct :
    (flatShell.{u, v} 1).obstruction ≠ (flatShell.{u, v} mark).obstruction := by
  rw [flatShell_obstruction, flatShell_obstruction, inv_one]
  exact Ne.symm (fun h => mark_ne_one (inv_eq_one.mp h))

namespace KernelCentral

private abbrev signature : Signature :=
  oneRole Modules.{u, v} (fun m => m.1) (fun m => m.1)

private def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ h => h) (fun e => nomatch e)

private def rejected : Realization signature.{u, v} :=
  realize signature
    (fun _ m _ => by
      letI := m.2.2.1
      exact outsider (Subgroup.center m.1))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {H : Type u} {G : Type v} [hH : Group H] [hG : Group G]
    (X : CrossedModule H G), ∀ h ∈ X.μ.ker,
      R.readout () ⟨H, G, hH, hG, X⟩ h ∈ Subgroup.center H

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  exact outsider_not_mem _ ⟨liftedA.{u}, liftedA_not_mem_center⟩
    (h liftId.{u, v} 1 (by rw [MonoidHom.mem_ker, map_one]))

def family : Registration arena.{u, v} (type_of% @CrossedModule.ker_le_center.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@CrossedModule.ker_le_center.{u, v}, rejected, rejected_law⟩
  sensitivity := oneRoleSensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨⟨_, _, inferInstance, inferInstance, flat.{u, v}⟩,
    1, mark, mark_ne_one.symm⟩

end KernelCentral

namespace FakeFlatness

private abbrev signature : Signature :=
  oneRole Modules.{u, v} (fun m => m.1) (fun m => m.2.1)

private def actual : Realization signature.{u, v} :=
  realize signature (fun _ m => by
    rcases m with ⟨H, G, hH, hG, X⟩
    letI := hH
    letI := hG
    intro h
    exact X.μ h) (fun e => nomatch e)

private def rejected : Realization signature.{u, v} :=
  realize signature (fun _ m _ => by letI := m.2.2.2.1; exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {H : Type u} {G : Type v} [hH : Group H] [hG : Group G]
    (X : CrossedModule H G) (p q : G) (h : H),
      X.μ h * p = q ↔ R.readout () ⟨H, G, hH, hG, X⟩ h = q * p⁻¹

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  have h := (law liftId.{u, v} 1 1 liftedA).mpr (by simp [rejected, realize])
  exact liftedA_not_mem_ker.{u, v} (MonoidHom.mem_ker.mpr (by simpa only [mul_one] using h))

def family : Registration arena.{u, v} (type_of% @Face.fake_flat_iff.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Face.fake_flat_iff.{u, v}, rejected, rejected_law⟩
  sensitivity := oneRoleSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨_, _, inferInstance, inferInstance, liftId.{u, v}⟩, 1, liftedA, ?_⟩
    intro h
    exact liftedA_not_mem_ker.{u, v}
      (MonoidHom.mem_ker.mpr ((map_one (liftId.{u, v}).μ).symm.trans h).symm)

end FakeFlatness

namespace Interchange

private abbrev Params := Σ H : Type u, Σ G : Type v, Σ hH : Group H,
  Σ hG : Group G, Σ X : @CrossedModule H G hH hG,
  Σ p : G, Σ q : G, Σ r : G, Σ p' : G, Σ q' : G, Σ _ : G,
  Σ _ : @Face H G hH hG X p q, Σ _ : @Face H G hH hG X p' q',
  @Face H G hH hG X q r

private abbrev signature : Signature :=
  oneRole Params.{u, v}
    (fun m => by
      rcases m with ⟨H, G, hH, hG, X, p, q, r, p', q', r', h, k, h'⟩
      exact @Face H G hH hG X q' r')
    (fun m => by
      rcases m with ⟨H, G, hH, hG, X, p, q, r, p', q', r', h, k, h'⟩
      letI := hG
      exact @Face H G hH hG X (p * p') (r * r'))

private def actual : Realization signature.{u, v} :=
  realize signature (fun _ m => by
    rcases m with ⟨H, G, hH, hG, X, p, q, r, p', q', r', h, k, h'⟩
    intro k'
    exact (h.horizontal k).vertical (h'.horizontal k'))
    (fun e => nomatch e)

private def rejected : Realization signature.{u, v} := freeze actual

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {H : Type u} {G : Type v} [hH : Group H] [hG : Group G]
    {X : CrossedModule H G} {p q r p' q' r' : G}
    (h : Face X p q) (k : Face X p' q') (h' : Face X q r) (k' : Face X q' r'),
      R.readout () ⟨H, G, hH, hG, X, p, q, r, p', q', r', h, k, h'⟩ k' =
        (h.vertical h').horizontal (k.vertical k')

private def sampleParams : Params.{u, v} :=
  ⟨_, _, inferInstance, inferInstance, flat.{u, v}, 1, 1, 1, 1, 1, 1,
    flatFace 1, flatFace 1, flatFace 1⟩

private theorem sample_distinct :
    actual.readout () sampleParams.{u, v} (flatFace 1) ≠
      actual.readout () sampleParams.{u, v} (flatFace mark) := by
  intro h
  have he := congrArg Face.label h
  change ((1 : FlatH.{u}) * (flat.{u, v}).act 1 1) * (1 * flat.{u, v}.act 1 1) =
    (1 * flat.{u, v}.act 1 mark) * (1 * flat.{u, v}.act 1 1) at he
  exact mark_ne_one.{u} (by
    simpa [flat, MulAut.one_apply] using he.symm)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  let i := flatFace.{u, v} 1
  let f := flatFace.{u, v} mark
  have hi := (Face.interchange i i i i).trans (law i i i i).symm
  have hf := (Face.interchange i i i f).trans (law i i i f).symm
  exact sample_distinct.{u, v} (hi.trans hf.symm)

def family : Registration arena.{u, v} (type_of% @Face.interchange.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Face.interchange.{u, v}, rejected, rejected_law⟩
  sensitivity := oneRoleSensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨sampleParams.{u, v}, flatFace 1, flatFace mark, sample_distinct⟩

end Interchange


namespace Shell

private abbrev signature : Signature :=
  oneRole Modules.{u, v} shellState (fun m => m.1)

private def actual : Realization signature.{u, v} :=
  realize signature (fun _ m => by
    rcases m with ⟨H, G, hH, hG, X⟩
    intro T
    exact T.obstruction)
    (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u, v} actual :=
  fun _ => ⟨⟨_, _, inferInstance, inferInstance, flat.{u, v}⟩,
    flatShell.{u, v} 1, flatShell.{u, v} mark, flatShell_distinct.{u, v}⟩

namespace Kernel

private def rejected : Realization signature.{u, v} :=
  realize signature (fun _ m _ => by
    rcases m with ⟨H, G, hH, hG, X⟩
    letI := hH
    exact outsider X.μ.ker)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {H : Type u} {G : Type v} [hH : Group H] [hG : Group G]
    {X : CrossedModule H G} (T : Tetrahedron X),
      R.readout () ⟨H, G, hH, hG, X⟩ T ∈ X.μ.ker

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  let X := liftId.{u, v}
  exact outsider_not_mem X.μ.ker ⟨liftedA, liftedA_not_mem_ker⟩ (law (unitShell X))

def family : Registration arena.{u, v} (type_of% @Tetrahedron.obstruction_mem_ker.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Tetrahedron.obstruction_mem_ker.{u, v}, rejected, rejected_law⟩
  sensitivity := oneRoleSensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Kernel

namespace Center

private def rejected : Realization signature.{u, v} :=
  realize signature (fun _ m _ => by
    letI := m.2.2.1
    exact outsider (Subgroup.center m.1))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {H : Type u} {G : Type v} [hH : Group H] [hG : Group G]
    {X : CrossedModule H G} (T : Tetrahedron X),
      R.readout () ⟨H, G, hH, hG, X⟩ T ∈ Subgroup.center H

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  exact outsider_not_mem _ ⟨liftedA.{u}, liftedA_not_mem_center⟩
    (law (unitShell liftId.{u, v}))

def family : Registration arena.{u, v} (type_of% @Tetrahedron.obstruction_mem_center.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Tetrahedron.obstruction_mem_center.{u, v}, rejected, rejected_law⟩
  sensitivity := oneRoleSensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Center

namespace Triviality

private def rejected : Realization signature.{u, v} :=
  realize signature (fun _ m _ => by letI := m.2.2.1; exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {H : Type u} {G : Type v} [hH : Group H] [hG : Group G]
    {X : CrossedModule H G} (T : Tetrahedron X),
      R.readout () ⟨H, G, hH, hG, X⟩ T = 1 ↔ T.left.label = T.right.label

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  let T := flatShell.{u, v} mark
  have h := T.obstruction_eq_one_iff.mpr ((law T).mp rfl)
  have he : mark.{u}⁻¹ = 1 := (flatShell_obstruction.{u, v} mark).symm.trans h
  exact mark_ne_one (inv_eq_one.mp he)

def family : Registration arena.{u, v} (type_of% @Tetrahedron.obstruction_eq_one_iff.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Tetrahedron.obstruction_eq_one_iff.{u, v}, rejected, rejected_law⟩
  sensitivity := oneRoleSensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Triviality
end Shell

namespace Quaternion

private abbrev signature : Signature :=
  oneRole Unit (fun _ => Tetrahedron q8CrossedModule) (fun _ => Q)

private def actual : Realization signature :=
  realize signature (fun _ _ T => T.obstruction) (fun e => nomatch e)

/-- Change the 012 face by the nonidentity element of the boundary kernel. -/
private def repaired : Tetrahedron q8CrossedModule :=
  { q8Tetrahedron with h012 := ⟨.xa 3, by decide⟩ }

private theorem left_label (T : Tetrahedron q8CrossedModule)
    (h01 : T.g01 = q8Boundary (.a 1)) (h123 : T.h123.label = .xa 0)
    (h013 : T.h013.label = .a 1) : T.left.label = .xa 3 := by
  change (1 * q8CrossedModule.act T.g01 T.h123.label) * T.h013.label = _
  rw [one_mul, h123, h013]
  change q8CrossedModule.act T.g01 (.xa 0) * QuaternionGroup.a 1 = _
  rw [h01]
  change q8CrossedModule.act (q8CrossedModule.μ (.a 1)) (.xa 0) * QuaternionGroup.a 1 = _
  rw [q8CrossedModule.peiffer]
  decide

private theorem repaired_obstruction : repaired.obstruction = 1 := by
  have hleft := left_label repaired rfl rfl rfl
  have hright : repaired.right.label = .xa 3 := by decide
  rw [Tetrahedron.obstruction, hleft, hright, mul_inv_cancel]

private theorem original_obstruction : q8Tetrahedron.obstruction = minusOne := by
  have hleft := left_label q8Tetrahedron rfl rfl rfl
  have hright : q8Tetrahedron.right.label = .xa 1 := by decide
  rw [Tetrahedron.obstruction, hleft, hright]
  decide

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => repaired.obstruction) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ T : Tetrahedron q8CrossedModule,
    R.readout () () T = minusOne ∧ T.obstruction ≠ 1

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨T, h, _⟩
  have he : repaired.obstruction = minusOne := h
  exact (by decide : (1 : Q) ≠ minusOne) (repaired_obstruction.symm.trans he)

def family : Registration arena (type_of% @q8_tetrahedron_nontrivial) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨q8_tetrahedron_nontrivial, rejected, rejected_law⟩
  sensitivity := oneRoleSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), q8Tetrahedron, repaired, ?_⟩
    change q8Tetrahedron.obstruction ≠ repaired.obstruction
    rw [original_obstruction, repaired_obstruction]
    decide

end Quaternion

def KernelCentral.audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CrossedModule.ker_le_center.{u, v})
    (Realization KernelCentral.signature.{u, v}) Unit Unit where
  unitName := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.CrossedModule.ker_le_center.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.KernelCentral.family
  realizationSource := none
  generated := false
  arena := .source ⟨KernelCentral.arena.{u, v}⟩
  objectArena := .source ⟨KernelCentral.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source KernelCentral.arena.{u, v} ⟨KernelCentral.family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize KernelCentral.signature KernelCentral.actual.readout KernelCentral.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def FakeFlatness.audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Face.fake_flat_iff.{u, v})
    (Realization FakeFlatness.signature.{u, v}) Unit Unit where
  unitName := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Face.fake_flat_iff.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.FakeFlatness.family
  realizationSource := none
  generated := false
  arena := .source ⟨FakeFlatness.arena.{u, v}⟩
  objectArena := .source ⟨FakeFlatness.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source FakeFlatness.arena.{u, v} ⟨FakeFlatness.family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize FakeFlatness.signature FakeFlatness.actual.readout FakeFlatness.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn",
        "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def Interchange.audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Face.interchange.{u, v})
    (Realization Interchange.signature.{u, v}) Unit Unit where
  unitName := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Face.interchange.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Interchange.family
  realizationSource := none
  generated := false
  arena := .source ⟨Interchange.arena.{u, v}⟩
  objectArena := .source ⟨Interchange.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Interchange.arena.{u, v} ⟨Interchange.family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Interchange.signature Interchange.actual.readout Interchange.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
    definition := none
    coordinates := #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def Shell.Kernel.audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Tetrahedron.obstruction_mem_ker.{u, v})
    (Realization Shell.signature.{u, v}) Unit Unit where
  unitName := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Tetrahedron.obstruction_mem_ker.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Shell.Kernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨Shell.Kernel.arena.{u, v}⟩
  objectArena := .source ⟨Shell.Kernel.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Shell.Kernel.arena.{u, v} ⟨Shell.Kernel.family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Shell.signature Shell.actual.readout Shell.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def Shell.Center.audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Tetrahedron.obstruction_mem_center.{u, v})
    (Realization Shell.signature.{u, v}) Unit Unit where
  unitName := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Tetrahedron.obstruction_mem_center.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Shell.Center.family
  realizationSource := none
  generated := false
  arena := .source ⟨Shell.Center.arena.{u, v}⟩
  objectArena := .source ⟨Shell.Center.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Shell.Center.arena.{u, v} ⟨Shell.Center.family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Shell.signature Shell.actual.readout Shell.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def Shell.Triviality.audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Tetrahedron.obstruction_eq_one_iff.{u, v})
    (Realization Shell.signature.{u, v}) Unit Unit where
  unitName := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Tetrahedron.obstruction_eq_one_iff.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Shell.Triviality.family
  realizationSource := none
  generated := false
  arena := .source ⟨Shell.Triviality.arena.{u, v}⟩
  objectArena := .source ⟨Shell.Triviality.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Shell.Triviality.arena.{u, v} ⟨Shell.Triviality.family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Shell.signature Shell.actual.readout Shell.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def Quaternion.audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q8_tetrahedron_nontrivial)
    (Realization Quaternion.signature) Unit Unit where
  unitName := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.q8_tetrahedron_nontrivial.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting.Quaternion.family
  realizationSource := none
  generated := false
  arena := .source ⟨Quaternion.arena⟩
  objectArena := .source ⟨Quaternion.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Quaternion.arena ⟨Quaternion.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Quaternion.signature Quaternion.actual.readout Quaternion.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting

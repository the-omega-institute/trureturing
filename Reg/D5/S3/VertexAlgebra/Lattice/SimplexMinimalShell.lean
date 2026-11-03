import D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
noncomputable section
open scoped Classical
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell
namespace Reg.D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell

universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equality : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
    (_hn : 2 ≤ Fintype.card ι) (y : ι → ℤ) (_hvar : ∃ i j, y i ≠ y j),
    2 * ((Fintype.card ι : ℤ) - 1) ≤ energy y ∧
      (R.readout () () (energy y) (2 * ((Fintype.card ι : ℤ) - 1)) ↔
        ∃ (a e : ℤ) (p : ι), (e = 1 ∨ e = -1) ∧
          ∀ i, y i = a + if i = p then e else 0)

-- A universe lift supplies the same inhabited counterexample in every source universe.
private theorem bad_all : ¬ arena.{u}.Law rejected := by
  intro h
  let y : ULift.{u} (Fin 2) → ℤ := fun i => if i.down = 1 then 1 else 0
  have hh := (h (ι := ULift.{u} (Fin 2)) (by decide) y
    ⟨⟨0⟩, ⟨1⟩, by decide⟩).2
  apply hh.mpr
  refine ⟨0, 1, ⟨1⟩, Or.inl rfl, ?_⟩
  intro i
  simp [y, ULift.ext_iff]

private theorem dependence : ObservationalDependence signature equality := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℤ) = 0) = ((1 : ℤ) = 0) at he
  have hn : (1 : ℤ) = 0 := he ▸ rfl
  omega

def family : Registration arena.{u} (type_of% (@complete_shell.{u})) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨complete_shell, rejected, bad_all⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad_all⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def shellAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_shell.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell.shellUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature equality.readout equality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms shellAudit
end Reg.D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell

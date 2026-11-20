import D5.S3.Combinatorics.Graph.CliqueFactorization.Algebraic
import Mathlib.Combinatorics.SimpleGraph.Clique
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.TypeTags.Basic

set_option autoImplicit false
noncomputable section
universe u v w

namespace Reg.D5.S3.Combinatorics.Graph.CliqueFactorization.Algebraic
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
local instance {V : Type u} : DecidableEq V := Classical.decEq V

abbrev Params := Σ V : Type u, Σ Ω : V → Type v, Σ A : Type w,
  Σ _ : CommGroup A, Σ _ : Fintype V, Σ _ : SimpleGraph V,
    Σ _ : ((i : V) → Ω i) → A, Finset V → ((i : V) → Ω i) → A

abbrev signature : Signature where
  Params := Params.{u, v, w}
  State p := (i : p.1) → p.2.1 i
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def reader (p : Params.{u, v, w}) (x : (i : p.1) → p.2.1 i) : p.2.2.1 :=
  p.2.2.2.2.2.2.1 x

def actual : Realization signature.{u, v, w} :=
  realize signature (fun _ p x => reader p x) (fun e => nomatch e)

def rejected : Realization signature.{u, v, w} :=
  realize signature (fun _ p _ => by letI := p.2.2.2.1; exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v, w}
  Law R := ∀ {V : Type u} {Ω : V → Type v} {A : Type w}
    [hA : CommGroup A] [hV : Fintype V] (G : SimpleGraph V)
    (f : ((i : V) → Ω i) → A),
    (∀ i j, i ≠ j → ¬ G.Adj i j → ∀ (x : (i : V) → Ω i) (a : Ω i) (b : Ω j),
      f x * f (Function.update (Function.update x i a) j b) =
        f (Function.update x i a) * f (Function.update x j b)) ↔
    ∃ Φ : Finset V → ((i : V) → Ω i) → A,
      (∀ s : Finset V, DependsOn (Φ s) (s : Set V)) ∧
      (∀ s : Finset V, ¬ G.IsClique (s : Set V) → ∀ x, Φ s x = 1) ∧
      (∀ x, R.readout () ⟨V, Ω, A, hA, hV, G, f, Φ⟩ x = ∏ s : Finset V, Φ s x)

private abbrev TestV := ULift.{u} Bool
private abbrev TestΩ (_ : TestV.{u}) := ULift.{v} Bool
private abbrev TestA := ULift.{w} (Multiplicative ℤ)

private def testf (x : (i : TestV.{u}) → TestΩ.{u, v} i) : TestA.{w} :=
  if (x ⟨false⟩).down = true ∧ (x ⟨true⟩).down = true then
    ⟨Multiplicative.ofAdd 1⟩ else 1

private theorem test_values :
    testf.{u, v, w} (fun _ => ⟨false⟩) = 1 ∧
    testf.{u, v, w} (fun _ => ⟨true⟩) ≠ 1 := by
  constructor
  · simp [testf]
  · intro h
    have he := congrArg (fun a : TestA.{w} => Multiplicative.toAdd a.down) h
    simp [testf] at he

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  classical
  intro law
  let G : SimpleGraph TestV.{u} := ⊥
  have factors : ∃ Φ : Finset TestV.{u} → ((i : TestV.{u}) → TestΩ.{u, v} i) → TestA.{w},
      (∀ s : Finset TestV.{u}, DependsOn (Φ s) (s : Set TestV.{u})) ∧
      (∀ s : Finset TestV.{u}, ¬ G.IsClique (s : Set TestV.{u}) → ∀ x, Φ s x = 1) ∧
      (∀ x, rejected.readout ()
        ⟨TestV.{u}, TestΩ.{u, v}, TestA.{w}, inferInstance, inferInstance,
          G, testf, Φ⟩ x = ∏ s : Finset TestV.{u}, Φ s x) := by
    refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
    · intro s x y h; rfl
    · intro s hs x; rfl
    · intro x; simp [rejected, realize]
  have rect := (law G testf).mpr factors
  have h := rect ⟨false⟩ ⟨true⟩ (by decide) (by simp [G])
    (fun _ => ⟨false⟩) ⟨true⟩ ⟨true⟩
  have he := congrArg (fun a : TestA.{w} => Multiplicative.toAdd a.down) h
  simp [testf, Function.update_apply] at he

private theorem dependence : ObservationalDependence signature.{u, v, w} actual := by
  intro role
  let p : Params.{u, v, w} :=
    ⟨TestV.{u}, TestΩ.{u, v}, TestA.{w}, inferInstance, inferInstance,
      ⊥, testf, fun _ _ => 1⟩
  refine ⟨p, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  change testf.{u, v, w} (fun _ => ⟨false⟩) ≠ testf.{u, v, w} (fun _ => ⟨true⟩)
  rw [test_values.1]
  exact Ne.symm test_values.2

def family : Registration arena.{u, v, w}
    (type_of% (@SimpleGraph.CliqueFactorization.rectangle_iff_clique_factorization.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@SimpleGraph.CliqueFactorization.rectangle_iff_clique_factorization.{u, v, w},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SimpleGraph.CliqueFactorization.rectangle_iff_clique_factorization.{u, v, w})
    (Realization signature.{u, v, w}) Unit Unit where
  unitName := `SimpleGraph.CliqueFactorization.rectangle_iff_clique_factorization.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.CliqueFactorization.Algebraic.family
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
    owner := `D5.S3.Combinatorics.Graph.CliqueFactorization.Algebraic
    definition := none
    coordinates := #[0, 1, 2, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.CliqueFactorization.Algebraic

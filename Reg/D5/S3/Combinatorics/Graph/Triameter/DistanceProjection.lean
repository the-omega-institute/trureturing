import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Triameter.DistanceProjection

/-! Source-bound triameter observations for the packing and projection estimates. -/

namespace Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Triameter
open _root_.D5.S3.Combinatorics.Graph.Triameter.EvenLegTriangle (H Vertex)
open _root_.D5.S3.ConceptDynamics.InformationEscape

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

abbrev signature : DependentFamily.Signature where
  Params := Σ V : Type u, Fintype V
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ p G => @triameter p.1 p.2 G) (fun e => nomatch e)

private theorem actual_dependence :
    DependentFamily.ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let V := ULift.{u} (Fin 3)
  refine ⟨⟨V, inferInstance⟩, ⊥, ⊤, ?_⟩
  change triameter (⊥ : SimpleGraph V) ≠ triameter (⊤ : SimpleGraph V)
  have hz : triameter (⊥ : SimpleGraph V) = 0 := by
    simp [triameter, perimeter, SimpleGraph.dist_bot]
  let a (i : Fin 3) : V := ⟨i⟩
  have h01 : a 0 ≠ a 1 := by decide
  have h02 : a 0 ≠ a 2 := by decide
  have h12 : a 1 ≠ a 2 := by decide
  have hle : 3 ≤ triameter (⊤ : SimpleGraph V) := by
    have h := Finset.le_sup (f := perimeter (⊤ : SimpleGraph V)) (Finset.mem_univ a)
    simpa [triameter, perimeter, SimpleGraph.dist_top_of_ne h01,
      SimpleGraph.dist_top_of_ne h02, SimpleGraph.dist_top_of_ne h12] using h
  omega

private def constant (n : ℕ) : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => n) (fun e => nomatch e)

private theorem singleton_indepNum : (⊤ : SimpleGraph (ULift.{u} Unit)).indepNum = 1 := by
  let V := ULift.{u} Unit
  let G : SimpleGraph V := ⊤
  obtain ⟨A, ha⟩ := G.exists_isNIndepSet_indepNum
  have hu : G.indepNum ≤ 1 := by
    rw [← ha.card_eq, ← show Fintype.card V = 1 by simp [V]]
    exact Finset.card_le_univ A
  let x : V := ⟨()⟩
  have hi : G.IsIndepSet (({x} : Finset V) : Set V) := by
    intro a ha b hb hne
    exact (hne (Subsingleton.elim a b)).elim
  have hl := hi.card_le_indepNum (t := {x})
  simp only [Finset.card_singleton] at hl
  exact Nat.le_antisymm hu hl

abbrev upperArena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V}, G.Connected →
    R.readout () ⟨V, inst⟩ G + 1 ≤ 4 * G.indepNum

abbrev projectionArena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V}, G.Connected →
    R.readout () ⟨V, inst⟩ G = 4 * G.indepNum - 1 →
    ∃ (q : Fin 3 → ℕ) (f : V → Vertex q),
      G.indepNum = q 0 + q 1 + q 2 + 1 ∧ Function.Surjective f ∧
      (∀ x y, G.Adj x y → f x = f y ∨ (H q).Adj (f x) (f y)) ∧
      (∀ u v, (H q).Adj u v → ∃ x y, G.Adj x y ∧ f x = u ∧ f y = v)

abbrev lowerArena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V}, G.Connected →
    ∀ {q : Fin 3 → ℕ} {f : V → Vertex q}, Function.Surjective f →
      (∀ x y, G.Adj x y → f x = f y ∨ (H q).Adj (f x) (f y)) →
      4 * (q 0 + q 1 + q 2) + 3 ≤ R.readout () ⟨V, inst⟩ G

private theorem upper_rejects_constant : ¬ upperArena.{u}.Law (constant.{u} 4) := by
  intro law
  have h := @law (ULift.{u} Unit) _ ⊤ SimpleGraph.connected_top
  rw [singleton_indepNum] at h
  exact (by decide : ¬ (5 : ℕ) ≤ 4) h

private theorem projection_rejects_constant : ¬ projectionArena.{u}.Law (constant.{u} 3) := by
  intro law
  have he : (3 : ℕ) = 4 * (⊤ : SimpleGraph (ULift.{u} Unit)).indepNum - 1 := by
    rw [singleton_indepNum]
  obtain ⟨q, f, _, hs, _, _⟩ := @law (ULift.{u} Unit) _ ⊤ SimpleGraph.connected_top he
  let a : Vertex q := ⟨0, 0⟩
  let b : Vertex q := ⟨1, 0⟩
  obtain ⟨v, hv⟩ := hs a
  obtain ⟨w, hw⟩ := hs b
  have hab : a = b := hv.symm.trans ((congrArg f (Subsingleton.elim v w)).trans hw)
  exact (by decide : (0 : Fin 3) ≠ 1) (congrArg Sigma.fst hab)

private theorem lower_rejects_constant : ¬ lowerArena.{u}.Law (constant.{u} 0) := by
  intro law
  let q : Fin 3 → ℕ := fun _ => 0
  let f : ULift.{u} (Vertex q) → Vertex q := ULift.down
  have hs : Function.Surjective f := fun x => ⟨⟨x⟩, rfl⟩
  have hmap (x y : ULift.{u} (Vertex q)) (_ : (⊤ : SimpleGraph _).Adj x y) :
      f x = f y ∨ (H q).Adj (f x) (f y) := by
    change x.down = y.down ∨ (H q).Adj x.down y.down
    obtain ⟨⟨i, a⟩⟩ := x
    obtain ⟨⟨j, b⟩⟩ := y
    by_cases h : i = j
    · subst j
      exact Or.inl (congrArg (Sigma.mk i) ((Fin.eq_zero a).trans (Fin.eq_zero b).symm))
    · exact Or.inr (Or.inr ⟨h, (Fin.eq_zero a ▸ rfl), (Fin.eq_zero b ▸ rfl)⟩)
  have h := @law (ULift.{u} (Vertex q)) _ ⊤ SimpleGraph.connected_top q f hs hmap
  exact (by decide : ¬ (3 : ℕ) ≤ 0) h

private theorem constant_sensitivity
    (L : DependentFamily.Realization signature.{u} → Prop) (n : ℕ) (rejects : ¬ L (constant.{u} n)) :
    DependentFamily.Sensitivity (⟨signature.{u}, L⟩ : DependentFamily.Arena) actual.{u} := by
  constructor
  · intro i
    refine ⟨constant n, ?_, rfl, rejects⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i

abbrev upperScope := type_of% (@triameter_le_indepNum.{u})

def upperEvidence : DependentFamily.Registration upperArena.{u} upperScope.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@triameter_le_indepNum.{u}, constant 4, upper_rejects_constant⟩
  sensitivity := constant_sensitivity upperArena.{u}.Law 4 upper_rejects_constant
  dependence := actual_dependence

def upperContract : Contract.Registration.{_, _, _, 0, 0, 0, u+1, u, 0, 0, 0, 0}
    (@triameter_le_indepNum.{u})
    (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.Triameter.triameter_le_indepNum
    "Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection/Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection.upperArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection.upperEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena.{u}⟩
  objectArena := .source ⟨upperArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena.{u} ⟨upperEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature.{u}
    (fun _ p G => @triameter p.1 p.2 G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Triameter.DistanceProjection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev projectionScope := type_of% (@k1_equality_projection.{u})

def projectionEvidence : DependentFamily.Registration projectionArena.{u} projectionScope.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@k1_equality_projection.{u}, constant 3, projection_rejects_constant⟩
  sensitivity := constant_sensitivity projectionArena.{u}.Law 3 projection_rejects_constant
  dependence := actual_dependence

def projectionContract : Contract.Registration.{_, _, _, 0, 0, 0, u+1, u, 0, 0, 0, 0}
    (@k1_equality_projection.{u})
    (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.Triameter.k1_equality_projection
    "Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection/Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection.projectionArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection.projectionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨projectionArena.{u}⟩
  objectArena := .source ⟨projectionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source projectionArena.{u} ⟨projectionEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature.{u}
    (fun _ p G => @triameter p.1 p.2 G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Triameter.DistanceProjection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev lowerScope := type_of% (@triameter_ge_of_evenLegTriangle.{u})

def lowerEvidence : DependentFamily.Registration lowerArena.{u} lowerScope.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@triameter_ge_of_evenLegTriangle.{u}, constant 0, lower_rejects_constant⟩
  sensitivity := constant_sensitivity lowerArena.{u}.Law 0 lower_rejects_constant
  dependence := actual_dependence

def lowerContract : Contract.Registration.{_, _, _, 0, 0, 0, u+1, u, 0, 0, 0, 0}
    (@triameter_ge_of_evenLegTriangle.{u})
    (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.Triameter.triameter_ge_of_evenLegTriangle
    "Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection/Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection.lowerArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection.lowerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena.{u}⟩
  objectArena := .source ⟨lowerArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena.{u} ⟨lowerEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature.{u}
    (fun _ p G => @triameter p.1 p.2 G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Triameter.DistanceProjection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.Triameter.DistanceProjection

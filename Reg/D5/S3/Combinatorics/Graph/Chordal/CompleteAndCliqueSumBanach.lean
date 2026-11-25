import D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.FinCases

/-! Source-bound observations of complete graph and clique-sum reconstruction radii. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph

noncomputable section
universe u v w
namespace Upper

abbrev signature : Signature where
  Params := Type u
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ V ε => ((Nat.card V : ℝ) - 2) / Nat.card V * ε) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (_hm : 2 ≤ Nat.card V)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε)
    (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : V → E, ∀ i j, i ≠ j → ‖g i j - (φ j - φ i)‖ ≤ R.readout () V ε

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 2)
  have hm : 2 ≤ Nat.card V := by simp [V, Nat.card_eq_fintype_card]
  obtain ⟨φ,hφ⟩ := h (V := V) hm (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl
    (by simp) (by simp)
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  have hab : a ≠ b := by
    intro he
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)
  have he := hφ a b hab
  change ‖(0 : ULift.{v} ℝ) - (φ b - φ a)‖ ≤ -1 at he
  linarith [norm_nonneg ((0 : ULift.{v} ℝ) - (φ b - φ a))]

def family : Registration arena.{u,v} (type_of% (@completeGraph_banach_upper_bound.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@completeGraph_banach_upper_bound.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨ULift.{u} (Fin 3), 0, 1, ?_⟩
    norm_num [actual, realize, Nat.card_eq_fintype_card]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@completeGraph_banach_upper_bound.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `SimpleGraph.completeGraph_banach_upper_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach.Upper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Upper
namespace Lower

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ m => ((m : ℝ) - 2) / m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (_hm : 2 ≤ m),
    ∃ g : Fin m → Fin m → ZeroDivSkew m,
      (∀ i j, g j i = -g i j) ∧
      (∀ i j l, i ≠ j → j ≠ l → i ≠ l → ‖g i j + g j l - g i l‖ ≤ 1) ∧
      ∀ φ : Fin m → ZeroDivSkew m, ∃ u v, u ≠ v ∧
        R.readout () () m ≤ ‖g u v - (φ v - φ u)‖

private theorem zero_two (f : ZeroDivSkew 2) : f = 0 := by
  have hd (i : Fin 2) : f.val i i = 0 := by linarith [f.property.1 i i]
  have h0 := f.property.2 (0 : Fin 2)
  have h1 := f.property.2 (1 : Fin 2)
  rw [Fin.sum_univ_two, hd] at h0 h1
  apply Subtype.ext
  funext i j
  change f.val i j = 0
  fin_cases i <;> fin_cases j
  · exact hd 0
  · change f.val (0 : Fin 2) 1 = 0
    simpa using h0
  · change f.val (1 : Fin 2) 0 = 0
    simpa using h1
  · exact hd 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨g, _, _, hL⟩ := h 2 (by decide)
  obtain ⟨i,j,_,he⟩ := hL (fun _ => 0)
  change 1 ≤ ‖g i j - (0 - 0)‖ at he
  rw [zero_two (g i j)] at he
  norm_num at he

def family : Registration arena (type_of% (@completeGraph_banach_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨completeGraph_banach_lower_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(),2,3,?_⟩
    norm_num [actual,realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@completeGraph_banach_lower_bound) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.completeGraph_banach_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach.Lower.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "body", "arg", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Lower
namespace Gluing

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ m R => (2 - 1 / (m : ℝ)) * R) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ {I : Type w} {V : Type u} {E : Type v}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Finite V]
    (T : SimpleGraph I) (_hT : T.IsTree) (G : SimpleGraph V) (P : I → Set V)
    (_hcover : ∀ x, ∃ a, x ∈ P a)
    (_hedge : ∀ x y, G.Adj x y → ∃ a, x ∈ P a ∧ y ∈ P a)
    (m : ℕ) (_hm : 1 ≤ m)
    (_hattach : ∀ a b, T.Adj a b → (P a ∩ P b).Nonempty ∧
      G.IsClique (P a ∩ P b) ∧ Nat.card ↥(P a ∩ P b) ≤ m)
    (_hdisjoint : ∀ a b, a ≠ b → ¬ T.Adj a b → Disjoint (P a) (P b))
    (_hsep : ∀ a b c, T.Adj a b → T.Adj a c → b ≠ c →
      Disjoint (P a ∩ P b) (P a ∩ P c) ∧
      ∀ x ∈ P a ∩ P b, ∀ y ∈ P a ∩ P c, ¬ G.Adj x y)
    (g : V → V → E) (R : ℝ) (_hR : 0 ≤ R)
    (φ : I → V → E)
    (_hfit : ∀ a x, x ∈ P a → ∀ y, y ∈ P a → G.Adj x y →
      ‖g x y - (φ a y - φ a x)‖ ≤ R),
    ∃ Φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (Φ y - Φ x)‖ ≤ A.readout () m R

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  classical
  intro h
  let I := ULift.{w} Unit
  let V := ULift.{u} (Fin 2)
  let a : I := ⟨()⟩
  let x : V := ⟨0⟩
  let y : V := ⟨1⟩
  have hT : (⊥ : SimpleGraph I).IsTree := by
    refine ⟨Connected.mk ?_, isAcyclic_bot⟩
    intro p q
    have he : p = q := Subsingleton.elim _ _
    subst q
    exact Walk.nil.reachable
  obtain ⟨Φ,hΦ⟩ := h (I := I) (V := V) (E := ULift.{v} ℝ) ⊥ hT ⊤
    (fun _ => Set.univ)
    (fun x => ⟨a,Set.mem_univ x⟩)
    (fun x y _ => ⟨a,Set.mem_univ x,Set.mem_univ y⟩)
    1 (by decide) (by simp) (by intro a b hab _; exact (hab (Subsingleton.elim _ _)).elim) (by simp)
    (fun _ _ => 0) 0 le_rfl (fun _ _ => 0) (by simp)
  have hxy : (⊤ : SimpleGraph V).Adj x y := by
    change x ≠ y
    intro he
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)
  have he := hΦ x y hxy
  change ‖(0 : ULift.{v} ℝ) - (Φ y - Φ x)‖ ≤ -1 at he
  linarith [norm_nonneg ((0 : ULift.{v} ℝ) - (Φ y - Φ x))]

def family : Registration arena.{u,v,w}
    (type_of% (@separatedCliqueSum_banach_gain_potential.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separatedCliqueSum_banach_gain_potential.{u,v,w}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨1,0,1,?_⟩
    norm_num [actual,realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@separatedCliqueSum_banach_gain_potential.{u,v,w}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.separatedCliqueSum_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach.Gluing.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach
    definition := none
    coordinates := #[12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "body", "body", "body",
        "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Gluing

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach

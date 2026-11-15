import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
import D5.S3.Combinatorics.Graph.Chordal.Characterization
import Reg.Support.DependentFamily

/-! Full source-family registrations for the joint table and the completion criterion. -/

open _root_.D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
universe u
noncomputable section
attribute [local instance] Fintype.ofFinite
set_option backward.isDefEq.respectTransparency false

abbrev signature : Signature where
  Params := Σ V : Type u, V → V → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p i => p.2 i) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

private theorem zero_cycles {V : Type*} (G : SimpleGraph V) :
    ∀ (m : ℕ), 3 ≤ m → ∀ c : Fin m → V, Function.Injective c →
      (∀ i, G.Adj (c i) (c (finRotate m i))) →
      ∀ F : Finset (Fin m), Odd F.card →
      (∑ _i ∈ F, (0 : ℝ)) - (∑ _i ∈ Finset.univ \ F, (0 : ℝ)) ≤
        ((F.card : ℝ) - 1) * Real.pi := by
  intro m _ c _ _ F hF
  have hcard : 1 ≤ F.card := by obtain ⟨k,hk⟩ := hF; omega
  have hreal : (1 : ℝ) ≤ F.card := by exact_mod_cast hcard
  simp only [Finset.sum_const_zero,sub_zero]
  exact mul_nonneg (sub_nonneg.mpr hreal) Real.pi_pos.le

namespace Angle
abbrev arena : Arena where
  signature := signature.{u}
  Law Z := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (θ : V → V → ℝ)
    (_hsym : ∀ a b, θ a b = θ b a) (_hd : ∀ a, θ a a = 0)
    (_hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (_hcycles : ∀ (m : ℕ), 3 ≤ m → ∀ c : Fin m → V, Function.Injective c →
      (∀ i, G.Adj (c i) (c (finRotate m i))) →
      ∀ F : Finset (Fin m), Odd F.card →
      (∑ i ∈ F, θ (c i) (c (finRotate m i))) -
        (∑ i ∈ Finset.univ \ F, θ (c i) (c (finRotate m i))) ≤
          ((F.card : ℝ) - 1) * Real.pi),
    ∃ Γ : V → V → ℝ, (∀ a b, Γ a b = Γ b a) ∧ (∀ a, Γ a a = 0) ∧
      (∀ a b, 0 ≤ Γ a b ∧ Γ a b ≤ Real.pi) ∧
      (∀ a b, G.Adj a b → Γ a b = Z.readout () ⟨V, θ⟩ a b) ∧
      (∀ a b c, Γ a b ≤ Γ a c + Γ c b) ∧
      (∀ a b c, Γ a b + Γ b c + Γ c a ≤ 2 * Real.pi)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin 2)
  obtain ⟨Γ,_,_,hb,he,_,_⟩ := h (V := V) ⊤ (fun _ _ => 0)
    (by intros; rfl) (by intros; rfl) (by intros; exact ⟨le_refl _,Real.pi_pos.le⟩)
    (zero_cycles ⊤)
  let i : V := ⟨0⟩
  let j : V := ⟨1⟩
  have hh := he i j (by change i ≠ j; intro hij; have := congrArg (fun a : V => a.down.val) hij; norm_num [i,j] at this)
  change Γ i j = -1 at hh
  linarith [(hb i j).1]

def evidence : Registration arena.{u} (type_of% @exists_joint_angle_table.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_joint_angle_table.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let V := ULift.{u} (Fin 2)
    let θ : V → V → ℝ := fun a _ => a.down.val
    refine ⟨⟨V,θ⟩,⟨0⟩,⟨1⟩,?_⟩
    intro he
    have hh := congrFun he (⟨0⟩ : V)
    norm_num [actual,realize,θ] at hh

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_joint_angle_table.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.QuadraticForms.PartialTwoTreePsdCompletion.exists_joint_angle_table.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.PartialTwoTreePsdCompletion.Angle.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p i => p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","arg","arg","fn","arg","body","body","body","arg","fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Angle
namespace Completion
abbrev arena : Arena where
  signature := signature.{u}
  Law Z := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (_hG : ∃ H : SimpleGraph V, G ≤ H ∧ H.IsChordal ∧
      ∀ C : Set V, H.IsClique C → Nat.card C ≤ 3)
    (A : Matrix V V ℝ) (_hsym : ∀ i j, A i j = A j i)
    (_hdiag : ∀ i, A i i = 1)
    (_hbound : ∀ i j, G.Adj i j → -1 ≤ A i j ∧ A i j ≤ 1),
    (∃ B : Matrix V V ℝ, B.PosSemidef ∧ B.rank ≤ 3 ∧
      (∀ i, B i i = 1) ∧ (∀ i j, G.Adj i j → B i j = Z.readout () ⟨V, A⟩ i j)) ↔
    ∀ (m : ℕ), 3 ≤ m → ∀ c : Fin m → V, Function.Injective c →
      (∀ i, G.Adj (c i) (c (finRotate m i))) →
      ∀ F : Finset (Fin m), Odd F.card →
      (∑ i ∈ F, Real.arccos (A (c i) (c (finRotate m i)))) -
        (∑ i ∈ Finset.univ \ F, Real.arccos (A (c i) (c (finRotate m i)))) ≤
          ((F.card : ℝ) - 1) * Real.pi

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin 3)
  have hp : (⊤ : SimpleGraph V).IsPEO (fun i => i.down.val) := by
    constructor
    · intro i j hij
      exact ULift.ext (Fin.ext hij)
    · intro v i _ j _ hij
      exact hij
  have hgraph : ∃ H : SimpleGraph V, (⊤ : SimpleGraph V) ≤ H ∧ H.IsChordal ∧
      ∀ C : Set V, H.IsClique C → Nat.card C ≤ 3 := by
    refine ⟨⊤,le_refl _,hp.isChordal,?_⟩
    intro C _
    simpa [V] using Nat.card_le_card_of_injective (Subtype.val : C → V) Subtype.val_injective
  have hc : ∀ (m : ℕ), 3 ≤ m → ∀ c : Fin m → V, Function.Injective c →
      (∀ i, (⊤ : SimpleGraph V).Adj (c i) (c (finRotate m i))) →
      ∀ F : Finset (Fin m), Odd F.card →
      (∑ i ∈ F, Real.arccos ((fun _ _ : V => (1 : ℝ)) (c i) (c (finRotate m i)))) -
        (∑ i ∈ Finset.univ \ F, Real.arccos ((fun _ _ : V => (1 : ℝ)) (c i) (c (finRotate m i)))) ≤
          ((F.card : ℝ) - 1) * Real.pi := by
    simpa only [Real.arccos_one] using zero_cycles (⊤ : SimpleGraph V)
  obtain ⟨B,hB,hr,hd,he⟩ := (h (V := V) ⊤ hgraph (Matrix.of (fun _ _ => 1))
    (by intros; rfl) (by intros; rfl) (by intros; norm_num)).mpr hc
  let c : Fin 3 → V := ULift.up
  have hb : ∃ T : Matrix (Fin 3) (Fin 3) ℝ, T.PosSemidef ∧ T.rank ≤ 3 ∧
      (∀ i, T i i = 1) ∧ (∀ i, T i (finRotate 3 i) = -1) := by
    refine ⟨B.submatrix c c,hB.submatrix c,?_,fun i => hd (c i),?_⟩
    · have hsub := B.rank_submatrix_le c c
      simp only [Matrix.rank_eq_finrank_span_cols] at hsub hr ⊢
      exact hsub.trans hr
    · intro i
      have hh := he (c i) (c (finRotate 3 i)) (by
        change c i ≠ c (finRotate 3 i)
        intro hi
        have hh := congrArg ULift.down hi
        fin_cases i <;> norm_num [finRotate_apply,c] at hh)
      exact hh
  have hh := (D5.S3.QuadraticForms.CycleRankThreePsdCompletion.cycle_rank_three_iff
    (n := 3) (by omega) (fun _ => -1) (by intros; norm_num)).mp hb Finset.univ (by decide)
  norm_num [Real.arccos_neg_one,Fin.sum_univ_succ] at hh
  linarith [Real.pi_pos]

def evidence : Registration arena.{u} (type_of% @partial_two_tree_rank_three_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@partial_two_tree_rank_three_iff.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let V := ULift.{u} (Fin 2)
    let A : V → V → ℝ := fun a _ => a.down.val
    refine ⟨⟨V,A⟩,⟨0⟩,⟨1⟩,?_⟩
    intro he
    have hh := congrFun he (⟨0⟩ : V)
    norm_num [actual,realize,A] at hh

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@partial_two_tree_rank_three_iff.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.QuadraticForms.PartialTwoTreePsdCompletion.partial_two_tree_rank_three_iff.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.PartialTwoTreePsdCompletion.Completion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p i => p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","arg","body","arg","arg","arg","body","body","body","arg","fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Completion
end
end Reg.D5.S3.QuadraticForms.PartialTwoTreePsdCompletion

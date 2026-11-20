import D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The target component count used to bound a forest connector. -/

open LeanInformationAudit Equiv Relation
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound

noncomputable section
universe u

private abbrev targetSignature : Signature where
  Params := Σ V : Type u, V → V → Prop
  State p := Finset (Component p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def size : Realization targetSignature.{u} :=
  realize targetSignature (fun _ _ targets => targets.card) (fun e => nomatch e)

private def zero : Realization targetSignature.{u} :=
  realize targetSignature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev forestArena : Arena where
  signature := targetSignature.{u}
  Law R := ∀ {V : Type u} [Finite V] (E : V → V → Prop) (k : V → Bool) (n : ℕ)
    (_h0 : Nat.card (Side k false) = n) (_h1 : Nat.card (Side k true) = n)
    (_hsize : Nat.card {p : V × V // E p.1 p.2} + 2 ≤ n)
    (μ : PMF (AlternatingCompletion E k))
    (_hμ : ∀ σ, μ σ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹),
    ∃ (t : Component E ≃ Tail E) (h : Component E ≃ Head E),
      (∀ A, Quotient.mk (EqvGen.setoid E) (t A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      ∀ (A : Component E) (targets : Finset (Component E)), A ∉ targets →
        let targetCount := R.readout () ⟨V, E⟩ targets
        μ.toOuterMeasure {σ | ∃ B ∈ targets, σ.1 (t A) = (h B).1} ≤
          (targetCount : ℝ≥0∞) /
            ((n - Nat.card {p : V × V // E p.1 p.2} - 1 : ℕ) : ℝ≥0∞)

private abbrev Four := ULift.{u} (Bool × Bool)

private def color (v : Four.{u}) : Bool := v.down.1

private theorem color_count (b : Bool) : Nat.card (Side color.{u} b) = 2 := by
  let e : Side color.{u} b ≃ Bool :=
    { toFun := fun v => v.1.down.2
      invFun := fun q => ⟨⟨(b, q)⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨a,c⟩, h⟩
        change a = b at h
        subst a
        rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card]

private def pristine : Four.{u} → Four.{u} → Prop := fun _ _ => False

private theorem pristine_class {a b : Four.{u}}
    (h : Quotient.mk (EqvGen.setoid pristine) a = Quotient.mk (EqvGen.setoid pristine) b) :
    a = b := by
  have he : EqvGen pristine a b := Quotient.exact h
  clear h
  induction he with
  | rel _ _ h => exact h.elim
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

private theorem rejectsZero : ¬ forestArena.{u}.Law zero := by
  classical
  intro law
  let V := Four.{u}
  let k : V → Bool := color
  let d : V → Bool := fun x => !(k x)
  have cnt (b : Bool) : Nat.card (Side k b) = 2 := color_count b
  have left : inventory k d false true = 2 := (cross_inventory k false).trans (cnt false)
  have right : inventory k d true false = 2 := (cross_inventory k true).trans (cnt true)
  have hV : Nat.card V = 4 := by simp [V, Four, Nat.card_eq_fintype_card]
  have hK : Nat.card (Compatible k d) = 2 := by
    rw [compatible_cycle_card k d (left.trans right.symm), hV, left, cnt, cnt]
    decide
  obtain ⟨σ⟩ := (Nat.card_pos_iff.mp (hK ▸ (by decide : 0 < 2))).1
  let completion : AlternatingCompletion pristine k :=
    ⟨σ.1, σ.2.1, σ.2.2.1, (fun _ _ he => he.elim), fun x => by
      exact (Bool.not_eq_iff.mp (σ.2.2.2 x)).symm⟩
  let : Nonempty (AlternatingCompletion pristine k) := ⟨completion⟩
  let : Fintype (AlternatingCompletion pristine k) := Fintype.ofFinite _
  let μ := uniformPmf (AlternatingCompletion pristine k)
  have hμ (τ : AlternatingCompletion pristine k) :
      μ τ = (Nat.card (AlternatingCompletion pristine k) : ℝ≥0∞)⁻¹ := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have edges : Nat.card {p : V × V // pristine p.1 p.2} = 0 := by
    let : IsEmpty {p : V × V // pristine p.1 p.2} := ⟨fun p => p.2.elim⟩
    simp
  obtain ⟨t, h, ht, hh, hm⟩ := law pristine k 2
    (cnt false) (cnt true) (by rw [edges]) μ hμ
  let : Fintype (Component pristine) := Fintype.ofFinite _
  let A : Component pristine := Quotient.mk _ (⟨(false, false)⟩ : V)
  let T := Finset.univ.erase A
  have no : A ∉ T := Finset.notMem_erase _ _
  have all : {c : AlternatingCompletion pristine k | ∃ B ∈ T, c.1 (t A) = (h B).1} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro c
    let head : Head pristine := ⟨c.1 (t A), fun ⟨_, hp⟩ => hp.elim⟩
    let B := h.symm head
    have he : (h B).1 = c.1 (t A) := congrArg Subtype.val (h.apply_symm_apply head)
    have hn : B ≠ A := by
      intro hb
      have ha : (h A).1 = (t A).1 := pristine_class ((hh A).trans (ht A).symm)
      have ec : c.1 (t A) = (t A).1 := he.symm.trans ((congrArg (fun C => (h C).1) hb).trans ha)
      exact c.2.2.2.2 (t A) (congrArg k ec)
    exact ⟨B, Finset.mem_erase.mpr ⟨hn, Finset.mem_univ _⟩, he.symm⟩
  have hmass : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)
  have hbad := hm A T no
  simp [zero, realize, all, hmass] at hbad

private theorem dependence : ObservationalDependence targetSignature.{u} size := by
  classical
  intro _
  let A : Component pristine := Quotient.mk _ (⟨(false, false)⟩ : Four.{u})
  refine ⟨⟨Four.{u}, pristine⟩, ∅, {A}, ?_⟩
  simp [size, realize]

def evidence : Registration forestArena.{u} (type_of% (@mass_of_successor_components.{u})) where
  actual := size
  bridge := Iff.rfl
  variation := ⟨@mass_of_successor_components.{u}, zero, rejectsZero⟩
  sensitivity := ⟨fun i => ⟨zero, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejectsZero⟩, fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@mass_of_successor_components.{u}) (Realization targetSignature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound.mass_of_successor_components
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨forestArena.{u}⟩
  objectArena := .source ⟨forestArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source forestArena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize targetSignature (fun _ _ targets => targets.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


namespace ArcCount

private abbrev signature : Signature where
  Params := Type u
  State V := V → V → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ V E => Nat.card {a : V × V // E a.1 a.2}) (fun e => nomatch e)

private def zero : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev One := ULift.{u} Unit

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨One.{u}, (fun _ _ => False), (fun _ _ => True), ?_⟩
  change Nat.card {a : One.{u} × One.{u} // False} ≠
    Nat.card {a : One.{u} × One.{u} // True}
  simp [Nat.card_eq_fintype_card]

private abbrev sparseArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (E : V → V → Prop)
    (σ : Perm V) (_full : σ.IsCycleOn Set.univ)
    (_hedge : ∀ a b, E a b → σ a = b)
    (_hsparse : R.readout () V E < Nat.card V), ∀ v, ¬ TransGen E v v

private theorem sparseRejectsZero : ¬ sparseArena.{u}.Law zero := by
  intro h
  let v : One.{u} := ULift.up ()
  have hs : (1 : Perm One.{u}).IsCycleOn Set.univ :=
    Equiv.Perm.isCycleOn_one.mpr (fun _ _ _ _ => Subsingleton.elim _ _)
  have hn : zero.readout () One.{u} (fun _ _ => True) < Nat.card One.{u} := by
    simp [zero, realize, Nat.card_eq_fintype_card]
  exact h (fun _ _ => True) 1 hs (fun _ _ _ => Subsingleton.elim _ _) hn v
    (TransGen.single trivial)

def sparseEvidence : Registration sparseArena.{u} (type_of% (@partial_cycle_acyclic.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@partial_cycle_acyclic.{u}, zero, sparseRejectsZero⟩
  sensitivity := ⟨fun i => ⟨zero,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, sparseRejectsZero⟩, fun e => nomatch e⟩
  dependence := dependence

private abbrev headArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (E : V → V → Prop) (k : V → Bool) (b : Bool),
    Nat.card (Side k b) - R.readout () V E ≤ Nat.card {x : Head E // k x = b}

private theorem headsRejectZero : ¬ headArena.{u}.Law zero := by
  intro h
  have hle := h (V := One.{u}) (fun _ _ => True) (fun _ => false) false
  simpa [zero, realize, Side, Head, Nat.card_eq_fintype_card] using hle

def headEvidence : Registration headArena.{u} (type_of% (@heads_card_ge.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@heads_card_ge.{u}, zero, headsRejectZero⟩
  sensitivity := ⟨fun i => ⟨zero,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, headsRejectZero⟩, fun e => nomatch e⟩
  dependence := dependence


def sparseRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@partial_cycle_acyclic.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound.partial_cycle_acyclic
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound.ArcCount.sparseEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sparseArena.{u}⟩
  objectArena := .source ⟨sparseArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sparseArena.{u} ⟨sparseEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ V E => Nat.card {a : V × V // E a.1 a.2}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def headRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@heads_card_ge.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound.heads_card_ge
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound.ArcCount.headEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨headArena.{u}⟩
  objectArena := .source ⟨headArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source headArena.{u} ⟨headEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ V E => Nat.card {a : V × V // E a.1 a.2}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ArcCount

end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound

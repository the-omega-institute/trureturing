import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.Symbolic.AmenableGardenOfEden

/-! Source-bound audits for full group cellular maps. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden
open MeasureTheory Filter Set Function
open scoped Pointwise

namespace Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden

noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

abbrev Inputs := Σ A : Type u, Σ G : Type v, Σ _ : Group G, Σ S : Finset G, (S → A) → A

abbrev codeSignature : Signature where
  Params := Inputs.{u,v}
  State P := P.2.1 → P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.2.1 → P.1
  Anchor := Empty
  finiteAnchor := inferInstance

def codeActual : Realization codeSignature.{u,v} :=
  realize codeSignature (fun _ P => @localMap P.2.1 P.2.2.1 P.1 P.2.2.2.1 P.2.2.2.2)
    (fun e => nomatch e)

def codeRejected : Realization codeSignature.{u,v} :=
  realize codeSignature (fun _ _ => id) (fun e => nomatch e)

def codeArena : Arena where
  signature := codeSignature.{u,v}
  Law R := ∀ {G : Type v} [inst : Group G] {A : Type u} [Finite A]
    (_ham : letI : MeasurableSpace G := ⊤
      NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)))
    (S : Finset G) (φ : (S → A) → A),
    Surjective (R.readout () ⟨A, G, inst, S, φ⟩) ↔ Preinjective S φ

theorem finite_amenable (G : Type v) [Group G] [Finite G] :
    letI : MeasurableSpace G := ⊤
    NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)) := by
  letI : MeasurableSpace G := ⊤
  letI : Fintype G := Fintype.ofFinite G
  have h : IsFoelner Gᵐᵒᵖ (Measure.count : Measure G)
      (pure () : Filter Unit) (fun _ => Set.univ) := IsFoelner.univ_of_isFiniteMeasure
  exact ((isFoelner_iff_tendsto _ _).mp h).neBot

private theorem codeRejected_law : ¬ codeArena.{u,v}.Law codeRejected := by
  classical
  intro hlaw
  let G := ULift.{v} Unit
  have hp := (@hlaw G inferInstance (ULift.{u} Bool) inferInstance
    (finite_amenable G) ∅ (fun _ => ULift.up false)).mp Function.surjective_id
  have he := hp (fun _ => ULift.up false) (fun _ => ULift.up true) (Set.toFinite _) rfl
  have hc := congrArg ULift.down (congrFun he (1 : G))
  cases hc

def codeFamily : Registration codeArena.{u,v}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.garden_of_eden.{u,v})) where
  actual := codeActual
  bridge := Iff.rfl
  variation := ⟨@garden_of_eden.{u,v}, codeRejected, codeRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨codeRejected, ?_, rfl, codeRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    classical
    intro i
    let G := ULift.{v} Unit
    let S : Finset G := {1}
    let P : Inputs.{u,v} := ⟨ULift.{u} Bool, G, inferInstance, S,
      fun w => w ⟨1, by simp [S]⟩⟩
    refine ⟨P, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
    intro he
    have hc := congrArg ULift.down (congrFun he (1 : G))
    cases hc

def registration_code : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.garden_of_eden.{u,v})
    (Realization codeSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.code
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.codeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨codeArena.{u,v}⟩
  objectArena := .source ⟨codeArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source codeArena.{u,v} ⟨codeFamily.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize codeSignature.{u,v}
    (fun _ P => @localMap P.2.1 P.2.2.1 P.1 P.2.2.2.1 P.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.AmenableGardenOfEden
    definition := none
    coordinates := #[0, 1, 2, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev CountInputs := Σ A : Type u, Σ G : Type v, Σ _ : Group G, Σ _S : Finset G, Finset G

abbrev countSignature : Signature where
  Params := CountInputs.{u,v}
  State P := (P.2.2.2.1 → P.1) → P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature.{u,v} :=
  realize countSignature (fun _ P φ => Nat.card
    (@ImagePatterns P.2.1 P.2.2.1 P.1 P.2.2.2.1 φ P.2.2.2.2)) (fun e => nomatch e)

def countRejected : Realization countSignature.{u,v} :=
  realize countSignature (fun _ P _ => Nat.card P.1 ^ P.2.2.2.2.card) (fun e => nomatch e)

def countArena : Arena where
  signature := countSignature.{u,v}
  Law R := ∀ {G : Type v} [inst : Group G] {A : Type u} [Finite A]
    (S : Finset G) (φ : (S → A) → A) {x y : G → A},
    x ≠ y → Set.Finite {g | x g ≠ y g} → localMap S φ x = localMap S φ y →
    ∃ C : Finset G, ∃ p q : C → A, p ≠ q ∧
      (∀ (t : G) (z : G → A), (∀ c : C, z (t * c) = p c) →
        localMap S φ (writePattern C q t z) = localMap S φ z) ∧
      ∀ F : Finset G, ∃ T : Finset G, T ⊆ F ∧
        (∀ t ∈ T, ∀ r ∈ T, t ≠ r → ∀ c : C, ∀ e : C, t * c ≠ r * e) ∧
        F.card ≤ T.card * C.card ^ 2 ∧
        T.card * C.card ≤ (F * insert 1 (S ∪ C)).card ∧
        R.readout () ⟨A, G, inst, S, F⟩ φ ≤ (Nat.card A ^ C.card - 1) ^ T.card *
          Nat.card A ^ ((F * insert 1 (S ∪ C)).card - T.card * C.card)

private theorem countRejected_law : ¬ countArena.{u,v}.Law countRejected := by
  classical
  intro hlaw
  let G := ULift.{v} Unit
  letI : DecidableEq G := fun a b => Classical.propDecidable (a = b)
  let φ : ((∅ : Finset G) → ULift.{u} Bool) → ULift.{u} Bool := fun _ => ⟨false⟩
  let x : G → ULift.{u} Bool := fun _ => ⟨false⟩
  let y : G → ULift.{u} Bool := fun _ => ⟨true⟩
  have hne : x ≠ y := by
    intro he
    have hc := congrArg ULift.down (congrFun he 1)
    cases hc
  obtain ⟨C, p, q, hpq, _herase, hpack⟩ := @hlaw G inferInstance (ULift.{u} Bool)
    inferInstance ∅ φ x y hne (Set.toFinite _) rfl
  obtain ⟨c, _⟩ := Function.ne_iff.mp hpq
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨c, c.property⟩
  have hCle : C.card ≤ 1 := by simpa [G] using Finset.card_le_univ C
  have hC : C.card = 1 := by omega
  obtain ⟨T, hTsub, _hdis, hdense, _hinside, hcount⟩ := hpack {1}
  have hTle : T.card ≤ 1 := by simpa using Finset.card_le_card hTsub
  have hT : T.card = 1 := by simp only [Finset.card_singleton, hC] at hdense; omega
  have hUle : (({1} : Finset G) * insert 1 (∅ ∪ C)).card ≤ 1 := by
    simpa [G] using Finset.card_le_univ (({1} : Finset G) * insert 1 (∅ ∪ C))
  have hUpos : 0 < (({1} : Finset G) * insert 1 (∅ ∪ C)).card := by
    apply Finset.card_pos.mpr
    refine ⟨1, ?_⟩
    simpa only [one_mul] using Finset.mul_mem_mul
      (Finset.mem_singleton_self (1 : G)) (Finset.mem_insert_self 1 (∅ ∪ C))
  have hU : (({1} : Finset G) * insert 1 (∅ ∪ C)).card = 1 := by omega
  change Nat.card (ULift.{u} Bool) ^ ({1} : Finset G).card ≤
    (Nat.card (ULift.{u} Bool) ^ C.card - 1) ^ T.card *
      Nat.card (ULift.{u} Bool) ^
        ((({1} : Finset G) * insert 1 (∅ ∪ C)).card - T.card * C.card) at hcount
  rw [hC, hT, hU] at hcount
  norm_num at hcount

private theorem count_constant :
    Nat.card (ImagePatterns ({1} : Finset (ULift.{v} Unit))
      (fun _ => (ULift.up false : ULift.{u} Bool)) {1}) = 1 := by
  classical
  simp [ImagePatterns, localMap]

private theorem count_projection_lower :
    2 ≤ Nat.card (ImagePatterns ({1} : Finset (ULift.{v} Unit))
      (fun w : ({1} : Finset (ULift.{v} Unit)) → ULift.{u} Bool => w ⟨1, by simp⟩) {1}) := by
  classical
  let G := ULift.{v} Unit
  let S : Finset G := {1}
  let φ : (S → ULift.{u} Bool) → ULift.{u} Bool := fun w => w ⟨1, by simp [S]⟩
  let key : ULift.{u} Bool → ImagePatterns S φ {1} := fun a =>
    ⟨fun _ => a, (fun _ => a), rfl⟩
  have hk : Injective key := by
    intro a b he
    exact congrFun (congrArg Subtype.val he) ⟨1, by simp⟩
  simpa [Nat.card_eq_fintype_card, S, φ] using Nat.card_le_card_of_injective key hk

def countFamily : Registration countArena.{u,v}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.collision_replacement_count.{u,v})) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@collision_replacement_count.{u,v}, countRejected, countRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, countRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    classical
    intro i
    let G := ULift.{v} Unit
    let S : Finset G := {1}
    let P : CountInputs.{u,v} := ⟨ULift.{u} Bool, G, inferInstance, S, {1}⟩
    let φc : (S → ULift.{u} Bool) → ULift.{u} Bool := fun _ => ⟨false⟩
    let φp : (S → ULift.{u} Bool) → ULift.{u} Bool := fun w => w ⟨1, by simp [S]⟩
    refine ⟨P, φc, φp, ?_⟩
    intro he
    change Nat.card (ImagePatterns S φc {1}) = Nat.card (ImagePatterns S φp {1}) at he
    have hc := count_constant.{u,v}
    have hl := count_projection_lower.{u,v}
    change Nat.card (ImagePatterns S φc {1}) = 1 at hc
    change 2 ≤ Nat.card (ImagePatterns S φp {1}) at hl
    omega

def registration_count : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.collision_replacement_count.{u,v})
    (Realization countSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.count
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨countArena.{u,v}⟩
  objectArena := .source ⟨countArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena.{u,v} ⟨countFamily.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize countSignature.{u,v} (fun _ P φ => Nat.card
    (@ImagePatterns P.2.1 P.2.2.1 P.1 P.2.2.2.1 φ P.2.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.AmenableGardenOfEden
    definition := none
    coordinates := #[0, 1, 2, 4, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden

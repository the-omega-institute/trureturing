import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass
import Reg.Support.SingleDependentReadout

/-! The attained transposition mass observes the weights of the joint readout pairs. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass

open _root_.D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

noncomputable section

abbrev Table := Fin 4 → Finset (Fin 4) → ℝ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Table) (fun _ => Table)

def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ w : Table,
    (∀ i B, B.card = 2 → w i B = 1 / 24) ∧
    (∀ i B, B.card ≠ 2 → w i B = 0) ∧
    (∀ (g : Equiv.Perm (Fin 4)) i B, w (g i) (g.finsetCongr B) = w i B) ∧
    (∀ i : Fin 4, (∑ B : Finset (Fin 4), w i B) = 1 / 4) ∧
    (∀ B : Finset (Fin 4), B.card = 2 → (∑ i : Fin 4, w i B) = 1 / 6) ∧
    (∑ i, ∑ B, w i B) = 1 ∧
    transpositionMass (R.readout () () w) 0 1 = 1 / 6

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨w, _, _, _, _, _, _, fixed⟩
  change transpositionMass (fun _ _ => 0) 0 1 = (1 : ℝ) / 6 at fixed
  unfold transpositionMass at fixed
  have zero (a : Prop) [Decidable a] : (if a then (0 : ℝ) else 0) = 0 := by simp
  simp_rw [zero, Finset.sum_const_zero] at fixed
  norm_num at fixed

def family : Registration arena (type_of% (@uniform_label_pair_attains)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_label_pair_attains, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), fun _ _ => 0, fun _ _ => 1, ?_⟩
    intro equal
    have eval := congrFun (congrFun equal 0) ∅
    exact (zero_ne_one : (0 : ℝ) ≠ 1) eval

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@uniform_label_pair_attains) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass.attainment
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


universe u

private abbrev OrderedLabels := {p : Fin 4 × Fin 4 // p.1 ≠ p.2}

private instance : MulAction (Equiv.Perm (Fin 4)) (ULift.{u} OrderedLabels) where
  smul g s := ⟨⟨(g s.down.val.1, g s.down.val.2), g.injective.ne s.down.property⟩⟩
  one_smul s := by cases s; rfl
  mul_smul g h s := rfl

abbrev boundSignature : Signature.{u + 1, u, 0, u, 0} where
  Params := Type u
  State S := S → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ S := S → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def boundActual : Realization boundSignature.{u} :=
  realize boundSignature (fun _ _ w => w) (fun e => nomatch e)

def boundRejected : Realization boundSignature.{u} :=
  realize boundSignature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev boundArena : Arena where
  signature := boundSignature.{u}
  Law R := ∀ {S : Type u} [Fintype S] [MulAction (Equiv.Perm (Fin 4)) S]
      (w : S → ℝ),
    (∀ s, 0 ≤ w s) → (∑ s, w s = 1) →
    (∀ (g : Equiv.Perm (Fin 4)) s, w (g • s) = w s) →
    ∀ (i : S → Fin 4) (B : S → Finset (Fin 4)), (∀ s, (B s).card = 2) →
    (∀ (g : Equiv.Perm (Fin 4)) s, i (g • s) = g (i s)) →
    (∀ (g : Equiv.Perm (Fin 4)) s, B (g • s) = g.finsetCongr (B s)) →
    ∀ [DecidablePred (fun s : S => Equiv.swap (0 : Fin 4) 1 • s = s)],
      (∑ s ∈ univ.filter (fun s => Equiv.swap (0 : Fin 4) 1 • s = s), R.readout () S w s) ≤ 1 / 6

private theorem bound_rejected_law : ¬ boundArena.{u}.Law boundRejected := by
  classical
  intro altered
  let S := ULift.{u} OrderedLabels
  let w : S → ℝ := fun _ => 1 / 12
  let i (s : S) : Fin 4 := s.down.val.1
  let B (s : S) : Finset (Fin 4) := {s.down.val.1, s.down.val.2}
  have size : Fintype.card S = 12 :=
    (Fintype.card_congr Equiv.ulift).trans (by decide)
  have normalized : ∑ s : S, w s = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, size, nsmul_eq_mul]
    norm_num
  have card (s : S) : (B s).card = 2 := by
    rw [show B s = insert s.down.val.1 {s.down.val.2} from rfl, Finset.card_insert_of_notMem]
    · rfl
    · simpa using s.down.property
  have pairCov (g : Equiv.Perm (Fin 4)) (s : S) : B (g • s) = g.finsetCongr (B s) := by
    change {g s.down.val.1, g s.down.val.2} = g.finsetCongr {s.down.val.1, s.down.val.2}
    simp [Equiv.finsetCongr_apply]
  have impossible := altered w (fun _ => by norm_num [w]) normalized (fun _ _ => rfl)
    i B card (fun _ _ => rfl) pairCov
  let s : S := ⟨⟨(2, 3), by decide⟩⟩
  have fixed : Equiv.swap (0 : Fin 4) 1 • s = s := by
    apply ULift.ext
    apply Subtype.ext
    change (Equiv.swap (0 : Fin 4) 1 2, Equiv.swap (0 : Fin 4) 1 3) = (2, 3)
    decide
  have lower : (1 : ℝ) ≤ ∑ t ∈ univ.filter (fun t : S => Equiv.swap (0 : Fin 4) 1 • t = t), 1 :=
    Finset.single_le_sum (fun _ _ => zero_le_one) (mem_filter.mpr ⟨mem_univ s, fixed⟩)
  change (∑ t ∈ univ.filter (fun t : S => Equiv.swap (0 : Fin 4) 1 • t = t), (1 : ℝ)) ≤ 1 / 6 at impossible
  linarith

def boundFamily : Registration boundArena.{u} (type_of% (@seeded_transposition_mass_le.{u})) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@seeded_transposition_mass_le.{u}, boundRejected, bound_rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨boundRejected, ?_, rfl, bound_rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{u+1}, fun _ => 0, fun _ => 1, ?_⟩
    intro equal
    exact (zero_ne_one : (0 : ℝ) ≠ 1) (congrFun equal PUnit.unit)

def boundRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@seeded_transposition_mass_le.{u}) (Realization boundSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass.bound
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass.boundFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena.{u}⟩
  objectArena := .source ⟨boundArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena.{u} ⟨boundFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass

import D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Mathlib.Data.ULift

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching

open _root_.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

abbrev natSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

namespace Reflection

def actual : Realization natSignature :=
  realize natSignature (fun _ q j => reflected q j) (fun e => nomatch e)

def rejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence natSignature actual := by
  intro role
  refine ⟨2, 0, 1, ?_⟩
  change reflected 2 0 ≠ reflected 2 1
  decide

abbrev divisibility : Arena where
  signature := natSignature
  Law R := ∀ {q : ℕ}, 0 < q → ∀ i j : ℕ,
    i % q = R.readout () q j ↔ q ∣ i + j + 1

private theorem rejects_divisibility : ¬ divisibility.Law rejected := by
  intro h
  have hbad := (h (q := 1) (by decide) 0 0).mpr (by decide)
  exact (by decide : ¬ (0 : ℕ) % 1 = 1) hbad

def divisibilityFamily : Registration divisibility (type_of% @reflected_eq_iff_dvd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reflected_eq_iff_dvd, rejected, rejects_divisibility⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    divisibility.Law actual rejected rejects_divisibility
  dependence := dependence

abbrev equality : Arena where
  signature := natSignature
  Law R := ∀ {q : ℕ}, 0 < q → ∀ i j : ℕ,
    reflected q i = R.readout () q j ↔ i % q = j % q

private theorem rejects_equality : ¬ equality.Law rejected := by
  intro h
  have hbad := (h (q := 1) (by decide) 0 0).mpr rfl
  exact (by decide : reflected 1 0 ≠ 1) hbad

def equalityFamily : Registration equality (type_of% @reflected_eq_reflected_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reflected_eq_reflected_iff, rejected, rejects_equality⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    equality.Law actual rejected rejects_equality
  dependence := dependence

def divisibilityAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reflected_eq_iff_dvd) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.reflected_eq_iff_dvd.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.Reflection.divisibilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨divisibility⟩
  objectArena := .source ⟨divisibility⟩
  catalog := .anonymous
  localNames := false
  realization := .source divisibility ⟨divisibilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n q => reflected n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def equalityAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reflected_eq_reflected_iff) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.reflected_eq_reflected_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.Reflection.equalityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨equality⟩
  objectArena := .source ⟨equality⟩
  catalog := .anonymous
  localNames := false
  realization := .source equality ⟨equalityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n q => reflected n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reflection

namespace Capacity

def actual : Realization natSignature :=
  realize natSignature (fun _ n q => commonCapacity n q) (fun e => nomatch e)

def rejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence natSignature actual := by
  intro role
  refine ⟨1, 1, 2, ?_⟩
  change commonCapacity 1 1 ≠ commonCapacity 1 2
  decide

abbrev count : Arena where
  signature := natSignature
  Law R := ∀ (n : ℕ) {q : ℕ}, 0 < q →
    capacity (range q) (range n) (range n) (· % q) (reflected q) = R.readout () n q

private theorem rejects_count : ¬ count.Law rejected := by
  intro h
  exact (by decide : capacity (range 1) (range 1) (range 1) (· % 1) (reflected 1) ≠ 0)
    (h 1 (q := 1) (by decide))

def countFamily : Registration count (type_of% @reflected_capacity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reflected_capacity, rejected, rejects_count⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity count.Law actual rejected rejects_count
  dependence := dependence

abbrev lower : Arena where
  signature := natSignature
  Law R := ∀ {n q k : ℕ}, 0 < q → ∀ {I J : Finset ℕ},
    I ⊆ range n → J ⊆ range n → I.card = k → J.card = k →
      2 * (k - R.readout () n q) ≤ residueLoss q I J

private theorem rejects_lower : ¬ lower.Law rejected := by
  intro h
  have hbad := h (n := 1) (q := 1) (k := 1) (by decide) (I := range 1) (J := range 1)
    (by decide) (by decide) (by decide) (by decide)
  exact (by decide : ¬ 2 * (1 - 0) ≤ residueLoss 1 (range 1) (range 1)) hbad

def lowerFamily : Registration lower (type_of% @residue_loss_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@residue_loss_lower, rejected, rejects_lower⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity lower.Law actual rejected rejects_lower
  dependence := dependence

abbrev attainment : Arena where
  signature := natSignature
  Law R := ∀ {p n k : ℕ}, 0 < p → k ≤ n → ∀ e : ℕ,
    ∃ I ⊆ range n, ∃ J ⊆ range n, I.card = k ∧ J.card = k ∧
      ∀ a ≤ e, residueLoss (p ^ a) I J = 2 * (k - R.readout () n (p ^ a))

private theorem rejects_attainment : ¬ attainment.Law rejected := by
  intro h
  obtain ⟨I, hI, J, hJ, hIc, hJc, hbad⟩ :=
    h (p := 2) (n := 1) (k := 1) (by decide) (by decide) 0
  have hi : I = range 1 := eq_of_subset_of_card_le hI (by simpa [hIc])
  have hj : J = range 1 := eq_of_subset_of_card_le hJ (by simpa [hJc])
  subst I
  subst J
  exact (by decide : residueLoss 1 (range 1) (range 1) ≠ 2 * (1 - 0)) (hbad 0 le_rfl)

def attainmentFamily : Registration attainment (type_of% @exists_residue_minimizer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_residue_minimizer, rejected, rejects_attainment⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    attainment.Law actual rejected rejects_attainment
  dependence := dependence

def countAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reflected_capacity) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.reflected_capacity.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.Capacity.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨count⟩
  objectArena := .source ⟨count⟩
  catalog := .anonymous
  localNames := false
  realization := .source count ⟨countFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n q => commonCapacity n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def lowerAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@residue_loss_lower) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.residue_loss_lower.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.Capacity.lowerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨lower⟩
  objectArena := .source ⟨lower⟩
  catalog := .anonymous
  localNames := false
  realization := .source lower ⟨lowerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n q => commonCapacity n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def attainmentAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_residue_minimizer) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.exists_residue_minimizer.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.Capacity.attainmentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨attainment⟩
  objectArena := .source ⟨attainment⟩
  catalog := .anonymous
  localNames := false
  realization := .source attainment ⟨attainmentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n q => commonCapacity n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "arg", "arg", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Capacity

namespace Hierarchy

open _root_.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

abbrev Parameters :=
  Σ (α : Type u) (β : Type v) (γ : Type w) (_ : DecidableEq γ),
    Σ (_ : ℕ → α → γ) (_ : ℕ → β → γ) (_ : ℕ → Finset γ) (_ : Finset β), ℕ

abbrev signature : Signature.{max (u + 1) (v + 1) (w + 1), u, 0, 0, 0} where
  Params := Parameters.{u, v, w}
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Read the squared discrepancy as the selected left subset varies. -/
abbrev observeLoss (p : Parameters.{u, v, w}) (I : Finset p.1) : ℕ :=
  let labels := p.2.2.2.2
  let level := labels.2.2.2.2
  @loss p.1 p.2.1 p.2.2.1 p.2.2.2.1
    (labels.2.2.1 level) I labels.2.2.2.1 (labels.1 level) (labels.2.1 level)

def actual : Realization signature.{u, v, w} :=
  realize signature (fun _ p I => observeLoss p I) (fun e => nomatch e)

def rejected : Realization signature.{u, v, w} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena.{max (u + 1) (v + 1) (w + 1), u, 0, 0, 0} where
  signature := signature.{u, v, w}
  Law R := ∀ {α : Type u} {β : Type v} {γ : Type w}
    [DecidableEq α] [DecidableEq β] [dec : DecidableEq γ]
    (A : Finset α) (B : Finset β) (f : ℕ → α → γ) (g : ℕ → β → γ)
    (t : ℕ → Finset γ) (e k : ℕ)
    (_hcard : A.card = B.card) (_hk : k ≤ A.card)
    (_hnest : ∀ j < e, ∀ x y, f j x = g j y → f (j + 1) x = g (j + 1) y)
    (_hcoarse : ∀ x ∈ A, ∀ y ∈ B, f e x = g e y)
    (_hf : ∀ j ≤ e, ∀ x ∈ A, f j x ∈ t j)
    (_hg : ∀ j ≤ e, ∀ y ∈ B, g j y ∈ t j)
    (_hbal : ∀ j ≤ e, ∀ c ∈ t j, gap (fiber A (f j) c) (fiber B (g j) c) ≤ 1),
    ∃ I ⊆ A, ∃ J ⊆ B, I.card = k ∧ J.card = k ∧
      ∀ j ≤ e, R.readout () ⟨α, β, γ, dec, f, g, t, J, j⟩ I =
        2 * (k - capacity (t j) A B (f j) (g j))

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  let f : ℕ → ULift.{u} ℕ → ULift.{w} ℕ := fun _ _ => ULift.up 0
  let g : ℕ → ULift.{v} ℕ → ULift.{w} ℕ := fun _ _ => ULift.up 0
  obtain ⟨I, _, J, _, _, _, hopt⟩ :=
    h ∅ ∅ f g (fun _ => ∅) 0 0
      (by simp) (by simp) (by simp [f, g])
      (by simp) (by simp) (by simp) (by simp)
  simpa [rejected, realize] using hopt 0 le_rfl

private theorem dependence : ObservationalDependence signature.{u, v, w} actual := by
  intro role
  let p : Parameters.{u, v, w} :=
    ⟨ULift.{u} ℕ, ULift.{v} ℕ, ULift.{w} ℕ, inferInstance, fun _ _ => ULift.up 0,
      fun _ _ => ULift.up 0, fun _ => {ULift.up 0}, ∅, 0⟩
  refine ⟨p, ∅, {ULift.up 0}, ?_⟩
  change (0 : ℕ) ≠ 1
  decide

def family : Registration arena.{u, v, w} (type_of% @simultaneous_minimizer.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneous_minimizer.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hother
      exact (hother (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@simultaneous_minimizer.{u, v, w}) (Realization signature.{u, v, w}) Unit Unit where
  unitName :=
    `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.simultaneous_minimizer.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching.Hierarchy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, w} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u, v, w} (fun _ p I => observeLoss p I) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
    definition := none
    coordinates := #[0, 1, 2, 8, 9, 10, 21, 22]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Hierarchy

end Reg.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching

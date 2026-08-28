/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The symmetric weak-Pareto kernel has an explicit finite quotient with complete enumeration. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.ParetoEqOnDecidableEquivalence
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/- Library-search audit trail (2026-08-28):
   * Two D5 collision searches for `FiniteParetoQuotient`, `paretoClass`,
     `paretoClassImage`, `quotientEnum`, and the planned theorem names found
     only the frozen finite-carrier and symmetric-kernel prerequisites.
   * The frozen `pareto_eq_on_equivalence_laws` theorem supplies exactly the
     reflexive, symmetric, and transitive laws used to identify equal classes.
   * Pinned Mathlib supplies `Finset.mem_filter`, `Finset.mem_image`,
     `Finset.mem_attach`, `Finset.card_eq_one`, and `Fintype.ofFinset`; no
     theorem packages this explicit finite Pareto class image or its laws.
   * `Setoid.Partition` concerns abstract set-valued classes and `Quotient`;
     the source instead requires computable `Finset` classes and their image. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/-- The explicit symmetric-kernel class of an element of the finite carrier. -/
def paretoClass
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x : ParetoCarrier F) : Finset (ParetoCarrier F) :=
  @Finset.filter _ (fun y => ParetoEqOn value F y x)
    (fun y => paretoEqOnDecidable value F y x) (carrierEnum F)

/-- The finite image of all explicit symmetric-kernel classes. -/
def paretoClassImage
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) : Finset (Finset (ParetoCarrier F)) :=
  (carrierEnum F).image (paretoClass value F)

/-- The finite Pareto quotient is the subtype of classes in the explicit class image. -/
def FiniteParetoQuotient
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) :=
  { C : Finset (ParetoCarrier F) // C ∈ paretoClassImage value F }

/-- Every element of the finite quotient, explicitly enumerated. -/
def quotientEnum
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) : Finset (FiniteParetoQuotient value F) :=
  (paretoClassImage value F).attach

/-- The explicit class image constructs a `Fintype` without an inhabitance assumption. -/
@[implicit_reducible]
def finiteParetoQuotientFintype
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) : Fintype (FiniteParetoQuotient value F) :=
  Fintype.ofFinset (paretoClassImage value F) (fun _ => Iff.rfl)

section Laws

variable {Action Information Residual Transfer Cost Risk : Type u}
variable [DecidableEq Action]
variable [Preorder Information] [Preorder Residual] [Preorder Transfer]
variable [Preorder Cost] [Preorder Risk]
variable [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
variable [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
variable [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
variable [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
variable [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]

/-- Every subtype element occurs in the attached carrier enumeration. -/
@[simp]
theorem mem_carrierEnum (F : Finset Action) (x : ParetoCarrier F) :
    x ∈ carrierEnum F := by
  simp [carrierEnum]

/-- Membership in an explicit class is exactly symmetric weak Pareto equivalence. -/
@[simp]
theorem mem_paretoClass
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x y : ParetoCarrier F) :
    y ∈ paretoClass value F x ↔ ParetoEqOn value F y x := by
  simp [paretoClass]

/-- Every finite-carrier element belongs to its own symmetric-kernel class. -/
theorem mem_paretoClass_self
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x : ParetoCarrier F) :
    x ∈ paretoClass value F x := by
  exact (mem_paretoClass value F x x).2
    ((pareto_eq_on_equivalence_laws value F).1 x)

/-- Two explicit classes are equal exactly when their representatives are equivalent. -/
theorem paretoClass_eq_iff
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x y : ParetoCarrier F) :
    paretoClass value F x = paretoClass value F y ↔
      ParetoEqOn value F x y := by
  constructor
  · intro classesEqual
    apply (mem_paretoClass value F y x).1
    rw [← classesEqual]
    exact mem_paretoClass_self value F x
  · intro equivalent
    apply Finset.ext
    intro z
    simp only [mem_paretoClass]
    rcases pareto_eq_on_equivalence_laws value F with
      ⟨_, symmetric, transitive⟩
    constructor
    · intro zEquivalentX
      exact transitive z x y zEquivalentX equivalent
    · intro zEquivalentY
      exact transitive z y x zEquivalentY (symmetric x y equivalent)

/-- Every quotient class is represented by some element of the finite carrier. -/
theorem finiteParetoQuotient_has_representative
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C : FiniteParetoQuotient value F) :
    ∃ x : ParetoCarrier F, paretoClass value F x = C.1 := by
  rcases Finset.mem_image.mp C.property with ⟨x, _, classEquals⟩
  exact ⟨x, classEquals⟩

/-- Every class in the explicit finite quotient is nonempty. -/
theorem finiteParetoQuotient_nonempty
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C : FiniteParetoQuotient value F) :
    C.1.Nonempty := by
  rcases finiteParetoQuotient_has_representative value F C with ⟨x, classEquals⟩
  rw [← classEquals]
  exact ⟨x, mem_paretoClass_self value F x⟩

/-- Reclassifying any member of a quotient class returns that same class. -/
theorem paretoClass_eq_of_mem_finiteParetoQuotient
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C : FiniteParetoQuotient value F)
    (z : ParetoCarrier F) (hz : z ∈ C.1) :
    paretoClass value F z = C.1 := by
  rcases finiteParetoQuotient_has_representative value F C with ⟨x, classEquals⟩
  rw [← classEquals] at hz
  exact (paretoClass_eq_iff value F z x).2
    ((mem_paretoClass value F x z).1 hz) |>.trans classEquals

/-- The attached class image enumerates every quotient element. -/
@[simp]
theorem mem_quotientEnum
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C : FiniteParetoQuotient value F) :
    C ∈ quotientEnum value F := by
  change C ∈ (paretoClassImage value F).attach
  exact Finset.mem_attach _ C

/-- An empty finite carrier has no quotient classes. -/
theorem finiteParetoQuotient_empty
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (hF : F = ∅) :
    ∀ _ : FiniteParetoQuotient value F, False := by
  subst F
  intro C
  rcases finiteParetoQuotient_has_representative value ∅ C with ⟨x, _⟩
  exact Finset.notMem_empty x.1 x.property

/-- A one-element finite carrier has exactly one quotient class. -/
theorem finiteParetoQuotient_unique_of_card_eq_one
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (hF : F.card = 1) :
    ∃ C : FiniteParetoQuotient value F,
      ∀ D : FiniteParetoQuotient value F, D = C := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hF
  let x : ParetoCarrier ({a} : Finset Action) := ⟨a, by simp⟩
  let C : FiniteParetoQuotient value ({a} : Finset Action) :=
    ⟨paretoClass value {a} x, by
      apply Finset.mem_image_of_mem
      exact mem_carrierEnum {a} x⟩
  refine ⟨C, ?_⟩
  intro D
  rcases finiteParetoQuotient_has_representative value {a} D with
    ⟨y, classEquals⟩
  have yEqualsX : y = x := by
    apply Subtype.ext
    change y.1 = a
    exact Finset.mem_singleton.mp y.property
  apply Subtype.ext
  change D.1 = C.1
  calc
    D.1 = paretoClass value {a} y := classEquals.symm
    _ = paretoClass value {a} x := by rw [yEqualsX]
    _ = C.1 := rfl

/-- Class membership, class equality, class stability, explicit enumeration, and both
degenerate-carrier laws hold for the finite symmetric-kernel quotient. -/
theorem finite_pareto_quotient_exact_and_complete
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) :
    (∀ x : ParetoCarrier F, x ∈ carrierEnum F) ∧
      (∀ x y : ParetoCarrier F,
        y ∈ paretoClass value F x ↔ ParetoEqOn value F y x) ∧
      (∀ x : ParetoCarrier F, x ∈ paretoClass value F x) ∧
      (∀ x y : ParetoCarrier F,
        paretoClass value F x = paretoClass value F y ↔
          ParetoEqOn value F x y) ∧
      (∀ C : FiniteParetoQuotient value F, C.1.Nonempty) ∧
      (∀ (C : FiniteParetoQuotient value F) (z : ParetoCarrier F),
        z ∈ C.1 → paretoClass value F z = C.1) ∧
      (∀ C : FiniteParetoQuotient value F, C ∈ quotientEnum value F) ∧
      (F = ∅ → ∀ _ : FiniteParetoQuotient value F, False) ∧
      (F.card = 1 → ∃ C : FiniteParetoQuotient value F,
        ∀ D : FiniteParetoQuotient value F, D = C) := by
  exact
    ⟨mem_carrierEnum F,
      fun x y => mem_paretoClass value F x y,
      mem_paretoClass_self value F,
      fun x y => paretoClass_eq_iff value F x y,
      finiteParetoQuotient_nonempty value F,
      fun C z => paretoClass_eq_of_mem_finiteParetoQuotient value F C z,
      mem_quotientEnum value F,
      finiteParetoQuotient_empty value F,
      finiteParetoQuotient_unique_of_card_eq_one value F⟩

end Laws

/-- A two-action instance has two distinct explicit classes, so the class image is not
forced to collapse to a singleton. -/
example :
    let F : Finset Bool := {false, true}
    let value : Bool → GainVector Nat Nat Nat Nat Nat := fun action =>
      if action then
        { information := 1
          residualCapture := 1
          transfer := 1
          lifecycleCost := 0
          risk := 0 }
      else
        { information := 0
          residualCapture := 0
          transfer := 0
          lifecycleCost := 1
          risk := 1 }
    ∃ x y : ParetoCarrier F,
      paretoClass value F x ≠ paretoClass value F y := by
  dsimp
  refine ⟨⟨false, by simp⟩, ⟨true, by simp⟩, ?_⟩
  intro classesEqual
  have equivalent :=
    (paretoClass_eq_iff (fun action : Bool =>
      if action then
        { information := 1
          residualCapture := 1
          transfer := 1
          lifecycleCost := 0
          risk := 0 }
      else
        { information := 0
          residualCapture := 0
          transfer := 0
          lifecycleCost := 1
          risk := 1 }) {false, true}
      ⟨false, by simp⟩ ⟨true, by simp⟩).1 classesEqual
  simp [ParetoEqOn, ParetoWeakOn, ParetoWeak] at equivalent

#print axioms finite_pareto_quotient_exact_and_complete

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

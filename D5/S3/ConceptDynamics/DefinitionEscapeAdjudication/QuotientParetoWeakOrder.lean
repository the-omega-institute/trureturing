/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite quotient weak Pareto dominance is a decidable partial order. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.FiniteParetoQuotient
import Mathlib.Data.Finset.Prod

/- Library-search audit trail (2026-08-28):
   * Two D5 searches for `QuotientParetoWeak`, quotient-level weak Pareto
     dominance, finite Pareto scans, and Pareto antisymmetry found only the
     frozen carrier, kernel, and explicit-quotient prerequisites imported above.
   * The frozen `pareto_weak_reflexive_transitive` theorem supplies the
     representative-level preorder laws; `paretoClass_eq_iff` and
     `paretoClass_eq_of_mem_finiteParetoQuotient` transport those laws between
     representatives of the same explicit class.
   * Pinned Lean's `Finset.any` and `decide` provide the finite scan. No abstract
     `Quotient` or independently invented equivalence relation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/-- Quotient weak Pareto dominance holds when some representatives of the two
explicit classes stand in the carrier-level weak Pareto relation. -/
def QuotientParetoWeak
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action)
    (C D : FiniteParetoQuotient value F) : Prop :=
  ∃ x ∈ C.1, ∃ y ∈ D.1, ParetoWeakOn value F x y

/-- The direct finite scan of both explicit classes for a dominating pair. -/
def quotientParetoWeakScan
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action)
    (C D : FiniteParetoQuotient value F) : Bool :=
  letI : DecidablePred fun pair : ParetoCarrier F × ParetoCarrier F =>
      ParetoWeakOn value F pair.1 pair.2 := fun pair => by
    unfold ParetoWeakOn ParetoWeak
    infer_instance
  decide (((C.1.product D.1).filter fun pair =>
    ParetoWeakOn value F pair.1 pair.2).Nonempty)

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

/-- The Boolean scan is true exactly when the existential quotient relation holds. -/
@[simp]
theorem quotientParetoWeakScan_eq_true_iff
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C D : FiniteParetoQuotient value F) :
    quotientParetoWeakScan value F C D = true ↔
      QuotientParetoWeak value F C D := by
  letI : DecidablePred fun pair : ParetoCarrier F × ParetoCarrier F =>
      ParetoWeakOn value F pair.1 pair.2 := fun pair => by
    unfold ParetoWeakOn ParetoWeak
    infer_instance
  simp only [quotientParetoWeakScan, decide_eq_true_eq, QuotientParetoWeak]
  constructor
  · rintro ⟨⟨x, y⟩, pairMem⟩
    rcases Finset.mem_filter.mp pairMem with ⟨productMem, weak⟩
    rcases Finset.mem_product.mp productMem with ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, weak⟩
  · rintro ⟨x, hx, y, hy, weak⟩
    exact
      ⟨(x, y), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hy⟩, weak⟩⟩

/-- Quotient weak Pareto dominance is decided by scanning the two finite classes. -/
def quotientParetoWeakDecidable
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C D : FiniteParetoQuotient value F) :
    Decidable (QuotientParetoWeak value F C D) :=
  decidable_of_iff (quotientParetoWeakScan value F C D = true)
    (quotientParetoWeakScan_eq_true_iff value F C D)

private theorem paretoEqOn_of_members_same_quotient
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C : FiniteParetoQuotient value F)
    (x : ParetoCarrier F) (hx : x ∈ C.1)
    (y : ParetoCarrier F) (hy : y ∈ C.1) :
    ParetoEqOn value F x y := by
  apply (paretoClass_eq_iff value F x y).1
  exact
    (paretoClass_eq_of_mem_finiteParetoQuotient value F C x hx).trans
      (paretoClass_eq_of_mem_finiteParetoQuotient value F C y hy).symm

/-- Existence of one dominating representative pair is equivalent to dominance
for every representative pair. -/
theorem quotientParetoWeak_iff_all_representatives
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C D : FiniteParetoQuotient value F) :
    QuotientParetoWeak value F C D ↔
      ∀ x : ParetoCarrier F, x ∈ C.1 →
        ∀ y : ParetoCarrier F, y ∈ D.1 → ParetoWeakOn value F x y := by
  rcases pareto_weak_reflexive_transitive value with ⟨_, transitive⟩
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩ x hx y hy
    have hxa :=
      (paretoEqOn_of_members_same_quotient value F C x hx a ha).1
    have hby :=
      (paretoEqOn_of_members_same_quotient value F D b hb y hy).1
    exact transitive (transitive hxa hab) hby
  · intro allRepresentatives
    rcases finiteParetoQuotient_nonempty value F C with ⟨x, hx⟩
    rcases finiteParetoQuotient_nonempty value F D with ⟨y, hy⟩
    exact ⟨x, hx, y, hy, allRepresentatives x hx y hy⟩

/-- The quotient relation is reflexive. -/
theorem quotientParetoWeak_refl
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C : FiniteParetoQuotient value F) :
    QuotientParetoWeak value F C C := by
  rcases finiteParetoQuotient_nonempty value F C with ⟨x, hx⟩
  exact ⟨x, hx, x, hx, (pareto_weak_reflexive_transitive value).1 x.1⟩

/-- The quotient relation is transitive. -/
theorem quotientParetoWeak_trans
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C D E : FiniteParetoQuotient value F)
    (hCD : QuotientParetoWeak value F C D)
    (hDE : QuotientParetoWeak value F D E) :
    QuotientParetoWeak value F C E := by
  have allCD := (quotientParetoWeak_iff_all_representatives value F C D).1 hCD
  rcases hCD with ⟨c, hc, _, _, _⟩
  rcases hDE with ⟨d, hd, e, he, hde⟩
  exact
    ⟨c, hc, e, he,
      (pareto_weak_reflexive_transitive value).2 (allCD c hc d hd) hde⟩

/-- Mutual quotient dominance forces equality of the explicit classes. -/
theorem quotientParetoWeak_antisymm
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (C D : FiniteParetoQuotient value F)
    (hCD : QuotientParetoWeak value F C D)
    (hDC : QuotientParetoWeak value F D C) :
    C = D := by
  have allDC := (quotientParetoWeak_iff_all_representatives value F D C).1 hDC
  rcases hCD with ⟨x, hx, y, hy, hxy⟩
  have hyx := allDC y hy x hx
  have classesEqual : paretoClass value F x = paretoClass value F y :=
    (paretoClass_eq_iff value F x y).2 ⟨hxy, hyx⟩
  apply Subtype.ext
  change C.1 = D.1
  calc
    C.1 = paretoClass value F x :=
      (paretoClass_eq_of_mem_finiteParetoQuotient value F C x hx).symm
    _ = paretoClass value F y := classesEqual
    _ = D.1 := paretoClass_eq_of_mem_finiteParetoQuotient value F D y hy

/-- When the action carrier is empty, there are no quotient elements, so every
quantified relation claim on the quotient is vacuous. -/
theorem quotientParetoWeak_vacuous_of_empty
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (hF : F = ∅) :
    ∀ C D : FiniteParetoQuotient value F,
      QuotientParetoWeak value F C D := by
  intro C
  exact False.elim (finiteParetoQuotient_empty value F hF C)

/-- Representative independence, finite-scan decidability, and the three
partial-order laws hold on the explicit finite Pareto quotient. -/
theorem quotient_pareto_weak_finite_decidable_partial_order
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) :
    (∀ C D : FiniteParetoQuotient value F,
      QuotientParetoWeak value F C D ↔
        ∀ x : ParetoCarrier F, x ∈ C.1 →
          ∀ y : ParetoCarrier F, y ∈ D.1 → ParetoWeakOn value F x y) ∧
      (∀ C D : FiniteParetoQuotient value F,
        quotientParetoWeakScan value F C D = true ↔
          QuotientParetoWeak value F C D) ∧
      (∀ C D : FiniteParetoQuotient value F,
        Nonempty (Decidable (QuotientParetoWeak value F C D))) ∧
      (∀ C : FiniteParetoQuotient value F,
        QuotientParetoWeak value F C C) ∧
      (∀ C D E : FiniteParetoQuotient value F,
        QuotientParetoWeak value F C D →
          QuotientParetoWeak value F D E →
            QuotientParetoWeak value F C E) ∧
      (∀ C D : FiniteParetoQuotient value F,
        QuotientParetoWeak value F C D →
          QuotientParetoWeak value F D C → C = D) ∧
      (F = ∅ → ∀ C D : FiniteParetoQuotient value F,
        QuotientParetoWeak value F C D) := by
  exact
    ⟨quotientParetoWeak_iff_all_representatives value F,
      quotientParetoWeakScan_eq_true_iff value F,
      fun C D => ⟨quotientParetoWeakDecidable value F C D⟩,
      quotientParetoWeak_refl value F,
      fun C D E => quotientParetoWeak_trans value F C D E,
      fun C D => quotientParetoWeak_antisymm value F C D,
      quotientParetoWeak_vacuous_of_empty value F⟩

end Laws

/-- A two-class finite instance where quotient dominance holds in exactly one
direction, witnessing that the relation and antisymmetry theorem are nonvacuous. -/
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
    ∃ C D : FiniteParetoQuotient value F,
      QuotientParetoWeak value F C D ∧
        ¬ QuotientParetoWeak value F D C := by
  dsimp
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
  let x : ParetoCarrier ({false, true} : Finset Bool) := ⟨true, by simp⟩
  let y : ParetoCarrier ({false, true} : Finset Bool) := ⟨false, by simp⟩
  let C : FiniteParetoQuotient value {false, true} :=
    ⟨paretoClass value {false, true} x,
      Finset.mem_image_of_mem (paretoClass value {false, true})
        (mem_carrierEnum {false, true} x)⟩
  let D : FiniteParetoQuotient value {false, true} :=
    ⟨paretoClass value {false, true} y,
      Finset.mem_image_of_mem (paretoClass value {false, true})
        (mem_carrierEnum {false, true} y)⟩
  refine ⟨C, D, ?_, ?_⟩
  · exact
      ⟨x, mem_paretoClass_self value {false, true} x,
        y, mem_paretoClass_self value {false, true} y,
        by simp [ParetoWeakOn, ParetoWeak, x, y]⟩
  · intro reverseDominance
    have allReverse :=
      (quotientParetoWeak_iff_all_representatives value {false, true} D C).1
        reverseDominance
    have impossible := allReverse y
      (mem_paretoClass_self value {false, true} y) x
      (mem_paretoClass_self value {false, true} x)
    simp [ParetoWeakOn, ParetoWeak, value, x, y] at impossible

#print axioms quotient_pareto_weak_finite_decidable_partial_order

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

import LeanInformationAuditFibTests.AuricFib.LawFixture
import LeanInformationAudit.AuricFibCapture

/-! Search-reduction AURIC obligations over the actual Interface LawFact.
Unknown describes missing evidence, not a third mathematical possibility. -/

namespace LeanInformationAuditFibTests.AuricFib.SearchReduction
open LeanInformationAudit LeanInformationAudit.AuricFib.Contract

universe t s r a v

variable {Statement : Prop} {occurrence : Statement}
  {client : Analysis.Client.{0, t, s, r, 0, a, v} occurrence} {family : LawFamily client}

def isStrict (fact : LawFact family) : Bool := match fact with
  | .separated _ => true
  | _ => false

def isCollapsed (fact : LawFact family) : Bool := match fact with
  | .identifiable _ => true
  | _ => false

theorem strict_fact_witness (fact : LawFact family) (h : isStrict fact = true) :
    ∃ θ φ, family.domain θ ∧ family.domain φ ∧
      Pyramid.CoarseEq (family.law θ) (family.law φ) ∧
      Pyramid.delta (family.law θ) ≠ Pyramid.delta (family.law φ) := by
  cases fact with
  | separated proof => exact proof
  | deltaSign _ _ => simp [isStrict] at h
  | positiveWidth _ => simp [isStrict] at h
  | identifiable _ => simp [isStrict] at h

theorem collapsed_fact_determines (fact : LawFact family) (h : isCollapsed fact = true) :
    ∀ θ φ, family.domain θ → family.domain φ →
      Pyramid.CoarseEq (family.law θ) (family.law φ) →
      Pyramid.delta (family.law θ) = Pyramid.delta (family.law φ) := by
  cases fact with
  | identifiable proof => exact proof
  | deltaSign _ _ => simp [isCollapsed] at h
  | positiveWidth _ => simp [isCollapsed] at h
  | separated _ => simp [isCollapsed] at h

/-- A1: no pair of actual LawFacts on this same family/domain can disagree. -/
theorem strict_collapsed_exclusive (strict collapsed : LawFact family)
    (hs : isStrict strict = true) (hc : isCollapsed collapsed = true) : False := by
  obtain ⟨θ, φ, hθ, hφ, same, different⟩ := strict_fact_witness strict hs
  exact different (collapsed_fact_determines collapsed hc θ φ hθ hφ same)

theorem fact_list_consistent (facts : List (LawFact family)) :
    ¬ (facts.any isStrict = true ∧ facts.any isCollapsed = true) := by
  rintro ⟨hs, hc⟩
  obtain ⟨strict, _, hs⟩ := List.any_eq_true.mp hs
  obtain ⟨collapsed, _, hc⟩ := List.any_eq_true.mp hc
  exact strict_collapsed_exclusive strict collapsed hs hc

open LeanInformationAudit.AuricFib (Capture classifyCapture taskCapture)

def capture (facts : List (LawFact family)) : Capture :=
  classifyCapture (facts.any isStrict) (facts.any isCollapsed)

theorem capture_strict_iff (facts : List (LawFact family)) :
    capture facts = .strict ↔ facts.any isStrict = true := by
  cases hs : facts.any isStrict <;> cases hc : facts.any isCollapsed <;>
    simp [capture, classifyCapture, hs, hc]

theorem capture_collapsed_iff (facts : List (LawFact family)) :
    capture facts = .collapsed ↔ facts.any isCollapsed = true := by
  have consistent := fact_list_consistent facts
  cases hs : facts.any isStrict <;> cases hc : facts.any isCollapsed <;>
    simp [capture, classifyCapture, hs, hc]
  exact False.elim (consistent ⟨hs, hc⟩)

theorem capture_unknown_iff (facts : List (LawFact family)) :
    capture facts = .unknown ↔
      facts.any isStrict = false ∧ facts.any isCollapsed = false := by
  cases hs : facts.any isStrict <;> cases hc : facts.any isCollapsed <;>
    simp [capture, classifyCapture, hs, hc]

theorem task_zero_collapsed (family : Capture) : taskCapture family false = .collapsed := rfl

theorem task_uses_delta (family : Capture) : taskCapture family true = family := rfl

/-- A1: exactly one evidence verdict is selected, including missing evidence. -/
theorem capture_exhaustive_exclusive (facts : List (LawFact family)) :
    (capture facts = .strict ∧ capture facts ≠ .collapsed ∧ capture facts ≠ .unknown) ∨
    (capture facts = .collapsed ∧ capture facts ≠ .strict ∧ capture facts ≠ .unknown) ∨
    (capture facts = .unknown ∧ capture facts ≠ .strict ∧ capture facts ≠ .collapsed) := by
  cases capture facts <;> simp

/-- The underlying mathematical alternatives are exhaustive. This classical
statement does not acquire a usable LawFact for a real submitted contract. -/
theorem family_separated_or_identifiable :
    (∃ θ φ, family.domain θ ∧ family.domain φ ∧
      Pyramid.CoarseEq (family.law θ) (family.law φ) ∧
      Pyramid.delta (family.law θ) ≠ Pyramid.delta (family.law φ)) ∨
    (∀ θ φ, family.domain θ → family.domain φ →
      Pyramid.CoarseEq (family.law θ) (family.law φ) →
      Pyramid.delta (family.law θ) = Pyramid.delta (family.law φ)) := by
  classical
  by_cases h : ∃ θ φ, family.domain θ ∧ family.domain φ ∧
      Pyramid.CoarseEq (family.law θ) (family.law φ) ∧
      Pyramid.delta (family.law θ) ≠ Pyramid.delta (family.law φ)
  · exact Or.inl h
  · right
    intro θ φ hθ hφ same
    by_contra different
    exact h ⟨θ, φ, hθ, hφ, same, different⟩

/-- A2: appending postprocessing of an existing readout, including constant
identity metadata, leaves its fibers unchanged. No full-state identity premise. -/
theorem postprocessing_no_new_separation {State Observation Extra : Type*}
    (readout : State → Observation) (post : Observation → Extra) (x y : State) :
    (readout x, post (readout x)) = (readout y, post (readout y)) ↔
      readout x = readout y := by
  constructor
  · exact fun h => congrArg Prod.fst h
  · intro h
    rw [h]

example {State Observation Metadata : Type*} (readout : State → Observation)
    (metadata : Metadata) (x y : State) :
    (readout x, metadata) = (readout y, metadata) ↔ readout x = readout y :=
  postprocessing_no_new_separation readout (fun _ => metadata) x y

/-- Full state identity is outside the metadata claim and can separate states. -/
theorem full_state_identity_can_separate :
    (fun _ : Bool => ()) false = (fun _ : Bool => ()) true ∧
    (((), id false) : Unit × Bool) ≠ ((), id true) := by decide

/-- A3: a normalized, nonnegative, source-bound constant family has positive
width and positive delta, yet no actual separated LawFact can be supplied. -/
theorem positive_width_and_sign_not_strict :
    (∀ θ, LawFixture.family.domain θ →
      0 < Pyramid.width (LawFixture.family.law θ)) ∧
    (∀ θ, LawFixture.family.domain θ →
      0 < Pyramid.delta (LawFixture.family.law θ)) ∧
    ¬ ∃ fact : LawFact LawFixture.family, isStrict fact = true := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ _
    norm_num [Pyramid.width, Pyramid.r, Pyramid.X, Pyramid.Y, Pyramid.Z,
      LawFixture.mass, LawFixture.starMasses, Masses.value]
  · intro θ _
    norm_num [Pyramid.delta, Pyramid.r, Pyramid.kappa, Pyramid.X, Pyramid.Y, Pyramid.Z,
      LawFixture.mass, LawFixture.starMasses, Masses.value]
  · rintro ⟨fact, hs⟩
    exact strict_collapsed_exclusive fact
      (.identifiable (by intro θ φ _ _ _; rfl)) hs rfl

/-- Sign and width facts alone leave the actual evidence verdict unknown. -/
example (width : ∀ θ, family.domain θ → 0 < Pyramid.width (family.law θ))
    (sign : DeltaSign) (signed : ∀ θ, family.domain θ →
      sign.Holds (Pyramid.delta (family.law θ))) :
    capture [.positiveWidth width, .deltaSign sign signed] = .unknown := rfl

example : capture (family := LawFixture.family)
    [.identifiable (by intro θ φ _ _ _; rfl)] = .collapsed := rfl

#print axioms strict_fact_witness
#print axioms collapsed_fact_determines
#print axioms strict_collapsed_exclusive
#print axioms fact_list_consistent
#print axioms capture_strict_iff
#print axioms capture_collapsed_iff
#print axioms capture_unknown_iff
#print axioms task_zero_collapsed
#print axioms task_uses_delta
#print axioms capture_exhaustive_exclusive
#print axioms family_separated_or_identifiable
#print axioms postprocessing_no_new_separation
#print axioms full_state_identity_can_separate
#print axioms positive_width_and_sign_not_strict

end LeanInformationAuditFibTests.AuricFib.SearchReduction

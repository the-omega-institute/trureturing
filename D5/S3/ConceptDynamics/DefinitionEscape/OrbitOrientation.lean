/- GID: D5/S3/ConceptDynamics/DefinitionEscape/OrbitOrientation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Readouts hide or expose free involutions; Boolean orientations are transversals. -/

import D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveNegation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.OrbitOrientation

universe u v

open D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveNegation

/-- A readout hides an involution when it is constant on every involutive
orbit. -/
def HiddenReadout
    {X : Type u} {Output : Type v}
    (negation : InvolutiveNegation X) (readout : X → Output) : Prop :=
  ∀ x, readout (negation.neg x) = readout x

/-- A Boolean readout orients an involutive orbit when it flips on the paired
point. -/
def NegatingReadout
    {X : Type u}
    (negation : InvolutiveNegation X) (readout : X → Bool) : Prop :=
  ∀ x, readout (negation.neg x) = !readout x

/-- A subset selecting exactly one side of every involutive orbit. -/
def OrbitTransversal
    {X : Type u}
    (negation : InvolutiveNegation X) (subset : Set X) : Prop :=
  ∀ x, x ∈ subset ↔ negation.neg x ∉ subset

/-- The true support of a Boolean readout. -/
def trueSupport {X : Type u} (readout : X → Bool) : Set X :=
  {x | readout x = true}

/-- A transversal is equivalently a subset whose involutive image is its
Boolean complement. -/
theorem orbitTransversal_iff_imageSet_eq_complement
    {X : Type u} (negation : InvolutiveNegation X) (subset : Set X) :
    OrbitTransversal negation subset ↔
      imageSet negation subset = subsetᶜ := by
  constructor
  · intro transversal
    ext x
    rw [mem_imageSet_iff]
    have atNegated := transversal (negation.neg x)
    simpa only [negation.involutive x, Set.mem_compl_iff] using atNegated
  · intro imageEquals x
    have atNegated :=
      Set.ext_iff.mp imageEquals (negation.neg x)
    simpa only [mem_imageSet_iff, negation.involutive x,
      Set.mem_compl_iff] using atNegated

/-- A transversal is equivalently disjoint from its involutive image while the
two pieces cover the whole source. -/
theorem orbitTransversal_iff_disjoint_union
    {X : Type u} (negation : InvolutiveNegation X) (subset : Set X) :
    OrbitTransversal negation subset ↔
      Disjoint subset (imageSet negation subset) ∧
        subset ∪ imageSet negation subset = Set.univ := by
  constructor
  · intro transversal
    constructor
    · refine Set.disjoint_left.2 ?_
      intro x xInSubset xInImage
      have negatedInSubset :=
        (mem_imageSet_iff negation subset x).1 xInImage
      exact (transversal x).1 xInSubset negatedInSubset
    · ext x
      constructor
      · intro _
        trivial
      · intro _
        by_cases xInSubset : x ∈ subset
        · exact Or.inl xInSubset
        · right
          apply (mem_imageSet_iff negation subset x).2
          exact
            (transversal (negation.neg x)).2
              (by simpa only [negation.involutive x] using xInSubset)
  · rintro ⟨disjoint, covers⟩
    intro x
    constructor
    · intro xInSubset negatedInSubset
      apply Set.disjoint_left.1 disjoint xInSubset
      exact
        (mem_imageSet_iff negation subset x).2 negatedInSubset
    · intro xNotInSubset
      have xInCover : x ∈ subset ∪ imageSet negation subset := by
        rw [covers]
        trivial
      rcases xInCover with xInSubset | xInImage
      · exact False.elim (xNotInSubset xInSubset)
      · exact (mem_imageSet_iff negation subset x).1 xInImage

/-- Every negating Boolean readout has a transversal true support. -/
theorem negatingReadout_trueSupport_transversal
    {X : Type u} (negation : InvolutiveNegation X)
    (readout : X → Bool)
    (negating : NegatingReadout negation readout) :
    OrbitTransversal negation (trueSupport readout) := by
  intro x
  change readout x = true ↔ readout (negation.neg x) ≠ true
  rw [negating x]
  cases readout x <;> decide

/-- Conversely, a Boolean readout is negating exactly when its true support is
an orbit transversal. -/
theorem negatingReadout_iff_trueSupport_transversal
    {X : Type u} (negation : InvolutiveNegation X)
    (readout : X → Bool) :
    NegatingReadout negation readout ↔
      OrbitTransversal negation (trueSupport readout) := by
  constructor
  · exact negatingReadout_trueSupport_transversal negation readout
  · intro transversal x
    have atX := transversal x
    change readout x = true ↔ readout (negation.neg x) ≠ true at atX
    cases readoutAtX : readout x <;>
      cases readoutAtNegated : readout (negation.neg x) <;>
      simp [readoutAtX, readoutAtNegated] at atX ⊺

/-- A supplied transversal constructs an explicit Boolean orientation. -/
noncomputable def transversalReadout
    {X : Type u} (subset : Set X) : X → Bool :=
  fun x => if x ∈ subset then true else false

/-- The Boolean readout constructed from a transversal flips on every orbit. -/
theorem transversalReadout_negating
    {X : Type u} (negation : InvolutiveNegation X)
    (subset : Set X) (transversal : OrbitTransversal negation subset) :
    NegatingReadout negation (transversalReadout subset) := by
  intro x
  by_cases xInSubset : x ∈ subset
  · have negatedNotInSubset : negation.neg x ∉ subset :=
      (transversal x).1 xInSubset
    simp [transversalReadout, xInSubset, negatedNotInSubset]
  · have negatedInSubset : negation.neg x ∈ subset := by
      have atNegated := (transversal (negation.neg x)).2
      apply atNegated
      simpa only [negation.involutive x] using xInSubset
    simp [transversalReadout, xInSubset, negatedInSubset]

/-- Every Boolean orbit pair is locally either hidden or negated. -/
theorem boolean_orbit_dichotomy
    {X : Type u} (negation : InvolutiveNegation X)
    (readout : X → Bool) (x : X) :
    readout (negation.neg x) = readout x ∨
      readout (negation.neg x) = !readout x := by
  cases readoutAtX : readout x <;>
    cases readoutAtNegated : readout (negation.neg x) <;>
    simp [readoutAtX, readoutAtNegated]

/-- The two Boolean orbit cases are mutually exclusive. -/
theorem boolean_orbit_cases_exclusive
    {X : Type u} (negation : InvolutiveNegation X)
    (readout : X → Bool) (x : X) :
    ¬(readout (negation.neg x) = readout x ∧
      readout (negation.neg x) = !readout x) := by
  rintro ⟨same, negated⟩
  rw [same] at negated
  cases readout x <;> simp at negated

/-- Every Boolean orbit pair realizes exactly one of the hidden and negated
local cases. -/
theorem boolean_orbit_exactly_one
    {X : Type u} (negation : InvolutiveNegation X)
    (readout : X → Bool) (x : X) :
    (readout (negation.neg x) = readout x ∨
      readout (negation.neg x) = !readout x) ∧
    ¬(readout (negation.neg x) = readout x ∧
      readout (negation.neg x) = !readout x) :=
  ⟨boolean_orbit_dichotomy negation readout x,
    boolean_orbit_cases_exclusive negation readout x⟩

/-- A globally negating Boolean readout excludes fixed points for the underlying
map. -/
theorem negatingReadout_excludes_fixedPoint
    {X : Type u} (neg : X → X) (readout : X → Bool)
    (negating : ∀ x, readout (neg x) = !readout x) :
    ∀ x, neg x ≠ x := by
  intro x fixed
  have atX := negating x
  rw [fixed] at atX
  cases readout x <;> simp at atX

/-- Hidden readouts identify every point with its involutive partner. -/
theorem hiddenReadout_pair_equal
    {X : Type u} {Output : Type v}
    (negation : InvolutiveNegation X) (readout : X → Output)
    (hidden : HiddenReadout negation readout) (x : X) :
    readout x = readout (negation.neg x) :=
  (hidden x).symm

/-- Negating Boolean readouts separate every point from its involutive partner. -/
theorem negatingReadout_pair_ne
    {X : Type u}
    (negation : InvolutiveNegation X) (readout : X → Bool)
    (negating : NegatingReadout negation readout) (x : X) :
    readout x ≠ readout (negation.neg x) := by
  rw [negating x]
  cases readout x <;> decide

#print axioms orbitTransversal_iff_imageSet_eq_complement
#print axioms orbitTransversal_iff_disjoint_union
#print axioms negatingReadout_iff_trueSupport_transversal
#print axioms transversalReadout_negating
#print axioms boolean_orbit_dichotomy
#print axioms boolean_orbit_exactly_one

end D5.S3.ConceptDynamics.DefinitionEscape.OrbitOrientation

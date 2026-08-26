/- GID: D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/BirthStageFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every eventually present object in an append-only filtration has a unique first stage. -/

import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Monotone.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.BirthStageFiltration

/-- An append-only filtration is a monotone sequence of sets. -/
def AppendOnly {V : Type*} (stage : Nat → Set V) : Prop :=
  Monotone stage

/-- The first stage at which an eventually present object appears. -/
noncomputable def birthStage
    {V : Type*} (stage : Nat → Set V) (node : V)
    (eventuallyPresent : ∃ level, node ∈ stage level) : Nat :=
  by
    classical
    exact Nat.find eventuallyPresent

/-- An object is present at its birth stage. -/
theorem birthStage_mem
    {V : Type*} (stage : Nat → Set V) (node : V)
    (eventuallyPresent : ∃ level, node ∈ stage level) :
    node ∈ stage (birthStage stage node eventuallyPresent) := by
  classical
  exact Nat.find_spec eventuallyPresent

/-- Birth is no later than any stage at which the object is present. -/
theorem birthStage_le_of_mem
    {V : Type*} (stage : Nat → Set V) (node : V)
    (eventuallyPresent : ∃ level, node ∈ stage level)
    {level : Nat} (present : node ∈ stage level) :
    birthStage stage node eventuallyPresent ≤ level := by
  classical
  exact Nat.find_min' eventuallyPresent present

/-- No stage strictly before birth contains the object. -/
theorem not_mem_before_birthStage
    {V : Type*} (stage : Nat → Set V) (node : V)
    (eventuallyPresent : ∃ level, node ∈ stage level)
    {level : Nat} (before : level < birthStage stage node eventuallyPresent) :
    node ∉ stage level := by
  intro present
  exact (not_le_of_gt before)
    (birthStage_le_of_mem stage node eventuallyPresent present)

/-- In an append-only filtration, every later stage contains an object born earlier. -/
theorem mem_of_birthStage_le
    {V : Type*} {stage : Nat → Set V}
    (appendOnly : AppendOnly stage) (node : V)
    (eventuallyPresent : ∃ level, node ∈ stage level)
    {level : Nat}
    (birthBefore : birthStage stage node eventuallyPresent ≤ level) :
    node ∈ stage level :=
  appendOnly birthBefore (birthStage_mem stage node eventuallyPresent)

/-- The birth stage is the unique level satisfying presence and absence at every earlier stage. -/
theorem birthStage_unique
    {V : Type*} (stage : Nat → Set V) (node : V)
    (eventuallyPresent : ∃ level, node ∈ stage level)
    {level : Nat}
    (present : node ∈ stage level)
    (absentEarlier : ∀ earlier, earlier < level → node ∉ stage earlier) :
    birthStage stage node eventuallyPresent = level := by
  apply Nat.le_antisymm
  · exact birthStage_le_of_mem stage node eventuallyPresent present
  · by_contra notLe
    have birthBefore : birthStage stage node eventuallyPresent < level :=
      Nat.lt_of_not_ge notLe
    exact absentEarlier _ birthBefore
      (birthStage_mem stage node eventuallyPresent)

#print axioms birthStage_unique
#print axioms mem_of_birthStage_le

end D5.S3.ConceptDynamics.DagSemantics.BirthStageFiltration

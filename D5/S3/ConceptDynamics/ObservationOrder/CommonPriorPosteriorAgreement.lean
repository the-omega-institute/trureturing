/- GID: D5/S3/ConceptDynamics/ObservationOrder/CommonPriorPosteriorAgreement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/CommonPriorPosteriorAgreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commonly known posteriors from a positive finite common prior agree. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-21):
   * Repository searches found no common-prior posterior-agreement theorem.
     `CommonRuleInformationConvergence` is adjacent but has no prior,
     conditional posterior, information partition, or common-knowledge cell.
   * Pinned Mathlib searches for Aumann agreement, agreeing to disagree,
     common priors, and common-knowledge posteriors found no exact theorem.
   * Exact pinned Mathlib hits `Finpartition`, `Finpartition.biUnion_parts`,
     `Finpartition.disjoint`, `Finpartition.nonempty_of_mem_parts`, and
     `Finset.sum_biUnion` supply the source information-cell decomposition and
     are applied directly below.
   * `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement

/-- Common-prior mass of a finite collection of worlds. -/
def priorMass {World : Type*} (prior : World -> Real)
    (worlds : Finset World) : Real :=
  ∑ world ∈ worlds, prior world

/-- Common-prior mass of the event inside a finite collection of worlds. -/
def eventMass {World : Type*} [DecidableEq World]
    (prior : World -> Real) (event worlds : Finset World) : Real :=
  ∑ world ∈ worlds, if world ∈ event then prior world else 0

/-- The posterior of an event conditional on one finite information cell. -/
def cellPosterior {World : Type*} [DecidableEq World]
    (prior : World -> Real) (event cell : Finset World) : Real :=
  eventMass prior event cell / priorMass prior cell

private lemma sum_over_finpartition {World : Type*} [DecidableEq World]
    {worlds : Finset World} (partition : Finpartition worlds)
    (value : World -> Real) :
    (∑ cell ∈ partition.parts, ∑ world ∈ cell, value world) =
      ∑ world ∈ worlds, value world := by
  calc
    (∑ cell ∈ partition.parts, ∑ world ∈ cell, value world) =
        ∑ world ∈ partition.parts.biUnion id, value world := by
      symm
      simpa only [id_eq] using
        (Finset.sum_biUnion (f := value) partition.disjoint)
    _ = ∑ world ∈ worlds, value world := by
      rw [partition.biUnion_parts]

private lemma priorMass_pos_of_part {World : Type*} [DecidableEq World]
    {worlds : Finset World} (partition : Finpartition worlds)
    (prior : World -> Real) (priorPositive : ∀ world, 0 < prior world)
    {cell : Finset World} (hcell : cell ∈ partition.parts) :
    0 < priorMass prior cell := by
  rw [priorMass]
  apply Finset.sum_pos'
  · intro world _
    exact (priorPositive world).le
  · rcases partition.nonempty_of_mem_parts hcell with ⟨world, hworld⟩
    exact ⟨world, hworld, priorPositive world⟩

private lemma posterior_average_on_partition {World : Type*}
    [DecidableEq World] {worlds : Finset World}
    (partition : Finpartition worlds) (prior : World -> Real)
    (event : Finset World) (posteriorValue : Real)
    (priorPositive : ∀ world, 0 < prior world)
    (posteriorConstant : ∀ cell ∈ partition.parts,
      cellPosterior prior event cell = posteriorValue) :
    eventMass prior event worlds =
      posteriorValue * priorMass prior worlds := by
  have hcell (cell : Finset World) (hcell : cell ∈ partition.parts) :
      eventMass prior event cell = posteriorValue * priorMass prior cell := by
    exact (div_eq_iff
      (ne_of_gt (priorMass_pos_of_part partition prior priorPositive hcell))).mp
      (posteriorConstant cell hcell)
  calc
    eventMass prior event worlds =
        ∑ cell ∈ partition.parts, eventMass prior event cell := by
      symm
      simpa only [eventMass] using sum_over_finpartition partition
        (fun world => if world ∈ event then prior world else 0)
    _ = ∑ cell ∈ partition.parts,
          posteriorValue * priorMass prior cell := by
      apply Finset.sum_congr rfl
      intro cell hcell'
      exact hcell cell hcell'
    _ = posteriorValue *
          ∑ cell ∈ partition.parts, priorMass prior cell := by
      rw [Finset.mul_sum]
    _ = posteriorValue * priorMass prior worlds := by
      congr 1
      simpa only [priorMass] using sum_over_finpartition partition prior

/-- With a positive normalized common prior, if each agent's posterior is
constant on every information cell forming the nonempty common-knowledge cell,
then the two commonly known posterior values agree. -/
theorem common_knowledge_posteriors_agree
    {World : Type*} [Fintype World] [DecidableEq World]
    (prior : World -> Real) (event commonCell : Finset World)
    (informationOne informationTwo : Finpartition commonCell)
    (posteriorOne posteriorTwo : Real)
    (priorPositive : ∀ world, 0 < prior world)
    (priorNormalized : ∑ world, prior world = 1)
    (commonCellNonempty : commonCell.Nonempty)
    (posteriorOneCommon : ∀ cell ∈ informationOne.parts,
      cellPosterior prior event cell = posteriorOne)
    (posteriorTwoCommon : ∀ cell ∈ informationTwo.parts,
      cellPosterior prior event cell = posteriorTwo) :
    posteriorOne = posteriorTwo := by
  have _commonPriorProbability : priorMass prior Finset.univ = 1 := by
    simpa [priorMass] using priorNormalized
  have hmassPositive : 0 < priorMass prior commonCell := by
    rw [priorMass]
    apply Finset.sum_pos'
    · intro world _
      exact (priorPositive world).le
    · rcases commonCellNonempty with ⟨world, hworld⟩
      exact ⟨world, hworld, priorPositive world⟩
  have havgOne := posterior_average_on_partition informationOne prior event
    posteriorOne priorPositive posteriorOneCommon
  have havgTwo := posterior_average_on_partition informationTwo prior event
    posteriorTwo priorPositive posteriorTwoCommon
  nlinarith

/-- All public hypotheses are realized by the uniform prior on two worlds and
the indiscrete information partition. -/
example : (1 / 2 : Real) = 1 / 2 := by
  let prior : Bool -> Real := fun _ => 1 / 2
  let event : Finset Bool := {true}
  let commonCell : Finset Bool := Finset.univ
  let information : Finpartition commonCell :=
    Finpartition.indiscrete (by simp [commonCell])
  apply common_knowledge_posteriors_agree prior event commonCell
    information information (1 / 2) (1 / 2)
  · intro world
    norm_num [prior]
  · norm_num [prior]
  · simp [commonCell]
  · intro cell hcell
    have hcell' : cell = commonCell := by
      simpa [information, Finpartition.indiscrete] using hcell
    subst cell
    norm_num [cellPosterior, eventMass, priorMass, prior, event, commonCell]
  · intro cell hcell
    have hcell' : cell = commonCell := by
      simpa [information, Finpartition.indiscrete] using hcell
    subst cell
    norm_num [cellPosterior, eventMass, priorMass, prior, event, commonCell]

#print axioms common_knowledge_posteriors_agree

end D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement

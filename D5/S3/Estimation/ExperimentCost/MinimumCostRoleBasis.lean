/- GID: D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis
   generality: G
   mirror-B: D5/B/S3/Estimation/ExperimentCost/MinimumCostRoleBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Greedy linear-role bases minimize real cost; empty, zero, and singleton cases hold. -/

/- Library-search audit trail (2026-08-25):
   * Repository searches for `Matroid`, `LinearIndependent`, and semantic greedy-basis terms
     found no minimum-cost role-basis theorem or equivalent theorem under an unrelated name.
   * Every pinned `Mathlib/Combinatorics/Matroid` source was searched for weight, cost,
     greedy, minimum, linear, and representable variants. There is no weighted greedy theorem
     and no constructor for a vector-represented matroid in the pinned version.
   * `IndepMatroid.ofFinitaryCardAugment` supplies only the matroid constructor used below.
     `Matroid.Indep.mem_fundCircuit_iff` and `IsBase.exchange_isBase_of_indep` supply the
     exchange step; no greedy optimality is imported or repackaged.
   * `LinearIndepOn.insert`, `linearIndepOn_iff_linearIndepOn_finset`, and
     `exists_finite_card_le_of_finite_of_linearIndependent_of_span` discharge the linear
     independence axioms. The minimum-cost induction itself is new to this module.
   * No prime-number fact occurs: the prime-sensor phrase is motivation, not a hypothesis.
-/

import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Data.List.Dedup
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis

open scoped BigOperators
open Set Submodule

variable {K E V : Type*}

/-- A role basis is an independent finite role set spanning every available role vector. -/
def IsRoleBasis [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (roles : Finset E) : Prop :=
  LinearIndepOn K roleVector (roles : Set E) /\
    span K (roleVector '' (roles : Set E)) = span K (Set.range roleVector)

private theorem linear_indep_augmentation
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) {I J : Set E}
    (independentI : LinearIndepOn K roleVector I) (finiteI : I.Finite)
    (independentJ : LinearIndepOn K roleVector J) (_finiteJ : J.Finite)
    (smaller : I.ncard < J.ncard) :
    exists e, e ∈ J /\ e ∉ I /\ LinearIndepOn K roleVector (insert e I) := by
  by_contra noExtension
  push Not at noExtension
  have imageJSubset : roleVector '' J ⊆ span K (roleVector '' I) := by
    rintro _ ⟨e, eInJ, rfl⟩
    by_cases eInI : e ∈ I
    · exact subset_span ⟨e, eInI, rfl⟩
    · by_contra outsideSpan
      exact noExtension e eInJ eInI (independentI.insert outsideSpan)
  have independentImageJ : LinearIndepOn K id (roleVector '' J) :=
    (linearIndepOn_iff_image independentJ.injOn).mp independentJ
  have imageCardLe := exists_finite_card_le_of_finite_of_linearIndependent_of_span
    (finiteI.image roleVector) independentImageJ imageJSubset
  obtain ⟨finiteImageJ, imageCardLe⟩ := imageCardLe
  have imageJNcard : (roleVector '' J).ncard = J.ncard := independentJ.injOn.ncard_image
  have imageINcard : (roleVector '' I).ncard = I.ncard := independentI.injOn.ncard_image
  have : J.ncard ≤ I.ncard := by
    rw [← Set.ncard_eq_toFinset_card _ finiteImageJ,
      ← Set.ncard_eq_toFinset_card _ (finiteI.image roleVector)] at imageCardLe
    simpa [imageJNcard, imageINcard] using imageCardLe
  exact (Nat.not_le_of_gt smaller) this

/-- The finitary linear matroid on role labels induced by their vector family. -/
noncomputable def linearRoleMatroid
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) : Matroid E :=
  (IndepMatroid.ofFinitaryCardAugment
    (Set.univ : Set E)
    (LinearIndepOn K roleVector)
    (by simp)
    (fun _ _ independent subset => independent.mono subset)
    (fun {I J} independentI finiteI independentJ finiteJ smaller =>
      linear_indep_augmentation (I := I) (J := J) roleVector
        independentI finiteI independentJ finiteJ smaller)
    (fun I allFinite =>
      linearIndepOn_iff_linearIndepOn_finset.mpr fun t subset =>
        allFinite t subset t.finite_toSet)
    (by simp)).matroid

@[simp] theorem linearRoleMatroid_indep_iff
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (roles : Set E) :
    (linearRoleMatroid (K := K) roleVector).Indep roles ↔ LinearIndepOn K roleVector roles :=
  Iff.rfl
#print axioms linearRoleMatroid_indep_iff

theorem linearRoleMatroid_isBase_iff
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (roles : Finset E) :
    (linearRoleMatroid (K := K) roleVector).IsBase (roles : Set E) ↔
      IsRoleBasis (K := K) roleVector roles := by
  let M := linearRoleMatroid (K := K) roleVector
  constructor
  · intro isBase
    have independent : LinearIndepOn K roleVector (roles : Set E) := isBase.indep
    refine ⟨independent, le_antisymm ?_ ?_⟩
    · apply span_mono
      rintro _ ⟨e, _, rfl⟩
      exact ⟨e, rfl⟩
    · rw [span_le]
      rintro _ ⟨e, rfl⟩
      by_contra outsideSpan
      have insertIndependent : M.Indep (insert e (roles : Set E)) :=
        independent.insert outsideSpan
      have eInRoles := isBase.mem_of_insert_indep insertIndependent
      exact outsideSpan (subset_span ⟨e, eInRoles, rfl⟩)
  · rintro ⟨independent, spans⟩
    apply (show M.Indep (roles : Set E) from independent).isBase_of_maximal
    intro larger largerIndependent rolesSubset
    apply Set.Subset.antisymm rolesSubset
    intro e eInLarger
    by_contra eNotInRoles
    have insertSubset : insert e (roles : Set E) ⊆ larger :=
      insert_subset eInLarger rolesSubset
    have insertIndependent : LinearIndepOn K roleVector (insert e (roles : Set E)) :=
      (show M.Indep larger from largerIndependent).subset insertSubset
    have eInSpan : roleVector e ∈ span K (roleVector '' (roles : Set E)) := by
      rw [spans]
      exact subset_span ⟨e, rfl⟩
    exact insertIndependent.notMem_span_of_insert (by simpa) eInSpan
#print axioms linearRoleMatroid_isBase_iff

noncomputable section

local instance : DecidableEq E := Classical.decEq E

/-- Scan the remaining roles, inserting a role exactly when independence is preserved. -/
noncomputable def greedyRoleScanFrom
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (chosen : Finset E) (scan : List E) : Finset E := by
  classical
  induction scan generalizing chosen with
  | nil => exact chosen
  | cons role remaining inductionHypothesis =>
      if (linearRoleMatroid (K := K) roleVector).Indep
          (insert role (chosen : Set E)) then
        exact inductionHypothesis (insert role chosen)
      else
        exact inductionHypothesis chosen

/-- The role-greedy algorithm starts with no selected roles. -/
noncomputable def greedyRoleScan
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (scan : List E) : Finset E :=
  greedyRoleScanFrom (K := K) roleVector ∅ scan.dedup

private theorem exchange_base_over_independent_subset
    {M : Matroid E} {A B : Set E} {e : E}
    (baseB : M.IsBase B) (eNotInBase : e ∉ B)
    (insertIndependent : M.Indep (insert e A)) :
    exists b, b ∈ B \ A /\ M.IsBase (insert e (B \ {b})) := by
  have eInGround : e ∈ M.E := insertIndependent.subset_ground (mem_insert e A)
  have eInClosure : e ∈ M.closure B := by rw [baseB.closure_eq]; exact eInGround
  have circuit := baseB.indep.fundCircuit_isCircuit eInClosure eNotInBase
  have notCircuitSubset : ¬ M.fundCircuit e B ⊆ insert e A := by
    intro circuitSubset
    exact circuit.not_indep (insertIndependent.subset circuitSubset)
  obtain ⟨b, bInCircuit, bNotInInsert⟩ := not_subset.mp notCircuitSubset
  have bNeE : b ≠ e := fun equal => bNotInInsert (equal ▸ mem_insert e A)
  have bInBase : b ∈ B := by
    have := M.fundCircuit_subset_insert e B bInCircuit
    simpa [bNeE] using this
  have exchangeIndependent : M.Indep (insert e B \ {b}) :=
    (baseB.indep.mem_fundCircuit_iff eInClosure eNotInBase).mp bInCircuit
  refine ⟨b, ⟨bInBase, fun bInA => bNotInInsert (mem_insert_of_mem e bInA)⟩, ?_⟩
  rw [← insert_sdiff_singleton_comm bNeE.symm] at exchangeIndependent
  exact baseB.exchange_isBase_of_indep eNotInBase exchangeIndependent

private theorem greedy_role_scan_from_minimum
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (cost : E -> ℝ)
    (remaining : List E) (chosen comparison : Finset E)
    (baseComparison :
      (linearRoleMatroid (K := K) roleVector).IsBase (comparison : Set E))
    (chosenSubset : chosen ⊆ comparison)
    (unscanned : comparison \ chosen ⊆ remaining.toFinset)
    (fresh : Disjoint chosen remaining.toFinset)
    (nodup : remaining.Nodup)
    (sorted : remaining.Pairwise fun e f => cost e ≤ cost f) :
    let result := greedyRoleScanFrom (K := K) roleVector chosen remaining;
    (linearRoleMatroid (K := K) roleVector).IsBase (result : Set E) ∧
      ∑ e ∈ result, cost e ≤ ∑ e ∈ comparison, cost e := by
  classical
  let M := linearRoleMatroid (K := K) roleVector
  induction remaining generalizing chosen comparison with
  | nil =>
      have comparisonSubset : comparison ⊆ chosen := by
        intro e eInComparison
        by_contra eNotInChosen
        have eInDifference : e ∈ comparison \ chosen :=
          Finset.mem_sdiff.mpr ⟨eInComparison, eNotInChosen⟩
        exact (by simpa using unscanned eInDifference)
      have equal : chosen = comparison := Finset.Subset.antisymm chosenSubset comparisonSubset
      subst comparison
      simpa [greedyRoleScanFrom]
  | cons e remaining inductionHypothesis =>
      have eNotInRemaining : e ∉ remaining := (List.nodup_cons.mp nodup).1
      have nodupRemaining : remaining.Nodup := (List.nodup_cons.mp nodup).2
      have sortedHead : ∀ f ∈ remaining, cost e ≤ cost f :=
        (List.pairwise_cons.mp sorted).1
      have sortedRemaining : remaining.Pairwise fun f g => cost f ≤ cost g :=
        (List.pairwise_cons.mp sorted).2
      have freshRemaining : Disjoint chosen remaining.toFinset := by
        apply Finset.disjoint_left.mpr
        intro x xInChosen xInRemaining
        exact (Finset.disjoint_left.mp fresh xInChosen) (by simp [xInRemaining])
      have insertFresh : Disjoint (insert e chosen) remaining.toFinset := by
        apply Finset.disjoint_left.mpr
        intro x xInInsert xInRemaining
        rcases Finset.mem_insert.mp xInInsert with rfl | xInChosen
        · exact eNotInRemaining (by simpa using xInRemaining)
        · exact (Finset.disjoint_left.mp fresh xInChosen) (by simp [xInRemaining])
      by_cases accepted : M.Indep (insert e (chosen : Set E))
      · simp only [greedyRoleScanFrom, M, accepted]
        by_cases eInComparison : e ∈ comparison
        · apply inductionHypothesis (chosen := insert e chosen) (comparison := comparison)
          · exact baseComparison
          · exact Finset.insert_subset eInComparison chosenSubset
          · intro x xInDifference
            have xNotInInsert := (Finset.mem_sdiff.mp xInDifference).2
            have xNeE : x ≠ e := by
              intro equal
              subst x
              exact xNotInInsert (Finset.mem_insert_self e chosen)
            have xInOldDifference : x ∈ comparison \ chosen := by
              refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp xInDifference).1, ?_⟩
              exact fun xInChosen => xNotInInsert (Finset.mem_insert_of_mem xInChosen)
            simpa [xNeE] using unscanned xInOldDifference
          · exact insertFresh
          · exact nodupRemaining
          · exact sortedRemaining
        · obtain ⟨b, bInDifference, exchanged⟩ :=
            exchange_base_over_independent_subset baseComparison
              (by simpa using eInComparison) accepted
          have bInComparison : b ∈ comparison := bInDifference.1
          have bNotInChosen : b ∉ chosen := bInDifference.2
          have bNeE : b ≠ e := fun equal =>
            eInComparison (equal ▸ bInComparison)
          have bInRemaining : b ∈ remaining := by
            have bInScan := unscanned (Finset.mem_sdiff.mpr bInDifference)
            simpa [bNeE] using bInScan
          let comparison' := insert e (comparison.erase b)
          have baseComparison' : M.IsBase (comparison' : Set E) := by
            simpa [comparison'] using exchanged
          have chosenSubset' : insert e chosen ⊆ comparison' := by
            apply Finset.insert_subset
            · exact Finset.mem_insert_self e (comparison.erase b)
            · intro x xInChosen
              apply Finset.mem_insert_of_mem
              exact Finset.mem_erase.mpr
                ⟨fun equal => bNotInChosen (equal ▸ xInChosen), chosenSubset xInChosen⟩
          have unscanned' : comparison' \ insert e chosen ⊆ remaining.toFinset := by
            intro x xInDifference
            have xInComparison' := (Finset.mem_sdiff.mp xInDifference).1
            have xNotInChosen' := (Finset.mem_sdiff.mp xInDifference).2
            have xNeE : x ≠ e := by
              intro equal
              subst x
              exact xNotInChosen' (Finset.mem_insert_self e chosen)
            have xInErased : x ∈ comparison.erase b := by
              simpa [comparison', xNeE] using xInComparison'
            have xInOldDifference : x ∈ comparison \ chosen := by
              apply Finset.mem_sdiff.mpr
              refine ⟨Finset.mem_of_mem_erase xInErased, ?_⟩
              exact fun xInChosen => xNotInChosen'
                (Finset.mem_insert_of_mem xInChosen)
            simpa [xNeE] using unscanned xInOldDifference
          have comparisonCost :
              ∑ x ∈ comparison', cost x ≤ ∑ x ∈ comparison, cost x := by
            have eNotInErased : e ∉ comparison.erase b := by
              exact fun eInErased => eInComparison (Finset.mem_of_mem_erase eInErased)
            calc
              ∑ x ∈ comparison', cost x =
                  cost e + ∑ x ∈ comparison.erase b, cost x := by
                    rw [Finset.sum_insert eNotInErased]
              _ ≤ cost b + ∑ x ∈ comparison.erase b, cost x :=
                add_le_add_left (sortedHead b bInRemaining) _
              _ = ∑ x ∈ comparison, cost x := by
                rw [add_comm]
                exact Finset.sum_erase_add comparison cost bInComparison
          obtain ⟨resultBase, resultCost⟩ := inductionHypothesis
            (chosen := insert e chosen) (comparison := comparison') baseComparison'
            chosenSubset' unscanned' insertFresh nodupRemaining sortedRemaining
          exact ⟨resultBase, resultCost.trans comparisonCost⟩
      · simp only [greedyRoleScanFrom, M, accepted]
        have eNotInComparison : e ∉ comparison := by
          intro eInComparison
          apply accepted
          apply baseComparison.indep.subset
          have finsetSubset := Finset.insert_subset eInComparison chosenSubset
          intro x xInInsert
          simpa using finsetSubset (by simpa using xInInsert)
        apply inductionHypothesis (chosen := chosen) (comparison := comparison)
        · exact baseComparison
        · exact chosenSubset
        · intro x xInDifference
          have xNeE : x ≠ e := fun equal =>
            eNotInComparison (equal ▸ (Finset.mem_sdiff.mp xInDifference).1)
          simpa [xNeE] using unscanned xInDifference
        · exact freshRemaining
        · exact nodupRemaining
        · exact sortedRemaining

/-- Scanning every role in nondecreasing cost order gives a minimum-cost role basis. -/
theorem greedy_role_scan_is_minimum_cost_basis
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (cost : E -> ℝ) (scan : List E)
    (exhaustive : ∀ e, e ∈ scan)
    (sorted : scan.Pairwise fun e f => cost e ≤ cost f) :
    IsRoleBasis (K := K) roleVector (greedyRoleScan (K := K) roleVector scan) ∧
      ∀ roles, IsRoleBasis (K := K) roleVector roles ->
        ∑ e ∈ greedyRoleScan (K := K) roleVector scan, cost e ≤
          ∑ e ∈ roles, cost e := by
  let M := linearRoleMatroid (K := K) roleVector
  have dedupNodup : scan.dedup.Nodup := List.nodup_dedup scan
  have dedupExhaustive : ∀ e, e ∈ scan.dedup := fun e =>
    List.mem_dedup.mpr (exhaustive e)
  have dedupSorted : scan.dedup.Pairwise fun e f => cost e ≤ cost f :=
    sorted.sublist (List.dedup_sublist scan)
  have compareWith (roles : Finset E) (baseRoles : M.IsBase (roles : Set E)) :
      M.IsBase (greedyRoleScan (K := K) roleVector scan : Set E) ∧
        ∑ e ∈ greedyRoleScan (K := K) roleVector scan, cost e ≤
          ∑ e ∈ roles, cost e := by
    simpa [M, greedyRoleScan] using
      (greedy_role_scan_from_minimum roleVector cost scan.dedup ∅ roles baseRoles
        (by simp) (by
          intro e _
          exact List.mem_toFinset.mpr (dedupExhaustive e))
        (by simp) dedupNodup dedupSorted)
  constructor
  · obtain ⟨base, isBase⟩ := M.exists_isBase
    have finiteBase : base.Finite :=
      scan.toFinset.finite_toSet.subset fun e _ => by simpa using exhaustive e
    let roles := finiteBase.toFinset
    have baseRoles : M.IsBase (roles : Set E) := by
      simpa [roles] using isBase
    exact (linearRoleMatroid_isBase_iff (K := K) roleVector
      (greedyRoleScan (K := K) roleVector scan)).mp (compareWith roles baseRoles).1
  · intro roles roleBasis
    have baseRoles : M.IsBase (roles : Set E) :=
      (linearRoleMatroid_isBase_iff (K := K) roleVector roles).mpr roleBasis
    exact (compareWith roles baseRoles).2
#print axioms greedy_role_scan_is_minimum_cost_basis

/-- A concrete negative-cost family still satisfies the greedy minimum theorem. -/
theorem negative_costs_preserve_greedy_optimality :
    let roleVector : Fin 1 -> ℚ := fun _ => 1
    let cost : Fin 1 -> ℝ := fun _ => -1
    (exists e, cost e < 0) ∧
      IsRoleBasis (K := ℚ) roleVector (greedyRoleScan (K := ℚ) roleVector [0]) ∧
        ∀ roles, IsRoleBasis (K := ℚ) roleVector roles ->
          ∑ e ∈ greedyRoleScan (K := ℚ) roleVector [0], cost e ≤
            ∑ e ∈ roles, cost e := by
  dsimp
  refine ⟨⟨0, by norm_num⟩, ?_⟩
  exact greedy_role_scan_is_minimum_cost_basis (K := ℚ)
    (fun _ : Fin 1 => (1 : ℚ)) (fun _ : Fin 1 => (-1 : ℝ)) [0]
    (by simp) (by simp)
#print axioms negative_costs_preserve_greedy_optimality

/-- When every role has the same cost, all role bases have the same total cost. -/
theorem equal_cost_role_bases_have_equal_total
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (roleVector : E -> V) (value : ℝ) (roles₁ roles₂ : Finset E)
    (basis₁ : IsRoleBasis (K := K) roleVector roles₁)
    (basis₂ : IsRoleBasis (K := K) roleVector roles₂) :
    ∑ _ ∈ roles₁, value = ∑ _ ∈ roles₂, value := by
  have base₁ := (linearRoleMatroid_isBase_iff (K := K) roleVector roles₁).mpr basis₁
  have base₂ := (linearRoleMatroid_isBase_iff (K := K) roleVector roles₂).mpr basis₂
  have cardEqual : roles₁.card = roles₂.card := by
    simpa using base₁.ncard_eq_ncard_of_isBase base₂
  simp [cardEqual]
#print axioms equal_cost_role_bases_have_equal_total

/-- On the empty role type, the empty greedy output is the unique minimum-cost basis. -/
theorem empty_role_scan_degenerate :
    let roleVector : Empty -> ℚ := Empty.elim
    let cost : Empty -> ℝ := Empty.elim
    greedyRoleScan (K := ℚ) roleVector [] = ∅ ∧
      IsRoleBasis (K := ℚ) roleVector ∅ ∧
        ∀ roles, IsRoleBasis (K := ℚ) roleVector roles ->
          ∑ e ∈ (∅ : Finset Empty), cost e ≤ ∑ e ∈ roles, cost e := by
  dsimp
  refine ⟨rfl, ?_⟩
  simpa [greedyRoleScan, greedyRoleScanFrom] using
    (greedy_role_scan_is_minimum_cost_basis (K := ℚ)
      (Empty.elim : Empty -> ℚ) (Empty.elim : Empty -> ℝ) []
      (by simp) (by simp))
#print axioms empty_role_scan_degenerate

/-- A single zero role is rejected, and the empty set is still the role basis. -/
theorem singleton_zero_role_is_skipped :
    greedyRoleScan (K := ℚ) (fun _ : Fin 1 => (0 : ℚ)) [0] = ∅ ∧
      IsRoleBasis (K := ℚ) (fun _ : Fin 1 => (0 : ℚ)) ∅ := by
  have result := greedy_role_scan_is_minimum_cost_basis (K := ℚ)
    (fun _ : Fin 1 => (0 : ℚ)) (fun _ : Fin 1 => (0 : ℝ)) [0]
    (by simp) (by simp)
  have output :
      greedyRoleScan (K := ℚ) (fun _ : Fin 1 => (0 : ℚ)) [0] = ∅ := by
    simp [greedyRoleScan, greedyRoleScanFrom, linearRoleMatroid_indep_iff,
      linearIndepOn_singleton_iff]
  exact ⟨output, output ▸ result.1⟩
#print axioms singleton_zero_role_is_skipped

/-- A single nonzero role is accepted and forms the one-role basis. -/
theorem singleton_nonzero_role_is_selected :
    greedyRoleScan (K := ℚ) (fun _ : Fin 1 => (1 : ℚ)) [0] = {0} ∧
      IsRoleBasis (K := ℚ) (fun _ : Fin 1 => (1 : ℚ)) {0} := by
  have result := greedy_role_scan_is_minimum_cost_basis (K := ℚ)
    (fun _ : Fin 1 => (1 : ℚ)) (fun _ : Fin 1 => (0 : ℝ)) [0]
    (by simp) (by simp)
  have output :
      greedyRoleScan (K := ℚ) (fun _ : Fin 1 => (1 : ℚ)) [0] = {0} := by
    simp [greedyRoleScan, greedyRoleScanFrom, linearRoleMatroid_indep_iff]
  exact ⟨output, output ▸ result.1⟩
#print axioms singleton_nonzero_role_is_selected

/-- Exhaustiveness is necessary: an empty scan misses the only nonzero role and is not a basis. -/
theorem exhaustive_scan_is_necessary :
    greedyRoleScan (K := ℚ) (fun _ : Fin 1 => (1 : ℚ)) [] = ∅ ∧
      ¬IsRoleBasis (K := ℚ) (fun _ : Fin 1 => (1 : ℚ)) ∅ := by
  refine ⟨rfl, ?_⟩
  rintro ⟨_, spans⟩
  have oneInSpan : (1 : ℚ) ∈ span ℚ (Set.range fun _ : Fin 1 => (1 : ℚ)) :=
    subset_span ⟨0, rfl⟩
  rw [← spans] at oneInSpan
  simp at oneInSpan
#print axioms exhaustive_scan_is_necessary

/-- Cost order is necessary: scanning the dearer of two equal vectors first is suboptimal. -/
theorem sorted_scan_is_necessary :
    let roleVector : Fin 2 -> ℚ := fun _ => 1
    let cost : Fin 2 -> ℝ := fun i => if i = 0 then 1 else 0
    let scan : List (Fin 2) := [0, 1]
    ¬scan.Pairwise (fun e f => cost e ≤ cost f) ∧
      greedyRoleScan (K := ℚ) roleVector scan = {0} ∧
        IsRoleBasis (K := ℚ) roleVector {1} ∧
          ∑ e ∈ ({1} : Finset (Fin 2)), cost e <
            ∑ e ∈ greedyRoleScan (K := ℚ) roleVector scan, cost e := by
  dsimp
  have accepted :
      (linearRoleMatroid (K := ℚ) (fun _ : Fin 2 => (1 : ℚ))).Indep
        (insert 0 (∅ : Set (Fin 2))) := by
    rw [linearRoleMatroid_indep_iff]
    simp
  have rejected :
      ¬(linearRoleMatroid (K := ℚ) (fun _ : Fin 2 => (1 : ℚ))).Indep
        (insert 1 ({0} : Set (Fin 2))) := by
    rw [linearRoleMatroid_indep_iff]
    intro independent
    exact Fin.zero_ne_one (independent.injOn (by simp) (by simp) rfl)
  have output :
      greedyRoleScan (K := ℚ) (fun _ : Fin 2 => (1 : ℚ)) [0, 1] = {0} := by
    have accepted' :
        (linearRoleMatroid (K := ℚ) (fun _ : Fin 2 => (1 : ℚ))).Indep
          (insert 0 ((∅ : Finset (Fin 2)) : Set (Fin 2))) := by
      simpa only [Finset.coe_empty] using accepted
    simp only [greedyRoleScan]
    have noDuplicates : ([0, 1] : List (Fin 2)).Nodup := by simp
    have dedupEq :
        @List.dedup (Fin 2) (Classical.decEq (Fin 2)) [0, 1] = [0, 1] :=
      @List.Nodup.dedup (Fin 2) (Classical.decEq (Fin 2)) [0, 1] noDuplicates
    rw [dedupEq]
    simp only [greedyRoleScanFrom]
    split
    · split
      · rename_i bothIndependent
        exfalso
        apply rejected
        simpa using bothIndependent
      · rfl
    · rename_i notAccepted
      exact (notAccepted accepted').elim
  refine ⟨by norm_num, output, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simp
    · congr 1
      ext x
      simp
  · rw [output]
    norm_num
#print axioms sorted_scan_is_necessary

/-- In a mixed family, a zero role is skipped while a nonzero role forms the basis. -/
theorem zero_role_among_nonzero_roles_is_skipped :
    let roleVector : Fin 2 -> ℚ := fun i => if i = 0 then 0 else 1
    greedyRoleScan (K := ℚ) roleVector [0, 1] = {1} ∧
      IsRoleBasis (K := ℚ) roleVector {1} := by
  dsimp
  have output :
      greedyRoleScan (K := ℚ)
        (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1) [0, 1] = {1} := by
    simp [greedyRoleScan, greedyRoleScanFrom]
  have result := greedy_role_scan_is_minimum_cost_basis (K := ℚ)
    (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)
    (fun _ : Fin 2 => (0 : ℝ)) [0, 1]
    (by intro e; fin_cases e <;> simp) (by simp)
  exact ⟨output, output ▸ result.1⟩
#print axioms zero_role_among_nonzero_roles_is_skipped

/-- A chosen subfamily covers the universe when the union of its sets contains it. -/
def IsSetCover [DecidableEq E] (ground : Finset E)
    (sets : V -> Finset E) [DecidableEq V] (chosen : Finset V) : Prop :=
  ground ⊆ chosen.biUnion sets

/-- Three sets where the unique largest first choice is incompatible with a two-set cover. -/
def setCoverExample (i : Fin 3) : Finset (Fin 6) :=
  if i = 0 then {0, 1, 2, 3}
  else if i = 1 then {0, 1, 4}
  else {2, 3, 5}

/-- Largest-new-coverage greedy uses three sets here, while sets one and two cover in two. -/
theorem greedy_set_cover_can_be_suboptimal :
    (∀ i, i ≠ 0 -> (setCoverExample i).card < (setCoverExample 0).card) ∧
      ¬ IsSetCover Finset.univ setCoverExample ({0, 1} : Finset (Fin 3)) ∧
      ¬ IsSetCover Finset.univ setCoverExample ({0, 2} : Finset (Fin 3)) ∧
      IsSetCover Finset.univ setCoverExample ({0, 1, 2} : Finset (Fin 3)) ∧
      IsSetCover Finset.univ setCoverExample ({1, 2} : Finset (Fin 3)) ∧
      ({1, 2} : Finset (Fin 3)).card < ({0, 1, 2} : Finset (Fin 3)).card := by
  simp only [IsSetCover]
  decide
#print axioms greedy_set_cover_can_be_suboptimal

end

end D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis

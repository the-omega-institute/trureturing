/- GID: D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual circular-deletion fibres discharge the generic lower bound for every supported adaptive full-history query policy. -/

import D5.S3.Combinatorics.CircularWords.UniformCycleAttainment
import D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound

open CircularDeletionTransport UniformCycleAttainment
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost

variable {α : Type} [DecidableEq α]
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem mem_fiber {A : Finset α} (x : A) (B C : Cycle α) :
    C ∈ fiber (read A) (carrier A) x B ↔ C ∈ carrier A ∧ read A x C = B := by
  simp only [fiber, Finset.mem_filter]

private theorem mem_paired {A : Finset α} (D : Finset (Cycle α)) (z : A) (C : Cycle α) :
    C ∈ paired (read A) D z ↔ C ∈ D ∧ ∃ E ∈ D, E ≠ C ∧ read A z E = read A z C := by
  simp only [paired, Finset.mem_filter]

/-- The generic first fibre is exactly the legal fixed-support deletion fibre. -/
def firstFiberEquiv (A : Finset α) (x : A) (B : Cycle α) :
    {C : Cycle α // C ∈ fiber (read A) (carrier A) x B} ≃ FirstLift A x B :=
  { toFun := fun C =>
      let h := (mem_fiber x B C.val).mp C.property
      let hlegal := mem_carrier_legal h.1
      ⟨C.val,hlegal.1,hlegal.2,h.2⟩
    invFun := fun C => ⟨C.val, (mem_fiber x B C.val).mpr
      ⟨legal_mem_carrier C.property.1 C.property.2.1,C.property.2.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem realized_first_legal {A : Finset α} (x : A) {B : Cycle α}
    (hB : B ∈ answers (read A) (carrier A) x) :
    B.Nodup ∧ B.toFinset = A.erase x.val := by
  obtain ⟨C,hC,rfl⟩ : ∃ C ∈ carrier A, read A x C = B := by
    simpa only [answers, Finset.mem_image] using hB
  have hlegal := mem_carrier_legal hC
  exact delete_legal hlegal.1 hlegal.2 x.val

theorem realized_first_size {A : Finset α} (hA : 4 ≤ A.card) (x : A)
    {B : Cycle α} (hB : B ∈ answers (read A) (carrier A) x) :
    (fiber (read A) (carrier A) x B).card = A.card - 1 := by
  have hlegal := realized_first_legal x hB
  exact (Nat.card_eq_finsetCard _).symm.trans
    ((Nat.card_congr (firstFiberEquiv A x B)).trans
      (firstLift_card (by omega) x hlegal.1 hlegal.2))

private theorem other_mem {W : Type} (D : Finset W) (hD : 2 ≤ D.card) (x : W) :
    ∃ y ∈ D, y ≠ x := by
  classical
  by_contra hn
  have hs : D ⊆ {x} := by
    intro y hy
    apply Finset.mem_singleton.mpr
    by_contra hne
    exact hn ⟨y,hy,hne⟩
  have hc := Finset.card_le_card hs
  simp only [Finset.card_singleton] at hc
  omega

/-- A repeated second query leaves every member of the first fibre ambiguous. -/
theorem repeated_paired {A : Finset α} (hA : 4 ≤ A.card) (x : A)
    {B : Cycle α} (hB : B ∈ answers (read A) (carrier A) x) :
    paired (read A) (fiber (read A) (carrier A) x B) x =
      fiber (read A) (carrier A) x B := by
  ext C
  constructor
  · intro h; exact ((mem_paired _ x C).mp h).1
  · intro hC
    obtain ⟨D,hD,hne⟩ := other_mem (fiber (read A) (carrier A) x B)
      (by rw [realized_first_size hA x hB]; omega) C
    exact (mem_paired _ x C).mpr ⟨hC,D,hD,hne,
      ((mem_fiber x B D).mp hD).2.trans ((mem_fiber x B C).mp hC).2.symm⟩

/-- For distinct supported queries the generic paired set is the actual set of
originals in the unique double fibre, restricted to this first residual. -/
theorem distinct_paired {A : Finset α} (hA : 4 ≤ A.card) (x z : A)
    (hxz : x.val ≠ z.val) (B : Cycle α) :
    paired (read A) (fiber (read A) (carrier A) x B) z =
      (ambiguous A x z).filter (fun C => delete x.val C = B) := by
  ext C
  constructor
  · intro h
    rcases (mem_paired _ z C).mp h with ⟨hC,D,hD,hne,he⟩
    rcases (mem_fiber x B C).mp hC with ⟨hC,hxC⟩
    rcases (mem_fiber x B D).mp hD with ⟨hD,hxD⟩
    have hmemC : C ∈ candidateSet A (pairHistory A x z (read A x C) (read A z C)) :=
      (mem_pair_candidates x z _ _ C).mpr ⟨hC,rfl,rfl⟩
    have hmemD : D ∈ candidateSet A (pairHistory A x z (read A x C) (read A z C)) :=
      (mem_pair_candidates x z _ _ D).mpr ⟨hD,hxD.trans hxC.symm,he⟩
    have htwo : 2 ≤ (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card := by
      by_contra hn
      have hle : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card ≤ 1 := by omega
      exact hne (Finset.card_le_one.mp hle D hmemD C hmemC)
    have hle : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card ≤ 2 := by
      rw [pair_candidates_card]
      exact pairLift_atMostTwo (by omega) x z hxz _ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hC,by omega⟩,hxC⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hU,hxC⟩
    rcases Finset.mem_filter.mp hU with ⟨hC,htwo⟩
    obtain ⟨D,hD,hne⟩ := other_mem
      (candidateSet A (pairHistory A x z (read A x C) (read A z C))) (by omega) C
    rcases (mem_pair_candidates x z _ _ D).mp hD with ⟨hD,hxD,hzD⟩
    exact (mem_paired _ z C).mpr ⟨(mem_fiber x B C).mpr ⟨hC,hxC⟩,
      D,(mem_fiber x B D).mpr ⟨hD,hxD.trans hxC⟩,hne,hzD⟩

/-- Every adaptive second query has at least two paired actual originals;
repetitions have A.card-1, distinct queries have exactly two. -/
theorem actual_paired_bound {A : Finset α} (hA : 4 ≤ A.card) (x : A)
    {B : Cycle α} (hB : B ∈ answers (read A) (carrier A) x) (z : A) :
    2 ≤ (paired (read A) (fiber (read A) (carrier A) x B) z).card := by
  by_cases hxz : x.val = z.val
  · have he : x = z := Subtype.ext hxz
    subst z
    rw [repeated_paired hA x hB,realized_first_size hA x hB]
    omega
  · rw [distinct_paired hA x z hxz B]
    have hlegal := realized_first_legal x hB
    rw [ambiguous_first_fiber_card hA x z hxz hlegal.1 hlegal.2]

/-- Full-history, pointwise-terminating, zero-error lower bound over ALL legal
cycles. Supported labels may repeat and each next query may depend on the entire
history. The traces are actual completed executions, with no common horizon
assumed. -/
theorem actual_history_lower_bound {A : Finset α} (hA : 4 ≤ A.card)
    {L : Type} (policy : History A → Sum (Query A) L)
    (tr : Cycle α → History A) (lab : Cycle α → L)
    (runs : ∀ C ∈ carrier A, ∃ n, execute (read A) policy n [] C = some (tr C,lab C))
    (output : L → Cycle α) (correct : ∀ C ∈ carrier A, output (lab C) = C) :
    (2 : ℚ) + 2 / (A.card - 1 : ℚ) ≤
      ((∑ C ∈ carrier A, (tr C).length : Nat) : ℚ) / ((carrier A).card : ℚ) := by
  have hA0 : A.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty (Query A) := ⟨⟨Classical.choose hA0,Classical.choose_spec hA0⟩⟩
  obtain ⟨q,hroot,hpartition,hbranch,htotal,hmean⟩ :=
    history_two_query_cost (read A) (carrier A) (carrier_nonempty hA0)
      (A.card-1) 2 (by omega) (by omega)
      (fun q B hB => realized_first_size hA q hB)
      (fun q B hB z => actual_paired_bound hA q hB z)
      policy tr lab runs output correct
  have hcast : ((A.card - 1 : Nat) : ℚ) = (A.card : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ A.card),Nat.cast_one]
  simpa only [hcast,Nat.cast_ofNat] using hmean

end
end D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound

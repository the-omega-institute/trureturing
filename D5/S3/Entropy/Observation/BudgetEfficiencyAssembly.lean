/- GID: D5/S3/Entropy/Observation/BudgetEfficiencyAssembly
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/BudgetEfficiencyAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Assemble refinement information, innovation budgets, and the finite closure-spectrum telescope. -/

import D5.S3.Entropy.Submodularity.RefinementInformationDecomposition
import D5.S3.Entropy.Observation.ConditionalChoiceOutcomeChainRule
import D5.S3.Entropy.EntropyNonneg
import D5.S3.ConceptDynamics.Completion.CompletionInformationCost
import D5.S3.Observer.Tomography.InnovationCountBound
import D5.S3.Observer.Prediction.StableDepthCardinalityBounds
import D5.S3.Observer.Separation.FiniteHistoryStability
import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

namespace D5.S3.Entropy.Observation.BudgetEfficiencyAssembly

open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.EntropyNonneg
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Observation.ConditionalChoiceOutcomeChainRule
open D5.S3.ConceptDynamics.Completion.CompletionInformationCost
open D5.S3.Entropy.Submodularity.RefinementInformationDecomposition
open D5.S3.Observer.Tomography.InnovationCountBound
open D5.S3.Observer.Prediction.StableDepthCardinalityBounds
open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.Observer.Separation.FiniteHistoryStability
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem stable_class_count_eq_complete
    {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    observationClassCount update readout
        (observationStabilityDepth update readout) =
      infiniteObservationClassCount update readout := by
  let hsetoid : observationSetoid update readout
      (observationStabilityDepth update readout) =
      infiniteObservationSetoid update readout := by
    apply Setoid.ext
    intro x y
    have hstable := (finite_history_stability update readout).2.2.1
    constructor
    · intro h
      have hfinite : (x, y) ∈ finiteFutureRelation update readout
          (observationStabilityDepth update readout) := by
        change ∀ k, k ≤ observationStabilityDepth update readout →
          observedAt update readout k x = observedAt update readout k y
        change futureReadoutWord update readout
            (observationStabilityDepth update readout) x =
          futureReadoutWord update readout
            (observationStabilityDepth update readout) y at h
        intro k hk
        simpa only [futureReadoutWord, observedAt] using
          congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
      have hinfinite : (x, y) ∈ infiniteFutureRelation update readout := by
        rw [← hstable]
        exact hfinite
      change (fun k : Nat => observedAt update readout k x) =
        (fun k : Nat => observedAt update readout k y)
      exact funext hinfinite
    · intro h
      have hinfinite : (x, y) ∈ infiniteFutureRelation update readout := by
        change (fun k : Nat => observedAt update readout k x) =
          (fun k : Nat => observedAt update readout k y) at h
        exact fun k => congrFun h k
      have hfinite : (x, y) ∈ finiteFutureRelation update readout
          (observationStabilityDepth update readout) := by
        rw [hstable]
        exact hinfinite
      change futureReadoutWord update readout
          (observationStabilityDepth update readout) x =
        futureReadoutWord update readout
          (observationStabilityDepth update readout) y
      funext k
      exact hfinite k (Nat.le_of_lt_succ k.isLt)
  exact Fintype.card_congr (Equiv.cast (congrArg Quotient hsetoid))

private theorem initial_class_count_eq_readout_range
    {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    observationClassCount update readout 0 =
      Nat.card (Set.range readout) := by
  letI : Fintype (Set.range readout) := Fintype.ofFinite _
  letI : Fintype (Quotient (Setoid.ker readout)) := Fintype.ofFinite _
  have hsetoid : observationSetoid update readout 0 = Setoid.ker readout := by
    apply Setoid.ext
    intro x y
    constructor
    · intro h
      change readout x = readout y
      change futureReadoutWord update readout 0 x =
        futureReadoutWord update readout 0 y at h
      simpa [futureReadoutWord, observedAt, Function.iterate_zero_apply] using
        congrFun h (0 : Fin 1)
    · intro h
      change readout x = readout y at h
      change futureReadoutWord update readout 0 x =
        futureReadoutWord update readout 0 y
      funext k
      have hk : k = (0 : Fin 1) := Fin.eq_zero k
      subst k
      simpa [futureReadoutWord, observedAt, Function.iterate_zero_apply] using h
  have hquot :
      Fintype.card (Quotient (observationSetoid update readout 0)) =
        Fintype.card (Quotient (Setoid.ker readout)) :=
    Fintype.card_congr (Equiv.cast (congrArg Quotient hsetoid))
  calc
    observationClassCount update readout 0 =
        Nat.card (Quotient (Setoid.ker readout)) := by
      simpa only [observationClassCount, Nat.card_eq_fintype_card] using hquot
    _ = Nat.card (Set.range readout) :=
      Nat.card_congr (Setoid.quotientKerEquivRange readout)

private theorem log_closure_telescope
    {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    ∑ k ∈ Finset.range (observationStabilityDepth update readout),
        (Real.log (observationClassCount update readout (k + 1)) -
          Real.log (observationClassCount update readout k)) =
      Real.log (infiniteObservationClassCount update readout) -
        Real.log (Nat.card (Set.range readout)) := by
  let f : Nat -> Real := fun k =>
    Real.log (observationClassCount update readout k)
  have htelescope : ∀ n, ∑ k ∈ Finset.range n, (f (k + 1) - f k) = f n - f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [show (∑ k ∈ Finset.range (observationStabilityDepth update readout),
      (Real.log (observationClassCount update readout (k + 1)) -
        Real.log (observationClassCount update readout k))) =
      ∑ k ∈ Finset.range (observationStabilityDepth update readout),
        (f (k + 1) - f k) by rfl]
  rw [htelescope]
  change Real.log (observationClassCount update readout
      (observationStabilityDepth update readout)) -
      Real.log (observationClassCount update readout 0) =
    Real.log (infiniteObservationClassCount update readout) -
      Real.log (Nat.card (Set.range readout))
  rw [stable_class_count_eq_complete, initial_class_count_eq_readout_range]

private theorem graph_joint_entropy_eq_pushforward
    {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    (mass : X -> Real) (first : X -> A) (second : X -> B)
    (forget : B -> A) (hforget : first = forget ∘ second) :
    shannonEntropy (completionLaw mass first second) =
      shannonEntropy (pushforward second mass) := by
  classical
  have hpoint (a : A) (b : B) :
      completionLaw mass first second (a, b) =
        if forget b = a then pushforward second mass b else 0 := by
    simp only [completionLaw, pushforward]
    by_cases h : forget b = a
    · simp only [if_pos h]
      apply Finset.sum_congr rfl
      intro x _
      have hfirst : first x = forget (second x) := congrFun hforget x
      by_cases hs : second x = b <;> simp [hs, hfirst, h]
    · simp only [if_neg h]
      apply Finset.sum_eq_zero
      intro x _
      have hfirst : first x = forget (second x) := congrFun hforget x
      by_cases hs : second x = b <;> simp [hs, hfirst, h]
  rw [shannonEntropy, Fintype.sum_prod_type]
  simp_rw [hpoint]
  calc
    (∑ a, ∑ b, Real.negMulLog
        (if forget b = a then pushforward second mass b else 0)) =
        ∑ b, ∑ a, Real.negMulLog
          (if forget b = a then pushforward second mass b else 0) :=
      Finset.sum_comm
    _ = ∑ b, Real.negMulLog (pushforward second mass b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single (forget b)]
      · simp
      · intro a _ h
        simp [Ne.symm h]
      · simp
    _ = shannonEntropy (pushforward second mass) := rfl

private theorem graph_conditional_entropy_eq_entropy_difference
    {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    (mass : X -> Real) (first : X -> A) (second : X -> B)
    (forget : B -> A) (hforget : first = forget ∘ second)
    (hmass : (forall x, 0 <= mass x) ∧ ∑ x, mass x = 1) :
    conditionalEntropy (completionLaw mass first second) =
      shannonEntropy (pushforward second mass) -
        shannonEntropy (pushforward first mass) := by
  have hcost := completion_information_cost mass first second hmass
  rw [graph_joint_entropy_eq_pushforward mass first second forget hforget] at hcost
  exact hcost.symm

private theorem conditional_mutual_information_le_xy
    {I K M : Type*} [Fintype I] [Fintype K] [Fintype M]
    (law : I × (K × M) -> Real)
    (hlaw : forall z, 0 <= law z) :
    conditionalMutualInformation law ≤ conditionalEntropy (xyProjection law) := by
  classical
  let reassociated : (I × M) × K -> Real :=
    fun z => law (z.1.1, (z.2, z.1.2))
  have hreassoc_nonneg : forall z, 0 <= reassociated z := by
    intro z
    exact hlaw (z.1.1, (z.2, z.1.2))
  have hxy_nonneg : forall z, 0 <= xyProjection law z := by
    intro z
    exact Finset.sum_nonneg fun m _ => hlaw (z.1, (z.2, m))
  have hxz_nonneg : forall z, 0 <= xzProjection law z := by
    intro z
    exact Finset.sum_nonneg fun k _ => hlaw (z.1, (k, z.2))
  have hmarginal_reassociated :
      marginal reassociated = xzProjection law := by
    funext z
    rfl
  have hentropy_reassociated :
      conditionalEntropy reassociated =
        shannonEntropy law - shannonEntropy (xzProjection law) := by
    have hchain := entropy_chain_rule reassociated hreassoc_nonneg
    rw [hmarginal_reassociated] at hchain
    have hswap : shannonEntropy reassociated = shannonEntropy law := by
      simp only [reassociated, shannonEntropy, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    rw [hswap] at hchain
    linarith
  have hentropy_xy :
      conditionalEntropy (xyProjection law) =
        shannonEntropy (xyProjection law) - shannonEntropy (marginal law) := by
    have hchain := entropy_chain_rule (xyProjection law) hxy_nonneg
    have hmarginal : marginal (xyProjection law) = marginal law := by
      funext i
      simp only [marginal, xyProjection, Fintype.sum_prod_type]
    rw [hmarginal] at hchain
    linarith
  have hdefect := conditional_mutual_information_eq_entropy_defect law hlaw
  have hcmiform :
      conditionalMutualInformation law =
        conditionalEntropy (xyProjection law) - conditionalEntropy reassociated := by
    calc
      conditionalMutualInformation law =
          shannonEntropy (xyProjection law) + shannonEntropy (xzProjection law) -
            shannonEntropy law - shannonEntropy (marginal law) := hdefect
      _ = (shannonEntropy (xyProjection law) - shannonEntropy (marginal law)) -
          (shannonEntropy law - shannonEntropy (xzProjection law)) := by ring
      _ = conditionalEntropy (xyProjection law) - conditionalEntropy reassociated := by
        rw [hentropy_xy, hentropy_reassociated]
  rw [hcmiform]
  linarith [conditional_entropy_nonneg reassociated hreassoc_nonneg]

private theorem xy_projection_refinement_law
    {P F Fine Coarse : Type*} [Fintype P] [Fintype F]
    (p : P × F -> Real) (fine : P -> Fine) (forget : Fine -> Coarse) :
    xyProjection
        (readoutPastFutureLaw (readoutFutureLaw p fine) forget) =
      completionLaw (marginal p) (forget ∘ fine) fine := by
  classical
  funext z
  simp only [xyProjection, readoutPastFutureLaw, readoutFutureLaw, completionLaw,
    pushforward, marginal, Function.comp_apply]
  by_cases hforget : forget z.2 = z.1
  · simp only [if_pos hforget]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hfine : fine x = z.2
    · simp [hfine, hforget]
    · have hpair_ne : (forget (fine x), fine x) ≠ z := by
        intro hpair
        exact hfine (congrArg Prod.snd hpair)
      simp [hfine, hpair_ne]
  · simp only [if_neg hforget]
    calc
      (∑ _ : F, (0 : Real)) = 0 := by simp
      _ = ∑ x, if (forget (fine x), fine x) = z then ∑ j, p (x, j) else 0 := by
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro x _
        by_cases hpair : (forget (fine x), fine x) = z
        · have hsecond : fine x = z.2 := congrArg Prod.snd hpair
          have hfirst : forget (fine x) = z.1 := congrArg Prod.fst hpair
          have : forget z.2 = z.1 := by
            calc
              forget z.2 = forget (fine x) := congrArg forget hsecond.symm
              _ = z.1 := hfirst
          exact (hforget this).elim
        · simp [hpair]

private theorem pushforward_entropy_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    (mass : X -> Real) (map : X -> Y)
    (hmass : (forall x, 0 <= mass x) ∧ ∑ x, mass x = 1) :
    shannonEntropy (pushforward map mass) ≤ shannonEntropy mass := by
  classical
  let joint : Y × X -> Real :=
    fun z => if map z.2 = z.1 then mass z.2 else 0
  have hjoint_nonneg : forall z, 0 <= joint z := by
    intro z
    simp only [joint]
    split_ifs
    · exact hmass.1 z.2
    · exact le_rfl
  have hjoint_entropy : shannonEntropy joint = shannonEntropy mass := by
    rw [shannonEntropy, Fintype.sum_prod_type]
    calc
      (∑ y, ∑ x, Real.negMulLog
          (if map x = y then mass x else 0)) =
          ∑ x, ∑ y, Real.negMulLog
            (if map x = y then mass x else 0) := Finset.sum_comm
      _ = ∑ x, Real.negMulLog (mass x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single (map x)]
        · simp
        · intro y _ hy
          simp [Ne.symm hy]
        · simp
      _ = shannonEntropy mass := rfl
  have hmarginal : marginal joint = pushforward map mass := by
    funext y
    rfl
  have hchain := entropy_chain_rule joint hjoint_nonneg
  rw [hmarginal, hjoint_entropy] at hchain
  have hconditional := conditional_entropy_nonneg joint hjoint_nonneg
  linarith

/-- The refinement information identity, finite entropy budget, and closure-spectrum
log-resolution telescope hold on their canonical carriers. -/
theorem budget_efficiency_assembly
    {P F X Q : Type*} [Fintype P] [Fintype F] [Fintype X]
    (C : Nat -> Type*) (fintypeC : forall n, Fintype (C n))
    (p : P × F -> Real)
    (hp : (forall z, 0 <= p z) ∧ ∑ z, p z = 1)
    (q : forall n, P -> C n)
    (forget : forall n, C (n + 1) -> C n)
    (hrefine : forall n, q n = forget n ∘ q (n + 1))
    (update : X -> X) (readout : X -> Q) :
    let mass : P -> Real := marginal p
    let h : Nat -> Real := fun n =>
      @conditionalEntropy (C n) (C (n + 1)) (fintypeC n) (fintypeC (n + 1))
        (completionLaw mass (q n) (q (n + 1)))
    let g : Nat -> Real := fun n =>
      @refinementGain P F (C (n + 1)) (C n) inferInstance inferInstance
        (fintypeC (n + 1)) (fintypeC n) p (q (n + 1)) (forget n)
    let eta : Nat -> Real := fun n => if h n = 0 then 0 else g n / h n
    (forall n, 0 <= g n ∧ g n <= h n ∧
      (0 < h n -> eta n = g n / h n) ∧ (h n = 0 -> eta n = 0)) ∧
    (Summable h ∧ (∑' n, h n) <= shannonEntropy mass ∧
      forall ε, 0 < ε ->
        (({n | ε <= h n} : Set Nat).ncard : Real) <=
          shannonEntropy mass / ε) ∧
    (∑ k ∈ Finset.range (observationStabilityDepth update readout),
        (Real.log (observationClassCount update readout (k + 1)) -
          Real.log (observationClassCount update readout k)) =
      Real.log (infiniteObservationClassCount update readout) -
        Real.log (Nat.card (Set.range readout))) := by
  classical
  let mass : P -> Real := marginal p
  let h : Nat -> Real := fun n =>
    @conditionalEntropy (C n) (C (n + 1)) (fintypeC n) (fintypeC (n + 1))
      (completionLaw mass (q n) (q (n + 1)))
  let g : Nat -> Real := fun n =>
    @refinementGain P F (C (n + 1)) (C n) inferInstance inferInstance
      (fintypeC (n + 1)) (fintypeC n) p (q (n + 1)) (forget n)
  let eta : Nat -> Real := fun n => if h n = 0 then 0 else g n / h n
  let qMass : forall n, C n -> Real := fun n => pushforward (q n) mass
  change (forall n, 0 <= g n ∧ g n <= h n ∧
      (0 < h n -> eta n = g n / h n) ∧ (h n = 0 -> eta n = 0)) ∧
    (Summable h ∧ (∑' n, h n) <= shannonEntropy mass ∧
      forall ε, 0 < ε ->
        (({n | ε <= h n} : Set Nat).ncard : Real) <=
          shannonEntropy mass / ε) ∧
    (∑ k ∈ Finset.range (observationStabilityDepth update readout),
        (Real.log (observationClassCount update readout (k + 1)) -
          Real.log (observationClassCount update readout k)) =
      Real.log (infiniteObservationClassCount update readout) -
        Real.log (Nat.card (Set.range readout)))
  have hmass : (forall x, 0 <= mass x) ∧ ∑ x, mass x = 1 := by
    constructor
    · intro x
      dsimp [mass, marginal]
      exact Finset.sum_nonneg fun y _ => hp.1 (x, y)
    · dsimp [mass]
      simpa only [marginal, Fintype.sum_prod_type] using hp.2
  have hqLaw (n : Nat) :
      (forall c, 0 <= qMass n c) ∧ ∑ c, qMass n c = 1 := by
    letI : Fintype (C n) := fintypeC n
    constructor
    · intro c
      dsimp [qMass]
      simp only [pushforward]
      exact Finset.sum_nonneg fun x _ => by
        by_cases hx : q n x = c <;> simp [hx, hmass.1 x]
    · dsimp [qMass]
      simp only [pushforward]
      rw [Finset.sum_comm]
      calc
        (∑ x, ∑ c, if q n x = c then mass x else 0) = ∑ x, mass x := by
          apply Finset.sum_congr rfl
          intro x _
          simp
        _ = 1 := hmass.2
  have hEqDiff (n : Nat) :
      h n = shannonEntropy (qMass (n + 1)) - shannonEntropy (qMass n) := by
    dsimp [h, qMass]
    exact graph_conditional_entropy_eq_entropy_difference mass (q n) (q (n + 1))
      (forget n) (hrefine n) hmass
  have hNonneg (n : Nat) : 0 <= h n := by
    dsimp [h, completionLaw, pushforward]
    apply conditional_entropy_nonneg
    intro z
    exact Finset.sum_nonneg fun x _ => by
      by_cases hz : (q n x, q (n + 1) x) = z <;> simp [hz, hmass.1 x]
  have hTelescope : forall N, ∑ n ∈ Finset.range N, h n =
      shannonEntropy (qMass N) - shannonEntropy (qMass 0) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, hEqDiff N]
        ring
  have hPartial : forall N, ∑ n ∈ Finset.range N, h n <= shannonEntropy mass := by
    intro N
    rw [hTelescope N]
    have hqNle := pushforward_entropy_le mass (q N) hmass
    have hq0nonneg := shannon_entropy_nonneg (qMass 0) (hqLaw 0)
    linarith
  have hSummable : Summable h :=
    summable_of_sum_range_le hNonneg hPartial
  have hBudget : (∑' n, h n) <= shannonEntropy mass :=
    Real.tsum_le_of_sum_range_le hNonneg hPartial
  have gNonneg (n : Nat) : 0 <= g n := by
    simpa [g] using
      (deterministic_refinement_information_decomposition p hp
        (q (n + 1)) (forget n)).2
  have gUpper (n : Nat) : g n <= h n := by
    let law : C n × (C (n + 1) × F) -> Real :=
      readoutPastFutureLaw (readoutFutureLaw p (q (n + 1))) (forget n)
    have hlaw : forall z, 0 <= law z := by
      intro z
      dsimp [law, readoutPastFutureLaw, readoutFutureLaw, pushforward]
      split_ifs
      · exact Finset.sum_nonneg fun x _ => by
          by_cases hx : q (n + 1) x = z.2.1 <;> simp [hx, hp.1 (x, z.2.2)]
      · exact le_rfl
    have hbound := conditional_mutual_information_le_xy law hlaw
    have hxy := xy_projection_refinement_law p (q (n + 1)) (forget n)
    rw [← hrefine n] at hxy
    rw [hxy] at hbound
    exact hbound
  have heta_pos (n : Nat) (hn : 0 < h n) : eta n = g n / h n := by
    dsimp [eta]
    rw [if_neg (ne_of_gt hn)]
  have heta_zero (n : Nat) (hn : h n = 0) : eta n = 0 := by
    dsimp [eta]
    rw [if_pos hn]
  refine ⟨?_, ?_, log_closure_telescope update readout⟩
  · intro n
    exact ⟨gNonneg n, gUpper n, heta_pos n, heta_zero n⟩
  · refine ⟨hSummable, hBudget, ?_⟩
    intro ε hε
    exact large_innovation_count_le_budget_div h (shannonEntropy mass) ε hNonneg
      hSummable hBudget hε

#print axioms budget_efficiency_assembly

end D5.S3.Entropy.Observation.BudgetEfficiencyAssembly

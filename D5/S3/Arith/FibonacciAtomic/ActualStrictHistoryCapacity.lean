/- GID: D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native continuations and strict alpha growth bound actual same-size families. -/

import D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore
import D5.S3.Arith.FibonacciAtomic.ActualHistorySingleHoleRecovery
import D5.S0.History.FinitePrefixAntichainBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualStrictHistoryCapacity

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore
open ActualLeafHistoryRigidity
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)
open scoped BigOperators

/-- The same recipe selects a continuation only along its own representative addresses
and nonempty actual report fibers. There is no transition from a singleton. -/
noncomputable def residual {m : Nat} {F : Fin m → Source} {S : Finset (Fin m)}
    (r : Recipe F S) : Hist (fun _ : Address => Reply) →
      Option (Σ T : Finset (Fin m), Recipe F T)
  | [] => some ⟨S, r⟩
  | e :: H => match r with
    | .singleton _ => none
    | .split T a _ next =>
      if e.1 = representative F a then
        if hy : (survivors T a.val e.2).Nonempty then residual (next e.2 hy) H
        else none
      else none
termination_by H => H.length

/-- The queue records every actual report, including branch and absent reports. -/
def queue {m : Nat} (F : Fin m → Source) (S : Finset (Fin m))
    (H : Hist (fun _ : Address => Reply)) : Finset (Fin m) :=
  S.filter (fun i => ∀ e ∈ H, readout e.1 (F i) = e.2)

/-- Immediate live native events use the split's one representative and a nonempty
four-valued survivor fiber. Singleton syntax has no live event. -/
def liveChild {m : Nat} {F : Fin m → Source} :
    {T : Finset (Fin m)} → Recipe F T → Sigma (fun _ : Address => Reply) → Prop
  | _, .singleton _, _ => False
  | T, .split _ a _ _, e => e.1 = representative F a ∧
      (survivors T a.val e.2).Nonempty

set_option maxHeartbeats 1000000 in
-- Universal reached histories and indexed child transports share the induction budget.
/-- A reached prefix of one native recipe determines its selected residual, its exact
all-report queue, every surviving suffix, and the terminal prefix antichain. -/
theorem reached_prefix {m : Nat} (F : Fin m → Source) {S : Finset (Fin m)}
    (r : Recipe F S) :
    (∀ H : Hist (fun _ : Address => Reply),
      (∃ i ∈ S, H.IsPrefix (routeTrace r i)) →
      ∃ R : (Σ T : Finset (Fin m), Recipe F T),
        residual r H = some R ∧ R.1 = queue F S H ∧
        (∀ i ∈ S, H.IsPrefix (routeTrace r i) ↔ i ∈ R.1) ∧
        (∀ i ∈ R.1, routeTrace r i = H ++ routeTrace R.2 i) ∧
        (∀ K, residual r (H ++ K) = residual R.2 K) ∧
        (∀ R', residual r H = some R' → R' = R) ∧
        (∀ e, (∃ i ∈ S, (H ++ [e]).IsPrefix (routeTrace r i)) ↔
          liveChild R.2 e)) ∧
    (∀ i ∈ S, ∀ j ∈ S,
      (routeTrace r i).IsPrefix (routeTrace r j) → i = j) := by
  classical
  have realized (a : actualVectors F) : vector F (representative F a) = a.val :=
    (List.Shortlex.wf (InvImage.wf Bool.toNat Nat.lt_wfRel.wf)).min_mem
      {u | vector F u = a.val} a.property
  have correspondence : ∀ {T : Finset (Fin m)} (q : Recipe F T),
      ∀ H : Hist (fun _ : Address => Reply),
      (∃ i ∈ T, H.IsPrefix (routeTrace q i)) →
      ∃ R : (Σ U : Finset (Fin m), Recipe F U),
        residual q H = some R ∧ R.1 = queue F T H ∧
        (∀ i ∈ T, H.IsPrefix (routeTrace q i) ↔ i ∈ R.1) ∧
        (∀ i ∈ R.1, routeTrace q i = H ++ routeTrace R.2 i) := by
    intro T q
    induction q with
    | singleton k =>
      intro H hH
      obtain ⟨i, hi, hp⟩ := hH
      have hnil : H = [] := by simpa only [routeTrace, List.prefix_nil] using hp
      subst H
      exact ⟨⟨{k}, .singleton k⟩, by simp only [residual], by simp [queue],
        fun i hi => by simp [hi], fun _ _ => rfl⟩
    | split T a hs next ih =>
      have transport (i : Fin m) (hi : i ∈ T) (y : Reply)
          (hy : (survivors T a.val y).Nonempty) (he : a.val i = y) :
          routeTrace (next (a.val i) ⟨i, by simp [survivors, hi]⟩) i =
            routeTrace (next y hy) i := by
        subst y
        rfl
      intro H hH
      cases H with
      | nil =>
        exact ⟨⟨T, .split T a hs next⟩, by simp only [residual], by simp [queue],
          fun _ hi => by simp [hi], fun _ _ => rfl⟩
      | cons e H =>
        obtain ⟨k, hk, hp⟩ := hH
        simp only [routeTrace, hk, ↓reduceDIte] at hp
        obtain ⟨he, htail⟩ := List.cons_prefix_cons.mp hp
        have hu : e.1 = representative F a := congrArg Sigma.fst he
        have hyk : e.2 = a.val k := congrArg Sigma.snd he
        have hky : k ∈ survivors T a.val e.2 := by simp [survivors, hk, hyk]
        have hy : (survivors T a.val e.2).Nonempty := ⟨k, hky⟩
        have htail' : H.IsPrefix (routeTrace (next e.2 hy) k) := by
          rw [transport k hk e.2 hy hyk.symm] at htail
          exact htail
        obtain ⟨R, hr, hqueue, hprefix, hsuffix⟩ := ih e.2 hy H ⟨k, hky, htail'⟩
        have hQ : queue F (survivors T a.val e.2) H = queue F T (e :: H) := by
          ext i
          have hv : readout (representative F a) (F i) = a.val i := congrFun (realized a) i
          simp [queue, survivors, hu, hv, and_assoc]
        refine ⟨R, ?_, hqueue.trans hQ, ?_, ?_⟩
        · simp only [residual, hu, ↓reduceIte, hy, ↓reduceDIte]
          exact hr
        · intro i hi
          by_cases hiy : a.val i = e.2
          · have hif : i ∈ survivors T a.val e.2 := by simp [survivors, hi, hiy]
            have hev : (⟨representative F a, a.val i⟩ : Sigma (fun _ : Address => Reply)) = e :=
              Sigma.ext hu.symm (heq_of_eq hiy)
            have hri : routeTrace (.split T a hs next) i =
                e :: routeTrace (next e.2 hy) i := by
              simp only [routeTrace, hi, ↓reduceDIte]
              rw [transport i hi e.2 hy hiy, hev]
            rw [hri, List.cons_prefix_cons]
            simpa using hprefix i hif
          · have hiR : i ∉ R.1 := by
              rw [hqueue]
              simp only [queue, Finset.mem_filter, survivors] at *
              exact fun h => hiy h.1.2
            simp only [routeTrace, hi, ↓reduceDIte, List.cons_prefix_cons]
            have hne : e ≠ (⟨representative F a, a.val i⟩ : Sigma (fun _ : Address => Reply)) :=
              fun he' => hiy (congrArg Sigma.snd he').symm
            simp [hne, hiR]
        · intro i hiR
          have hif : i ∈ survivors T a.val e.2 := by
            rw [hqueue] at hiR
            exact (Finset.mem_filter.mp hiR).1
          have hi : i ∈ T := (Finset.mem_filter.mp hif).1
          have hiy : a.val i = e.2 := (Finset.mem_filter.mp hif).2
          have hev : (⟨representative F a, a.val i⟩ : Sigma (fun _ : Address => Reply)) = e :=
            Sigma.ext hu.symm (heq_of_eq hiy)
          have hri : routeTrace (.split T a hs next) i =
              e :: routeTrace (next e.2 hy) i := by
            simp only [routeTrace, hi, ↓reduceDIte]
            rw [transport i hi e.2 hy hiy, hev]
          rw [hri, hsuffix i hiR]
          rfl
  have append_transport : ∀ H : Hist (fun _ : Address => Reply),
      ∀ {T : Finset (Fin m)} (q : Recipe F T)
        (R : Σ U : Finset (Fin m), Recipe F U),
      residual q H = some R → ∀ K, residual q (H ++ K) = residual R.2 K := by
    intro H
    induction H with
    | nil =>
      intro T q R hr K
      simp only [residual] at hr
      have he := Option.some.inj hr
      subst R
      simp only [List.nil_append]
    | cons e H ih =>
      intro T q R hr K
      cases q with
      | singleton k => simp only [residual, reduceCtorEq] at hr
      | split T a hs next =>
          by_cases hu : e.1 = representative F a
          · by_cases hy : (survivors T a.val e.2).Nonempty
            · simp only [residual, hu, ↓reduceIte, hy, ↓reduceDIte] at hr
              simpa only [List.cons_append, residual, hu, ↓reduceIte, hy, ↓reduceDIte]
                using ih (next e.2 hy) R hr K
            · simp only [residual, hu, ↓reduceIte, hy, ↓reduceDIte, reduceCtorEq] at hr
          · simp only [residual, hu, ↓reduceIte, reduceCtorEq] at hr
  have immediate {T : Finset (Fin m)} (q : Recipe F T)
      (e : Sigma (fun _ : Address => Reply)) :
      (∃ i ∈ T, [e].IsPrefix (routeTrace q i)) ↔
        liveChild q e := by
    cases q with
    | singleton k => simp [routeTrace, liveChild]
    | split T a hs next =>
        change _ ↔ e.1 = representative F a ∧ (survivors T a.val e.2).Nonempty
        constructor
        · rintro ⟨i, hi, hp⟩
          simp only [routeTrace, hi, ↓reduceDIte, List.cons_prefix_cons] at hp
          have hu := congrArg Sigma.fst hp.1
          have hy := congrArg Sigma.snd hp.1
          exact ⟨hu, i, by simp [survivors, hi, hy]⟩
        · rintro ⟨hu, i, hi⟩
          have hiT := (Finset.mem_filter.mp hi).1
          have hy := (Finset.mem_filter.mp hi).2
          refine ⟨i, hiT, ?_⟩
          simp only [routeTrace, hiT, ↓reduceDIte, List.cons_prefix_cons]
          exact ⟨Sigma.ext hu (heq_of_eq hy.symm), List.nil_prefix⟩
  refine ⟨?_, ?_⟩
  · intro H hH
    obtain ⟨R, hr, hQ, hpre, hsuf⟩ := correspondence r H hH
    refine ⟨R, hr, hQ, hpre, hsuf, append_transport H r R hr, ?_, ?_⟩
    · intro R' hr'
      exact (Option.some.inj (hr'.symm.trans hr))
    · intro e
      rw [← immediate R.2 e]
      constructor
      · rintro ⟨i, hi, hp⟩
        have hpar : H.IsPrefix (routeTrace r i) := by
          rcases hp with ⟨z, hz⟩
          exact ⟨[e] ++ z, by simpa only [List.append_assoc] using hz⟩
        have hiR := (hpre i hi).mp hpar
        rw [hsuf i hiR] at hp
        rcases hp with ⟨z, hz⟩
        exact ⟨i, hiR, z, List.append_cancel_left (by
          simpa only [List.append_assoc] using hz)⟩
      · rintro ⟨i, hiR, z, hz⟩
        have hi : i ∈ S := by
          rw [hQ] at hiR
          exact (Finset.mem_filter.mp hiR).1
        refine ⟨i, hi, z, ?_⟩
        rw [hsuf i hiR, List.append_assoc, hz]
  intro i hi j hj hp
  obtain ⟨R, _hr, hQ, hpre, hsuf⟩ := correspondence r (routeTrace r i) ⟨i, hi, List.prefix_rfl⟩
  have hiR : i ∈ R.1 := (hpre i hi).mp List.prefix_rfl
  have hjR : j ∈ R.1 := (hpre j hj).mp hp
  have hempty : routeTrace R.2 i = [] := by
    have he := congrArg List.length (hsuf i hiR)
    simp only [List.length_append] at he
    exact List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨U, q⟩ := R
  cases q with
  | singleton k =>
      have hik : i = k := Finset.mem_singleton.mp hiR
      have hjk : j = k := Finset.mem_singleton.mp hjR
      exact hik.trans hjk.symm
  | split U a hs next =>
      simp only [routeTrace, hiR, ↓reduceDIte] at hempty
      cases hempty

#print axioms reached_prefix

/-- The original source30.11 count, with singleton boundary weights. -/
def M : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, 0 => 1
  | r + 1, t + 1 => M r (t + 1) + 2 * M (r + 1) t
termination_by r t => r + t

/-- The original common individual-optimum complex on actual family indices. -/
def K {m : Nat} (F : Fin m → Source) : Set (Finset (Fin m)) :=
  {S | ∃ p : Strategy, ∀ i ∈ S, cost p (F i) = (F i).length}

/-- Empty and singleton index sets. Injectivity identifies them with actual source subsets. -/
def Kcircle (m : Nat) : Set (Finset (Fin m)) := {S | S.card ≤ 1}

/-- Distinct acquired leaf addresses; logically forced leaves are excluded. -/
def leafPaid (H : Hist (fun _ : Address => Reply)) : Finset Address :=
  ((H.filter fun e => chi e.2 = 0).map Sigma.fst).toFinset

/-- Distinct acquired branch or absent addresses. -/
def nonleafPaid (H : Hist (fun _ : Address => Reply)) : Finset Address :=
  ((H.filter fun e => chi e.2 = 1).map Sigma.fst).toFinset

/-- The same actual history, expressed in the existing geometry owner's pair carrier. -/
def reports (H : Hist (fun _ : Address => Reply)) : LeafHistory :=
  H.map (fun e => (e.1, e.2))

/-- The maximum counts output alpha leaves, with no composition promise on unknown inputs. -/
noncomputable def maxAlpha {m : Nat} (F : Fin m → Source) : Nat :=
  Finset.univ.sup fun i => (alphaLeaves (F i)).card

set_option maxHeartbeats 2000000 in
-- Full-domain seed laws and the native all-history budget share the proof budget.
/-- The complete source31.7 capacity claim for one actual positive same-size family. -/
theorem result.{u} (m : Nat) (hm : 0 < m) (F : Fin m → Source)
    (hpos : ∀ i, Positive (F i)) (hinj : Function.Injective F)
    (n t : Nat) (hsize : ∀ i, (F i).length = n)
    (hK : K F = Kcircle m)
    (hbudget : D m hm F ≤ (n + t : Nat) ∨ W.{u} m hm F ≤ (n + t : Nat) ∨
      Wu m hm F ≤ (n + t : Nat)) :
    m ≤ M (maxAlpha F - 1) t := by
  classical
  open MeasureTheory in
  have randomEqualities : W.{u} m hm F = D m hm F ∧ Wu m hm F = D m hm F := by
    let sourceCode (P : Source) : Σ v : Nat × Nat, GenealogicalFiberTransport.Fiber v :=
      ⟨GenealogicalFiberTransport.composition P, P, rfl⟩
    have sourceCodeInj : Function.Injective sourceCode := by
      intro P Q he
      exact congrArg (fun x => x.2.val) he
    haveI : Countable Source := sourceCodeInj.countable
    have executionCost (p : Strategy) (U : Source) : extendedCost p.policy U = (cost p U : ENNReal) := by
      have he : ∃ n x, D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute
          readout p.policy n [] U = some x := by
        obtain ⟨n, x, hr, _⟩ := p.correct U
        exact ⟨n, x, hr⟩
      have hr := (Classical.choose_spec (Classical.choose_spec he))
      have ht := (Classical.choose_spec (Classical.choose_spec (p.correct U))).1
      have huniq := source_foundation.2.2.2.2.2.2.2 p.policy _ _ [] U _ _ hr ht
      unfold extendedCost
      rw [dif_pos he]
      exact congrArg (fun x => ((paid x.1).card : ENNReal)) huniq
    have valid (p : Strategy) (U : Source) : ¬ wrongReturn p.policy U ∧ ¬ diverges p.policy U := by
      obtain ⟨n, x, hx, hcorrect⟩ := p.correct U
      refine ⟨?_, ?_⟩
      · rintro ⟨k, y, hy, hbad⟩
        have hxy := source_foundation.2.2.2.2.2.2.2 p.policy n k [] U x y hx hy
        exact hbad (hxy ▸ hcorrect)
      · exact fun h => h ⟨n, x, hx⟩
    let constant {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (p : Strategy) :
        RandomContract μ := {
      policy := fun _ => p.policy
      wrongMeasurable := fun U => by simpa only [Set.setOf_false, (valid p U).1] using MeasurableSet.empty
      divergenceMeasurable := fun U => by simpa only [Set.setOf_false, (valid p U).2] using MeasurableSet.empty
      wrongNull := fun U => by simp [(valid p U).1]
      divergenceNull := fun U => by simp [(valid p U).2]
      measurableCost := fun _ => measurable_const }
    let constantUniform (p : Strategy) : UniformRandomStrategy := {
      policy := fun _ => p.policy
      wrongMeasurable := fun U => by simpa only [Set.setOf_false, (valid p U).1] using MeasurableSet.empty
      divergenceMeasurable := fun U => by simpa only [Set.setOf_false, (valid p U).2] using MeasurableSet.empty
      wrongNull := fun U => by simp [(valid p U).1]
      divergenceNull := fun U => by simp [(valid p U).2]
      measurableCost := fun _ => measurable_const }
    have lower {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (q : RandomContract μ) : D m hm F ≤ ∫⁻ seed, maxOn hm (fun i => extendedCost (q.policy seed) (F i)) ∂μ := by
      have good : ∀ᵐ seed ∂μ, ∀ U : Source,
          ¬ wrongReturn (q.policy seed) U ∧ ¬ diverges (q.policy seed) U := by
        rw [ae_all_iff]
        intro U
        exact (ae_iff.mpr (by simpa only [not_not] using q.wrongNull U)).and
          (ae_iff.mpr (by simpa only [not_not] using q.divergenceNull U))
      have hg : ∀ᵐ seed ∂μ, D m hm F ≤ maxOn hm (fun i => extendedCost (q.policy seed) (F i)) := by
        filter_upwards [good] with seed hseed
        let p : Strategy := {
          policy := q.policy seed
          correct := fun U => by
            have hterm := (hseed U).2
            unfold diverges at hterm
            obtain ⟨n, x, hx⟩ := not_not.mp hterm
            refine ⟨n, x, hx, ?_⟩
            by_contra hbad
            exact (hseed U).1 ⟨n, x, hx, hbad⟩ }
        have hle : D m hm F ≤ maxOn hm (fun i => (cost p (F i) : ENNReal)) := sInf_le ⟨p, rfl⟩
        have he : (fun i => extendedCost (q.policy seed) (F i)) = (fun i => (cost p (F i) : ENNReal)) := by
          funext i
          exact executionCost p (F i)
        rw [he]
        exact hle
      simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hg
    letI : IsProbabilityMeasure unitSeedMeasure := by
      refine ⟨?_⟩
      simp only [unitSeedMeasure, Measure.completion_apply]
      change (volume : Measure unitInterval) Set.univ = 1
      exact measure_univ
    have lowerUniform (q : UniformRandomStrategy) : D m hm F ≤
        ∫⁻ seed, maxOn hm (fun i => extendedCost (q.policy seed) (F i)) ∂unitSeedMeasure := by
      have good : ∀ᵐ seed ∂unitSeedMeasure, ∀ U : Source,
          ¬ wrongReturn (q.policy seed) U ∧ ¬ diverges (q.policy seed) U := by
        rw [ae_all_iff]
        intro U
        exact (ae_iff.mpr (by simpa only [not_not] using q.wrongNull U)).and
          (ae_iff.mpr (by simpa only [not_not] using q.divergenceNull U))
      have hg : ∀ᵐ seed ∂unitSeedMeasure, D m hm F ≤ maxOn hm (fun i => extendedCost (q.policy seed) (F i)) := by
        filter_upwards [good] with seed hseed
        let p : Strategy := {
          policy := q.policy seed
          correct := fun U => by
            have hterm := (hseed U).2
            unfold diverges at hterm
            obtain ⟨n, x, hx⟩ := not_not.mp hterm
            refine ⟨n, x, hx, ?_⟩
            by_contra hbad
            exact (hseed U).1 ⟨n, x, hx, hbad⟩ }
        have hle : D m hm F ≤ maxOn hm (fun i => (cost p (F i) : ENNReal)) := sInf_le ⟨p, rfl⟩
        have he : (fun i => extendedCost (q.policy seed) (F i)) = (fun i => (cost p (F i) : ENNReal)) := by
          funext i
          exact executionCost p (F i)
        rw [he]
        exact hle
      simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hg
    have Wlower : D m hm F ≤ W.{u} m hm F := by
      apply le_sInf
      rintro z ⟨q, rfl⟩
      letI := q.measurableSpace
      letI := q.probability
      exact lower q.seedMeasure q.controller
    have Wupper : W.{u} m hm F ≤ D m hm F := by
      apply le_sInf
      rintro z ⟨p, rfl⟩
      let μ : Measure PUnit.{u+1} := Measure.dirac PUnit.unit
      let q : RandomStrategy.{u} := {
        Ω := PUnit.{u+1}, measurableSpace := inferInstance, seedMeasure := μ,
        probability := by dsimp [μ]; infer_instance,
        controller := constant μ p }
      calc
        W.{u} m hm F ≤ ∫⁻ seed, maxOn hm (fun i => extendedCost (q.controller.policy seed) (F i)) ∂μ :=
          sInf_le ⟨q, rfl⟩
        _ = maxOn hm (fun i => (cost p (F i) : ENNReal)) := by
          simp only [q, constant, executionCost, lintegral_const]
          simp [μ]
    have ULower : D m hm F ≤ Wu m hm F := by
      apply le_sInf
      rintro z ⟨q, rfl⟩
      exact lowerUniform q
    have UUpper : Wu m hm F ≤ D m hm F := by
      apply le_sInf
      rintro z ⟨p, rfl⟩
      let q := constantUniform p
      calc
        Wu m hm F ≤ ∫⁻ seed, maxOn hm (fun i => extendedCost (q.policy seed) (F i)) ∂unitSeedMeasure :=
          sInf_le ⟨q, rfl⟩
        _ = maxOn hm (fun i => (cost p (F i) : ENNReal)) := by
          simp only [q, constantUniform, executionCost, lintegral_const, measure_univ, mul_one]
    exact ⟨le_antisymm Wupper Wlower, le_antisymm UUpper ULower⟩
  have hcost : D m hm F ≤ (n + t : Nat) := by
    rcases hbudget with h | h | h
    · exact h
    · simpa only [randomEqualities.1] using h
    · simpa only [randomEqualities.2] using h
  let s := maxAlpha F
  have leafLen (P : Source) (hP : Positive P) : (leaves P).length = P.length := by
    have hc := ActualJointResponseCostCore.result 1 (by decide) (fun _ => P)
      (fun _ => hP) (fun i j _ => Subsingleton.elim i j)
    obtain ⟨v, hv⟩ := hc.2.1
    obtain ⟨q, pi, _hpi, hp⟩ := hc.2.2.1 v hv
    let i : Fin 1 := 0
    obtain ⟨_cv, hpaid, _hv, _hn, hl, _hd, _hs, htotal⟩ := hp i
    have hnil : routeTrace q i = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil] at hpaid htotal
    simp only [paid, List.map_nil, List.toFinset_nil, Finset.empty_union,
      Finset.empty_sdiff, Finset.card_empty, Nat.add_zero] at hpaid htotal
    have he : cost pi P = (leaves P).toFinset.card := by
      change (paid (terminal pi P).1).card = _
      simpa only [paid] using congrArg Finset.card hpaid
    have hcard := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 P).1
    exact htotal.symm.trans (he.trans hcard)
  have badPair (i j : Fin m) (u : Address)
      (hi : readout u (F i) = .alpha) (hj : readout u (F j) = .beta) : False := by
    have hij : i ≠ j := by intro he; subst j; rw [hi] at hj; cases hj
    let G : Fin 2 → Source := fun k => if k = 0 then F i else F j
    have hGp : ∀ k, Positive (G k) := by intro k; dsimp [G]; split <;> exact hpos _
    have hGi : Function.Injective G := by
      intro k l he
      fin_cases k <;> fin_cases l
      · rfl
      · have hF : F i = F j := by simpa [G] using he
        exact (hij (hinj hF)).elim
      · have hF : F i = F j := by simpa [G] using he.symm
        exact (hij (hinj hF)).elim
      · rfl
    let a : actualVectors G := ⟨vector G u, u, rfl⟩
    have hai : Function.Injective a.val := by
      intro k l he
      fin_cases k <;> fin_cases l <;> simp [a, vector, G, hi, hj] at he ⊢
    have fibers (y : Reply) : (survivors Finset.univ a.val y).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro k hk l hl
      exact hai ((Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm)
    let next : ∀ y : Reply, (survivors Finset.univ a.val y).Nonempty →
        Recipe G (survivors Finset.univ a.val y) := by
      intro y hy
      let k := Classical.choose hy
      have hk := Classical.choose_spec hy
      have hsingle : survivors Finset.univ a.val y = {k} := by
        ext l
        constructor
        · intro hl
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp (fibers y) _ hl _ hk)
        · intro hl
          exact Finset.mem_singleton.mp hl ▸ hk
      rw [hsingle]
      exact .singleton k
    have hsplit : 2 ≤ (Finset.univ.image a.val).card := by
      have he : (Finset.univ.image a.val).card = (Finset.univ : Finset (Fin 2)).card :=
        Finset.card_image_iff.mpr (fun k _ l _ h => hai h)
      simpa using (he : (Finset.univ.image a.val).card = Finset.univ.card).ge
    let q : Recipe G Finset.univ := .split Finset.univ a hsplit next
    have singletonGain {T : Finset (Fin 2)} (z : Recipe G T) (hT : T.card ≤ 1) :
        ∀ k, gain z k = 0 := by
      cases z with
      | singleton k => intro l; rfl
      | split T b hs z =>
          have hc := Finset.card_image_le (s := T) (f := b.val)
          omega
    have hg (k : Fin 2) : gain q k = 0 := by
      simp only [q, gain, Finset.mem_univ, ↓reduceDIte]
      rw [singletonGain _ (fibers _)]
      fin_cases k <;> simp [a, vector, G, hi, hj, chi]
    let v : Fin 2 → Nat := fun k => (leaves (G k)).length
    have hv : v ∈ core G := ⟨q, fun k => by simp only [v, hg, Nat.add_zero]⟩
    have hp := ActualJointResponseCostCore.result 2 (by decide) G hGp hGi
    obtain ⟨_q, p, _hp, hcosts⟩ := hp.2.2.1 v hv
    have hpi : cost p (F i) = (F i).length := by
      simpa [G, v, leafLen (F i) (hpos i)] using (hcosts 0).1
    have hpj : cost p (F j) = (F j).length := by
      simpa [G, v, leafLen (F j) (hpos j)] using (hcosts 1).1
    have hmem : ({i, j} : Finset (Fin m)) ∈ K F := by
      refine ⟨p, ?_⟩
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hpi
      · exact hpj
    rw [hK] at hmem
    change ({i, j} : Finset (Fin m)).card ≤ 1 at hmem
    simp [hij] at hmem
  have noLeafConflict (i j : Fin m) (u : Address)
      (hi : chi (readout u (F i)) = 0) (hj : chi (readout u (F j)) = 0) :
      readout u (F i) = readout u (F j) := by
    cases he : readout u (F i) <;> cases hf : readout u (F j) <;>
      simp only [he, hf, chi] at hi hj ⊢
    all_goals first | rfl | omega | exact (badPair i j u he hf).elim | exact (badPair j i u hf he).elim
  have hc := ActualJointResponseCostCore.result m hm F hpos hinj
  let T : Finset (Fin m → Nat) := hc.1.toFinset
  have hT : T.Nonempty := by
    obtain ⟨w, hw⟩ := hc.2.1
    exact ⟨w, hc.1.mem_toFinset.mpr hw⟩
  obtain ⟨v, hvT, hmin⟩ := T.exists_min_image (fun v => maxOn hm (fun i => (v i : ENNReal))) hT
  have hv : v ∈ core F := hc.1.mem_toFinset.mp hvT
  obtain ⟨r, pi, hpi, hpaths⟩ := hc.2.2.1 v hv
  have hD : D m hm F = maxOn hm (fun i => (v i : ENNReal)) := by
    apply le_antisymm
    · apply sInf_le
      refine ⟨pi, ?_⟩
      congr 1
      funext i
      exact congrArg (fun x : Nat => (x : ENNReal)) (hpaths i).1.symm
    · apply le_sInf
      rintro z ⟨p, rfl⟩
      obtain ⟨w, hw, hdom⟩ := hc.2.2.2.1 p
      calc
        maxOn hm (fun i => (v i : ENNReal)) ≤ maxOn hm (fun i => (w i : ENNReal)) :=
          hmin w (hc.1.mem_toFinset.mpr hw)
        _ ≤ maxOn hm (fun i => (cost p (F i) : ENNReal)) := by
          apply Finset.sup'_le
          intro i hi
          exact le_trans (by exact_mod_cast hdom i) (Finset.le_sup' (f := fun i => (cost p (F i) : ENNReal)) hi)
  have leafCard (i : Fin m) : (alphaLeaves (F i)).card ≤ s :=
    Finset.le_sup (f := fun i => (alphaLeaves (F i)).card) (Finset.mem_univ i)
  have native := reached_prefix F r
  let terminalRoutes : Finset (Hist (fun _ : Address => Reply)) := Finset.univ.image (routeTrace r)
  have terminalCard : terminalRoutes.card = m := by
    rw [Finset.card_image_iff.mpr]
    · simp [terminalRoutes]
    · intro i hi j hj he
      exact native.2 i hi j hj (by rw [he])
  have antichain : ∀ H ∈ terminalRoutes, ∀ J ∈ terminalRoutes,
      H.IsPrefix J → H = J := by
    rintro H hH J hJ hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hJ
    rw [native.2 i hi j hj hp]
  rcases actual_address_geometry with
    ⟨_classify, _small, rows, decode, historyLaw, _overlap, _zero,
      _absent, _leafPrefix, _context, gammaShape, _gammaBlocks, _single,
      readAt, _appendSubtree, _leafNode, alphaSem⟩
  have actualMatch (H : Hist (fun _ : Address => Reply)) (i : Fin m)
      (hi : i ∈ queue F Finset.univ H) :
      Compatible (reports H) (F i) := by
    refine ⟨hpos i, ?_⟩
    intro u y he _hy
    obtain ⟨e, heH, heq⟩ := List.mem_map.mp he
    have hr := (Finset.mem_filter.mp hi).2 e heH
    have hu := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    exact (congrArg (fun x => readout x (F i)) hu).symm.trans (hr.trans hy)
  have representativeRead (a : actualVectors F) (i : Fin m) :
      readout (representative F a) (F i) = a.val i := by
    exact congrFun ((List.Shortlex.wf (InvImage.wf Bool.toNat Nat.lt_wfRel.wf)).min_mem
      {u | vector F u = a.val} a.property) i
  have constantNoSplit (T : Finset (Fin m)) (a : actualVectors F)
      (hs : 2 ≤ (T.image a.val).card) (y : Reply)
      (hconst : ∀ i ∈ T, a.val i = y) : False := by
    have hsub : T.image a.val ⊆ {y} := by
      rintro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      simpa only [Finset.mem_singleton] using hconst i hi
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have decodedReport (u w : Address) (y : Reply) (b : BlockKind)
      (hd : decodeBlock u y = some (w, b)) (P : Source)
      (hsub : subtree w P = some b.tree) : readout u P = y := by
    have hrev : u = u.reverse.reverse := (List.reverse_reverse u).symm
    unfold decodeBlock at hd
    split at hd <;> try contradiction
    all_goals
      rename_i hrevEq
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl⟩
      rw [hrev, hrevEq]
      simp only [List.reverse_cons, List.reverse_reverse, List.append_assoc]
      rw [readAt, hsub]
      rfl
  have strictAlpha (H : Hist (fun _ : Address => Reply))
      (T : Finset (Fin m)) (a : actualVectors F)
      (hs : 2 ≤ (T.image a.val).card) (hT : T = queue F Finset.univ H)
      (y : Reply) (hy : (survivors T a.val y).Nonempty) (hl : chi y = 0) :
      (gamma (reports H)).card <
        (gamma (reports (H ++ [⟨representative F a, y⟩]))).card := by
    let u := representative F a
    obtain ⟨i, hi⟩ := hy
    have hiT := (Finset.mem_filter.mp hi).1
    have hiy := (Finset.mem_filter.mp hi).2
    have hyLeaf : y = .alpha ∨ y = .beta := by cases y <;> simp [chi] at hl ⊢
    have hr : readout u (F i) = y := (representativeRead a i).trans hiy
    obtain ⟨d, hd, _unique⟩ := decode (F i) (hpos i) u y hyLeaf hr
    let anchor : Address := d.1 ++ (match d.2 with | .a => [false, true] | .c => [true, true])
    have ha : anchor ∉ gamma (reports H) := by
      intro ha
      have fixed (j : Fin m) (hj : j ∈ T) : subtree d.1 (F j) = some d.2.tree := by
        have hjQ : j ∈ queue F Finset.univ H := by simpa only [← hT] using hj
        have hjH := actualMatch H j hjQ
        have hAlpha := (alphaSem (F j) anchor).mp ((historyLaw (reports H) (F j) hjH).2 ha)
        cases hb : d.2 with
        | a =>
            exact (rows (F j) (hpos j) d.1).2.2.1 (by simpa [anchor, hb] using hAlpha)
        | c =>
            exact (rows (F j) (hpos j) d.1).2.2.2.2 (by simpa [anchor, hb] using hAlpha)
      apply constantNoSplit T a hs y
      intro j hj
      exact (representativeRead a j).symm.trans (decodedReport u d.1 y d.2 hd.1 (F j) (fixed j hj))
    have hblock : d ∈ forcedBlocks (reports (H ++ [⟨u, y⟩])) := by
      simp only [reports, List.map_append, List.map_cons, List.map_nil, forcedBlocks,
        List.filterMap_append, List.filterMap_cons, hd.1, List.filterMap_nil]
      simp
    have haNew : anchor ∈ gamma (reports (H ++ [⟨u, y⟩])) := by
      rw [gammaShape]
      cases hb : d.2 with
      | a =>
          have he : d = (d.1, BlockKind.a) := Prod.ext rfl hb
          exact Or.inl ⟨d.1, by exact he ▸ hblock, by simp [anchor, hb]⟩
      | c =>
          have he : d = (d.1, BlockKind.c) := Prod.ext rfl hb
          exact Or.inr ⟨d.1, by exact he ▸ hblock, Or.inr (by simp [anchor, hb])⟩
    have hsub : gamma (reports H) ⊆ gamma (reports (H ++ [⟨u, y⟩])) := by
      intro x hx
      obtain ⟨d', hd', hx⟩ := Finset.mem_biUnion.mp hx
      apply Finset.mem_biUnion.mpr
      refine ⟨d', ?_, hx⟩
      simpa only [reports, List.map_append, forcedBlocks, List.filterMap_append,
        List.toFinset_append, Finset.mem_union] using Or.inl hd'
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun he => ha (he.symm ▸ haNew)⟩)
  have paidPrefix (H J : Hist (fun _ : Address => Reply)) (hp : H.IsPrefix J) : paid H ⊆ paid J := by
    obtain ⟨K, rfl⟩ := hp
    simp only [paid, List.map_append, List.toFinset_append]
    exact Finset.subset_union_left
  have fresh (H : Hist (fun _ : Address => Reply)) (T : Finset (Fin m))
      (a : actualVectors F) (hs : 2 ≤ (T.image a.val).card)
      (hT : T = queue F Finset.univ H) : representative F a ∉ paid H := by
    intro hu
    obtain ⟨e, he, heu⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    apply constantNoSplit T a hs e.2
    intro i hi
    have hQ : i ∈ queue F Finset.univ H := hT ▸ hi
    have hh := (Finset.mem_filter.mp hQ).2 e he
    exact (representativeRead a i).symm.trans
      ((congrArg (fun u => readout u (F i)) heu).symm.trans hh)
  have leafAppend (H : Hist (fun _ : Address => Reply)) (e : Sigma (fun _ : Address => Reply)) :
      leafPaid (H ++ [e]) = if chi e.2 = 0 then insert e.1 (leafPaid H) else leafPaid H := by
    by_cases hl : chi e.2 = 0 <;>
      simp [leafPaid, List.filter_append, hl, Finset.union_comm]
  have nonleafAppend (H : Hist (fun _ : Address => Reply)) (e : Sigma (fun _ : Address => Reply)) :
      nonleafPaid (H ++ [e]) = if chi e.2 = 1 then insert e.1 (nonleafPaid H) else nonleafPaid H := by
    by_cases hl : chi e.2 = 1 <;>
      simp [nonleafPaid, List.filter_append, hl, Finset.union_comm]
  have gammaNonleaf (H : Hist (fun _ : Address => Reply))
      (e : Sigma (fun _ : Address => Reply)) (hn : chi e.2 = 1) :
      gamma (reports (H ++ [e])) = gamma (reports H) := by
    obtain ⟨u, y⟩ := e
    cases y <;> simp [chi] at hn
    all_goals simp [reports, gamma, forcedBlocks, decodeBlock]
  have leafSubset (H : Hist (fun _ : Address => Reply)) : leafPaid H ⊆ paid H := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, (List.mem_filter.mp he).1, rfl⟩)
  have nonleafSubset (H : Hist (fun _ : Address => Reply)) : nonleafPaid H ⊆ paid H := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, (List.mem_filter.mp he).1, rfl⟩)
  have growth : ∀ H : Hist (fun _ : Address => Reply),
      (∃ i ∈ Finset.univ, H.IsPrefix (routeTrace r i)) →
      (leafPaid H).card ≤ (gamma (reports H)).card := by
    intro H
    induction H using List.reverseRecOn with
    | nil => intro _; simp [leafPaid, reports, gamma, forcedBlocks]
    | append_singleton H e ih =>
        intro hH
        have hpar : ∃ i ∈ Finset.univ, H.IsPrefix (routeTrace r i) := by
          obtain ⟨i, hi, K, he⟩ := hH
          exact ⟨i, hi, [e] ++ K, by simpa only [List.append_assoc] using he⟩
        have hg := ih hpar
        obtain ⟨R, _hr, hQ, _hp, _hsuf, _happ, _huniq, hchildren⟩ := native.1 H hpar
        have hch := (hchildren e).mp hH
        obtain ⟨T, q⟩ := R
        cases q with
        | singleton i => exact hch.elim
        | split T a hs next =>
            obtain ⟨hu, hy⟩ := hch
            obtain ⟨u, y⟩ := e
            change u = representative F a at hu
            subst u
            have hfr := fresh H T a hs hQ
            by_cases hl : chi y = 0
            · have hnew := strictAlpha H T a hs hQ y hy hl
              have hnot : representative F a ∉ leafPaid H := fun h => hfr (leafSubset H h)
              rw [leafAppend, if_pos hl, Finset.card_insert_of_notMem hnot]
              omega
            · rw [leafAppend, if_neg hl]
              have hn : chi y = 1 := by cases y <;> simp [chi] at hl ⊢
              rw [gammaNonleaf H _ hn]
              exact hg
  have singletonThreshold (H : Hist (fun _ : Address => Reply))
      (hH : ∃ i ∈ Finset.univ, H.IsPrefix (routeTrace r i))
      (hf : s - 1 ≤ (leafPaid H).card) : (queue F Finset.univ H).card ≤ 1 := by
    have hg := growth H hH
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hPi := actualMatch H i hi
    have hPj := actualMatch H j hj
    have hsub := (historyLaw (reports H) (F i) hPi).2
    have hdiff : (uncovered (reports H) (F i)).card ≤ 1 := by
      rw [uncovered, Finset.card_sdiff_of_subset hsub]
      have hs := leafCard i
      have hgc := Finset.card_le_card hsub
      omega
    exact hinj ((ActualHistorySingleHoleRecovery.complete_history_rigidity
      (reports H) (F i) hPi).2.2 hdiff (F j) hPj ((hsize j).trans (hsize i).symm)).symm
  have leafChi (P : Source) (u : Address) :
      u ∈ (leaves P).toFinset ↔ chi (readout u P) = 0 := by
    change u ∈ ActualImageSevenLeafSeparation.leafAddresses P ↔ _
    rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.1 P).2 u]
    cases he : readout u P <;> simp [ActualImageSevenLeafSeparation.leafLabel, he, chi]
  have nonleafExact (H : Hist (fun _ : Address => Reply)) (i : Fin m)
      (hp : H.IsPrefix (routeTrace r i)) :
      nonleafPaid H = paid H \ (leaves (F i)).toFinset := by
    obtain ⟨R, _hr, hQ, hprefix, _hs⟩ := native.1 H ⟨i, Finset.mem_univ i, hp⟩
    have hiQ : i ∈ queue F Finset.univ H := hQ ▸ (hprefix i (Finset.mem_univ i)).mp hp
    have hactual := (Finset.mem_filter.mp hiQ).2
    ext u
    constructor
    · intro hu
      obtain ⟨e, he, heu⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
      have heH := (List.mem_filter.mp he).1
      have heChi : chi e.2 = 1 := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
      refine Finset.mem_sdiff.mpr ⟨nonleafSubset H hu, ?_⟩
      rw [leafChi]
      have hread : readout u (F i) = e.2 := by rw [← heu]; exact hactual e heH
      rw [hread]
      omega
    · intro hu
      obtain ⟨huH, huNot⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨e, heH, heu⟩ := List.mem_map.mp (List.mem_toFinset.mp huH)
      have hread : readout u (F i) = e.2 := by rw [← heu]; exact hactual e heH
      have hnot : chi e.2 ≠ 0 := by
        rw [← hread]
        exact fun hz => huNot ((leafChi (F i) u).mpr hz)
      have hn : chi e.2 = 1 := by cases hy : e.2 <;> simp [hy, chi] at hnot ⊢
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨heH, by simpa using hn⟩, heu⟩)
  have charged (i : Fin m) : cost pi (F i) = n + (nonleafPaid (routeTrace r i)).card := by
    have hp := (hpaths i).2.2.2.2.2.2.2
    rw [leafLen (F i) (hpos i), hsize i,
      ← nonleafExact (routeTrace r i) i List.prefix_rfl] at hp
    exact hp
  have prototypeBudget (i : Fin m) : (nonleafPaid (routeTrace r i)).card ≤ t := by
    have hvb : (v i : ENNReal) ≤ (n + t : Nat) := by
      apply le_trans (Finset.le_sup' (f := fun i => (v i : ENNReal)) (Finset.mem_univ i))
      change maxOn hm (fun i => (v i : ENNReal)) ≤ _
      rw [← hD]
      exact hcost
    have hnat : v i ≤ n + t := by exact_mod_cast hvb
    have hp := charged i
    rw [(hpaths i).1] at hp
    omega
  have prefixNonleaf (H : Hist (fun _ : Address => Reply)) (i : Fin m)
      (hp : H.IsPrefix (routeTrace r i)) : (nonleafPaid H).card ≤ t := by
    apply le_trans (Finset.card_le_card (show nonleafPaid H ⊆ nonleafPaid (routeTrace r i) from ?_))
      (prototypeBudget i)
    rw [nonleafExact H i hp, nonleafExact (routeTrace r i) i List.prefix_rfl]
    intro u hu
    obtain ⟨huH, hn⟩ := Finset.mem_sdiff.mp hu
    exact Finset.mem_sdiff.mpr ⟨paidPrefix H (routeTrace r i) hp huH, hn⟩
  let live (H : Hist (fun _ : Address => Reply)) : Prop :=
    ∃ i ∈ Finset.univ, H.IsPrefix (routeTrace r i)
  have liveParent (H : Hist (fun _ : Address => Reply)) (e : Sigma (fun _ : Address => Reply))
      (h : live (H ++ [e])) : live H := by
    obtain ⟨i, hi, K, he⟩ := h
    exact ⟨i, hi, [e] ++ K, by simpa only [List.append_assoc] using he⟩
  have strictBudgets (H : Hist (fun _ : Address => Reply)) (hH : live H)
      (T : Finset (Fin m)) (a : actualVectors F) (hs : 2 ≤ (T.image a.val).card)
      (hQ : T = queue F Finset.univ H)
      (children : ∀ e, live (H ++ [e]) ↔ e.1 = representative F a ∧
        (survivors T a.val e.2).Nonempty) :
      (leafPaid H).card < s - 1 ∧ (nonleafPaid H).card < t := by
    have hf : (leafPaid H).card < s - 1 := by
      by_contra h
      have hcard := singletonThreshold H hH (by omega)
      rw [← hQ] at hcard
      have himage := Finset.card_image_le (s := T) (f := a.val)
      omega
    have hT : T.Nonempty := by
      by_contra h
      have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [hz] at hs
    obtain ⟨i, hi⟩ := hT
    have hn : ∃ j ∈ T, chi (a.val j) = 1 := by
      by_contra h
      have hl : ∀ j ∈ T, chi (a.val j) = 0 := by
        intro j hj
        have hnot : chi (a.val j) ≠ 1 := fun he => h ⟨j, hj, he⟩
        cases he : a.val j <;> simp [he, chi] at hnot ⊢
      apply constantNoSplit T a hs (a.val i)
      intro j hj
      have he := noLeafConflict j i (representative F a)
        (by rw [representativeRead]; exact hl j hj)
        (by rw [representativeRead]; exact hl i hi)
      simpa only [representativeRead] using he
    obtain ⟨j, hj, hjn⟩ := hn
    let e : Sigma (fun _ : Address => Reply) := ⟨representative F a, a.val j⟩
    have hy : (survivors T a.val (a.val j)).Nonempty := ⟨j, by simp [survivors, hj]⟩
    have hchild : live (H ++ [e]) := (children e).mpr ⟨rfl, hy⟩
    obtain ⟨k, _hk, hp⟩ := hchild
    have hc := prefixNonleaf (H ++ [e]) k hp
    have hfr := fresh H T a hs hQ
    have hnot : e.1 ∉ nonleafPaid H := fun h => hfr (nonleafSubset H h)
    rw [nonleafAppend, if_pos hjn, Finset.card_insert_of_notMem hnot] at hc
    exact ⟨hf, by omega⟩
  let B (H : Hist (fun _ : Address => Reply)) : Nat :=
    if live H then M (s - 1 - (leafPaid H).card) (t - (nonleafPaid H).card) else 0
  have localBudget : ∀ H (C : Finset (Sigma (fun _ : Address => Reply))),
      ∑ e ∈ C, B (H ++ [e]) ≤ B H := by
    intro H C
    by_cases hH : live H
    · obtain ⟨R, _hr, hQ, _hp, _hs, _ha, _hu, hchildren⟩ := native.1 H hH
      obtain ⟨T, q⟩ := R
      cases q with
      | singleton k =>
          have hz : ∀ e, ¬ live (H ++ [e]) := fun e he => (hchildren e).mp he
          simp only [B, hH, ↓reduceIte]
          simp [B, hz]
      | split T a hs next =>
          have children : ∀ e, live (H ++ [e]) ↔ e.1 = representative F a ∧
              (survivors T a.val e.2).Nonempty := hchildren
          obtain ⟨hf, hc⟩ := strictBudgets H hH T a hs hQ children
          let L := C.filter fun e => live (H ++ [e]) ∧ chi e.2 = 0
          let N := C.filter fun e => live (H ++ [e]) ∧ chi e.2 = 1
          let lw := M (s - 1 - (leafPaid H).card - 1) (t - (nonleafPaid H).card)
          let nw := M (s - 1 - (leafPaid H).card) (t - (nonleafPaid H).card - 1)
          have hL : L.card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro e he d hd
            have hel := (Finset.mem_filter.mp he).2
            have hdl := (Finset.mem_filter.mp hd).2
            obtain ⟨heu, i, hi⟩ := (children e).mp hel.1
            obtain ⟨hdu, j, hj⟩ := (children d).mp hdl.1
            have hiy := (Finset.mem_filter.mp hi).2
            have hjy := (Finset.mem_filter.mp hj).2
            have hc := noLeafConflict i j (representative F a)
              (by rw [representativeRead, hiy]; exact hel.2)
              (by rw [representativeRead, hjy]; exact hdl.2)
            rw [representativeRead, representativeRead, hiy, hjy] at hc
            exact Sigma.ext (heu.trans hdu.symm) (heq_of_eq hc)
          have hN : N.card ≤ 2 := by
            have hsub : N ⊆ {⟨representative F a, Reply.branch⟩,
                ⟨representative F a, Reply.absent⟩} := by
              intro e he
              have hen := (Finset.mem_filter.mp he).2
              have heu := ((children e).mp hen.1).1
              obtain ⟨u, y⟩ := e
              change u = representative F a at heu
              subst u
              cases y <;> simp [chi] at hen ⊢
            exact le_trans (Finset.card_le_card hsub) (by simp)
          have weights (e : Sigma (fun _ : Address => Reply)) (he : live (H ++ [e])) :
              B (H ++ [e]) = if chi e.2 = 0 then lw else nw := by
            have heu := ((children e).mp he).1
            have hfr := fresh H T a hs hQ
            have hnotL : e.1 ∉ leafPaid H := by rw [heu]; exact fun h => hfr (leafSubset H h)
            have hnotN : e.1 ∉ nonleafPaid H := by rw [heu]; exact fun h => hfr (nonleafSubset H h)
            by_cases hl : chi e.2 = 0
            · have hn : chi e.2 ≠ 1 := by omega
              simp [B, he, leafAppend, nonleafAppend, hl, hn,
                Finset.card_insert_of_notMem hnotL, lw, Nat.sub_sub, Nat.add_assoc]
            · have hn : chi e.2 = 1 := by cases hy : e.2 <;> simp [hy, chi] at hl ⊢
              simp [B, he, leafAppend, nonleafAppend, hl, hn,
                Finset.card_insert_of_notMem hnotN, nw, Nat.sub_sub, Nat.add_assoc]
          have partition : C.filter (fun e => live (H ++ [e])) = L ∪ N := by
            ext e
            dsimp only [L, N]
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
            cases hy : e.2 <;> simp [hy, chi]
          have hd : Disjoint L N := by
            apply Finset.disjoint_left.mpr
            intro e he hn
            have h0 := (Finset.mem_filter.mp he).2.2
            have h1 := (Finset.mem_filter.mp hn).2.2
            omega
          have hsum : ∑ e ∈ C, B (H ++ [e]) = L.card * lw + N.card * nw := by
            calc
              ∑ e ∈ C, B (H ++ [e]) = ∑ e ∈ C.filter (fun e => live (H ++ [e])), B (H ++ [e]) := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro e _
                by_cases he : live (H ++ [e]) <;> simp [B, he]
              _ = (∑ e ∈ L, B (H ++ [e])) + ∑ e ∈ N, B (H ++ [e]) := by
                rw [partition, Finset.sum_union hd]
              _ = L.card * lw + N.card * nw := by
                congr 1
                · trans ∑ _e ∈ L, lw
                  · apply Finset.sum_congr rfl
                    intro e he
                    have hel := (Finset.mem_filter.mp he).2
                    rw [weights e hel.1, if_pos hel.2]
                  · simp
                · trans ∑ _e ∈ N, nw
                  · apply Finset.sum_congr rfl
                    intro e he
                    have hen := (Finset.mem_filter.mp he).2
                    rw [weights e hen.1, if_neg (by omega)]
                  · simp
          have recurrence : M (s - 1 - (leafPaid H).card) (t - (nonleafPaid H).card) = lw + 2 * nw := by
            have hr : s - 1 - (leafPaid H).card = (s - 1 - (leafPaid H).card - 1) + 1 := by omega
            have hb : t - (nonleafPaid H).card = (t - (nonleafPaid H).card - 1) + 1 := by omega
            dsimp [lw, nw]
            rw [hr, hb]
            simp only [M, Nat.add_sub_cancel]
          rw [hsum]
          simp only [B, hH, ↓reduceIte, recurrence]
          exact Nat.add_le_add (by simpa using Nat.mul_le_mul_right lw hL) (Nat.mul_le_mul_right nw hN)
    · have hz : ∀ e, ¬ live (H ++ [e]) := fun e he => hH (liveParent H e he)
      simp [B, hH, hz]
  have positiveM (r t : Nat) : 1 ≤ M r t := by
    induction t generalizing r with
    | zero => cases r <;> simp [M]
    | succ t ih =>
        cases r with
        | zero => simp [M]
        | succ r =>
            rw [M]
            have hp := ih (r + 1)
            omega
  calc
    m = terminalRoutes.card := terminalCard.symm
    _ = ∑ _H ∈ terminalRoutes, 1 := by simp
    _ ≤ ∑ H ∈ terminalRoutes, B H := by
      apply Finset.sum_le_sum
      intro H hH
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hH
      have hl : live (routeTrace r i) := ⟨i, hi, List.prefix_rfl⟩
      simp only [B, hl, ↓reduceIte]
      exact positiveM _ _
    _ ≤ B [] := D5.S0.History.FinitePrefixAntichainBudget.result B localBudget terminalRoutes antichain
    _ = M (maxAlpha F - 1) t := by
      have hl : live [] := ⟨⟨0, hm⟩, Finset.mem_univ _, List.nil_prefix⟩
      simp [B, hl, leafPaid, nonleafPaid, s]

#print axioms result

end D5.S3.Arith.FibonacciAtomic.ActualStrictHistoryCapacity

/- GID: D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite actual-vector routing, simultaneous cost core, and complete result. -/

import D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
import Mathlib.Data.List.Shortlex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore

open ActualTreeReadoutAcquisition
open scoped BigOperators
open GenealogicalFiberTransport (Source substitution)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- Address order is shortlex, with left before right at equal length. -/
def addressOrder : Address → Address → Prop :=
  List.Shortlex (InvImage (· < ·) Bool.toNat)

/-- The first actual address realizing the complete joint response vector. -/
noncomputable def representative {m : Nat} (F : Fin m → Source)
    (a : actualVectors F) : Address :=
  (List.Shortlex.wf (InvImage.wf Bool.toNat Nat.lt_wfRel.wf)).min
    {u | vector F u = a.val} a.property

/-- The nonempty child selected by an actual report. -/
def survivors {m : Nat} (S : Finset (Fin m)) (a : Fin m → Reply) (y : Reply) : Finset (Fin m) :=
  S.filter (fun i => a i = y)

/-- Literal finite splitting choices; empty response children are omitted.
Singletons terminate routing but do not certify an unknown input. -/
inductive Recipe {m : Nat} (F : Fin m → Source) : Finset (Fin m) → Type
  | singleton (i : Fin m) : Recipe F {i}
  | split (S : Finset (Fin m)) (a : actualVectors F)
      (splits : 2 ≤ (S.image a.val).card)
      (next : ∀ y : Reply, (survivors S a.val y).Nonempty →
        Recipe F (survivors S a.val y)) : Recipe F S

/-- The recursively defined response excess, independently of any attained strategy cost. -/
def gain {m : Nat} {F : Fin m → Source} :
    {S : Finset (Fin m)} → Recipe F S → Fin m → Nat
  | _, .singleton _, _ => 0
  | S, .split _ a _ next, i => if hi : i ∈ S then
      chi (a.val i) + gain (next (a.val i) ⟨i, by simp [survivors, hi]⟩) i
    else 0

/-- All recursive excess vectors on the given survivor coordinates. -/
def Gamma {m : Nat} (F : Fin m → Source) (S : Finset (Fin m)) : Set (S → Nat) :=
  Set.range (fun r : Recipe F S => fun i : S => gain r i.val)

/-- The complete recursive numerical core retains all recipe vectors. -/
def core {m : Nat} (F : Fin m → Source) : Set (Fin m → Nat) :=
  {v | ∃ r : Recipe F Finset.univ, ∀ i, v i = (leaves (F i)).length + gain r i}

/-- Finite actual routing and labelled-leaf phases, followed when needed by acquisition. -/
inductive Controller
  | accept
  | fallback
  | query (u : Address) (next : Reply → Controller)

/-- Replay only this controller's requested reports; entering fallback leaves a fresh suffix. -/
noncomputable def controllerPolicy : Controller → Policy
  | .accept, _ => .inr true
  | .fallback, h => acquisitionPolicy h
  | .query u _, [] => .inl u
  | .query u next, a :: h => if a.1 = u then controllerPolicy (next a.2) h else .inr false

/-- Actual additional execution, with an independent acquisition run at fallback entry. -/
noncomputable def controllerOutcome : Controller → Source → Hist (fun _ : Address => Reply) × Bool
  | .accept, _ => ([],true)
  | .fallback, U => (acquisitionTrace [] U, finiteDecision U)
  | .query u next, U =>
      let p := controllerOutcome (next (readout u U)) U
      (⟨u,readout u U⟩ :: p.1, p.2)

/-- Test the complete prototype leaves in their fixed order; mismatches restart acquisition. -/
noncomputable def verifyController (V : Source) : List Address → Controller
  | [] => .accept
  | q :: qs => .query q (fun y =>
      if y = readout q V then verifyController V qs else .fallback)

/-- Full-vector representatives route before the selected complete labelled-leaf test. -/
noncomputable def recipeController {m : Nat} {F : Fin m → Source} :
    {S : Finset (Fin m)} → Recipe F S → Controller
  | _, .singleton i => verifyController (F i) (leaves (F i))
  | S, .split _ a _ next => .query (representative F a) (fun y =>
      if hy : (survivors S a.val y).Nonempty then recipeController (next y hy)
      else .fallback)

/-- The requested route reports on one prototype, without verifier or fallback reports. -/
noncomputable def routeTrace {m : Nat} {F : Fin m → Source} :
    {S : Finset (Fin m)} → Recipe F S → Fin m → Hist (fun _ : Address => Reply)
  | _, .singleton _, _ => []
  | S, .split _ a _ next, i => if hi : i ∈ S then
      ⟨representative F a, a.val i⟩ ::
        routeTrace (next (a.val i) ⟨i, by simp [survivors, hi]⟩) i
    else []


/-- A partial prototype verifier accepts exactly matching reports or positive inputs. -/
theorem verifier (V U : Source) (qs : List Address) :
    (controllerOutcome (verifyController V qs) U).2 = true ↔
      (∀ q ∈ qs, readout q U = readout q V) ∨ Positive U := by
  classical
  induction qs with
  | nil => simp [verifyController, controllerOutcome]
  | cons q qs ih =>
    by_cases he : readout q U = readout q V
    · simp only [verifyController, controllerOutcome, he, ↓reduceIte]
      simpa [he] using ih
    · simp only [verifyController, controllerOutcome, he, ↓reduceIte]
      rw [acquisition_foundation.1 U]
      simp [he]

/-- A prototype matches every requested address of its own verifier. -/
theorem matched (V : Source) (qs : List Address) :
    controllerOutcome (verifyController V qs) V =
      (qs.map (fun q => ⟨q,readout q V⟩),true) := by
  classical
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [verifyController, controllerOutcome, ih]

theorem phase_foundation :
    (∀ c : Controller, ∀ U : Source,
      execute readout (controllerPolicy c) ((controllerOutcome c U).1.length+1) [] U =
        some (controllerOutcome c U)) ∧
    (∀ V : Source, Positive V → ∀ U : Source,
      (controllerOutcome (verifyController V (leaves V)) U).2 = true ↔ Positive U) ∧
    (∀ V : Source, controllerOutcome (verifyController V (leaves V)) V =
      ((leaves V).map (fun q => ⟨q,readout q V⟩),true)) ∧
    (∀ (m : Nat) (F : Fin m → Source), (∀ i, Positive (F i)) →
      ∀ (S : Finset (Fin m)) (r : Recipe F S) (U : Source),
        (controllerOutcome (recipeController r) U).2 = true ↔ Positive U) ∧
    (∀ (m : Nat) (F : Fin m → Source) (S : Finset (Fin m)) (r : Recipe F S),
      ∀ i ∈ S,
        controllerOutcome (recipeController r) (F i) =
          (routeTrace r i ++ (leaves (F i)).map (fun q => ⟨q,readout q (F i)⟩),true) ∧
        paid (controllerOutcome (recipeController r) (F i)).1 =
          paid (routeTrace r i) ∪ (leaves (F i)).toFinset) := by
  classical
  have phase (outer inner : Policy) (priorHist : Hist (fun _ : Address => Reply))
      (hp : ∀ h, outer (priorHist ++ h) = inner h) :
      ∀ n h U, execute readout outer n (priorHist ++ h) U = execute readout inner n h U := by
    intro n
    induction n with
    | zero => intro h U; rfl
    | succ n ih =>
      intro h U
      simp only [execute, hp]
      cases he : inner h with
      | inr b => rfl
      | inl q =>
        simpa only [List.append_assoc] using
          congrArg (Option.map (fun p => (⟨q,readout q U⟩ :: p.1,p.2)))
            (ih (h ++ [⟨q,readout q U⟩]) U)
  have execution (c : Controller) (U : Source) :
      execute readout (controllerPolicy c) ((controllerOutcome c U).1.length+1) [] U =
        some (controllerOutcome c U) := by
    induction c with
    | accept => rfl
    | fallback => exact acquisition_foundation.2 U
    | query q next ih =>
      let y := readout q U
      have hp : ∀ h, controllerPolicy (.query q next) ([⟨q,y⟩] ++ h) =
          controllerPolicy (next y) h := by intro h; simp [controllerPolicy]
      have hs := phase (controllerPolicy (.query q next)) (controllerPolicy (next y))
        [⟨q,y⟩] hp ((controllerOutcome (next y) U).1.length+1) [] U
      simp only [List.append_nil] at hs
      change execute readout (controllerPolicy (.query q next))
        ((controllerOutcome (next y) U).1.length+1+1) [] U =
          some (⟨q,y⟩ :: (controllerOutcome (next y) U).1,
            (controllerOutcome (next y) U).2)
      rw [execute]
      change (execute readout (controllerPolicy (.query q next))
        ((controllerOutcome (next y) U).1.length+1) [⟨q,y⟩] U).map
          (fun p => (⟨q,y⟩ :: p.1,p.2)) = _
      rw [hs, ih y]
      rfl
  have correct (V : Source) (hv : Positive V) (U : Source) :
      (controllerOutcome (verifyController V (leaves V)) U).2 = true ↔ Positive U := by
    rw [verifier]
    constructor
    · rintro (h | h)
      · have he := source_foundation.2.2.1 V U h
        simpa [he] using hv
      · exact h
    · exact Or.inr
  have realized (m : Nat) (F : Fin m → Source) (a : actualVectors F) :
      vector F (representative F a) = a.val :=
    (List.Shortlex.wf (InvImage.wf Bool.toNat Nat.lt_wfRel.wf)).min_mem
      {u | vector F u = a.val} a.property
  have prototype (m : Nat) (F : Fin m → Source) (S : Finset (Fin m)) (r : Recipe F S) :
      ∀ i ∈ S, controllerOutcome (recipeController r) (F i) =
        (routeTrace r i ++ (leaves (F i)).map (fun q => ⟨q,readout q (F i)⟩),true) ∧
        paid (controllerOutcome (recipeController r) (F i)).1 =
          paid (routeTrace r i) ∪ (leaves (F i)).toFinset := by
    have traces : ∀ i ∈ S, controllerOutcome (recipeController r) (F i) =
        (routeTrace r i ++ (leaves (F i)).map (fun q => ⟨q,readout q (F i)⟩),true) := by
      induction r with
      | singleton j =>
        intro i hi
        have he : i = j := Finset.mem_singleton.mp hi
        subst i
        simpa [recipeController, routeTrace] using matched (F j) (leaves (F j))
      | split S a hs next ih =>
        intro i hi
        have hr : readout (representative F a) (F i) = a.val i :=
          congrFun (realized m F a) i
        have hy : (survivors S a.val (a.val i)).Nonempty := ⟨i,by simp [survivors,hi]⟩
        have hc : i ∈ survivors S a.val (a.val i) := by simp [survivors,hi]
        have ht := ih (a.val i) hy i hc
        have hnext : (fun y => if hy : (survivors S a.val y).Nonempty then
            recipeController (next y hy) else .fallback)
              (readout (representative F a) (F i)) = recipeController (next (a.val i) hy) := by
          rw [hr]
          simp only [hy, ↓reduceDIte]
        change (⟨representative F a,readout (representative F a) (F i)⟩ ::
          (controllerOutcome ((fun y => if hy : (survivors S a.val y).Nonempty then
            recipeController (next y hy) else .fallback)
              (readout (representative F a) (F i))) (F i)).1,
          (controllerOutcome ((fun y => if hy : (survivors S a.val y).Nonempty then
            recipeController (next y hy) else .fallback)
              (readout (representative F a) (F i))) (F i)).2) = _
        rw [hnext,ht]
        simp only [routeTrace, hi, ↓reduceDIte, hr, List.cons_append]
    intro i hi
    have ht := traces i hi
    refine ⟨ht, ?_⟩
    rw [ht]
    simp [paid, List.map_append, List.map_map, Function.comp_def]
  refine ⟨execution, correct, fun V => matched V (leaves V), ?_, prototype⟩
  intro m F hpos S r
  induction r with
  | singleton i => exact correct (F i) (hpos i)
  | split S a hs next ih =>
    intro U
    simp only [recipeController, controllerOutcome]
    by_cases hy : (survivors S a.val (readout (representative F a) U)).Nonempty
    · simp only [hy, ↓reduceDIte]
      exact ih _ hy U
    · simp only [hy, ↓reduceDIte, controllerOutcome]
      exact acquisition_foundation.1 U

/-- One fixed total original-domain strategy for each complete recursive routing recipe. -/
noncomputable def recipeStrategy {m : Nat} {F : Fin m → Source}
    (hpos : ∀ i, Positive (F i)) {S : Finset (Fin m)} (r : Recipe F S) : Strategy where
  policy := controllerPolicy (recipeController r)
  correct U := ⟨(controllerOutcome (recipeController r) U).1.length+1,
    controllerOutcome (recipeController r) U, phase_foundation.1 _ U,
    phase_foundation.2.2.2.1 m F hpos S r U⟩

theorem cost_foundation :
    (∀ V : Source, (leaves V).Nodup ∧
      ∀ u : Address, chi (readout u V) = if u ∈ leaves V then 0 else 1) ∧
    (∀ (m : Nat) (F : Fin m → Source) (hpos : ∀ i, Positive (F i))
      (S : Finset (Fin m)) (r : Recipe F S), ∀ i ∈ S,
      terminal (recipeStrategy hpos r) (F i) = controllerOutcome (recipeController r) (F i) ∧
      ((routeTrace r i).map (fun q => vector F q.1)).Nodup ∧
      ((routeTrace r i).map Sigma.fst).Nodup ∧
      (routeTrace r i).length ≤ S.card - 1 ∧
      gain r i = ((routeTrace r i).map (fun q => chi q.2)).sum ∧
      (paid (routeTrace r i) \ (leaves (F i)).toFinset).card = gain r i ∧
      cost (recipeStrategy hpos r) (F i) = (leaves (F i)).length + gain r i) ∧
    (∀ (m : Nat) (F : Fin m → Source),
      core F ⊆ {v | ∀ i, (leaves (F i)).length ≤ v i ∧
        v i ≤ (leaves (F i)).length + m - 1}) := by
  classical
  have leafFacts : ∀ V : Source, (leaves V).Nodup ∧
      ∀ u : Address, chi (readout u V) = if u ∈ leaves V then 0 else 1 := by
    intro V
    induction V with
    | of b =>
      constructor
      · simp [leaves]
      · intro u; cases u <;> cases b <;> simp [readout, leaves, chi]
    | mul s t hs ht =>
      constructor
      · rw [leaves, List.nodup_append]
        refine ⟨hs.1.map (fun _ _ h => List.cons.inj h |>.2),
          ht.1.map (fun _ _ h => List.cons.inj h |>.2), ?_⟩
        intro u hu v hv he
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
        cases he
      · intro u
        cases u with
        | nil => simp [leaves, readout, chi]
        | cons b u =>
          cases b with
          | false => simpa [leaves,readout] using hs.2 u
          | true => simpa [leaves,readout] using ht.2 u
  have realized (m : Nat) (F : Fin m → Source) (a : actualVectors F) :
      vector F (representative F a) = a.val :=
    (List.Shortlex.wf (InvImage.wf Bool.toNat Nat.lt_wfRel.wf)).min_mem
      {u | vector F u = a.val} a.property
  have different {m : Nat} (S : Finset (Fin m)) (a : Fin m → Reply)
      (hs : 2 ≤ (S.image a).card) (i : Fin m) (hi : i ∈ S) :
      ∃ j ∈ S, a j ≠ a i := by
    by_contra hn
    push Not at hn
    have hsub : S.image a ⊆ {a i} := by
      intro y hy
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
      simpa using hn j hj
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have smaller {m : Nat} (S : Finset (Fin m)) (a : Fin m → Reply)
      (hs : 2 ≤ (S.image a).card) (i : Fin m) (hi : i ∈ S) :
      (survivors S a (a i)).card < S.card := by
    obtain ⟨j,hj,hne⟩ := different S a hs i hi
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have : j ∈ survivors S a (a i) := he.symm ▸ hj
    exact hne (Finset.mem_filter.mp this).2
  have path : ∀ (m : Nat) (F : Fin m → Source) (S : Finset (Fin m)) (r : Recipe F S),
      ∀ i ∈ S,
      ((routeTrace r i).map (fun q => vector F q.1)).Nodup ∧
      (∀ v ∈ (routeTrace r i).map (fun q => vector F q.1), ∃ j ∈ S, v j ≠ v i) ∧
      (routeTrace r i).length ≤ S.card - 1 ∧
      gain r i = ((routeTrace r i).map (fun q => chi q.2)).sum ∧
      gain r i ≤ (routeTrace r i).length ∧
      (∀ q ∈ routeTrace r i, q.2 = readout q.1 (F i)) := by
    intro m F S r
    induction r with
    | singleton j =>
      intro i hi
      simp [routeTrace, gain]
    | split S a hs next ih =>
      intro i hi
      have hc : i ∈ survivors S a.val (a.val i) := by simp [survivors,hi]
      have hy : (survivors S a.val (a.val i)).Nonempty := ⟨i,hc⟩
      obtain ⟨hn,hd,hl,hg,hb,ht⟩ := ih (a.val i) hy i hc
      have hr := realized m F a
      have hri := congrFun hr i
      have hsmall := smaller S a.val hs i hi
      have hnot : a.val ∉ (routeTrace (next (a.val i) hy) i).map
          (fun q => vector F q.1) := by
        intro hm
        obtain ⟨j,hj,hne⟩ := hd _ hm
        exact hne (Finset.mem_filter.mp hj).2
      simp only [routeTrace,hi,↓reduceDIte,List.map_cons,hr,List.nodup_cons]
      refine ⟨⟨hnot,hn⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact different S a.val hs i hi
        · obtain ⟨j,hj,hne⟩ := hd v hv
          exact ⟨j,(Finset.mem_filter.mp hj).1,hne⟩
      · simp only [List.length_cons]
        have hnS : 0 < S.card := Finset.card_pos.mpr ⟨i,hi⟩
        have hnchild : 0 < (survivors S a.val (a.val i)).card := Finset.card_pos.mpr hy
        omega
      · simp only [gain,hi,↓reduceDIte,List.sum_cons,hg]
      · simp only [gain,hi,↓reduceDIte,List.length_cons]
        have hx : chi (a.val i) ≤ 1 := by cases a.val i <;> decide
        omega
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hri.symm
        · exact ht q hq
  have accounting (m : Nat) (F : Fin m → Source) (hpos : ∀ i, Positive (F i))
      (S : Finset (Fin m)) (r : Recipe F S) (i : Fin m) (hi : i ∈ S) :
      terminal (recipeStrategy hpos r) (F i) = controllerOutcome (recipeController r) (F i) ∧
      ((routeTrace r i).map (fun q => vector F q.1)).Nodup ∧
      ((routeTrace r i).map Sigma.fst).Nodup ∧
      (routeTrace r i).length ≤ S.card - 1 ∧
      gain r i = ((routeTrace r i).map (fun q => chi q.2)).sum ∧
      (paid (routeTrace r i) \ (leaves (F i)).toFinset).card = gain r i ∧
      cost (recipeStrategy hpos r) (F i) = (leaves (F i)).length + gain r i := by
    let p := recipeStrategy hpos r
    have hterminal := Classical.choose_spec (Classical.choose_spec (p.correct (F i)))
    change execute readout p.policy (Classical.choose (p.correct (F i))) [] (F i) =
      some (terminal p (F i)) ∧ _ at hterminal
    have he := source_foundation.2.2.2.2.2.2.2 p.policy _ _ [] (F i) _ _ hterminal.1
      (show execute readout p.policy ((controllerOutcome (recipeController r) (F i)).1.length+1)
        [] (F i) = some (controllerOutcome (recipeController r) (F i)) from
          phase_foundation.1 (recipeController r) (F i))
    obtain ⟨hn,hd,hl,hg,hb,ht⟩ := path m F S r i hi
    have hnq : ((routeTrace r i).map Sigma.fst).Nodup :=
      List.Nodup.of_map (vector F) (by simpa only [List.map_map,Function.comp_def] using hn)
    have count : ∀ qs : List Address, qs.Nodup →
        (qs.toFinset \ (leaves (F i)).toFinset).card =
          (qs.map (fun q => chi (readout q (F i)))).sum := by
      intro qs hqs
      induction qs with
      | nil => simp
      | cons q qs ih =>
        obtain ⟨hnot,hnqs⟩ := List.nodup_cons.mp hqs
        by_cases hleaf : q ∈ leaves (F i)
        · simp [Finset.insert_sdiff_of_mem,hleaf,ih hnqs,leafFacts]
        · have hneq : q ∉ qs.toFinset \ (leaves (F i)).toFinset := by simp [hnot]
          simp [Finset.insert_sdiff_of_notMem,hleaf,hneq,ih hnqs,leafFacts, Nat.add_comm]
    have hcount := count ((routeTrace r i).map Sigma.fst) hnq
    have hmap : ((routeTrace r i).map (fun q => chi (readout q.1 (F i)))) =
        ((routeTrace r i).map (fun q => chi q.2)) := by
      apply List.map_congr_left
      intro q hq
      rw [ht q hq]
    simp only [List.map_map,Function.comp_def] at hcount
    rw [hmap,← hg] at hcount
    change (paid (routeTrace r i) \ (leaves (F i)).toFinset).card = gain r i at hcount
    refine ⟨he,hn,hnq,hl,hg,hcount,?_⟩
    have hp := (phase_foundation.2.2.2.2 m F S r i hi).2
    change (paid (terminal p (F i)).1).card = _
    rw [he,hp,← Finset.card_sdiff_add_card]
    rw [hcount, List.toFinset_card_of_nodup (leafFacts (F i)).1]
    omega
  refine ⟨leafFacts,accounting,?_⟩
  intro m F v hv i
  obtain ⟨r,hr⟩ := hv
  have hp := path m F Finset.univ r i (Finset.mem_univ i)
  have hb : gain r i ≤ m - 1 := by
    have hh := hp.2.2.1
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    exact hp.2.2.2.2.1.trans hh
  rw [hr i]
  constructor
  · omega
  · have hm : 0 < m := i.isLt |> Nat.zero_lt_of_lt
    omega

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Pruned candidates)

private theorem normalization_foundation (m : Nat) (hm : 0 < m) (F : Fin m → Source)
    (hpos : ∀ i, Positive (F i)) (hinj : Function.Injective F) (pi : Strategy) :
    ∃ (Q : Finset Address) (p : PassiveProtocol Q (fun _ => Reply)),
      Pruned (fun q i => readout q.val (F i)) Finset.univ p ∧
      ∀ i : Fin m,
        ((runPassiveProtocol (fun q i => readout q.val (F i)) p i).map
          (fun a => (⟨a.1.val,a.2⟩ : Sigma (fun _ : Address => Reply)))).Sublist
            (terminal pi (F i)).1 ∧
        candidates (fun q i => readout q.val (F i)) Finset.univ
          (runPassiveProtocol (fun q i => readout q.val (F i)) p i) = {i} ∧
        (runPassiveProtocol (fun q i => readout q.val (F i)) p i).length ≤ m - 1 := by
  classical
  let Q : Finset Address := Finset.univ.biUnion (fun i : Fin m => paid (terminal pi (F i)).1)
  let forget : Hist (fun _ : Q => Reply) → Hist (fun _ : Address => Reply) :=
    List.map (fun a => ⟨a.1.val,a.2⟩)
  let lift : Hist (fun _ : Address => Reply) → Hist (fun _ : Q => Reply) :=
    List.filterMap (fun a => if hq : a.1 ∈ Q then
      some (⟨⟨a.1,hq⟩,a.2⟩ : Sigma (fun _ : Q => Reply)) else none)
  let policy : Hist (fun _ : Q => Reply) → Sum Q Unit := fun h =>
    match pi.policy (forget h) with
    | .inr _ => .inr ()
    | .inl q => if hq : q ∈ Q then .inl ⟨q,hq⟩ else .inr ()
  let read : Q → Fin m → Reply := fun q i => readout q.val (F i)
  have inQ (i : Fin m) : ∀ a ∈ (terminal pi (F i)).1, a.1 ∈ Q := by
    intro a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ i,?_⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have roundtrip : ∀ t : Hist (fun _ : Address => Reply),
      (∀ a ∈ t, a.1 ∈ Q) → forget (lift t) = t := by
    intro t
    induction t with
    | nil => intro _; rfl
    | cons a t ih =>
      intro ht
      have hq := ht a (List.mem_cons_self ..)
      have htail := ih (fun b hb => ht b (List.mem_cons_of_mem _ hb))
      simp only [lift,List.filterMap_cons,hq,↓reduceDIte,forget,List.map_cons]
      exact congrArg (a :: ·) htail
  have restriction : ∀ n h (hq : Hist (fun _ : Q => Reply)) i t b,
      forget hq = h → execute readout pi.policy n h (F i) = some (t,b) →
      (∀ a ∈ t, a.1 ∈ Q) → execute read policy n hq i = some (lift t,()) := by
    intro n
    induction n with
    | zero => intro h hq i t b _ he _; simp [execute] at he
    | succ n ih =>
      intro h hq i t b hh he hQ
      cases hp : pi.policy h with
      | inr c =>
        simp only [execute,hp,Option.some.injEq,Prod.mk.injEq] at he
        obtain ⟨rfl,rfl⟩ := he
        simp [execute,policy,hh,hp,lift]
      | inl q =>
        simp only [execute,hp,Option.map_eq_some_iff] at he
        obtain ⟨⟨s,c⟩,hs,he⟩ := he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl,rfl⟩ := he
        have hqQ := hQ ⟨q,readout q (F i)⟩ (List.mem_cons_self ..)
        have htQ : ∀ a ∈ s, a.1 ∈ Q := fun a ha => hQ a (List.mem_cons_of_mem _ ha)
        have hstep := ih (h ++ [⟨q,readout q (F i)⟩])
          (hq ++ [⟨⟨q,hqQ⟩,readout q (F i)⟩]) i s c
          (by simp [forget,hh]) hs htQ
        simp only [execute,policy,hh,hp,hqQ,↓reduceDIte]
        change (execute read policy n (hq ++ [⟨⟨q,hqQ⟩,readout q (F i)⟩]) i).map
          (fun z => (⟨⟨q,hqQ⟩,readout q (F i)⟩ :: z.1,z.2)) = _
        rw [hstep]
        simp [lift,hqQ]
  have original (i : Fin m) :
      execute readout pi.policy (Classical.choose (pi.correct (F i))) [] (F i) =
        some (terminal pi (F i)) :=
    (Classical.choose_spec (Classical.choose_spec (pi.correct (F i)))).1
  let tr : Fin m → Hist (fun _ : Q => Reply) := fun i => lift (terminal pi (F i)).1
  have runs (i : Fin m) : execute read policy (Classical.choose (pi.correct (F i))) [] i =
      some (tr i,()) := restriction _ [] [] i _ _ rfl (original i) (inQ i)
  have truthful : ∀ (n : Nat) (h : Hist (fun _ : Address => Reply)) U t b,
      execute readout pi.policy n h U = some (t,b) →
      ∀ a ∈ t, readout a.1 U = a.2 := by
    intro n
    induction n with
    | zero => intro h U t b he; simp [execute] at he
    | succ n ih =>
      intro h U t b he
      cases hp : pi.policy h with
      | inr c =>
        simp only [execute,hp,Option.some.injEq,Prod.mk.injEq] at he
        obtain ⟨rfl,rfl⟩ := he
        simp
      | inl q =>
        simp only [execute,hp,Option.map_eq_some_iff] at he
        obtain ⟨⟨s,c⟩,hs,he⟩ := he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl,rfl⟩ := he
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · exact ih _ U s c hs a ha
  have fibers (i : Fin m) : candidates read Finset.univ (tr i) = {i} := by
    ext j
    simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hj
      have matched : ∀ a ∈ (terminal pi (F i)).1, readout a.1 (F j) = a.2 := by
        intro a ha
        have hr := roundtrip _ (inQ i)
        rw [← hr] at ha
        obtain ⟨b,hb,he⟩ := List.mem_map.mp ha
        subst a
        exact hj b hb
      have he : F j = F i := source_foundation.2.2.1 (F i) (F j) (by
        intro u hu
        have hpaid := source_foundation.2.2.2.2.1 pi (F i) (hpos i)
        have hum := hpaid (List.mem_toFinset.mpr hu)
        obtain ⟨a,ha,hau⟩ := List.mem_map.mp (List.mem_toFinset.mp hum)
        rw [← hau]
        exact (matched a ha).trans (truthful _ [] _ _ _ (original i) a ha).symm)
      exact hinj he
    · intro he
      subst j
      intro a ha
      have hr := roundtrip _ (inQ i)
      have ham : (⟨a.1.val,a.2⟩ : Sigma (fun _ : Address => Reply)) ∈ (terminal pi (F i)).1 := by
        rw [← hr]
        exact List.mem_map.mpr ⟨a,ha,rfl⟩
      exact truthful _ [] _ _ _ (original i) _ ham
  let B := Finset.univ.sup (fun i : Fin m => (tr i).length)
  have hC : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0,hm⟩,Finset.mem_univ _⟩
  have feasible : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∃ n t l,
      execute read policy n [] i = some (t,l) ∧ True ∧
        (t.map (fun _ => (1 : Nat))).sum + 0 ≤ B := by
    intro i _
    refine ⟨_,tr i,(),runs i,True.intro,?_⟩
    simpa using Finset.le_sup (f := fun i : Fin m => (tr i).length) (Finset.mem_univ i)
  have supply := D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.result
    (Z := ℝ) read (fun _ => 1) (fun _ (_ : Unit) => True) (fun _ _ => 0)
    (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) Finset.univ hC B
    ⟨(),True.intro,rfl⟩ (fun _ _ => ⟨(),True.intro,rfl⟩)
  obtain ⟨p,d,hp,hpaths,_⟩ := supply.1 policy feasible
  refine ⟨Q,p,hp,?_⟩
  intro i
  have hh := hpaths i (Finset.mem_univ i) _ (tr i) () (runs i)
  refine ⟨?_, hh.2.2.2.2.1.trans (fibers i), ?_⟩
  · have hs := hh.2.2.1.map (fun a => (⟨a.1.val,a.2⟩ : Sigma (fun _ : Address => Reply)))
    change (forget (runPassiveProtocol read p i)).Sublist (forget (tr i)) at hs
    rw [show forget (tr i) = (terminal pi (F i)).1 from roundtrip _ (inQ i)] at hs
    exact hs
  · simpa only [Finset.card_univ,Fintype.card_fin] using hh.2.2.2.1

/-- The complete finite cost core on distinct actual positive prototypes. -/
theorem result (m : Nat) (hm : 0 < m) (F : Fin m → Source)
    (hpos : ∀ i, Positive (F i)) (hinj : Function.Injective F) :
    (core F).Finite ∧ (core F).Nonempty ∧
    (∀ v ∈ core F, ∃ (r : Recipe F Finset.univ) (sigma : Strategy),
      sigma = recipeStrategy hpos r ∧ ∀ i,
        cost sigma (F i) = v i ∧
        paid (terminal sigma (F i)).1 = paid (routeTrace r i) ∪ (leaves (F i)).toFinset ∧
        ((routeTrace r i).map (fun q => vector F q.1)).Nodup ∧
        ((routeTrace r i).map Sigma.fst).Nodup ∧
        (routeTrace r i).length ≤ m - 1 ∧
        (paid (routeTrace r i) \ (leaves (F i)).toFinset).card =
          ((routeTrace r i).map (fun q => chi q.2)).sum ∧
        (Finset.sum (paid (routeTrace r i)) (fun u => chi (readout u (F i)))) =
          (paid (routeTrace r i) \ (leaves (F i)).toFinset).card ∧
        cost sigma (F i) = (leaves (F i)).length +
          (paid (routeTrace r i) \ (leaves (F i)).toFinset).card) ∧
    (∀ pi : Strategy, ∃ v ∈ core F, ∀ i, v i ≤ cost pi (F i)) ∧
    core F ⊆ {v | ∀ i, (leaves (F i)).length ≤ v i ∧
      v i ≤ (leaves (F i)).length + m - 1} := by
  classical
  have realized (a : actualVectors F) : vector F (representative F a) = a.val :=
    (List.Shortlex.wf (InvImage.wf Bool.toNat Nat.lt_wfRel.wf)).min_mem
      {u | vector F u = a.val} a.property
  have convert (Q : Finset Address) :
      ∀ (p : PassiveProtocol Q (fun _ => Reply)) (S : Finset (Fin m)), S.Nonempty →
        Pruned (fun q i => readout q.val (F i)) S p →
        (∀ i ∈ S, candidates (fun q i => readout q.val (F i)) S
          (runPassiveProtocol (fun q i => readout q.val (F i)) p i) = {i}) →
        ∃ r : Recipe F S, ∀ i ∈ S,
          gain r i = ((runPassiveProtocol (fun q i => readout q.val (F i)) p i).map
            (fun q => chi q.2)).sum ∧
          (routeTrace r i).map (fun q => vector F q.1) =
            (runPassiveProtocol (fun q i => readout q.val (F i)) p i).map
              (fun q => vector F q.1.val) := by
    intro p
    induction p with
    | stop =>
      intro S hS _ hsingle
      obtain ⟨i,hi⟩ := hS
      have he : S = {i} := by simpa [candidates,runPassiveProtocol] using hsingle i hi
      subst S
      refine ⟨.singleton i,?_⟩
      intro j hj
      simp [gain,routeTrace,runPassiveProtocol]
    | query q next ih =>
      intro S hS hp hsingle
      let a : actualVectors F := ⟨vector F q.val,⟨q.val,rfl⟩⟩
      have hsplit : 2 ≤ (S.image a.val).card := by
        by_contra hn
        have hc : (S.image a.val).card ≤ 1 := by omega
        obtain ⟨i,hi⟩ := hS
        have he : D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.fiber
            (fun q i => readout q.val (F i)) S q (readout q.val (F i)) = S := by
          ext j
          simp only [D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.fiber,
            Finset.mem_filter,and_iff_left_iff_imp]
          intro hj
          exact Finset.card_le_one.mp hc (a.val j) (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
            (a.val i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
        have hh := hp.1 (readout q.val (F i))
        rw [he] at hh
        omega
      have children : ∀ y (hy : (survivors S a.val y).Nonempty),
          ∃ r : Recipe F (survivors S a.val y), ∀ i ∈ survivors S a.val y,
            gain r i = ((runPassiveProtocol (fun q i => readout q.val (F i)) (next y) i).map
              (fun q => chi q.2)).sum ∧
            (routeTrace r i).map (fun q => vector F q.1) =
              (runPassiveProtocol (fun q i => readout q.val (F i)) (next y) i).map
                (fun q => vector F q.1.val) := by
        intro y hy
        have hchildset : survivors S a.val y =
            D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.fiber
              (fun q i => readout q.val (F i)) S q y := by
          unfold survivors D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.fiber
          exact @Finset.filter_congr_decidable (Fin m) S
            (fun i => readout q.val (F i) = y)
            (fun i => instDecidableEqReply (readout q.val (F i)) y)
            (fun i => Classical.propDecidable _)
        apply ih y (survivors S a.val y) hy
        · rw [hchildset]; exact hp.2 y
        · intro i hi
          have hiy : readout q.val (F i) = y := (Finset.mem_filter.mp hi).2
          have hc : candidates (fun q i => readout q.val (F i)) (survivors S a.val y)
              (runPassiveProtocol (fun q i => readout q.val (F i)) (next y) i) =
            candidates (fun q i => readout q.val (F i)) S
              (runPassiveProtocol (fun q i => readout q.val (F i)) (.query q next) i) := by
            rw [hchildset]
            ext j
            simp [candidates,runPassiveProtocol,hiy,
              D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.fiber,and_assoc]
          exact hc.trans (hsingle i (Finset.mem_filter.mp hi).1)
      choose child hchild using children
      refine ⟨.split S a hsplit child,?_⟩
      intro i hi
      have hy : (survivors S a.val (a.val i)).Nonempty := ⟨i,by simp [survivors,hi]⟩
      obtain ⟨hg,hv⟩ := hchild (a.val i) hy i (by simp [survivors,hi])
      constructor
      · simpa [gain,hi,runPassiveProtocol,a,vector] using congrArg (chi (a.val i) + ·) hg
      · simpa [routeTrace,hi,runPassiveProtocol,realized,a,vector] using
          congrArg ((a.val) :: ·) hv
  have dominate (pi : Strategy) : ∃ r : Recipe F Finset.univ,
      ∀ i, (leaves (F i)).length + gain r i ≤ cost pi (F i) := by
    obtain ⟨Q,p,hp,hpaths⟩ := normalization_foundation m hm F hpos hinj pi
    obtain ⟨r,hr⟩ := convert Q p Finset.univ ⟨⟨0,hm⟩,Finset.mem_univ _⟩ hp
      (fun i _ => (hpaths i).2.1)
    refine ⟨r,?_⟩
    intro i
    let t := runPassiveProtocol (fun q i => readout q.val (F i)) p i
    let qs := t.map (fun q => q.1.val)
    have routeFacts := cost_foundation.2.1 m F hpos Finset.univ r i (Finset.mem_univ _)
    have hv := (hr i (Finset.mem_univ _)).2
    have hv' : (routeTrace r i).map (fun q => vector F q.1) =
        t.map (fun q => vector F q.1.val) := hv
    have hnv : (t.map (fun q => vector F q.1.val)).Nodup := hv' ▸ routeFacts.2.1
    have hn : qs.Nodup := List.Nodup.of_map (vector F) (by
      simpa only [qs,List.map_map,Function.comp_def] using hnv)
    have hsub : qs.toFinset ⊆ paid (terminal pi (F i)).1 := by
      intro u hu
      obtain ⟨a,ha,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
      subst u
      have ha' := (hpaths i).1.subset (List.mem_map.mpr ⟨a,ha,rfl⟩)
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,ha',rfl⟩)
    have truth : ∀ (p : PassiveProtocol Q (fun _ => Reply)), ∀ a ∈
        runPassiveProtocol (fun q i => readout q.val (F i)) p i, readout a.1.val (F i) = a.2 := by
      intro p
      induction p with
      | stop => simp [runPassiveProtocol]
      | query q next ih =>
        intro a ha
        simp only [runPassiveProtocol,List.mem_cons] at ha
        rcases ha with rfl | ha
        · rfl
        · exact ih _ a ha
    have count : ∀ us : List Address, us.Nodup →
        (us.toFinset \ (leaves (F i)).toFinset).card =
          (us.map (fun q => chi (readout q (F i)))).sum := by
      intro us hus
      induction us with
      | nil => simp
      | cons u us ih =>
        obtain ⟨hne,hnd⟩ := List.nodup_cons.mp hus
        have hf := (cost_foundation.1 (F i)).2
        by_cases hl : u ∈ leaves (F i)
        · simp [Finset.insert_sdiff_of_mem,hl,ih hnd,hf]
        · have hx : u ∉ us.toFinset \ (leaves (F i)).toFinset := by simp [hne]
          simp [Finset.insert_sdiff_of_notMem,hl,hx,ih hnd,hf,Nat.add_comm]
    have hc := count qs hn
    have he : gain r i = (qs.toFinset \ (leaves (F i)).toFinset).card := by
      rw [(hr i (Finset.mem_univ _)).1,hc]
      simp only [qs,List.map_map,Function.comp_def]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      rw [truth p a ha]
    have hle := Finset.card_le_card (show qs.toFinset \ (leaves (F i)).toFinset ⊆
        paid (terminal pi (F i)).1 \ (leaves (F i)).toFinset from
      fun u hu => Finset.mem_sdiff.mpr
        ⟨hsub (Finset.mem_sdiff.mp hu).1,(Finset.mem_sdiff.mp hu).2⟩)
    have hbase := source_foundation.2.2.2.2.1 pi (F i) (hpos i)
    have htotal := Finset.card_sdiff_add_card_eq_card hbase
    have hleaf := List.toFinset_card_of_nodup (cost_foundation.1 (F i)).1
    rw [he]
    change _ ≤ (paid (terminal pi (F i)).1).card
    omega
  have bounds := cost_foundation.2.2 m F
  have finiteCore : (core F).Finite := by
    have box : {v : Fin m → Nat | ∀ i,
        v i ∈ Set.Icc (leaves (F i)).length ((leaves (F i)).length + m - 1)}.Finite :=
      Set.Finite.pi' (fun i => Set.finite_Icc _ _)
    exact box.subset bounds
  obtain ⟨r0,_⟩ := dominate fallback
  have nonemptyCore : (core F).Nonempty :=
    ⟨fun i => (leaves (F i)).length + gain r0 i, r0,fun _ => rfl⟩
  refine ⟨finiteCore,nonemptyCore,?_,?_,bounds⟩
  · intro v hv
    obtain ⟨r,hr⟩ := hv
    refine ⟨r,recipeStrategy hpos r,rfl,?_⟩
    intro i
    obtain ⟨he,hn,hnq,hl,hg,hcount,hcost⟩ :=
      cost_foundation.2.1 m F hpos Finset.univ r i (Finset.mem_univ _)
    have hp := (phase_foundation.2.2.2.2 m F Finset.univ r i (Finset.mem_univ _)).2
    have finsetCount : ∀ us : List Address, us.Nodup →
        (Finset.sum us.toFinset (fun u => chi (readout u (F i)))) =
          (us.toFinset \ (leaves (F i)).toFinset).card := by
      intro us hus
      induction us with
      | nil => simp
      | cons u us ih =>
        obtain ⟨hne,hnd⟩ := List.nodup_cons.mp hus
        by_cases hl' : u ∈ leaves (F i)
        · have hneFin : u ∉ us.toFinset := by simpa using hne
          have hlFin : u ∈ (leaves (F i)).toFinset := by simpa using hl'
          rw [List.toFinset_cons, Finset.sum_insert hneFin]
          rw [Finset.insert_sdiff_of_mem us.toFinset hlFin]
          simp [ih hnd, (cost_foundation.1 (F i)).2 u, hl']
        · have hneFin : u ∉ us.toFinset := by simpa using hne
          have hlFin : u ∉ (leaves (F i)).toFinset := by simpa using hl'
          rw [List.toFinset_cons, Finset.sum_insert hneFin]
          rw [Finset.insert_sdiff_of_notMem us.toFinset hlFin]
          have hdiff : u ∉ us.toFinset \ (leaves (F i)).toFinset := by
            simp [hne]
          rw [Finset.card_insert_of_notMem hdiff]
          simpa [ih hnd, (cost_foundation.1 (F i)).2 u, hl', Nat.add_comm]
    have hsum : (Finset.sum (paid (routeTrace r i)) (fun u => chi (readout u (F i)))) =
        (paid (routeTrace r i) \ (leaves (F i)).toFinset).card :=
      finsetCount ((routeTrace r i).map Sigma.fst) hnq
    refine ⟨hcost.trans (hr i).symm,?_,hn,hnq,?_,?_,?_,?_⟩
    · rw [he]; exact hp
    · simpa only [Finset.card_univ,Fintype.card_fin] using hl
    · exact hcount.trans hg
    · exact hsum
    · rw [hcost,hcount]
  · intro pi
    obtain ⟨r,hr⟩ := dominate pi
    exact ⟨fun i => (leaves (F i)).length + gain r i,⟨r,fun _ => rfl⟩,hr⟩


end D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore

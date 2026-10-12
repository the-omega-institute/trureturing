/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original controller chronological horizon and literal support. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy terminal readout leaves
  acquisitionTrace nodes)
open ActualFiniteObserverAbsentElimination (Allowed Q_N)
open ActualObserverAbsorbingNormalization (allowedSources allowedSources_exact)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualCoarseReadoutCompletion (encodeHistory compileRaw)
open ActualJointResponseCostCore (Controller controllerPolicy controllerOutcome
  verifyController phase_foundation)
open ActualExactTraceCompiler (ExactState strategyPrefixes strategy_state_card_bound)
open ActualObserverFiniteTable (BoundedAddress)
open ActualPureAcquisitionCompiler (trace_addresses nodes_length)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (execute)

abbrev CoarseHistory := List (Sigma (fun _ : Address => Option Bool))

/-- The longest syntactic query branch of a passive route. -/
def routeHorizon : PassiveProtocol Address (fun _ => Option Bool) → Nat
  | .stop => 0
  | .query _ next =>
      1 + max (routeHorizon (next none))
        (max (routeHorizon (next (some false))) (routeHorizon (next (some true))))

/-- Every literal query occurring in a passive route, across all branches. -/
def routeSupport : PassiveProtocol Address (fun _ => Option Bool) → Finset Address
  | .stop => ∅
  | .query q next =>
      insert q (routeSupport (next none) ∪
        (routeSupport (next (some false)) ∪ routeSupport (next (some true))))

/-- The largest prototype leaf count, with the empty family maximum equal to zero. -/
noncomputable def prototypeMax {m : Nat} (F : Fin m → Source) : Nat :=
  Finset.univ.sup (fun i => (F i).length)

/-- The union of all literal prototype leaf addresses. -/
noncomputable def prototypeLeaves {m : Nat} (F : Fin m → Source) : Finset Address :=
  Finset.univ.biUnion (fun i => (leaves (F i)).toFinset)

/-- The bounded literal alphabet from the source-domain contract. -/
noncomputable def qNFinset (N : Nat) : Finset Address :=
  (Finset.univ : Finset (BoundedAddress N)).image Subtype.val

private theorem mem_qNFinset {N : Nat} {q : Address} :
    q ∈ qNFinset N ↔ q.length ≤ N - 1 := by
  classical
  constructor
  · intro h
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
    exact a.property
  · intro h
    refine Finset.mem_image.mpr ⟨⟨q, h⟩, Finset.mem_univ _, rfl⟩

private theorem nodes_count (U : Source) : (nodes U).length = 2 * U.length - 1 := by
  induction U with
  | of b => cases b <;> decide
  | mul s t hs ht =>
      simp only [nodes, List.length_cons, List.length_append, List.length_map,
        FreeMagma.length] at *
      have hspos := s.length_pos
      have htpos := t.length_pos
      omega

private theorem acquisition_length (N : Nat) (U : Source) (allowed : Allowed N U)
    (positive : 1 ≤ N) : (acquisitionTrace [] U).length ≤ 2 * N - 1 := by
  have htrace := congrArg List.length (trace_addresses U [])
  simp only [List.length_map, nodes_count] at htrace
  have hlen := U.length_pos
  change U.length ≤ N at allowed
  rw [htrace]
  omega

private theorem acquisition_support (N : Nat) (U : Source) (allowed : Allowed N U) :
    ∀ a ∈ acquisitionTrace [] U, a.1 ∈ qNFinset N := by
  intro a ha
  have mapped := trace_addresses U []
  simp only [List.nil_append, List.map_id'] at mapped
  have hq : a.1 ∈ nodes U := by
    rw [← mapped]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  exact mem_qNFinset.mpr (by
    have hq' := nodes_length U a.1 hq
    change U.length ≤ N at allowed
    omega)

private theorem verifier_bound (V U : Source) (qs : List Address) :
    (controllerOutcome (verifyController V qs) U).1.length ≤
      qs.length + (acquisitionTrace [] U).length := by
  induction qs with
  | nil => simp [verifyController, controllerOutcome]
  | cons q qs ih =>
      by_cases h : readout q U = readout q V
      · simp only [verifyController, controllerOutcome, h, ↓reduceIte,
          List.length_cons]
        omega
      · simp only [verifyController, controllerOutcome, h, ↓reduceIte,
          List.length_cons]
        omega

private theorem verifier_support (V U : Source) (qs : List Address) :
    ∀ a ∈ (controllerOutcome (verifyController V qs) U).1,
      a.1 ∈ qs.toFinset ∪ (nodes U).toFinset := by
  induction qs with
  | nil => simp [verifyController, controllerOutcome]
  | cons q qs ih =>
      intro a ha
      by_cases h : readout q U = readout q V
      · simp only [verifyController, controllerOutcome, h, ↓reduceIte,
          List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr
            List.mem_cons_self))
        · have tail := ih a ha
          rcases Finset.mem_union.mp tail with hq | hn
          · exact Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr
              (List.mem_cons_of_mem q (List.mem_toFinset.mp hq))))
          · exact Finset.mem_union.mpr (Or.inr hn)
      · simp only [verifyController, controllerOutcome, h, ↓reduceIte,
          List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr
            List.mem_cons_self))
        · have mapped := trace_addresses U []
          simp only [List.nil_append, List.map_id'] at mapped
          have hn : a.1 ∈ nodes U := by
            rw [← mapped]
            exact List.mem_map.mpr ⟨a, ha, rfl⟩
          exact Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hn))

private theorem prototype_max_bound {m : Nat} (F : Fin m → Source) (i : Fin m) :
    (leaves (F i)).length ≤ prototypeMax F :=
  by
    have count : (leaves (F i)).length = (F i).length := by
      rw [← List.toFinset_card_of_nodup
        (ActualJointResponseCostCore.cost_foundation.1 (F i)).1]
      exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).1
    rw [count]
    unfold prototypeMax
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin m)))
      (f := fun j : Fin m => (F j).length) (Finset.mem_univ i)

private theorem prototype_leaf_mem {m : Nat} (F : Fin m → Source) (i : Fin m)
    {q : Address} (h : q ∈ leaves (F i)) : q ∈ prototypeLeaves F := by
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr h⟩

private theorem compiled_bound {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool))
    (g : CoarseHistory) (N : Nat) (U : Source) (allowed : Allowed N U)
    (positive : 1 ≤ N) :
    (controllerOutcome (compileRaw F decode p g) U).1.length ≤
      routeHorizon p + prototypeMax F + (2 * N - 1) := by
  induction p generalizing g with
  | stop =>
      cases h : decode g with
      | none =>
          have ha := acquisition_length N U allowed positive
          simp only [compileRaw, h, controllerOutcome, List.length_nil,
            routeHorizon, Nat.zero_add]
          omega
      | some i =>
          simp only [compileRaw, h, routeHorizon]
          have hv := verifier_bound (F i) U (leaves (F i))
          have hm := prototype_max_bound F i
          have ha := acquisition_length N U allowed positive
          omega
  | query q next ih =>
      have child := ih (kappa (readout q U)) (g ++ [⟨q, kappa (readout q U)⟩])
      simp only [compileRaw, controllerOutcome, List.length_cons, routeHorizon] at child ⊢
      have hr : routeHorizon (next (kappa (readout q U))) ≤
          max (routeHorizon (next none))
            (max (routeHorizon (next (some false))) (routeHorizon (next (some true)))) := by
        cases h : kappa (readout q U) with
        | none => simp [h]
        | some b => cases b <;> simp [h]
      omega

private theorem compiled_support {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool))
    (g : CoarseHistory) (N : Nat) (U : Source) (allowed : Allowed N U) :
    ∀ a ∈ (controllerOutcome (compileRaw F decode p g) U).1,
      a.1 ∈ qNFinset N ∪ routeSupport p ∪ prototypeLeaves F := by
  induction p generalizing g with
  | stop =>
      cases h : decode g with
      | none =>
          intro a ha
          simp only [compileRaw, h, controllerOutcome] at ha
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (acquisition_support N U allowed a ha))))
      | some i =>
          intro a ha
          simp only [compileRaw, h] at ha
          have hs := verifier_support (F i) U (leaves (F i)) a ha
          rcases Finset.mem_union.mp hs with hs | hs
          · exact Finset.mem_union.mpr (Or.inr (prototype_leaf_mem F i
              (List.mem_toFinset.mp hs)))
          · rw [Finset.mem_union]
            exact Or.inl (Finset.mem_union.mpr (Or.inl (by
              have hn : a.1 ∈ (nodes U).toFinset := hs
              apply mem_qNFinset.mpr
              have hlen := nodes_length U a.1 (List.mem_toFinset.mp hn)
              change U.length ≤ N at allowed
              omega)))
  | query q next ih =>
      intro a ha
      simp only [compileRaw, controllerOutcome, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (by simp [routeSupport]))))
      · have child := ih (kappa (readout q U))
          (g ++ [⟨q, kappa (readout q U)⟩]) a ha
        have childSupport : a.1 ∈ qNFinset N ∪ routeSupport (next (kappa (readout q U))) ∪
            prototypeLeaves F := child
        rcases Finset.mem_union.mp childSupport with hs | hp
        · rcases Finset.mem_union.mp hs with hq | hr
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hq)))
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
              (Or.inr (by
                simp only [routeSupport, Finset.mem_insert, Finset.mem_union]
                cases hk : kappa (readout q U) with
                | none =>
                    rw [hk] at hr
                    exact Or.inr (Or.inl hr)
                | some b =>
                    rw [hk] at hr
                    cases b with
                    | false => exact Or.inr (Or.inr (Or.inl hr))
                    | true => exact Or.inr (Or.inr (Or.inr hr))))))
        · exact Finset.mem_union.mpr (Or.inr hp)

private theorem policy_transfer (raw cooked : ActualTreeReadoutAcquisition.Policy)
    (U : Source) : ∀ (n : Nat) (h t : List (Sigma (fun _ : Address => Reply))) (b : Bool),
      execute readout raw n h U = some (t,b) →
      (∀ g, g.IsPrefix t → cooked (h ++ g) = raw (h ++ g)) →
      execute readout cooked n h U = some (t,b) := by
  intro n
  induction n with
  | zero => intro h t b hr _; simp [execute] at hr
  | succ n ih =>
      intro h t b hr agree
      have start := agree [] List.nil_prefix
      simp only [List.append_nil] at start
      rw [execute, start]
      cases step : raw h with
      | inr z => simpa [execute, step] using hr
      | inl q =>
          simp only [execute, step, Option.map_eq_some_iff] at hr
          obtain ⟨⟨t', b'⟩, hr, e⟩ := hr
          cases e
          change (execute readout cooked n
            (h ++ [⟨q, readout q U⟩]) U).map
              (fun z => (⟨q, readout q U⟩ :: z.1, z.2)) = _
          have restAgreement : ∀ g, g.IsPrefix t' →
              cooked ((h ++ [⟨q, readout q U⟩]) ++ g) =
                raw ((h ++ [⟨q, readout q U⟩]) ++ g) := by
            intro g hp
            simpa only [List.append_assoc, List.singleton_append] using
              agree (⟨q, readout q U⟩ :: g)
                (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
          exact congrArg (Option.map (fun z => (⟨q, readout q U⟩ :: z.1, z.2)))
            (ih (h ++ [⟨q, readout q U⟩]) t' b' hr restAgreement)

private theorem normalized_compile_run {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (U : Source) :
    ∃ n, execute readout
      (fun h => controllerPolicy (compileRaw F decode p [])
        (encodeHistory (kappa_hist h))) n [] U =
      some (controllerOutcome (compileRaw F decode p []) U) := by
  let norm : List (Sigma (fun _ : Address => Reply)) →
      List (Sigma (fun _ : Address => Reply)) := fun h => encodeHistory (kappa_hist h)
  let policy : ActualTreeReadoutAcquisition.Policy := fun h =>
    controllerPolicy (compileRaw F decode p []) (norm h)
  let repr : Reply → Reply := fun y =>
    match kappa y with
    | some true => .alpha
    | some false => .beta
    | none => .branch
  have norm_map (h : List (Sigma (fun _ : Address => Reply))) :
      norm h = h.map (fun a => (⟨a.1, repr a.2⟩ : Sigma (fun _ : Address => Reply))) := by
    simp only [norm, encodeHistory, kappa_hist, List.map_map, Function.comp_def, repr]
    rfl
  have repr_coarse (y : Reply) : kappa (repr y) = kappa y := by cases y <;> rfl
  have leaf_reply (V : Source) (q : Address) (hq : q ∈ leaves V) :
      readout q V = .alpha ∨ readout q V = .beta := by
    obtain ⟨b, hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 V).2 q |>.mp
      (List.mem_toFinset.mpr hq)
    cases he : readout q V with
    | alpha => exact Or.inl rfl
    | beta => exact Or.inr rfl
    | branch => simp [ActualImageSevenLeafSeparation.leafLabel, he] at hb
    | absent => simp [ActualImageSevenLeafSeparation.leafLabel, he] at hb
  have norm_prefix (h : List (Sigma (fun _ : Address => Reply)))
      (hp : h.IsPrefix (acquisitionTrace [] U)) : norm h = h := by
    exact ActualCoarseReadoutCompletion.acquisition_prefix_representative U h hp
  have verify_prefix (V : Source) (qs : List Address) (onlyLeaves : ∀ q ∈ qs, q ∈ leaves V) :
      ∀ h, h.IsPrefix (controllerOutcome (verifyController V qs) U).1 →
        controllerPolicy (verifyController V qs) (norm h) =
          controllerPolicy (verifyController V qs) h := by
    induction qs with
    | nil => intro h _; rfl
    | cons q qs ih =>
        intro h hp
        have hl := leaf_reply V q (onlyLeaves q List.mem_cons_self)
        have eq_test (y : Reply) : repr y = readout q V ↔ y = readout q V := by
          rcases hl with hl | hl <;> cases y <;> simp [repr, kappa, hl]
        cases h with
        | nil => rfl
        | cons a h =>
            change (a :: h).IsPrefix (⟨q, readout q U⟩ :: _) at hp
            have head := (List.cons_prefix_cons.mp hp).1
            have tail := (List.cons_prefix_cons.mp hp).2
            subst a
            simp only [norm_map, List.map_cons, verifyController, controllerPolicy,
              ↓reduceIte, eq_test]
            by_cases he : readout q U = readout q V
            · simp only [he, ↓reduceIte] at tail ⊢
              rw [← norm_map h]
              exact ih (fun r hr => onlyLeaves r (List.mem_cons_of_mem q hr)) h tail
            · simp only [he, ↓reduceIte]
              have hacq : h.IsPrefix (acquisitionTrace [] U) := by
                simpa [controllerOutcome, he] using tail
              rw [← norm_map h]
              exact congrArg ActualTreeReadoutAcquisition.acquisitionPolicy
                (norm_prefix h hacq)
  have compile_prefix :
      ∀ (r : PassiveProtocol Address (fun _ => Option Bool)) (g : CoarseHistory),
      ∀ h, h.IsPrefix (controllerOutcome (compileRaw F decode r g) U).1 →
        controllerPolicy (compileRaw F decode r g) (norm h) =
          controllerPolicy (compileRaw F decode r g) h := by
    intro r
    induction r with
    | stop =>
        intro g h hp
        cases hd : decode g with
        | none =>
            simp only [compileRaw, hd, controllerOutcome, controllerPolicy]
            have hacq : h.IsPrefix (acquisitionTrace [] U) := by
              simpa [compileRaw, hd, controllerOutcome] using hp
            exact congrArg ActualTreeReadoutAcquisition.acquisitionPolicy
              (norm_prefix h hacq)
        | some i =>
            simp only [compileRaw, hd]
            have hv : h.IsPrefix
                (controllerOutcome (verifyController (F i) (leaves (F i))) U).1 := by
              simpa [compileRaw, hd] using hp
            exact verify_prefix (F i) (leaves (F i)) (fun q hq => hq) h hv
    | query q next ih =>
        intro g h hp
        cases h with
        | nil => rfl
        | cons a h =>
            change (a :: h).IsPrefix (⟨q, readout q U⟩ :: _) at hp
            have head := (List.cons_prefix_cons.mp hp).1
            have tail := (List.cons_prefix_cons.mp hp).2
            subst a
            simp only [norm_map, List.map_cons, compileRaw, controllerPolicy, ↓reduceIte,
              repr_coarse]
            rw [← norm_map h]
            exact ih (kappa (readout q U))
              (g ++ [⟨q, kappa (readout q U)⟩]) h tail
  have rawRun := phase_foundation.1 (compileRaw F decode p []) U
  have normRun :
      execute readout policy ((controllerOutcome (compileRaw F decode p []) U).1.length + 1) [] U =
        some (controllerOutcome (compileRaw F decode p []) U) := by
    exact policy_transfer (controllerPolicy (compileRaw F decode p [])) policy U _ [] _ _
      rawRun (fun h hp => compile_prefix p [] h hp)
  exact ⟨_, normRun⟩

private theorem terminal_eq_controllerOutcome {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (π : Strategy)
    (policy : π.policy = fun h => controllerPolicy (compileRaw F decode p [])
      (encodeHistory (kappa_hist h))) (U : Source) :
    terminal π U = controllerOutcome (compileRaw F decode p []) U := by
  obtain ⟨n, run⟩ := normalized_compile_run F decode p U
  have chosen := Classical.choose_spec (Classical.choose_spec (π.correct U))
  have normalized : execute readout π.policy n [] U =
      some (controllerOutcome (compileRaw F decode p []) U) := by
    simpa [policy] using run
  have unique := ActualTreeReadoutAcquisition.source_foundation.2.2.2.2.2.2.2
    π.policy _ n [] U (terminal π U) (controllerOutcome (compileRaw F decode p []) U)
    (by simpa [terminal] using chosen.1) normalized
  exact unique

theorem actual_completion_horizon {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (positive : 1 ≤ N)
    (policy : π.policy = fun h => controllerPolicy (compileRaw F decode p [])
      (encodeHistory (kappa_hist h))) :
    (∀ U : Source, terminal π U = controllerOutcome (compileRaw F decode p []) U) ∧
    (∀ U : Source, Allowed N U →
      (terminal π U).1.length ≤ routeHorizon p + prototypeMax F + (2 * N - 1) ∧
      (∀ a ∈ (terminal π U).1,
        a.1 ∈ qNFinset N ∪ routeSupport p ∪ prototypeLeaves F)) ∧
    Fintype.card (ExactState (strategyPrefixes N π)) ≤
      1 + (allowedSources N).card *
        (routeHorizon p + prototypeMax F + (2 * N - 1) + 1) *
        2 ^ min (qNFinset N ∪ routeSupport p ∪ prototypeLeaves F).card
          (routeHorizon p + prototypeMax F + (2 * N - 1)) := by
  refine ⟨terminal_eq_controllerOutcome F decode p π policy, ?_⟩
  constructor
  · intro U allowed
    rw [terminal_eq_controllerOutcome F decode p π policy U]
    exact ⟨compiled_bound F decode p [] N U allowed positive,
      compiled_support F decode p [] N U allowed⟩
  · apply strategy_state_card_bound N π
    · intro U allowed
      exact (terminal_eq_controllerOutcome F decode p π policy U) ▸
        compiled_bound F decode p [] N U allowed positive
    · intro U allowed a ha
      rw [terminal_eq_controllerOutcome F decode p π policy U] at ha
      exact compiled_support F decode p [] N U allowed a ha

end D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon

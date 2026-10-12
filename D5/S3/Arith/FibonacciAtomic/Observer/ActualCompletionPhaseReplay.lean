/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original coarse controller phases with local histories and verifier resets. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy readout leaves acquisitionPolicy)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualCoarseReadoutCompletion (encodeHistory compileRaw)
open ActualJointResponseCostCore (controllerPolicy verifyController)
open ActualImageSevenLeafSeparation (leafLabel seven_leaf_separation)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open ActualExactTraceCompiler
open ActualFiniteObserverAbsentElimination

/-- Only the current phase's local coarse history is observed. Verification
also records its selected prototype and remaining literal leaf requests. -/
inductive PhaseLabel (m : Nat)
  | route (suffix : CoarseHistory)
  | verify (selected : Fin m) (remaining : List Address) (suffix : CoarseHistory)
  | acquisition (suffix : CoarseHistory)
  | malformed
  deriving DecidableEq

private def coarseReply : Option Bool → Reply
  | some true => .alpha
  | some false => .beta
  | none => .branch

private noncomputable def acquisitionReadout {m : Nat} (g : CoarseHistory) :
    PhaseLabel m × Sum Address Bool :=
  (.acquisition g, acquisitionPolicy (encodeHistory g))

/-- Replay the original verifier on quotient representatives. Its first
mismatch starts acquisition on the unconsumed, fresh local suffix. -/
noncomputable def verifyPhase {m : Nat} (F : Fin m → Source) (i : Fin m) :
    List Address → CoarseHistory → CoarseHistory → PhaseLabel m × Sum Address Bool
  | [], seen, _ => (.verify i [] seen, .inr true)
  | q :: qs, seen, [] => (.verify i (q :: qs) seen, .inl q)
  | q :: qs, seen, a :: g =>
      if a.1 = q then
        if coarseReply a.2 = readout q (F i) then verifyPhase F i qs (seen ++ [a]) g
        else acquisitionReadout g
      else (.malformed, .inr false)

/-- Replay the original route. A route exit resets the local history before
the selected verifier or acquisition phase starts. -/
noncomputable def routePhase {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m)) :
    PassiveProtocol Address (fun _ => Option Bool) → CoarseHistory → CoarseHistory →
      PhaseLabel m × Sum Address Bool
  | .stop, seen, g => match decode seen with
      | some i => verifyPhase F i (leaves (F i)) [] g
      | none => acquisitionReadout g
  | .query q _, seen, [] => (.route seen, .inl q)
  | .query q next, seen, a :: g =>
      if a.1 = q then routePhase F decode (next a.2) (seen ++ [a]) g
      else (.malformed, .inr false)

private theorem verify_action {m : Nat} (F : Fin m → Source) (i : Fin m)
    (qs : List Address) (seen g : CoarseHistory) :
    (verifyPhase F i qs seen g).2 =
      controllerPolicy (verifyController (F i) qs) (encodeHistory g) := by
  induction qs generalizing seen g with
  | nil => rfl
  | cons q qs ih =>
      cases g with
      | nil => rfl
      | cons a g =>
          rcases a with ⟨r, z⟩
          by_cases address : r = q
          · subst r
            simp only [verifyPhase, verifyController, encodeHistory, List.map_cons,
              controllerPolicy]
            change (if coarseReply z = readout q (F i) then
                verifyPhase F i qs (seen ++ [⟨q, z⟩]) g else acquisitionReadout g).2 =
              controllerPolicy (if coarseReply z = readout q (F i) then
                verifyController (F i) qs else .fallback) (encodeHistory g)
            by_cases matched : coarseReply z = readout q (F i)
            · simpa only [if_pos matched] using ih (seen ++ [⟨q, z⟩]) g
            · simp only [if_neg matched, acquisitionReadout, controllerPolicy]
          · simp [verifyPhase, verifyController, controllerPolicy, encodeHistory, address]

private theorem route_action {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (seen g : CoarseHistory) :
    (routePhase F decode p seen g).2 =
      controllerPolicy (compileRaw F decode p seen) (encodeHistory g) := by
  induction p generalizing seen g with
  | stop =>
      cases choice : decode seen <;>
        simp [routePhase, compileRaw, choice, verify_action, acquisitionReadout, controllerPolicy]
  | query q next ih =>
      cases g with
      | nil => rfl
      | cons a g =>
          rcases a with ⟨r, z⟩
          by_cases address : r = q
          · subst r
            cases z with
            | none => simp [routePhase, compileRaw, controllerPolicy, encodeHistory, kappa, ih]
            | some b => cases b <;>
                simp [routePhase, compileRaw, controllerPolicy, encodeHistory, kappa, ih]
          · simp [routePhase, compileRaw, controllerPolicy, encodeHistory, address]

private theorem route_reset {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (U : Source)
    (seen s : CoarseHistory) :
    routePhase F decode p seen
        (runPassiveProtocol (fun q W => leafLabel W q) p U ++ s) =
      routePhase F decode .stop
        (seen ++ runPassiveProtocol (fun q W => leafLabel W q) p U) s := by
  induction p generalizing seen with
  | stop => simp [runPassiveProtocol]
  | query q next ih =>
      have rest := ih (leafLabel U q) (seen ++ [⟨q, leafLabel U q⟩])
      rw [List.append_assoc, List.singleton_append] at rest
      simpa [runPassiveProtocol, routePhase] using rest

private theorem coarseReply_kappa (z : Option Bool) : kappa (coarseReply z) = z := by
  cases z with
  | none => rfl
  | some b => cases b <;> rfl

theorem leaf_representative (V : Source) (q : Address) (member : q ∈ leaves V) :
    coarseReply (leafLabel V q) = readout q V := by
  obtain ⟨b, label⟩ := ((seven_leaf_separation.1 V).2 q).mp (List.mem_toFinset.mpr member)
  cases report : readout q V <;> simp [leafLabel, report, coarseReply] at label ⊢

private theorem verify_matched {m : Nat} (F : Fin m → Source) (i : Fin m)
    (pre tail : List Address) (seen g : CoarseHistory)
    (matched : ∀ q ∈ pre, coarseReply (leafLabel (F i) q) = readout q (F i)) :
    verifyPhase F i (pre ++ tail) seen
        (pre.map (fun q => ⟨q, leafLabel (F i) q⟩) ++ g) =
      verifyPhase F i tail (seen ++ pre.map (fun q => ⟨q, leafLabel (F i) q⟩)) g := by
  induction pre generalizing seen with
  | nil => simp
  | cons q pre ih =>
      have first := matched q List.mem_cons_self
      have rest := ih (seen ++ [⟨q, leafLabel (F i) q⟩])
        (fun r member => matched r (List.mem_cons_of_mem q member))
      simpa [verifyPhase, first, List.append_assoc] using rest

private theorem verifier_reset {m : Nat} (F : Fin m → Source) (i : Fin m)
    (pre rest : List Address) (q : Address) (y : Reply) (s : CoarseHistory)
    (split : leaves (F i) = pre ++ q :: rest)
    (mismatch : kappa y ≠ leafLabel (F i) q) :
    verifyPhase F i (leaves (F i)) []
        (pre.map (fun a => ⟨a, leafLabel (F i) a⟩) ++ [⟨q, kappa y⟩] ++ s) =
      (.acquisition s, acquisitionPolicy (encodeHistory s)) := by
  have matched r (member : r ∈ pre) :
      coarseReply (leafLabel (F i) r) = readout r (F i) := by
    apply leaf_representative
    rw [split]
    exact List.mem_append_left _ member
  have different : coarseReply (kappa y) ≠ readout q (F i) := by
    intro equal
    apply mismatch
    calc
      kappa y = kappa (coarseReply (kappa y)) := (coarseReply_kappa _).symm
      _ = kappa (readout q (F i)) := congrArg kappa equal
      _ = leafLabel (F i) q := rfl
  rw [split, List.append_assoc, verify_matched F i pre (q :: rest) [] _ matched]
  simp [verifyPhase, different, acquisitionReadout]

private theorem verify_ne_route {m : Nat} (F : Fin m → Source) (i : Fin m)
    (qs : List Address) (seen g phaseHistory : CoarseHistory) :
    (verifyPhase F i qs seen g).1 ≠ .route phaseHistory := by
  induction qs generalizing seen g with
  | nil => simp [verifyPhase]
  | cons q qs ih =>
      cases g with
      | nil => simp [verifyPhase]
      | cons a g =>
          by_cases address : a.1 = q
          · by_cases matched : coarseReply a.2 = readout q (F i)
            · simpa only [verifyPhase, if_pos address, if_pos matched] using
                ih (seen ++ [a]) g
            · simp [verifyPhase, address, matched, acquisitionReadout]
          · simp [verifyPhase, address]

private theorem route_local {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool))
    (seen g phaseHistory : CoarseHistory)
    (label : (routePhase F decode p seen g).1 = .route phaseHistory) :
    phaseHistory = seen ++ g := by
  induction p generalizing seen g with
  | stop =>
      cases choice : decode seen with
      | none => simp [routePhase, choice, acquisitionReadout] at label
      | some i => exact (verify_ne_route F i (leaves (F i)) [] g phaseHistory
          (by simpa only [routePhase, choice] using label)).elim
  | query q next ih =>
      cases g with
      | nil => simpa [routePhase] using label.symm
      | cons a g =>
          by_cases address : a.1 = q
          · have rest := ih a.2 (seen ++ [a]) g
                (by simpa only [routePhase, if_pos address] using label)
            simpa only [List.append_assoc, List.singleton_append] using rest
          · simp [routePhase, address] at label

private theorem verify_residual {m : Nat} (F : Fin m → Source) (i j : Fin m)
    (qs rest : List Address) (seen g phaseHistory : CoarseHistory)
    (label : (verifyPhase F i qs seen g).1 = .verify j rest phaseHistory) :
    j = i ∧ ∃ used leftover : CoarseHistory,
      g = used ++ leftover ∧ qs = used.map Sigma.fst ++ rest ∧
      phaseHistory = seen ++ used ∧ (rest ≠ [] → leftover = []) ∧
      ∀ a ∈ used, a.2 = leafLabel (F i) a.1 := by
  induction qs generalizing seen g with
  | nil =>
      simp only [verifyPhase, PhaseLabel.verify.injEq] at label
      rcases label with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, [], g, by simp⟩
  | cons q qs ih =>
      cases g with
      | nil =>
          simp only [verifyPhase, PhaseLabel.verify.injEq] at label
          rcases label with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, [], [], by simp⟩
      | cons a g =>
          by_cases address : a.1 = q
          · by_cases matched : coarseReply a.2 = readout q (F i)
            · obtain ⟨same, used, leftover, history, residual, suffix, exhausted, truth⟩ :=
                ih (seen ++ [a]) g
                  (by simpa only [verifyPhase, if_pos address, if_pos matched] using label)
              refine ⟨same, a :: used, leftover, ?_, ?_, ?_, exhausted, ?_⟩
              · simpa only [List.cons_append] using congrArg (List.cons a) history
              · simp only [List.map_cons, List.cons_append, address, residual]
              · simpa only [List.append_assoc, List.singleton_append] using suffix
              · intro b member
                rcases List.mem_cons.mp member with rfl | member
                · calc
                    b.2 = kappa (coarseReply b.2) := (coarseReply_kappa _).symm
                    _ = kappa (readout b.1 (F i)) := by rw [address, matched]
                    _ = leafLabel (F i) b.1 := rfl
                · exact truth b member
            · simp [verifyPhase, address, matched, acquisitionReadout] at label
          · simp [verifyPhase, address] at label

/-- The finite image uses genuine local phase labels, without retaining the
full global coarse prefix as an extra observation. -/
noncomputable def phaseAlphabet {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy) :
    Finset (PhaseLabel m) :=
  (strategyPrefixes N π).image (fun g => (routePhase F decode p [] g).1)

/-- The sink receives the fixed malformed label. All other rows carry the
original parser's phase observation. -/
noncomputable def observerPhase {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy) :
    ExactState (strategyPrefixes N π) → PhaseLabel m
  | .inl r => (routePhase F decode p [] r.1.1).1
  | .inr _ => .malformed

/-- The parser computes the original controller action, resets the route's
local history at its exit, and supplies the exact finite phase observation
on every actual compiled prefix. -/
theorem phase_replay_contract {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (positive : 1 ≤ N)
    (policy : π.policy = fun h =>
      controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h))) :
    (∀ g, (routePhase F decode p [] g).2 =
      controllerPolicy (compileRaw F decode p []) (encodeHistory g)) ∧
    (∀ U s, routePhase F decode p []
        (runPassiveProtocol (fun q W => leafLabel W q) p U ++ s) =
      routePhase F decode .stop
        (runPassiveProtocol (fun q W => leafLabel W q) p U) s) ∧
    (∀ (i : Fin m) (pre rest : List Address) (q : Address) (y : Reply) (s : CoarseHistory),
      leaves (F i) = pre ++ q :: rest → kappa y ≠ leafLabel (F i) q →
      verifyPhase F i (leaves (F i)) []
          (pre.map (fun a => ⟨a, leafLabel (F i) a⟩) ++ [⟨q, kappa y⟩] ++ s) =
        (.acquisition s, acquisitionPolicy (encodeHistory s))) ∧
    (∀ seen g phaseHistory,
      (routePhase F decode p seen g).1 = .route phaseHistory → phaseHistory = seen ++ g) ∧
    (∀ (i j : Fin m) (qs rest : List Address) (seen g phaseHistory : CoarseHistory),
      (verifyPhase F i qs seen g).1 = .verify j rest phaseHistory →
      j = i ∧ ∃ used leftover : CoarseHistory,
        g = used ++ leftover ∧ qs = used.map Sigma.fst ++ rest ∧
        phaseHistory = seen ++ used ∧ (rest ≠ [] → leftover = []) ∧
        ∀ a ∈ used, a.2 = leafLabel (F i) a.1) ∧
    (∀ U, Allowed N U → ∀ e h,
      ActualPrefix (strategyObserver N π positive) U e h →
        observerPhase F decode p N π e = (routePhase F decode p [] (kappa_hist h)).1 ∧
        observerPhase F decode p N π e ∈ phaseAlphabet F decode p N π ∧
        (routePhase F decode p [] (kappa_hist h)).2 = π.policy h) := by
  have coarse : Function.FactorsThrough π.policy kappa_hist := by
    intro h k equal
    simp only [policy, equal]
  refine ⟨route_action F decode p [], ?_, verifier_reset F,
    route_local F decode p, verify_residual F, ?_⟩
  · intro U s
    simpa using route_reset F decode p U [] s
  · intro U allowed e h pref
    obtain ⟨r, rfl, history, cache, original⟩ :=
      strategy_actual_prefix_replay N π positive coarse U allowed pref
    refine ⟨?_, ?_, ?_⟩
    · simp only [observerPhase, history]
    · exact Finset.mem_image.mpr ⟨r.1.1, r.1.2, rfl⟩
    · rw [route_action, policy]

end D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay

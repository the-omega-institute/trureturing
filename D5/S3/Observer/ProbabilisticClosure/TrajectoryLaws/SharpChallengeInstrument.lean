/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SharpChallengeInstrument
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SharpChallengeInstrument
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A homogeneous challenge instrument separates fixed words from causal feedback. -/

import D5.S3.TotalVariation.Metric
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.DeriveFintype

noncomputable section

open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SharpChallengeInstrument

open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric

/-- The four kinds of observable symbols are disjoint. -/
inductive Output (A : Type) where
  | challenge : A → Output A
  | bit : Bool → Output A
  | failure : Output A
  | finished : Output A
  deriving DecidableEq, Fintype

/-- The countdown belongs to the hidden state, rather than to the transition clock. -/
inductive State (A : Type) (n : ℕ) where
  | start : Bool → State A n
  | awaiting : Bool → Fin (n + 1) → A → State A n
  | fail : State A n
  | done : State A n
  deriving DecidableEq, Fintype

/-- A chronological full record, with a constant empty initial archive. -/
@[reducible] def Record (A Y : Type) : ℕ → Type
  | 0 => Unit
  | t + 1 => Record A Y t × A × Y

instance recordFintype (A Y : Type) [Fintype A] [Fintype Y] (t : ℕ) :
    Fintype (Record A Y t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ t ih => exact inferInstanceAs (Fintype (Record A Y t × A × Y))

instance recordDecidableEq (A Y : Type) [DecidableEq A] [DecidableEq Y] (t : ℕ) :
    DecidableEq (Record A Y t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ t ih => exact inferInstanceAs (DecidableEq (Record A Y t × A × Y))

/-- Every row, including an unreachable history, is a probability distribution on actions. -/
abbrev Policy (A Y : Type) := ∀ t, Record A Y t → PMF A

/-- One joint output/successor sample. The emitted and stored challenges are the same draw. -/
def instrument {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (n : ℕ) (a : A) : State A n → PMF (Output A × State A n)
  | .start z => (PMF.uniformOfFintype A).map fun r =>
      (.challenge r, .awaiting z ⟨n, Nat.lt_succ_self n⟩ r)
  | .awaiting z k r =>
      if a = r then
        if hk : k.val = 0 then PMF.pure (.bit z, .done)
        else (PMF.uniformOfFintype A).map fun s =>
          (.challenge s, .awaiting z ⟨k.val - 1, by omega⟩ s)
      else PMF.pure (.failure, .fail)
  | .fail => PMF.pure (.failure, .fail)
  | .done => PMF.pure (.finished, .done)

/-- Operational execution: state and history, then a history action, then the joint row. -/
def execute {A X Y : Type} (K : A → X → PMF (Y × X)) (π : Policy A Y)
    (p : PMF X) : (t : ℕ) → PMF (X × Record A Y t)
  | 0 => p.map fun x => (x, ())
  | t + 1 => (execute K π p t).bind fun xh =>
      (π t xh.2).bind fun a =>
        (K a xh.1).map fun yx => (yx.2, xh.2, a, yx.1)

/-- The accessible experiment law forgets only the hidden current state. -/
def recordLaw {A X Y : Type} (K : A → X → PMF (Y × X)) (π : Policy A Y)
    (p : PMF X) (t : ℕ) : PMF (Record A Y t) :=
  (execute K π p t).map Prod.snd

/-- The full output sequence is the action-forgetting projection of the same record. -/
def outputs {A Y : Type} : (t : ℕ) → Record A Y t → Record Unit Y t
  | 0, _ => ()
  | t + 1, h => (outputs t h.1, (), h.2.2)

/-- A total common policy that copies the most recently observed challenge. -/
def matchingPolicy {A : Type} (a₀ : A) : Policy A (Output A)
  | 0, _ => PMF.pure a₀
  | _ + 1, h => PMF.pure (match h.2.2 with
      | .challenge r => r
      | _ => a₀)

/-- A fixed action schedule, independent of every observation. -/
def fixedPolicy {A Y : Type} (a : ℕ → A) : Policy A Y := fun t _ => PMF.pure (a t)

/-- A finite word extended by a default action after its specified horizon. -/
def extendWord {A : Type} {H : ℕ} (a₀ : A) (a : Fin H → A) (t : ℕ) : A :=
  if ht : t < H then a ⟨t, ht⟩ else a₀

/-- The concrete instrument's record law under the hidden bit prior. -/
def law {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (n : ℕ) (π : Policy A (Output A)) (z : Bool) (t : ℕ) :=
  recordLaw (instrument n) π (PMF.pure (.start z)) t

/-- A live prefix has matched all challenges except its last, still pending challenge. -/
def liveRecord {A : Type} (a : ℕ → A) : (j : ℕ) → A → Record A (Output A) (j + 1)
  | 0, r => ((), a 0, .challenge r)
  | j + 1, r => (liveRecord a j (a (j + 1)), a (j + 1), .challenge r)

/-- The complete successful record includes the final hidden bit symbol. -/
def successRecord {A : Type} (a : ℕ → A) (n : ℕ) (z : Bool) :
    Record A (Output A) (n + 2) :=
  (liveRecord a n (a (n + 1)), a (n + 1), .bit z)

/-- Full failure mass, extended at every step without discarding the earlier record. -/
def failureMass {A : Type} [Fintype A] [DecidableEq A] (a : ℕ → A) :
    (j : ℕ) → Record A (Output A) (j + 1) → ℝ≥0∞
  | 0, _ => 0
  | j + 1, h => if h.2 = (a (j + 1), Output.failure) then
      failureMass a j h.1 +
        ∑ r : A, if r ≠ a (j + 1) ∧ h.1 = liveRecord a j r then
          (Fintype.card A : ℝ≥0∞)⁻¹ ^ (j + 1) else 0
      else 0

/-- Finite-word distance computed on full output sequences. -/
def fixedDistance {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (n : ℕ) (a : ℕ → A) : ℝ :=
  totalVariation
    (fun h => ((law n (fixedPolicy a) false (n + 2)).map (outputs (n + 2)) h).toReal)
    (fun h => ((law n (fixedPolicy a) true (n + 2)).map (outputs (n + 2)) h).toReal)

/-- Feedback distance uses the full action/output record. -/
def feedbackDistance {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (n : ℕ) (π : Policy A (Output A)) : ℝ :=
  totalVariation (fun h => (law n π false (n + 2) h).toReal)
    (fun h => (law n π true (n + 2) h).toReal)

/-- A complete joint path also retains every earlier hidden state. -/
@[reducible] def HiddenPath (A X Y : Type) : ℕ → Type
  | 0 => X
  | t+1 => HiddenPath A X Y t × A × Y × X

instance hiddenPathFintype (A X Y : Type) [Fintype A] [Fintype X] [Fintype Y]
    (t : ℕ) : Fintype (HiddenPath A X Y t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype X)
  | succ t ih => exact inferInstanceAs (Fintype (HiddenPath A X Y t × A × Y × X))

/-- Current state and accessible record of a complete hidden path. -/
def pathView {A X Y : Type} : (t : ℕ) → HiddenPath A X Y t → X × Record A Y t
  | 0, x => (x, ())
  | t+1, h => (h.2.2.2, (pathView t h.1).2, h.2.1, h.2.2.1)

/-- The same sequential experiment with all hidden states retained for conditioning. -/
def pathExecution {A X Y : Type} (K : A → X → PMF (Y × X)) (π : Policy A Y)
    (p : PMF X) : (t : ℕ) → PMF (HiddenPath A X Y t)
  | 0 => p
  | t+1 => (pathExecution K π p t).bind fun h =>
      (π t (pathView t h).2).bind fun a =>
        (K a (pathView t h).1).map fun yx => (h, a, yx.1, yx.2)

/-- Initial mass times the sequential policy and joint-row factors along a complete path. -/
def pathProduct {A X Y : Type} (K : A → X → PMF (Y × X)) (π : Policy A Y)
    (p : PMF X) : (t : ℕ) → HiddenPath A X Y t → ℝ≥0∞
  | 0, x => p x
  | t+1, h => pathProduct K π p t h.1 *
      (π t (pathView t h.1).2 h.2.1 *
        K h.2.1 (pathView t h.1).1 (h.2.2.1, h.2.2.2))

set_option maxHeartbeats 1200000 in
-- The joint path law, two execution inductions, and distance calculation share one proof.
/-- Exact complete-record laws and distances for every action count and horizon at least two. -/
theorem result (m H : ℕ) (hm : 2 ≤ m) (hH : 2 ≤ H) :
    letI : NeZero m := ⟨by omega⟩
    ∃ n : ℕ, H = n + 2 ∧
      (∀ (a : Fin m) (x : State (Fin m) n),
        (∀ yx, 0 ≤ (instrument n a x yx).toReal) ∧
        ∑ yx, (instrument n a x yx).toReal = 1) ∧
      (∀ (π : Policy (Fin m) (Output (Fin m))) (z : Bool) (t : ℕ)
        (x : State (Fin m) n) (h : Record (Fin m) (Output (Fin m)) t)
        (a : Fin m) (y : Output (Fin m)),
        execute (instrument n) π (PMF.pure (.start z)) (t+1) (x,h,a,y) =
          ∑ s, execute (instrument n) π (PMF.pure (.start z)) t (s,h) *
            (π t h a * instrument n a s (y,x))) ∧
      (∀ (π : Policy (Fin m) (Output (Fin m))) (z : Bool) (t : ℕ),
        (pathExecution (instrument n) π (PMF.pure (.start z)) t).map (pathView t) =
          execute (instrument n) π (PMF.pure (.start z)) t ∧
        ∀ h, pathExecution (instrument n) π (PMF.pure (.start z)) t h =
          pathProduct (instrument n) π (PMF.pure (.start z)) t h) ∧
      (∀ (a : ℕ → Fin m) (z : Bool) h,
        law n (fixedPolicy a) z (n+2) h = failureMass a (n+1) h +
          if h = successRecord a n z then (m : ℝ≥0∞)⁻¹ ^ (n+1) else 0) ∧
      (∀ a : ℕ → Fin m,
        (∑ h, (failureMass a (n+1) h).toReal) = 1 - (m : ℝ)⁻¹ ^ (n+1) ∧
        (∀ z, failureMass a (n+1) (successRecord a n z) = 0) ∧
        (∀ j ≤ n, ∀ r, r ≠ a (j+1) →
          failureMass a (j+1) (liveRecord a j r, a (j+1), Output.failure) =
            (m : ℝ≥0∞)⁻¹ ^ (j+1)) ∧
        (∀ j ≤ n, ∀ h : Record (Fin m) (Output (Fin m)) (j+1),
          h.2.2 = Output.failure →
          failureMass a (j+1) (h, a (j+1), Output.failure) = failureMass a j h) ∧
        fixedDistance n a = (m : ℝ)⁻¹ ^ (n+1) ∧
        feedbackDistance n (fixedPolicy a) = (m : ℝ)⁻¹ ^ (n+1)) ∧
      IsGreatest (Set.range fun a : Fin H → Fin m =>
        fixedDistance n (extendWord ⟨0, by omega⟩ a)) ((m : ℝ)⁻¹ ^ (n+1)) ∧
      (∀ z, ∀ h ∈ (law n (matchingPolicy (⟨0, by omega⟩ : Fin m)) z (n+2)).support,
        h.2.2 = Output.bit z) ∧
      feedbackDistance n (matchingPolicy (⟨0, by omega⟩ : Fin m)) = 1 ∧
      (∀ π : Policy (Fin m) (Output (Fin m)), feedbackDistance n π ≤ 1) ∧
      sSup (Set.range (feedbackDistance (A := Fin m) n)) = 1 := by
  classical
  let : NeZero m := ⟨by omega⟩
  have norm {T : Type} [Fintype T] (p : PMF T) : ∑ t, (p t).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun t _ => p.apply_ne_top t)]
    simpa [tsum_fintype] using congrArg ENNReal.toReal p.tsum_coe
  have step {A X Y : Type} [Fintype A] [Fintype X] [Fintype Y]
      (K : A → X → PMF (Y × X)) (π : Policy A Y) (p : PMF X)
      (t : ℕ) (x : X) (h : Record A Y t) (a : A) (y : Y) :
      execute K π p (t + 1) (x, h, a, y) =
        ∑ s, execute K π p t (s, h) * (π t h a * K a s (y, x)) := by
    have hm (s : X) (h' : Record A Y t) (a' : A) :
        ((K a' s).map fun yx => (yx.2, h', a', yx.1)) (x, h, a, y) =
          if h = h' ∧ a = a' then K a' s (y, x) else 0 := by
      simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Prod.mk.injEq]
      by_cases hh : h = h' <;> by_cases ha : a = a' <;>
        simp [hh, ha, ite_and]
    change (∑' sh, execute K π p t sh *
      ∑' b, π t sh.2 b * ((K b sh.1).map fun yx => (yx.2, sh.2, b, yx.1))
        (x, h, a, y)) = _
    simp_rw [hm]
    simp [tsum_fintype, Fintype.sum_prod_type, mul_ite, ite_and]
  have paths {A X Y : Type} [Fintype A] [Fintype X] [Fintype Y]
      (K : A → X → PMF (Y × X)) (π : Policy A Y) (p : PMF X) :
      ∀ t, (pathExecution K π p t).map (pathView t) = execute K π p t ∧
        ∀ h, pathExecution K π p t h = pathProduct K π p t h := by
    classical
    intro t
    induction t with
    | zero => exact ⟨rfl, fun _ => rfl⟩
    | succ t ih =>
      constructor
      · rw [execute, ← ih.1, PMF.bind_map, pathExecution, PMF.map_bind]
        congr 1
        funext h
        simp [PMF.map_bind, PMF.map_comp, Function.comp_def, pathView]
      · rintro ⟨h, a, y, x⟩
        have hm (h' : HiddenPath A X Y t) (b : A) :
            ((K b (pathView t h').1).map fun yx => (h',b,yx.1,yx.2)) (h,a,y,x) =
            if h = h' ∧ a = b then K b (pathView t h').1 (y,x) else 0 := by
          by_cases hh : h = h' <;> by_cases ha : a = b <;>
            simp [PMF.map_apply, tsum_fintype, Prod.mk.injEq, hh, ha]
        change (∑' h', pathExecution K π p t h' *
          ∑' b, π t (pathView t h').2 b *
            ((K b (pathView t h').1).map fun yx => (h',b,yx.1,yx.2)) (h,a,y,x)) = _
        simp_rw [hm]
        simp [tsum_fintype, mul_ite, ite_and, ih.2, pathProduct]
  have fixed_law {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
      (n : ℕ) (a : ℕ → A) (z : Bool) :
      ∀ h, law n (fixedPolicy a) z (n+2) h = failureMass a (n+1) h +
        if h = successRecord a n z then (Fintype.card A : ℝ≥0∞)⁻¹ ^ (n+1) else 0 := by
    classical
    have propagate {T R : Type} [Fintype T] [Fintype R] [DecidableEq T]
        (p : PMF T) (f : R → T) (c : ℝ≥0∞) (d : T → ℝ≥0∞)
        (hp : ∀ x, p x = d x + ∑ r, if x = f r then c else 0)
        {B : Type} (q : T → PMF B) (b : B) :
        p.bind q b = (∑ x, d x * q x b) + ∑ r, c * q (f r) b := by
      simp only [PMF.bind_apply, tsum_fintype, hp, add_mul, Finset.sum_add_distrib]
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp [ite_mul]
    have hprefix :
      ∀ (j : ℕ) (hj : j ≤ n) (xh : State A n × Record A (Output A) (j + 1)),
        execute (instrument n) (fixedPolicy a) (PMF.pure (.start z)) (j + 1) xh =
          (if xh.1 = .fail then failureMass a j xh.2 else 0) +
          ∑ r : A, if xh = (.awaiting z ⟨n - j, by omega⟩ r, liveRecord a j r)
            then (Fintype.card A : ℝ≥0∞)⁻¹ ^ (j + 1) else 0 := by
      intro j
      induction j with
      | zero =>
        intro hj xh
        simp [execute, fixedPolicy, PMF.pure_map, PMF.pure_bind, instrument,
          PMF.map_comp, PMF.map_apply, tsum_fintype, liveRecord, failureMass,
          PMF.uniformOfFintype_apply, Function.comp_def]
      | succ j ih =>
        intro hj xh
        have hj' : j ≤ n := by omega
        have hk : n - j ≠ 0 := by omega
        have hcount : n - j - 1 = n - (j + 1) := by omega
        have ht (r : A) (q : State A n × Record A (Output A) (j+2)) :
            ((instrument n (a (j+1)) (.awaiting z ⟨n-j, by omega⟩ r)).map
              fun yx => (yx.2, liveRecord a j r, a (j+1), yx.1)) q =
            if a (j+1) = r then
              ∑ u : A, if q = (.awaiting z ⟨n-(j+1), by omega⟩ u,
                liveRecord a (j+1) u) then (Fintype.card A : ℝ≥0∞)⁻¹ else 0
            else if q = (.fail, liveRecord a j r, a (j+1), .failure) then 1 else 0 := by
          by_cases hr : a (j+1) = r
          · subst r
            simp [instrument, hk, PMF.map_comp, PMF.map_apply, tsum_fintype,
              PMF.uniformOfFintype_apply, liveRecord, Function.comp_def, hcount]
            congr 1
          · simp [instrument, hr, PMF.pure_map, PMF.pure_apply]
        change ((execute (instrument n) (fixedPolicy a) (PMF.pure (.start z)) (j+1)).bind
          (fun sh => (PMF.pure (a (j+1))).bind fun b =>
            (instrument n b sh.1).map fun yx => (yx.2, sh.2, b, yx.1))) xh = _
        simp only [PMF.pure_bind]
        rw [propagate (execute (instrument n) (fixedPolicy a) (PMF.pure (.start z)) (j+1))
          (fun r : A => (.awaiting z ⟨n-j, by omega⟩ r, liveRecord a j r))
          ((Fintype.card A : ℝ≥0∞)⁻¹ ^ (j+1))
          (fun sh => if sh.1 = .fail then failureMass a j sh.2 else 0)
          (by intro sh; exact ih hj' sh)]
        simp_rw [ht]
        rcases xh with ⟨s, h, b, y⟩
        by_cases hs : s = State.fail
        · subst s
          by_cases hb : b = a (j+1) <;> by_cases hy : y = Output.failure <;>
            simp [Fintype.sum_prod_type, ite_mul, instrument,
              PMF.pure_apply, Prod.mk.injEq, failureMass,
              liveRecord, mul_ite, ite_and, hb, hy, eq_comm]
        · simp [Fintype.sum_prod_type, ite_mul, instrument, hs,
            PMF.pure_apply, Prod.mk.injEq,
            liveRecord, mul_ite, ite_and, pow_succ, Finset.mul_sum,
            and_assoc, and_left_comm, and_comm]
    have ht (r : A) (h : Record A (Output A) (n+2)) :
        ((instrument n (a (n+1)) (.awaiting z ⟨n-n, by omega⟩ r)).map
          fun yx => (liveRecord a n r, a (n+1), yx.1)) h =
        (if r = a (n+1) then if h = successRecord a n z then 1 else 0 else 0) +
        (if r ≠ a (n+1) ∧ h = (liveRecord a n r, a (n+1), .failure) then 1 else 0) := by
      by_cases hr : r = a (n+1)
      · subst r
        simp [instrument, PMF.pure_map, PMF.pure_apply, successRecord]
        congr 1
      · simp [instrument, hr, Ne.symm hr, PMF.pure_map, PMF.pure_apply]
    intro h
    rw [law, recordLaw, execute, PMF.map_bind]
    simp only [fixedPolicy, PMF.pure_bind, PMF.map_comp, Function.comp_def]
    rw [propagate (execute (instrument n) (fixedPolicy a) (PMF.pure (.start z)) (n+1))
      (fun r : A => (.awaiting z ⟨n-n, by omega⟩ r, liveRecord a n r))
      ((Fintype.card A : ℝ≥0∞)⁻¹ ^ (n+1))
      (fun sh => if sh.1 = .fail then failureMass a n sh.2 else 0)
      (by intro sh; exact hprefix n le_rfl sh)]
    simp_rw [ht]
    rcases h with ⟨h, b, y⟩
    simp [Fintype.sum_prod_type, ite_mul, instrument,
      PMF.pure_apply, Prod.mk.injEq, failureMass, successRecord,
      mul_add, mul_ite, Finset.sum_add_distrib, ite_and,
      and_assoc, and_left_comm, and_comm]
    by_cases hb : b = a (n+1) <;> by_cases hy : y = Output.failure <;>
      simp [hb, hy, add_comm]
  have matching_success {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
      (n : ℕ) (a₀ : A) (z : Bool) :
      ∀ h ∈ (law n (matchingPolicy a₀) z (n + 2)).support,
        h.2.2 = Output.bit z := by
    classical
    have live : ∀ (j : ℕ) (hj : j ≤ n)
        (xh : State A n × Record A (Output A) (j + 1)),
        xh ∈ (execute (instrument n) (matchingPolicy a₀)
          (PMF.pure (.start z)) (j + 1)).support →
        ∃ r, xh.1 = .awaiting z ⟨n - j, by omega⟩ r ∧ xh.2.2.2 = .challenge r := by
      intro j
      induction j with
      | zero =>
        intro hj xh hx
        simp only [execute, PMF.pure_map, PMF.pure_bind, matchingPolicy,
          instrument] at hx
        rw [PMF.map_comp] at hx
        obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        exact ⟨r, rfl, rfl⟩
      | succ j ih =>
        intro hj xh hx
        obtain ⟨sh, hsh, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        obtain ⟨r, hs, hy⟩ := ih (by omega) sh hsh
        change xh ∈ ((matchingPolicy a₀ (j+1) sh.2).bind _).support at hx
        simp only [matchingPolicy, hy, PMF.pure_bind, hs, instrument, ite_true] at hx
        have hk : n - j ≠ 0 := by omega
        simp only [dif_neg hk] at hx
        rw [PMF.map_comp] at hx
        obtain ⟨r', hr', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        refine ⟨r', ?_, rfl⟩
        congr 1
    intro h hh
    obtain ⟨xh, hxh, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    obtain ⟨sh, hsh, hxh⟩ := (PMF.mem_support_bind_iff _ _ _).mp hxh
    obtain ⟨r, hs, hy⟩ := live n le_rfl sh hsh
    change xh ∈ ((matchingPolicy a₀ (n+1) sh.2).bind _).support at hxh
    simp only [matchingPolicy, hy, PMF.pure_bind, hs, instrument, Nat.sub_self,
      PMF.pure_map, PMF.mem_support_pure_iff, ite_true, dite_true] at hxh
    subst xh
    rfl
  have shifted_tv {T : Type} [Fintype T] [DecidableEq T] (F : T → ℝ) (c : ℝ) (hc : 0 ≤ c)
      (l r : T) (hlr : l ≠ r) :
      totalVariation (fun t => F t + if t = l then c else 0)
        (fun t => F t + if t = r then c else 0) = c := by
    classical
    have hp (t : T) :
        |(F t + if t = l then c else 0) - (F t + if t = r then c else 0)| =
          (if t = l then c else 0) + (if t = r then c else 0) := by
      by_cases hl : t = l <;> by_cases hr : t = r
      · exact False.elim (hlr (hl.symm.trans hr))
      · simp [hl, hlr, abs_of_nonneg hc]
      · simp [hr, Ne.symm hlr, abs_of_nonneg hc]
      · simp [hl, hr]
    simp only [totalVariation, hp, Finset.sum_add_distrib]
    simp
    ring
  have map_real {T U : Type} [Fintype T] [DecidableEq U] (p : PMF T) (f : T → U) (u : U) :
      ((p.map f) u).toReal = ∑ t, if u = f t then (p t).toReal else 0 := by
    classical
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro t ht
      split_ifs <;> rfl
    · intro t ht
      split_ifs <;> simp [p.apply_ne_top]
  have map_shift {T U : Type} [Fintype T] [DecidableEq T] [DecidableEq U] (F : T → ℝ) (c : ℝ)
      (s : T) (f : T → U) (u : U) :
      (∑ t, if u = f t then F t + (if t = s then c else 0) else 0) =
        (∑ t, if u = f t then F t else 0) + (if u = f s then c else 0) := by
    classical
    have ht (t : T) :
        (if u = f t then F t + (if t = s then c else 0) else 0) =
          (if u = f t then F t else 0) +
          (if u = f t then (if t = s then c else 0) else 0) := by
      by_cases h : u = f t <;> simp [h]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      simp [hts]
    · simp
  have disjoint_tv {T : Type} [Fintype T] (p q : PMF T) (E : Finset T)
      (hp : ∀ t ∈ p.support, t ∈ E) (hq : ∀ t ∈ q.support, t ∉ E) :
      totalVariation (fun t => (p t).toReal) (fun t => (q t).toReal) = 1 := by
    classical
    have norm (r : PMF T) : ∑ t, (r t).toReal = 1 := by
      rw [← ENNReal.toReal_sum (fun t _ => r.apply_ne_top t)]
      simpa [tsum_fintype] using congrArg ENNReal.toReal r.tsum_coe
    have hep : ∑ t ∈ E, (p t).toReal = 1 := by
      rw [← norm p]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro t ht hn
      have : p t = 0 := by
        by_contra h
        exact hn (hp t h)
      simp [this]
    have heq : ∑ t ∈ E, (q t).toReal = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have : q t = 0 := by
        by_contra h
        exact hq t h ht
      simp [this]
    apply le_antisymm
    · exact total_variation_le_one _ _ ⟨fun _ => ENNReal.toReal_nonneg, norm p⟩
        ⟨fun _ => ENNReal.toReal_nonneg, norm q⟩
    · have hb := (total_variation_eq_sup_event_gap
        (fun t => (p t).toReal) (fun t => (q t).toReal)
        ((norm p).trans (norm q).symm)).2 (Set.mem_range_self E)
      simpa [hep, heq] using hb
  let n := H - 2
  have hn : H = n + 2 := by dsimp [n]; omega
  let a₀ : Fin m := ⟨0, by omega⟩
  let α : ℝ := (m : ℝ)⁻¹ ^ (n+1)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hreal (a : ℕ → Fin m) (z : Bool)
      (h : Record (Fin m) (Output (Fin m)) (n+2)) :
      (law n (fixedPolicy a) z (n+2) h).toReal = (failureMass a (n+1) h).toReal +
        if h = successRecord a n z then α else 0 := by
    have he := fixed_law n a z h
    have hf : failureMass a (n+1) h ≠ ∞ :=
      ne_top_of_le_ne_top ((law n (fixedPolicy a) z (n+2)).apply_ne_top h)
        (by rw [he]; exact le_add_right le_rfl)
    have hi : (if h = successRecord a n z then
        (Fintype.card (Fin m) : ℝ≥0∞)⁻¹ ^ (n+1) else 0) ≠ ∞ :=
      ne_top_of_le_ne_top ((law n (fixedPolicy a) z (n+2)).apply_ne_top h)
        (by rw [he]; exact le_add_left le_rfl)
    rw [he, ENNReal.toReal_add hf hi]
    split_ifs <;> simp [α]
  have hmap {U : Type} [Fintype U] [DecidableEq U] (a : ℕ → Fin m) (z : Bool)
      (f : Record (Fin m) (Output (Fin m)) (n+2) → U) (u : U) :
      (((law n (fixedPolicy a) z (n+2)).map f) u).toReal =
        (∑ h, if u = f h then (failureMass a (n+1) h).toReal else 0) +
        if u = f (successRecord a n z) then α else 0 := by
    rw [map_real]
    simp_rw [hreal]
    exact map_shift (fun h => (failureMass a (n+1) h).toReal) α
      (successRecord a n z) f u
  have hfixed (a : ℕ → Fin m) :
      fixedDistance n a = α ∧ feedbackDistance n (fixedPolicy a) = α := by
    constructor
    · unfold fixedDistance
      simp_rw [hmap]
      exact shifted_tv _ α hα _ _ (by simp [successRecord, outputs])
    · unfold feedbackDistance
      simp_rw [hreal]
      exact shifted_tv _ α hα _ _ (by simp [successRecord])
  have hmatch : feedbackDistance n (matchingPolicy a₀) = 1 := by
    apply disjoint_tv (law n (matchingPolicy a₀) false (n+2))
      (law n (matchingPolicy a₀) true (n+2))
      (Finset.univ.filter fun h => h.2.2 = Output.bit false)
    · intro h hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ h, matching_success n a₀ false h hh⟩
    · intro h hh he
      have hfalse := (Finset.mem_filter.mp he).2
      have htrue := matching_success n a₀ true h hh
      simp [htrue] at hfalse
  have hbound (π : Policy (Fin m) (Output (Fin m))) : feedbackDistance n π ≤ 1 :=
    total_variation_le_one _ _
      ⟨fun _ => ENNReal.toReal_nonneg, norm _⟩
      ⟨fun _ => ENNReal.toReal_nonneg, norm _⟩
  have hgreat : IsGreatest (Set.range (feedbackDistance (A := Fin m) n)) 1 :=
    ⟨⟨matchingPolicy a₀, hmatch⟩, by rintro v ⟨π, rfl⟩; exact hbound π⟩
  refine ⟨n, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmatch, hbound, hgreat.csSup_eq⟩
  · intro a x
    exact ⟨fun _ => ENNReal.toReal_nonneg, norm _⟩
  · intro π z t x h a y
    exact step _ _ _ _ _ _ _ _
  · intro π z t
    exact paths _ _ _ t
  · intro a z h
    simpa using fixed_law n a z h
  · intro a
    refine ⟨?_, ?_, ?_, ?_, (hfixed a).1, (hfixed a).2⟩
    · have hs := norm (law n (fixedPolicy a) false (n+2))
      simp_rw [hreal] at hs
      simp only [Finset.sum_add_distrib] at hs
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hs
      dsimp [α] at hs
      linarith
    · intro z
      simp [failureMass, successRecord]
    · intro j hj r hr
      have hzero : failureMass a j (liveRecord a j r) = 0 := by
        cases j <;> simp [failureMass, liveRecord]
      have hinj (u : Fin m) : liveRecord a j r = liveRecord a j u ↔ r = u := by
        cases j <;> simp [liveRecord]
      suffices (∑ u : Fin m, if u = a (j+1) then 0
          else if r = u then (m : ℝ≥0∞)⁻¹ ^ (j+1) else 0) =
          (m : ℝ≥0∞)⁻¹ ^ (j+1) by
        simpa [failureMass, hzero, hinj, ite_and] using this
      rw [Finset.sum_eq_single r]
      · simp [hr]
      · intro u hu hur
        simp [Ne.symm hur]
      · simp
    · intro j hj h hh
      have hne (r : Fin m) : h ≠ liveRecord a j r := by
        intro he
        have hy := congrArg (fun v : Record (Fin m) (Output (Fin m)) (j+1) => v.2.2) he
        cases j <;> simp [liveRecord, hh] at hy
      simp [failureMass, hne]
  · refine ⟨⟨fun _ => a₀, (hfixed _).1⟩, ?_⟩
    rintro v ⟨a, rfl⟩
    exact le_of_eq (hfixed _).1
  · exact matching_success n a₀

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SharpChallengeInstrument

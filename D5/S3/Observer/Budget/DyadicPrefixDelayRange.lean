/- GID: D5/S3/Observer/Budget/DyadicPrefixDelayRange
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/DyadicPrefixDelayRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Causal final-query delays realize whole dyadic prefix time tables. -/

import D5.S3.Observer.Budget.TerminalClockCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.DyadicPrefixDelayRange

open DyadicForwardWaitingOptimality TerminalClockCompression

/-- Follow the earliest midpoint tree, adding the table's whole-period delay
only to its final query. The interval start at that node identifies its pair. -/
def delayedMidpoint (P : Nat) (K : Nat → Nat) : (d : Nat) → Nat → Nat → Protocol d
  | 0, a, _ => .stop a
  | d + 1, a, now =>
      let m := a + 2 ^ d
      let w := (P - m + P - now % P) % P
      if d = 0 then
        .query (w + P * K (a / 2)) (fun bit => .stop (if bit = 0 then a else m))
      else
        .query w (fun bit => delayedMidpoint P K d
          (if bit = 0 then a else m) (now + w))

private theorem midpoint_time_le_protocol {P : Nat} {read : Nat → Nat → Fin 2}
    (law : ∀ n r, r < P → read n r = threshold P n r) (d : Nat) :
    ∀ (p : Protocol (d + 1)) a now early,
      a + 2 ^ (d + 1) ≤ P → CorrectOn read p now a (2 ^ (d + 1)) →
      early ≤ now → ∀ r, a ≤ r → r < a + 2 ^ (d + 1) →
      (execute read (DyadicForwardWaitingOptimality.midpoint P (d + 1) a early) early r).2 ≤
        (execute read p now r).2 := by
  have first_phase (early actual w : Nat) (hP : 0 < P) (hw : w < P)
      (hbefore : early ≤ actual) (hphase : (early + w) % P = actual % P) :
      early + w ≤ actual := by
    by_contra hn
    have hlt : actual < early + w := by omega
    have hcong : actual ≡ early + w [MOD P] := hphase.symm
    obtain ⟨k, hk⟩ :=
      (Nat.modEq_iff_exists_eq_add (Nat.le_of_lt hlt)).mp hcong
    by_cases hz : k = 0
    · simp only [hz, mul_zero, add_zero] at hk
      omega
    · have hkp : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hz
      have hmul := Nat.mul_le_mul_left P hkp
      simp only [mul_one] at hmul
      omega
  have phase (a early k : Nat) (hi : a + 2 ^ (k + 1) ≤ P) :
      let m := a + 2 ^ k
      let w := (P - m + P - early % P) % P
      (early + w) % P = P - m := by
    dsimp only
    have hp := Nat.two_pow_pos k
    have hP : 0 < P := by omega
    have hn := Nat.mod_lt early hP
    have hm : 0 < a + 2 ^ k ∧ a + 2 ^ k < P := by
      have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
      omega
    have hmod : (P - (a + 2 ^ k) + P - early % P) + early % P =
        P - (a + 2 ^ k) + P := by omega
    rw [Nat.add_mod, Nat.add_mod_mod, Nat.add_comm, Nat.mod_add_mod,
      hmod, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  induction d with
  | zero =>
      intro p a now early hi hc hbefore r hlo hhi
      cases p with
      | stop answer =>
          have h0 := hc a (by omega) (by omega)
          have h1 := hc (a + 1) (by omega) (by omega)
          simp only [execute] at h0 h1
          omega
      | query wait next =>
          obtain ⟨cut, _, _⟩ := forced_midpoint next law hi hc
          let w := (P - (a + 1) + P - early % P) % P
          have hp : (early + w) % P = P - (a + 1) := by
            simpa only [w, pow_zero] using phase a early 0 hi
          have hactual : (now + wait) % P = P - (a + 1) := by
            have hm := Nat.mod_lt (now + wait) (by omega : 0 < P)
            simpa only [pow_zero] using (show (now + wait) % P = P - (a + 1) by omega)
          have hmin := first_phase early (now + wait) w (by omega)
            (Nat.mod_lt _ (by omega)) (by omega) (by rw [hp, hactual])
          change (execute read (.query w (fun bit =>
            DyadicForwardWaitingOptimality.midpoint P 0
              (if bit = 0 then a else a + 1) (early + w))) early r).2 ≤
            (execute read (.query wait next) now r).2
          simp only [execute, DyadicForwardWaitingOptimality.midpoint]
          cases next (read (now + wait) r) with
          | stop answer => simpa only [execute] using hmin
  | succ d ih =>
      intro p a now early hi hc hbefore r hlo hhi
      cases p with
      | stop answer =>
          have h0 := hc a (by omega) (by omega)
          have h1 := hc (a + 1) (by omega) (by omega)
          simp only [execute] at h0 h1
          omega
      | query wait next =>
          obtain ⟨cut, left, right⟩ := forced_midpoint next law hi hc
          let m := a + 2 ^ (d + 1)
          let w := (P - m + P - early % P) % P
          have hp : (early + w) % P = P - m := by
            simpa only [m, w] using phase a early (d + 1) (by simpa only [Nat.add_assoc] using hi)
          have hactual : (now + wait) % P = P - m := by
            have hm := Nat.mod_lt (now + wait) (by omega : 0 < P)
            dsimp [m]
            omega
          have hmin := first_phase early (now + wait) w (by omega)
            (Nat.mod_lt _ (by omega)) (by omega) (by rw [hp, hactual])
          have he : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by rw [pow_succ]; omega
          have earlyRead : read (early + w) r = if r < m then 0 else 1 := by
            rw [law _ _ (by omega), threshold, hp]
            dsimp [m]
            split_ifs <;> omega
          have actualRead : read (now + wait) r = if r < m then 0 else 1 := by
            rw [law _ _ (by omega), threshold, hactual]
            dsimp [m]
            split_ifs <;> omega
          change (execute read (DyadicForwardWaitingOptimality.midpoint P (d + 1)
            (if read (early + w) r = 0 then a else m) (early + w)) (early + w) r).2 ≤
            (execute read (next (read (now + wait) r)) (now + wait) r).2
          by_cases hr : r < m
          · rw [earlyRead, actualRead, if_pos hr, if_pos rfl]
            exact ih (next 0) a (now + wait) (early + w) (by omega) left hmin
              r hlo (by dsimp [m] at hr; omega)
          · rw [earlyRead, actualRead, if_neg hr,
              if_neg (by decide : (1 : Fin 2) ≠ 0)]
            exact ih (next 1) m (now + wait) (early + w) (by omega) (by
              dsimp [m] at *
              simpa only [show a + 2 ^ (d + 1) = m by rfl] using right) hmin
              r (by omega) (by omega)

theorem delayed_midpoint_execute (P : Nat) (K : Nat → Nat)
    (read : Nat → Nat → Fin 2)
    (periodic : ∀ n r k, r < P → read (n + P * k) r = read n r)
    (law : ∀ n r, r < P → read n r = threshold P n r)
    (d : Nat) : ∀ a now r, a % 2 = 0 → a + 2 ^ (d + 1) ≤ P →
      a ≤ r → r < a + 2 ^ (d + 1) →
      (execute read (delayedMidpoint P K (d + 1) a now) now r).1 =
        (execute read (DyadicForwardWaitingOptimality.midpoint P (d + 1) a now) now r).1 ∧
      (execute read (delayedMidpoint P K (d + 1) a now) now r).2 =
        (execute read (DyadicForwardWaitingOptimality.midpoint P (d + 1) a now) now r).2 +
          P * K (r / 2) := by
  induction d with
  | zero =>
      intro a now r ha hiP hlo hhi
      have hr : r / 2 = a / 2 := by omega
      simp only [delayedMidpoint, DyadicForwardWaitingOptimality.midpoint,
        pow_zero, ↓reduceIte, execute]
      rw [show now + ((P - (a + 1) + P - now % P) % P + P * K (a / 2)) =
        (now + (P - (a + 1) + P - now % P) % P) + P * K (a / 2) by omega,
        periodic _ _ _ (by omega)]
      simp only [hr]
      exact ⟨trivial, trivial⟩
  | succ d ih =>
      intro a now r ha hiP hlo hhi
      let m := a + 2 ^ (d + 1)
      let w := (P - m + P - now % P) % P
      have hm : m % 2 = 0 := by
        dsimp [m]
        have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
        omega
      have hP : 0 < P := by omega
      have phase : (now + w) % P = P - m := by
        have hn := Nat.mod_lt now hP
        have hmP : 0 < m ∧ m < P := by dsimp [m] at *; omega
        have hmod : (P - m + P - now % P) + now % P = P - m + P := by omega
        dsimp [w]
        rw [Nat.add_mod, Nat.add_mod_mod, Nat.add_comm, Nat.mod_add_mod,
          hmod, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have branch : read (now + w) r = if r < m then 0 else 1 := by
        rw [law _ _ (by omega), threshold, phase]
        dsimp [m]
        split_ifs <;> omega
      simp only [delayedMidpoint, DyadicForwardWaitingOptimality.midpoint,
        show d + 1 ≠ 0 by omega, ↓reduceIte, execute]
      change (execute read (delayedMidpoint P K (d + 1)
        (if read (now + w) r = 0 then a else m) (now + w)) (now + w) r).1 =
          (execute read (DyadicForwardWaitingOptimality.midpoint P (d + 1)
            (if read (now + w) r = 0 then a else m) (now + w)) (now + w) r).1 ∧
        (execute read (delayedMidpoint P K (d + 1)
          (if read (now + w) r = 0 then a else m) (now + w)) (now + w) r).2 =
          (execute read (DyadicForwardWaitingOptimality.midpoint P (d + 1)
            (if read (now + w) r = 0 then a else m) (now + w)) (now + w) r).2 +
            P * K (r / 2)
      by_cases hr : r < m
      · rw [branch, if_pos hr, if_pos rfl]
        exact ih a (now + w) r ha (by omega) hlo (by dsimp [m] at hr; omega)
      · rw [branch, if_neg hr, if_neg (by decide : (1 : Fin 2) ≠ 0)]
        exact ih m (now + w) r hm (by omega) (by omega) (by omega)

/-- One causal raw-bit controller realizes the entire nonnegative delay table;
the table is consulted only at the final query, after its pair is known. -/
theorem arbitrary_prefix_delay_table (d : Nat) (b : Fin 2) (K : Nat → Nat) :
    let P := 2 ^ (d + 1)
    ∃ p : Protocol (d + 1), CorrectOn (rawBit P b) p 0 0 P ∧
      ∀ t u, t < 2 ^ d → u < 2 →
        terminalTime P b p (2 * t + u) =
          (P - 1 + P * t.bitIndices.length - 2 * t) + P * K t := by
  dsimp only
  let P := 2 ^ (d + 1)
  let q := delayedMidpoint P K (d + 1) 0 0
  let p := transport P b q 0
  have law (n r : Nat) (hr : r < P) : sensor P b n r = threshold P n r :=
    ((dyadic_forward_waiting_optimality (d + 1) b).1 n r hr).2
  have periodic (n r k : Nat) (hr : r < P) :
      sensor P b (n + P * k) r = sensor P b n r := by
    rw [law _ _ hr, law _ _ hr]
    simp only [threshold, Nat.add_mul_mod_self_left]
  have compare (r : Nat) (hr : r < P) :=
    delayed_midpoint_execute P K (sensor P b) periodic law d 0 0 r
      (by decide) (by dsimp [P]; omega) (by omega) (by simpa [P] using hr)
  refine ⟨p, ?_, ?_⟩
  · intro r hlo hhi
    rw [show p = transport P b q 0 by rfl, (transport_execute P b q 0 r).1]
    rw [show q = delayedMidpoint P K (d + 1) 0 0 by rfl,
      (compare r (by simpa only [P, Nat.zero_add] using hhi)).1]
    have h := (dyadic_forward_waiting_optimality (d + 1) b).2.2.1 r hlo hhi
    rw [rawMidpoint,
      (transport_execute P b (DyadicForwardWaitingOptimality.midpoint P (d + 1) 0 0)
        0 r).1] at h
    exact h
  · intro t u ht hu
    have hr : 2 * t + u < P := by dsimp [P]; omega
    have hdiv : (2 * t + u) / 2 = t := by omega
    have he := (earliest_midpoint_terminal_time d b t u ht hu).1
    change terminalTime P b (rawMidpoint P b (d + 1)) (2 * t + u) =
      P - 1 + P * t.bitIndices.length - 2 * t at he
    change (execute (rawBit P b) p 0 (2 * t + u)).2 = _
    rw [show p = transport P b q 0 by rfl, (transport_execute P b q 0 _).1]
    rw [show q = delayedMidpoint P K (d + 1) 0 0 by rfl,
      (compare (2 * t + u) hr).2, hdiv]
    exact congrArg (fun n => n + P * K t) (by
      simpa only [terminalTime, rawMidpoint,
        (transport_execute P b (DyadicForwardWaitingOptimality.midpoint P (d + 1) 0 0)
          0 (2 * t + u)).1] using he)

/-- Every successful raw-bit controller has the earliest midpoint time plus
an integral number of periods on every prefix, for either final source bit. -/
theorem arbitrary_protocol_prefix_time (d : Nat) (b : Fin 2)
    (p : Protocol (d + 1))
    (hc : CorrectOn (rawBit (2 ^ (d + 1)) b) p 0 0 (2 ^ (d + 1)))
    (t u : Nat) (ht : t < 2 ^ d) (hu : u < 2) :
    let P := 2 ^ (d + 1)
    ∃ k : Nat, terminalTime P b p (2 * t + u) =
      (P - 1 + P * t.bitIndices.length - 2 * t) + P * k := by
  dsimp only
  let P := 2 ^ (d + 1)
  have law (n r : Nat) (hr : r < P) : sensor P b n r = threshold P n r :=
    ((dyadic_forward_waiting_optimality (d + 1) b).1 n r hr).2
  have decoded : CorrectOn (sensor P b) (transport P b p 0) 0 0 P := by
    intro r hlo hhi
    rw [(transport_execute P b p 0 r).2]
    exact hc r hlo hhi
  have hr : 2 * t + u < P := by dsimp [P]; omega
  have lower := midpoint_time_le_protocol law d (transport P b p 0) 0 0 0
    (by dsimp [P]; omega) decoded (by omega) (2 * t + u) (by omega)
      (by simpa only [P, Nat.zero_add] using hr)
  have lowerRaw : terminalTime P b (rawMidpoint P b (d + 1)) (2 * t + u) ≤
      terminalTime P b p (2 * t + u) := by
    simpa only [terminalTime, rawMidpoint,
      (transport_execute P b (DyadicForwardWaitingOptimality.midpoint P (d + 1) 0 0)
        0 (2 * t + u)).1,
      (transport_execute P b p 0 (2 * t + u)).2] using lower
  have correctEarly := (dyadic_forward_waiting_optimality (d + 1) b).2.2.1
  have phaseP := (terminal_pair_fiber_bijection_and_clock_injectivity d b p hc).1 t ht
  have phaseE := (terminal_pair_fiber_bijection_and_clock_injectivity d b
    (rawMidpoint P b (d + 1)) correctEarly).1 t ht
  have sourcePhase (q : Protocol (d + 1))
      (hpair : terminalTime P b q (2 * t) = terminalTime P b q (2 * t + 1) ∧
        terminalTime P b q (2 * t) % P = P - 1 - 2 * t) :
      terminalTime P b q (2 * t + u) % P = P - 1 - 2 * t := by
    have hu01 : u = 0 ∨ u = 1 := by omega
    rcases hu01 with rfl | rfl
    · simpa only [Nat.add_zero] using hpair.2
    · rw [← hpair.1]
      exact hpair.2
  have congruent : terminalTime P b (rawMidpoint P b (d + 1)) (2 * t + u) ≡
      terminalTime P b p (2 * t + u) [MOD P] := by
    exact (sourcePhase _ ⟨phaseE.1, phaseE.2.1⟩).trans
      (sourcePhase _ ⟨phaseP.1, phaseP.2.1⟩).symm
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add lowerRaw).mp congruent
  refine ⟨k, ?_⟩
  have he := (earliest_midpoint_terminal_time d b t u ht hu).1
  change terminalTime P b (rawMidpoint P b (d + 1)) (2 * t + u) =
    P - 1 + P * t.bitIndices.length - 2 * t at he
  rw [he] at hk
  change terminalTime P b p (2 * t + u) =
    (P - 1 + P * t.bitIndices.length - 2 * t) + P * k
  simpa only [Nat.mul_comm P k] using hk

/-- The hidden family contains exactly the successful raw controllers whose
actual last read meets the common deadline on every original source. -/
def deadlineFamily (d : Nat) (b : Fin 2) (D : Nat)
    (p : Protocol (d + 1)) : Prop :=
  let P := 2 ^ (d + 1)
  CorrectOn (rawBit P b) p 0 0 P ∧
    ∀ r, r < P → terminalTime P b p r ≤ D

/-- An impossible deadline has no successful controller. Above the sharp wait,
one causal tree realizes each permitted prefix time on both last-bit siblings.
An eligible prefix also gives two actual controllers and different sources with
the same uncorrected final bit. -/
theorem deadline_prefix_time_range_and_collision (d : Nat) (b : Fin 2) (D : Nat) :
    ((D < sharpWait (d + 1) →
      ¬ ∃ p : Protocol (d + 1), deadlineFamily d b D p) ∧
    (sharpWait (d + 1) ≤ D →
      ∀ t u k : Nat, t < 2 ^ d → u < 2 →
        ((∃ p : Protocol (d + 1), deadlineFamily d b D p ∧
          terminalTime (2 ^ (d + 1)) b p (2 * t + u) =
            (2 ^ (d + 1) - 1 + 2 ^ (d + 1) * t.bitIndices.length - 2 * t) +
              2 ^ (d + 1) * k) ↔
          (2 ^ (d + 1) - 1 + 2 ^ (d + 1) * t.bitIndices.length - 2 * t) +
            2 ^ (d + 1) * k ≤ D))) ∧
    (∀ t : Nat, t < 2 ^ d → sharpWait (d + 1) ≤ D →
      (2 ^ (d + 1) - 1 + 2 ^ (d + 1) * t.bitIndices.length - 2 * t) +
        2 ^ (d + 1) ≤ D →
      ∃ p₀ p₁ : Protocol (d + 1),
        deadlineFamily d b D p₀ ∧ deadlineFamily d b D p₁ ∧
        terminalTime (2 ^ (d + 1)) b p₁ (2 * t + 1) =
          terminalTime (2 ^ (d + 1)) b p₀ (2 * t) + 2 ^ (d + 1) ∧
        (terminalRecord (2 ^ (d + 1)) b p₀ (2 * t)).2 =
          (terminalRecord (2 ^ (d + 1)) b p₁ (2 * t + 1)).2) := by
  let P := 2 ^ (d + 1)
  have hsharp := (dyadic_forward_waiting_optimality (d + 1) b).2.1
  have hearly := (dyadic_forward_waiting_optimality (d + 1) b).2.2.2
  have range :
      (D < sharpWait (d + 1) →
        ¬ ∃ p : Protocol (d + 1), deadlineFamily d b D p) ∧
      (sharpWait (d + 1) ≤ D →
        ∀ t u k : Nat, t < 2 ^ d → u < 2 →
          ((∃ p : Protocol (d + 1), deadlineFamily d b D p ∧
            terminalTime P b p (2 * t + u) =
              (P - 1 + P * t.bitIndices.length - 2 * t) + P * k) ↔
            (P - 1 + P * t.bitIndices.length - 2 * t) + P * k ≤ D)) := by
    constructor
    · intro hD ⟨p, hp⟩
      have hmin := hsharp.2 ⟨p, hp.1, hp.2⟩
      omega
    · intro hD t u k ht hu
      constructor
      · rintro ⟨p, hp, htime⟩
        rw [← htime]
        exact hp.2 _ (by omega)
      · intro htime
        let K : Nat → Nat := fun v => if v = t then k else 0
        obtain ⟨p, hc, times⟩ := arbitrary_prefix_delay_table d b K
        refine ⟨p, ⟨hc, ?_⟩, ?_⟩
        · intro r hr
          have hq : r / 2 < 2 ^ d := by omega
          have hu' : r % 2 < 2 := Nat.mod_lt _ (by decide)
          have hsplit : 2 * (r / 2) + r % 2 = r := by omega
          have hactual := times (r / 2) (r % 2) hq hu'
          rw [hsplit] at hactual
          rw [hactual]
          by_cases hrt : r / 2 = t
          · simp only [K, if_pos hrt]
            simpa only [hrt, P] using htime
          · simp only [K, if_neg hrt, mul_zero, add_zero]
            have he := (earliest_midpoint_terminal_time d b (r / 2) (r % 2) hq hu').1
            have hb := hearly r (by simpa only [P] using hr)
            rw [hsplit] at he
            change terminalTime P b (rawMidpoint P b (d + 1)) r ≤
              sharpWait (d + 1) at hb
            rw [he] at hb
            exact hb.trans hD
        · simpa only [K, if_pos rfl, P] using times t u ht hu
  refine ⟨range, ?_⟩
  intro t ht hD helig
  have helig' : (P - 1 + P * t.bitIndices.length - 2 * t) + P * 1 ≤ D := by
    simpa only [P, mul_one] using helig
  have hbase : (P - 1 + P * t.bitIndices.length - 2 * t) + P * 0 ≤ D := by
    simp only [mul_zero, add_zero]
    exact le_trans (Nat.le_add_right _ _) (by simpa only [mul_one] using helig')
  obtain ⟨p₀, hp₀, htime₀⟩ := (range.2 hD t 0 0 ht (by decide)).2 hbase
  obtain ⟨p₁, hp₁, htime₁⟩ := (range.2 hD t 1 1 ht (by decide)).2 helig'
  have htime₀' : terminalTime P b p₀ (2 * t) =
      P - 1 + P * t.bitIndices.length - 2 * t := by
    simpa only [Nat.add_zero, mul_zero] using htime₀
  have pair₀ := (terminal_pair_fiber_bijection_and_clock_injectivity d b p₀ hp₀.1).1 t ht
  have pair₁ := (terminal_pair_fiber_bijection_and_clock_injectivity d b p₁ hp₁.1).1 t ht
  have hcycle : cycleCount P b p₁ t = cycleCount P b p₀ t + 1 := by
    change terminalTime P b p₁ (2 * t) / P = terminalTime P b p₀ (2 * t) / P + 1
    rw [pair₁.1, htime₁, htime₀']
    simpa only [mul_one] using
      (Nat.add_mul_div_left (P - 1 + P * t.bitIndices.length - 2 * t) 1
        (Nat.two_pow_pos (d + 1)))
  refine ⟨p₀, p₁, hp₀, hp₁, ?_, ?_⟩
  · rw [htime₀', htime₁]
    simp only [mul_one]
    rfl
  · apply Fin.ext
    have hbit₀ := pair₀.2.2 0 (by decide)
    have hbit₁ := pair₁.2.2 1 (by decide)
    change (terminalRecord P b p₀ (2 * t)).2.val =
      (b.val + cycleCount P b p₀ t + 0) % 2 at hbit₀
    change (terminalRecord P b p₁ (2 * t + 1)).2.val =
      (b.val + cycleCount P b p₁ t + 1) % 2 at hbit₁
    rw [hbit₀, hbit₁, hcycle]
    omega

/-- The delay parity is measured relative to the earliest time of the prefix. -/
def earliestTime (d t : Nat) : Nat :=
  2 ^ (d + 1) - 1 + 2 ^ (d + 1) * t.bitIndices.length - 2 * t

def clockTag (d n : Nat) : Fin (2 ^ d) × Fin 2 :=
  let P := 2 ^ (d + 1)
  let t := ((P - 1 - n % P) / 2) % (2 ^ d)
  (⟨t, Nat.mod_lt _ (Nat.two_pow_pos d)⟩,
   ⟨((n - earliestTime d t) / P) % 2, Nat.mod_lt _ (by decide)⟩)

/-- Count only labels of times reached by an actual deadline-family controller. -/
noncomputable def realizedTimes (d : Nat) (b : Fin 2) (D : Nat) :
    Finset Nat := by
  classical
  exact (Finset.range (D + 1)).filter (fun n =>
    ∃ p : Protocol (d + 1), deadlineFamily d b D p ∧
      ∃ r : Fin (2 ^ (d + 1)), terminalTime (2 ^ (d + 1)) b p r.val = n)

noncomputable def familyClockLabels {Z : Type*} (d : Nat) (b : Fin 2)
    (D : Nat) (phi : Nat → Z) : Finset Z := by
  classical
  exact (realizedTimes d b D).image phi

def eligiblePrefixes (d D : Nat) : Finset (Fin (2 ^ d)) :=
  Finset.univ.filter (fun t => earliestTime d t.val + 2 ^ (d + 1) ≤ D)

private def requiredTags (d D : Nat) : Finset (Fin (2 ^ d) × Fin 2) :=
  (Finset.univ.image (fun t : Fin (2 ^ d) => (t, 0))) ∪
    ((eligiblePrefixes d D).image (fun t => (t, 1)))

def tagDecode (d : Nat) (b : Fin 2)
    (z : Fin (2 ^ d) × Fin 2) (y : Fin 2) : Nat :=
  2 * z.1.val +
    (y.val + b.val + earliestTime d z.1.val / 2 ^ (d + 1) + z.2.val) % 2

/-- The operational minimum counts labels actually used by a universal
time-only encoder. The same decoder receives the uncorrected raw final bit for
every controller in the deadline family. -/
theorem deadline_family_operational_capacity (d : Nat) (b : Fin 2) (D : Nat) :
    (D < sharpWait (d + 1) →
      ¬ ∃ p : Protocol (d + 1), deadlineFamily d b D p) ∧
    (sharpWait (d + 1) ≤ D →
      (∀ (Z : Type*) (phi : Nat → Z) (recover : Z → Fin 2 → Nat),
        (∀ p : Protocol (d + 1), deadlineFamily d b D p →
          ∀ r, r < 2 ^ (d + 1) →
            recover (phi (terminalTime (2 ^ (d + 1)) b p r))
              (terminalRecord (2 ^ (d + 1)) b p r).2 = r) →
        2 ^ d + (eligiblePrefixes d D).card ≤
          (familyClockLabels d b D phi).card) ∧
      (∀ p : Protocol (d + 1), deadlineFamily d b D p →
        ∀ r, r < 2 ^ (d + 1) →
          tagDecode d b (clockTag d (terminalTime (2 ^ (d + 1)) b p r))
            (terminalRecord (2 ^ (d + 1)) b p r).2 = r) ∧
      (familyClockLabels d b D (clockTag d)).card =
        2 ^ d + (eligiblePrefixes d D).card) := by
  classical
  refine ⟨(deadline_prefix_time_range_and_collision d b D).1.1, ?_⟩
  intro hD
  have clockTag_actual
      (p : Protocol (d + 1))
      (hc : CorrectOn (rawBit (2 ^ (d + 1)) b) p 0 0 (2 ^ (d + 1)))
      (t k : Nat) (ht : t < 2 ^ d)
      (hn : terminalTime (2 ^ (d + 1)) b p (2 * t) =
        earliestTime d t + 2 ^ (d + 1) * k) :
      clockTag d (terminalTime (2 ^ (d + 1)) b p (2 * t)) =
        (⟨t, ht⟩, ⟨k % 2, Nat.mod_lt _ (by decide)⟩) := by
    let P := 2 ^ (d + 1)
    have hp : P = 2 * 2 ^ d := by dsimp [P]; rw [pow_succ]; omega
    have hphase :=
      (terminal_pair_fiber_bijection_and_clock_injectivity d b p hc).1 t ht |>.2.1
    change terminalTime P b p (2 * t) % P = P - 1 - 2 * t at hphase
    have hpre : (P - 1 - (terminalTime P b p (2 * t)) % P) / 2 = t := by
      rw [hphase]
      omega
    have hprefix : ((P - 1 - (terminalTime P b p (2 * t)) % P) / 2) %
        (2 ^ d) = t := by rw [hpre, Nat.mod_eq_of_lt ht]
    have hdelay : ((terminalTime P b p (2 * t) - earliestTime d t) / P) % 2 =
        k % 2 := by
      rw [hn]
      change ((earliestTime d t + P * k - earliestTime d t) / P) % 2 = k % 2
      rw [Nat.add_sub_cancel_left]
      exact congrArg (· % 2) (Nat.mul_div_cancel_left k (Nat.two_pow_pos (d + 1)))
    apply Prod.ext
    · apply Fin.ext
      exact hprefix
    · apply Fin.ext
      simpa only [clockTag, P, hprefix] using hdelay
  have requiredTags_card :
      (requiredTags d D).card = 2 ^ d + (eligiblePrefixes d D).card := by
    classical
    unfold requiredTags
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective, Finset.card_image_of_injective]
      · simp
      · intro x y h
        exact Prod.mk.inj h |>.1
      · intro x y h
        exact Prod.mk.inj h |>.1
    · apply Finset.disjoint_left.mpr
      intro z hz hw
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨s, _, h⟩ := Finset.mem_image.mp hw
      exact Fin.zero_ne_one (congrArg Prod.snd h.symm)
  have realizedTags_eq_required :
      (realizedTimes d b D).image (clockTag d) = requiredTags d D := by
    classical
    let P := 2 ^ (d + 1)
    have hP : P = 2 * 2 ^ d := by dsimp [P]; rw [pow_succ]; omega
    have range := (deadline_prefix_time_range_and_collision d b D).1.2 hD
    have earlyBound (t : Nat) (ht : t < 2 ^ d) : earliestTime d t ≤ D := by
      have h := (dyadic_forward_waiting_optimality (d + 1) b).2.2.2 (2 * t)
        (by dsimp [P] at hP ⊢; omega)
      have he := (earliest_midpoint_terminal_time d b t 0 ht (by decide)).1
      change terminalTime P b (rawMidpoint P b (d + 1)) (2 * t) =
        earliestTime d t at he
      change terminalTime P b (rawMidpoint P b (d + 1)) (2 * t) ≤
        sharpWait (d + 1) at h
      rw [he] at h
      exact h.trans hD
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hbound, p, ⟨hc, hd⟩, r, htime⟩ := by
        simpa only [realizedTimes, Finset.mem_filter, Finset.mem_range] using hn
      let t := r.val / 2
      let u := r.val % 2
      have ht : t < 2 ^ d := by dsimp [t]; have := r.isLt; omega
      have hu : u < 2 := Nat.mod_lt _ (by decide)
      have hr : 2 * t + u = r.val := by dsimp [t, u]; omega
      obtain ⟨k, hk⟩ := arbitrary_protocol_prefix_time d b p hc t u ht hu
      change terminalTime P b p (2 * t + u) = earliestTime d t + P * k at hk
      have siblings := (terminal_pair_fiber_bijection_and_clock_injectivity d b p hc).1 t ht |>.1
      have hn' : terminalTime P b p (2 * t) = earliestTime d t + P * k := by
        rcases (show u = 0 ∨ u = 1 by omega) with h | h
        · simpa only [h, Nat.add_zero] using hk
        · have hk1 : terminalTime P b p (2 * t + 1) = earliestTime d t + P * k := by
            simpa only [h] using hk
          exact siblings.trans hk1
      have htag := clockTag_actual p hc t k ht hn'
      have hclock : clockTag d n =
          (⟨t, ht⟩, ⟨k % 2, Nat.mod_lt _ (by decide)⟩) := by
        rw [← htime, ← hr]
        rcases (show u = 0 ∨ u = 1 by omega) with h | h
        · simpa only [h, Nat.add_zero] using htag
        · simpa only [h, ← siblings] using htag
      rw [hclock]
      rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with hk0 | hk1
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨⟨t, ht⟩, Finset.mem_univ _, by simp [hk0]⟩
      · have hkpos : 1 ≤ k := by omega
        have hmul : P ≤ P * k := by
          simpa only [mul_one] using Nat.mul_le_mul_left P hkpos
        have helig : earliestTime d t + P ≤ D := by
          have := hd r.val r.isLt
          rw [← hr, hk] at this
          omega
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨⟨t, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, helig⟩,
          by simp [hk1]⟩
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
        have he := earlyBound t.val t.isLt
        obtain ⟨p, hp, htime⟩ :=
          (range t.val 0 0 t.isLt (by decide)).2 (by simpa [earliestTime, P] using he)
        have hn : earliestTime d t.val ∈ realizedTimes d b D := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr (by omega), p, hp,
            ⟨2 * t.val, by have := t.isLt; omega⟩, ?_⟩
          simpa [earliestTime, P] using htime
        apply Finset.mem_image.mpr
        refine ⟨earliestTime d t.val, hn, ?_⟩
        have htag := clockTag_actual p hp.1 t.val 0 t.isLt (by
          simpa [earliestTime, P] using htime)
        rw [show terminalTime P b p (2 * t.val) = earliestTime d t.val by
          simpa [earliestTime, P] using htime] at htag
        simpa using htag
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
        have helig := (Finset.mem_filter.mp ht).2
        obtain ⟨p, hp, htime⟩ :=
          (range t.val 0 1 t.isLt (by decide)).2 (by simpa [earliestTime, P] using helig)
        have hn : earliestTime d t.val + P ∈ realizedTimes d b D := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr (by omega), p, hp,
            ⟨2 * t.val, by have := t.isLt; omega⟩, ?_⟩
          simpa [earliestTime, P] using htime
        apply Finset.mem_image.mpr
        refine ⟨earliestTime d t.val + P, hn, ?_⟩
        have htag := clockTag_actual p hp.1 t.val 1 t.isLt (by
          simpa [earliestTime, P] using htime)
        rw [show terminalTime P b p (2 * t.val) = earliestTime d t.val + P by
          simpa [earliestTime, P] using htime] at htag
        simpa [Nat.one_mod] using htag
  have clockTag_common_decoder
      (p : Protocol (d + 1))
      (hc : CorrectOn (rawBit (2 ^ (d + 1)) b) p 0 0 (2 ^ (d + 1)))
      (r : Nat) (hr : r < 2 ^ (d + 1)) :
      tagDecode d b (clockTag d (terminalTime (2 ^ (d + 1)) b p r))
        (terminalRecord (2 ^ (d + 1)) b p r).2 = r := by
    let P := 2 ^ (d + 1)
    let t := r / 2
    let u := r % 2
    have ht : t < 2 ^ d := by
      dsimp [t, P] at *
      omega
    have hu : u < 2 := Nat.mod_lt _ (by decide)
    have hsplit : 2 * t + u = r := by dsimp [t, u]; omega
    obtain ⟨k, hk⟩ := arbitrary_protocol_prefix_time d b p hc t u ht hu
    change terminalTime P b p (2 * t + u) = earliestTime d t + P * k at hk
    have pair := (terminal_pair_fiber_bijection_and_clock_injectivity d b p hc).1 t ht
    have htime : terminalTime P b p (2 * t) = earliestTime d t + P * k := by
      rcases (show u = 0 ∨ u = 1 by omega) with h | h
      · simpa only [h, Nat.add_zero] using hk
      · have hk1 : terminalTime P b p (2 * t + 1) = earliestTime d t + P * k := by
          simpa only [h] using hk
        exact pair.1.trans hk1
    have htag := clockTag_actual p hc t k ht htime
    have hactual : clockTag d (terminalTime P b p r) =
        (⟨t, ht⟩, ⟨k % 2, Nat.mod_lt _ (by decide)⟩) := by
      rw [← hsplit]
      rcases (show u = 0 ∨ u = 1 by omega) with h | h
      · simpa only [h, Nat.add_zero] using htag
      · rw [h, ← pair.1]
        exact htag
    have hcycle : cycleCount P b p t = earliestTime d t / P + k := by
      change terminalTime P b p (2 * t) / P = _
      rw [htime]
      exact Nat.add_mul_div_left (earliestTime d t) k (Nat.two_pow_pos (d + 1))
    have hbit := pair.2.2 u hu
    change (terminalRecord P b p (2 * t + u)).2.val =
      (b.val + cycleCount P b p t + u) % 2 at hbit
    rw [hsplit] at hbit
    rw [hactual]
    change 2 * t +
      ((terminalRecord P b p r).2.val + b.val + earliestTime d t / P + k % 2) % 2 = r
    rw [hbit, hcycle]
    have hb := b.isLt
    omega
  have htags := realizedTags_eq_required
  have hcard := requiredTags_card
  refine ⟨?_, ?_, ?_⟩
  · intro Z phi recover hrec
    have common_decoder_separates_tags
        {n m : Nat} (hn : n ∈ realizedTimes d b D)
        (hm : m ∈ realizedTimes d b D) (hphi : phi n = phi m) :
        clockTag d n = clockTag d m := by
      let P := 2 ^ (d + 1)
      have hp : P = 2 * 2 ^ d := by dsimp [P]; rw [pow_succ]; omega
      obtain ⟨_, p, hfamily, r, hrn⟩ := by
        simpa only [realizedTimes, Finset.mem_filter, Finset.mem_range] using hn
      obtain ⟨_, q, gfamily, s, hsm⟩ := by
        simpa only [realizedTimes, Finset.mem_filter, Finset.mem_range] using hm
      let t := r.val / 2
      let v := s.val / 2
      have ht : t < 2 ^ d := by dsimp [t]; have := r.isLt; omega
      have hv : v < 2 ^ d := by dsimp [v]; have := s.isLt; omega
      have pairp :=
        (terminal_pair_fiber_bijection_and_clock_injectivity d b p hfamily.1).1 t ht
      have pairq :=
        (terminal_pair_fiber_bijection_and_clock_injectivity d b q gfamily.1).1 v hv
      have timep : terminalTime P b p (2 * t) = n := by
        have hu : r.val % 2 = 0 ∨ r.val % 2 = 1 := by omega
        rcases hu with hu | hu
        · have he : 2 * t = r.val := by dsimp [t]; omega
          rw [he]
          exact hrn
        · have he : 2 * t + 1 = r.val := by dsimp [t]; omega
          rw [pairp.1, he]
          exact hrn
      have timeq : terminalTime P b q (2 * v) = m := by
        have hu : s.val % 2 = 0 ∨ s.val % 2 = 1 := by omega
        rcases hu with hu | hu
        · have he : 2 * v = s.val := by dsimp [v]; omega
          rw [he]
          exact hsm
        · have he : 2 * v + 1 = s.val := by dsimp [v]; omega
          rw [pairq.1, he]
          exact hsm
      let u := (b.val + cycleCount P b p t) % 2
      let w := (b.val + cycleCount P b q v) % 2
      have hu : u < 2 := Nat.mod_lt _ (by decide)
      have hw : w < 2 := Nat.mod_lt _ (by decide)
      have zeroP : (terminalRecord P b p (2 * t + u)).2 = 0 := by
        apply Fin.ext
        have hbit : (terminalRecord P b p (2 * t + u)).2.val =
            (b.val + cycleCount P b p t + u) % 2 := pairp.2.2 u hu
        rw [hbit]
        dsimp [u]
        omega
      have zeroQ : (terminalRecord P b q (2 * v + w)).2 = 0 := by
        apply Fin.ext
        have hbit : (terminalRecord P b q (2 * v + w)).2.val =
            (b.val + cycleCount P b q v + w) % 2 := pairq.2.2 w hw
        rw [hbit]
        dsimp [w]
        omega
      have sourceEq : 2 * t + u = 2 * v + w := by
        have hfirst := hrec p hfamily (2 * t + u) (by have := r.isLt; dsimp [t]; omega)
        have hsecond := hrec q gfamily (2 * v + w) (by have := s.isLt; dsimp [v]; omega)
        have htp : terminalTime P b p (2 * t + u) = n := by
          rcases (show u = 0 ∨ u = 1 by omega) with h | h
          · rw [h]; simpa only [Nat.add_zero] using timep
          · rw [h, ← pairp.1]; exact timep
        have htq : terminalTime P b q (2 * v + w) = m := by
          rcases (show w = 0 ∨ w = 1 by omega) with h | h
          · rw [h]; simpa only [Nat.add_zero] using timeq
          · rw [h, ← pairq.1]; exact timeq
        rw [htp, zeroP] at hfirst
        rw [htq, zeroQ] at hsecond
        rw [hphi, hsecond] at hfirst
        exact hfirst.symm
      have tv : t = v := by omega
      have uw : u = w := by omega
      obtain ⟨k, hk⟩ := arbitrary_protocol_prefix_time d b p hfamily.1 t 0 ht (by decide)
      obtain ⟨l, hl⟩ := arbitrary_protocol_prefix_time d b q gfamily.1 v 0 hv (by decide)
      change terminalTime P b p (2 * t) = earliestTime d t + P * k at hk
      change terminalTime P b q (2 * v) = earliestTime d v + P * l at hl
      have tagp := clockTag_actual p hfamily.1 t k ht hk
      have tagq := clockTag_actual q gfamily.1 v l hv hl
      rw [timep] at tagp
      rw [timeq] at tagq
      have cyclesp : cycleCount P b p t = earliestTime d t / P + k := by
        change terminalTime P b p (2 * t) / P = _
        rw [hk]
        exact Nat.add_mul_div_left (earliestTime d t) k (Nat.two_pow_pos (d + 1))
      have cyclesq : cycleCount P b q v = earliestTime d v / P + l := by
        change terminalTime P b q (2 * v) / P = _
        rw [hl]
        exact Nat.add_mul_div_left (earliestTime d v) l (Nat.two_pow_pos (d + 1))
      have kl : k % 2 = l % 2 := by
        dsimp [u, w] at uw
        rw [cyclesp, cyclesq, ← tv] at uw
        omega
      rw [tagp, tagq]
      exact Prod.ext (Fin.ext tv) (Fin.ext kl)
    let labels := familyClockLabels d b D phi
    have chooseTime (z : Z) (hz : z ∈ labels) :
        ∃ n ∈ realizedTimes d b D, phi n = z := by
      simpa only [labels, familyClockLabels] using Finset.mem_image.mp hz
    let pick (z : Z) : Nat :=
      if hz : z ∈ labels then Classical.choose (chooseTime z hz) else 0
    have pick_mem (z : Z) (hz : z ∈ labels) : pick z ∈ realizedTimes d b D := by
      simpa only [pick, dif_pos hz] using (Classical.choose_spec (chooseTime z hz)).1
    have pick_phi (z : Z) (hz : z ∈ labels) : phi (pick z) = z := by
      simpa only [pick, dif_pos hz] using (Classical.choose_spec (chooseTime z hz)).2
    let toTag : Z → Fin (2 ^ d) × Fin 2 := fun z => clockTag d (pick z)
    have surj : Set.SurjOn toTag labels ((realizedTimes d b D).image (clockTag d)) := by
      intro tag htag
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp htag
      have hz : phi n ∈ labels := Finset.mem_image.mpr ⟨n, hn, rfl⟩
      refine ⟨phi n, hz, ?_⟩
      exact common_decoder_separates_tags
        (pick_mem (phi n) hz) hn (pick_phi (phi n) hz)
    have bound := Finset.card_le_card_of_surjOn toTag surj
    rw [htags, hcard] at bound
    exact bound
  · intro p hp r hr
    exact clockTag_common_decoder p hp.1 r hr
  · have hlabels : familyClockLabels d b D (clockTag d) = requiredTags d D := by
      ext z
      simpa only [familyClockLabels, Finset.mem_image] using
        (Finset.ext_iff.mp htags z)
    exact (congrArg (fun s : Finset (Fin (2 ^ d) × Fin 2) => s.card) hlabels).trans hcard

#print axioms midpoint_time_le_protocol
#print axioms delayed_midpoint_execute
#print axioms arbitrary_prefix_delay_table
#print axioms arbitrary_protocol_prefix_time
#print axioms deadline_prefix_time_range_and_collision
#print axioms deadline_family_operational_capacity

end D5.S3.Observer.Budget.DyadicPrefixDelayRange

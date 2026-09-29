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

#print axioms midpoint_time_le_protocol
#print axioms delayed_midpoint_execute
#print axioms arbitrary_prefix_delay_table
#print axioms arbitrary_protocol_prefix_time
#print axioms deadline_prefix_time_range_and_collision

end D5.S3.Observer.Budget.DyadicPrefixDelayRange

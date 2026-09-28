/- GID: D5/S3/Observer/Budget/TerminalClockCompression
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/TerminalClockCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Successful dyadic sensor protocols have a sharp terminal clock encoding. -/

import D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
import Mathlib.Data.Nat.BitIndices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.TerminalClockCompression

open DyadicForwardWaitingOptimality
open private forced_midpoint transport_execute from
  D5.S3.Observer.Budget.DyadicForwardWaitingOptimality

/-- Elapsed time at the final query of the actual raw-bit controller. -/
def terminalTime (P : Nat) (b : Fin 2) {j : Nat} (p : Protocol j) (r : Nat) : Nat :=
  (execute (rawBit P b) p 0 r).2

/-- The quotient is computed from the known schedule, at the even sibling. -/
def cycleCount (P : Nat) (b : Fin 2) {j : Nat} (p : Protocol j) (t : Nat) : Nat :=
  terminalTime P b p (2 * t) / P

/-- The receiver sees the latched phase and final uncorrected sensor bit. -/
def terminalRecord (P : Nat) (b : Fin 2) {j : Nat} (p : Protocol j) (r : Nat) :
    Nat × Fin 2 :=
  (terminalTime P b p r % P, rawBit P b (terminalTime P b p r) r)

/-- Addition and subtraction of the known correction coincide modulo two. -/
def decode (P : Nat) (b : Fin 2) {j : Nat} (p : Protocol j) (s : Nat) (y : Fin 2) : Nat :=
  let t := (P - 1 - s) / 2
  2 * t + (y.val + b.val + cycleCount P b p t) % 2

/-- A successful threshold controller reaches one final query for each adjacent
pair, whose phase is forced by the two remaining possible sources. -/
private theorem terminal_siblings {P : Nat} {read : Nat → Nat → Fin 2}
    (law : ∀ n r, r < P → read n r = threshold P n r) (d : Nat) :
    ∀ (p : Protocol (d + 1)) a now,
    a % 2 = 0 → a + 2 ^ (d + 1) ≤ P →
    CorrectOn read p now a (2 ^ (d + 1)) →
    ∀ t, a ≤ 2 * t → 2 * t < a + 2 ^ (d + 1) →
    (execute read p now (2 * t)).2 = (execute read p now (2 * t + 1)).2 ∧
    (execute read p now (2 * t)).2 % P = P - 1 - 2 * t := by
  induction d with
  | zero =>
    intro p a now ha hi hc t hlo hhi
    have he : 2 * t = a := by omega
    cases p with
    | stop answer =>
      have h0 := hc a (by omega) (by norm_num)
      have h1 := hc (a + 1) (by omega) (by omega)
      simp only [execute] at h0 h1
      omega
    | query wait next =>
      obtain ⟨cut, _, _⟩ := forced_midpoint next law hi hc
      have hP : 0 < P := by omega
      have hm := Nat.mod_lt (now + wait) hP
      have time (r : Nat) : (execute read (.query wait next) now r).2 = now + wait := by
        simp only [execute]
        cases next (read (now + wait) r) with
        | stop _ => rfl
      rw [time, time]
      simp only [pow_zero] at cut
      exact ⟨rfl, by omega⟩
  | succ d ih =>
    intro p a now ha hi hc t hlo hhi
    have hd : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
    have he : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by rw [pow_succ]; omega
    have hpos := Nat.two_pow_pos d
    cases p with
    | stop answer =>
      have h0 := hc a (by omega) (by omega)
      have h1 := hc (a + 1) (by omega) (by omega)
      simp only [execute] at h0 h1
      omega
    | query wait next =>
      obtain ⟨cut, left, right⟩ := forced_midpoint next law hi hc
      by_cases ht : 2 * t < a + 2 ^ (d + 1)
      · have hread (u : Nat) (hu : u < 2) : read (now + wait) (2 * t + u) = 0 := by
          rw [law _ _ (by omega), threshold, cut, if_pos (by omega)]
        have h0 : read (now + wait) (2 * t) = 0 := by simpa using hread 0 (by decide)
        simpa only [execute, h0, hread 1 (by decide)] using
          ih (next 0) a (now + wait) ha (by omega) left t hlo ht
      · have hread (u : Nat) (hu : u < 2) : read (now + wait) (2 * t + u) = 1 := by
          rw [law _ _ (by omega), threshold, cut, if_neg (by omega)]
        have h0 : read (now + wait) (2 * t) = 1 := by simpa using hread 0 (by decide)
        simpa only [execute, h0, hread 1 (by decide)] using
          ih (next 1) (a + 2 ^ (d + 1)) (now + wait) (by omega)
            (by omega) right t (by omega) (by omega)


/-- Only labels attained on an actual source are counted. -/
noncomputable def clockLabels {Z : Type*} (P : Nat) (b : Fin 2) {j : Nat}
    (p : Protocol j) (phi : Nat → Z) : Finset Z := by
  classical
  exact Finset.univ.image (fun r : Fin P => phi (terminalTime P b p r.val))

/-- A known successful minimum-query controller has an invertible terminal pair;
the attained phase alphabet is the smallest possible clock alphabet. -/
theorem terminal_pair_fiber_bijection_and_clock_injectivity (d : Nat) (b : Fin 2)
    (p : Protocol (d + 1)) (hc : CorrectOn (rawBit (2 ^ (d + 1)) b) p 0 0 (2 ^ (d + 1))) :
    let P := 2 ^ (d + 1)
    (∀ t, t < 2 ^ d →
      terminalTime P b p (2 * t) = terminalTime P b p (2 * t + 1) ∧
      terminalTime P b p (2 * t) % P = P - 1 - 2 * t ∧
      ∀ u, u < 2 →
        (terminalRecord P b p (2 * t + u)).2.val = (b.val + cycleCount P b p t + u) % 2) ∧
    (∀ r, r < P → decode P b p (terminalRecord P b p r).1
      (terminalRecord P b p r).2 = r) ∧
    Set.BijOn (terminalRecord P b p) {r | r < P}
      {sy | sy.1 < P ∧ sy.1 % 2 = 1} ∧
    (clockLabels P b p (fun n => n % P)).card = 2 ^ d ∧
    (∀ (Z : Type) (phi : Nat → Z) (recover : Z → Fin 2 → Nat),
      (∀ r, r < P → recover (phi (terminalTime P b p r)) (terminalRecord P b p r).2 = r) →
      2 ^ d ≤ (clockLabels P b p phi).card) := by
  classical
  dsimp only
  let P := 2 ^ (d + 1)
  have hP : P = 2 * 2 ^ d := by dsimp [P]; rw [pow_succ]; omega
  have hpos := Nat.two_pow_pos d
  have lawP (n r : Nat) (hr : r < P) : sensor P b n r = threshold P n r := by
    have h := (dyadic_forward_waiting_optimality (d + 1) b).1 n r (by simpa [P] using hr)
    simpa [P] using h.2
  have rawlawP (n r : Nat) (hr : r < P) :
      (rawBit P b n r).val = (b.val + n / P + (threshold P n r).val) % 2 := by
    have h := (dyadic_forward_waiting_optimality (d + 1) b).1 n r (by simpa [P] using hr)
    simpa [P] using h.1
  have trans (r : Nat) :
      execute (sensor P b) (transport P b p 0) 0 r = execute (rawBit P b) p 0 r := by
    exact (transport_execute P b p 0 r).2
  have hcorrect : CorrectOn (sensor P b) (transport P b p 0) 0 0 P := by
    intro r hlo hhi
    rw [trans]
    exact hc r hlo hhi
  have siblings (t : Nat) (ht : t < 2 ^ d) :
      terminalTime P b p (2 * t) = terminalTime P b p (2 * t + 1) ∧
      terminalTime P b p (2 * t) % P = P - 1 - 2 * t := by
    have h := terminal_siblings (P := P) lawP d
      (transport P b p 0) 0 0 (by decide) (by dsimp [P]; omega)
      hcorrect t (by omega) (by dsimp [P] at hP ⊢; omega)
    rw [trans, trans] at h
    exact h
  have time (t u : Nat) (ht : t < 2 ^ d) (hu : u < 2) :
      terminalTime P b p (2 * t + u) = terminalTime P b p (2 * t) := by
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
    · simp
    · exact (siblings t ht).1.symm
  have phase (t u : Nat) (ht : t < 2 ^ d) (hu : u < 2) :
      (terminalRecord P b p (2 * t + u)).1 = P - 1 - 2 * t := by
    exact (congrArg (· % P) (time t u ht hu)).trans (siblings t ht).2
  have bit (t u : Nat) (ht : t < 2 ^ d) (hu : u < 2) :
      (terminalRecord P b p (2 * t + u)).2.val = (b.val + cycleCount P b p t + u) % 2 := by
    change (rawBit P b (terminalTime P b p (2 * t + u)) (2 * t + u)).val = _
    rw [time t u ht hu, rawlawP _ _ (by omega)]
    have cut : (threshold P (terminalTime P b p (2 * t)) (2 * t + u)).val = u := by
      unfold threshold
      rw [(siblings t ht).2]
      split_ifs <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
    rw [cut]
    rfl
  have inverse (r : Nat) (hr : r < P) :
      decode P b p (terminalRecord P b p r).1 (terminalRecord P b p r).2 = r := by
    have ht : r / 2 < 2 ^ d := by have := hP; omega
    have hu : r % 2 < 2 := Nat.mod_lt _ (by decide)
    have decomp : 2 * (r / 2) + r % 2 = r := by omega
    have hs := phase (r / 2) (r % 2) ht hu
    have hb := bit (r / 2) (r % 2) ht hu
    rw [decomp] at hs hb
    unfold decode
    rw [hs, show (P - 1 - (P - 1 - 2 * (r / 2))) / 2 = r / 2 by omega, hb]
    dsimp
    have hmod : (((b.val + cycleCount P b p (r / 2) + r % 2) % 2 +
        b.val + cycleCount P b p (r / 2)) % 2) = r % 2 := by
      rw [Nat.add_mod, Nat.add_mod]
      omega
    rw [hmod]
    omega
  have onto (s : Nat) (y : Fin 2) (hs : s < P) (ho : s % 2 = 1) :
      ∃ r, r < P ∧ terminalRecord P b p r = (s, y) := by
    let t := (P - 1 - s) / 2
    let u := (y.val + b.val + cycleCount P b p t) % 2
    have ht : t < 2 ^ d := by dsimp [t]; have := hP; omega
    have hu : u < 2 := Nat.mod_lt _ (by decide)
    refine ⟨2 * t + u, by omega, Prod.ext ?_ ?_⟩
    · rw [phase t u ht hu]
      dsimp [t]
      omega
    · apply Fin.ext
      rw [bit t u ht hu]
      have hy := y.isLt
      dsimp [u]
      omega
  have phase_labels : clockLabels P b p (fun n => n % P) =
      Finset.univ.image (fun t : Fin (2 ^ d) => P - 1 - 2 * t.val) := by
    ext s
    simp only [clockLabels, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, rfl⟩
      have hr : r.val / 2 < 2 ^ d := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
        have hp := hP
        have hr' := r.isLt
        omega
      refine ⟨⟨r.val / 2, hr⟩, ?_⟩
      have h := phase (r.val / 2) (r.val % 2) hr
        (Nat.mod_lt _ (by decide))
      have decomp : 2 * (r.val / 2) + r.val % 2 = r.val := by omega
      rw [decomp] at h
      exact h.symm
    · rintro ⟨t, rfl⟩
      refine ⟨⟨2 * t.val, by have := t.isLt; have hp := hP; omega⟩,
        (siblings t.val t.isLt).2⟩
  refine ⟨fun t ht => ⟨(siblings t ht).1, (siblings t ht).2, fun u hu => bit t u ht hu⟩,
    inverse, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    change r < P at hr
    have ht : r / 2 < 2 ^ d := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
      have hp := hP
      omega
    have hs := phase (r / 2) (r % 2) ht (Nat.mod_lt _ (by decide))
    have decomp : 2 * (r / 2) + r % 2 = r := by omega
    rw [decomp] at hs
    change (terminalRecord P b p r).1 < P ∧ (terminalRecord P b p r).1 % 2 = 1
    rw [hs]
    have hform : P - 1 - 2 * (r / 2) = 2 * (2 ^ d - 1 - r / 2) + 1 := by
      rw [hP]
      omega
    rw [hform]
    constructor
    · have hp := hP
      omega
    · simp [Nat.add_mod]
  · intro r hr s hs eq
    have hi := inverse r hr
    rw [eq, inverse s hs] at hi
    exact hi.symm
  · rintro ⟨s, y⟩ ⟨hs, ho⟩
    exact onto s y hs ho
  · rw [phase_labels, Finset.card_image_of_injective]
    · simp
    · intro x y h
      apply Fin.ext
      change P - 1 - 2 * x.val = P - 1 - 2 * y.val at h
      have hx := x.isLt
      have hy := y.isLt
      have hp := hP
      have hx' : 2 * x.val ≤ P - 1 := by omega
      have hy' : 2 * y.val ≤ P - 1 := by omega
      have hxrec : P - 1 = (P - 1 - 2 * x.val) + 2 * x.val :=
        (Nat.sub_add_cancel hx').symm
      have hyrec : P - 1 = (P - 1 - 2 * y.val) + 2 * y.val :=
        (Nat.sub_add_cancel hy').symm
      have hxy : 2 * x.val = 2 * y.val := by omega
      omega
  · intro Z phi recover hrec
    let label (t : Fin (2 ^ d)) := phi (terminalTime P b p (2 * t.val))
    have inj : Function.Injective label := by
      intro t v heq
      let u := (b.val + cycleCount P b p t.val) % 2
      let w := (b.val + cycleCount P b p v.val) % 2
      have hu : u < 2 := Nat.mod_lt _ (by decide)
      have hw : w < 2 := Nat.mod_lt _ (by decide)
      have zero_t : (terminalRecord P b p (2 * t.val + u)).2 = 0 := by
        apply Fin.ext
        rw [bit _ _ t.isLt hu]
        dsimp [u]; omega
      have zero_v : (terminalRecord P b p (2 * v.val + w)).2 = 0 := by
        apply Fin.ext
        rw [bit _ _ v.isLt hw]
        dsimp [w]; omega
      have ht := hrec (2 * t.val + u) (by have := t.isLt; omega)
      have hv := hrec (2 * v.val + w) (by have := v.isLt; omega)
      rw [time _ _ t.isLt hu, zero_t] at ht
      rw [time _ _ v.isLt hw, zero_v] at hv
      change label t = label v at heq
      change recover (label t) 0 = _ at ht
      change recover (label v) 0 = _ at hv
      rw [heq, hv] at ht
      apply Fin.ext
      omega
    have sub : Finset.univ.image label ⊆ clockLabels P b p phi := by
      intro z hz
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_image.mpr
      exact ⟨⟨2 * t.val, by have := t.isLt; omega⟩, Finset.mem_univ _, rfl⟩
    have bound := Finset.card_le_card sub
    rw [Finset.card_image_of_injective _ inj] at bound
    simpa using bound



/-- The earliest midpoint controller determines its period correction by the
binary weight of the recovered prefix, for both possible final source bits. -/
theorem earliest_midpoint_terminal_time (d : Nat) (b : Fin 2) (t u : Nat)
    (ht : t < 2 ^ d) (hu : u < 2) :
    let P := 2 ^ (d + 1)
    let p := rawMidpoint P b (d + 1)
    terminalTime P b p (2 * t + u) = P - 1 + P * t.bitIndices.length - 2 * t ∧
    cycleCount P b p t = t.bitIndices.length := by
  have weight (k t : Nat) (ht : t < 2 ^ k) :
      (2 ^ k + t).bitIndices.length = t.bitIndices.length + 1 := by
    induction k generalizing t with
    | zero =>
      have ht0 : t = 0 := by simpa using ht
      subst t
      norm_num [Nat.bitIndices]
    | succ k ih =>
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
      have hq : t / 2 < 2 ^ k := by omega
      have hh := ih (t / 2) hq
      rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with h | h
      · have he : t = 2 * (t / 2) := by omega
        rw [he, hp, ← Nat.mul_add, Nat.bitIndices_two_mul, Nat.bitIndices_two_mul]
        simpa using hh
      · have he : t = 2 * (t / 2) + 1 := by omega
        have he' : 2 ^ (k + 1) + t = 2 * (2 ^ k + t / 2) + 1 := by omega
        rw [he', Nat.bitIndices_two_mul_add_one, he, Nat.bitIndices_two_mul_add_one]
        simp only [List.length_cons, List.length_map]
        have hdiv : (2 * (t / 2) + 1) / 2 = t / 2 := by omega
        rw [hdiv]
        rw [hh]
  have exact_time {P : Nat} {read : Nat → Nat → Fin 2}
      (law : ∀ n r, r < P → read n r = threshold P n r) (k : Nat) :
      ∀ a now t u, a + 2 ^ (k + 1) ≤ P → t < 2 ^ k → u < 2 →
      (execute read (midpoint P (k + 1) a now) now (a + 2 * t + u)).2 + 2 * t =
        (now + (P - (a + 2 ^ k) + P - now % P) % P) +
          (2 ^ k - 1) + P * t.bitIndices.length := by
    induction k with
    | zero =>
      intro a now t u hi ht hu
      have ht0 : t = 0 := by simpa using ht
      subst t
      simp [DyadicForwardWaitingOptimality.midpoint, execute]
    | succ k ih =>
      intro a now t u hi ht hu
      have hq := Nat.two_pow_pos k
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
      have hp' : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
      have hP : 0 < P := by omega
      let m := a + 2 ^ (k + 1)
      let w := (P - m + P - now % P) % P
      let n := now + w
      have phase : n % P = P - m := by
        have hn := Nat.mod_lt now hP
        have hm : 0 < m ∧ m < P := by dsimp [m]; omega
        have hmod : (P - m + P - now % P) + now % P = P - m + P := by omega
        dsimp [n, w]
        rw [Nat.add_mod, Nat.add_mod_mod, Nat.add_comm, Nat.mod_add_mod, hmod,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have sr : read n (a + 2 * t + u) = if t < 2 ^ k then 0 else 1 := by
        rw [law _ _ (by omega), threshold, phase]
        dsimp [m]
        split_ifs <;> omega
      change (execute read (.query w (fun bit => midpoint P (k + 1)
        (if bit = 0 then a else m) n)) now (a + 2 * t + u)).2 + 2 * t =
          n + (2 ^ (k + 1) - 1) + P * t.bitIndices.length
      simp only [execute]
      change (execute read (midpoint P (k + 1)
        (if read n (a + 2 * t + u) = 0 then a else m) n) n
        (a + 2 * t + u)).2 + 2 * t = _
      by_cases hleft : t < 2 ^ k
      · rw [sr, if_pos hleft, if_pos rfl]
        have step : (P - (a + 2 ^ k) + P - n % P) % P = 2 ^ k := by
          rw [phase]
          have he : P - (a + 2 ^ k) + P - (P - m) = P + 2 ^ k := by dsimp [m]; omega
          rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have h := ih a n t u (by omega) hleft hu
        rw [step] at h
        omega
      · rw [sr, if_neg hleft, if_neg (by decide : (1 : Fin 2) ≠ 0)]
        have ht' : t - 2 ^ k < 2 ^ k := by omega
        have step : (P - (m + 2 ^ k) + P - n % P) % P = P - 2 ^ k := by
          rw [phase]
          have he : P - (m + 2 ^ k) + P - (P - m) = P - 2 ^ k := by dsimp [m]; omega
          rw [he, Nat.mod_eq_of_lt (by omega)]
        have h := ih m n (t - 2 ^ k) u (by dsimp [m]; omega) ht' hu
        have hr : m + 2 * (t - 2 ^ k) + u = a + 2 * t + u := by dsimp [m]; omega
        rw [step, hr] at h
        have hw := weight k (t - 2 ^ k) ht'
        rw [show 2 ^ k + (t - 2 ^ k) = t by omega] at hw
        rw [hw, Nat.mul_add, Nat.mul_one]
        omega
  dsimp only
  let P := 2 ^ (d + 1)
  have hP : P = 2 * 2 ^ d := by dsimp [P]; rw [pow_succ]; omega
  have hpos := Nat.two_pow_pos d
  have law (n r : Nat) (hr : r < P) : sensor P b n r = threshold P n r :=
    ((dyadic_forward_waiting_optimality (d + 1) b).1 n r hr).2
  have timing (u : Nat) (hu : u < 2) :
      terminalTime P b (rawMidpoint P b (d + 1)) (2 * t + u) + 2 * t =
        P - 1 + P * t.bitIndices.length := by
    have h := exact_time law d 0 0 t u (by dsimp [P]; omega) ht hu
    have hw : (P - (0 + 2 ^ d) + P - 0 % P) % P = 2 ^ d := by
      simp only [Nat.zero_add, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right]
      rw [show P - 2 ^ d = 2 ^ d by omega, Nat.mod_eq_of_lt (by omega)]
    rw [hw] at h
    unfold terminalTime rawMidpoint
    rw [(transport_execute P b (midpoint P (d + 1) 0 0) 0 _).1]
    simpa only [Nat.zero_add, show 2 ^ d + (2 ^ d - 1) = P - 1 by omega] using h
  constructor
  · have h := timing u hu
    change terminalTime P b (rawMidpoint P b (d + 1)) (2 * t + u) =
      P - 1 + P * t.bitIndices.length - 2 * t
    omega
  · unfold cycleCount
    have h := timing 0 (by decide)
    simp only [Nat.add_zero] at h
    have he : terminalTime P b (rawMidpoint P b (d + 1)) (2 * t) =
        (P - 1 - 2 * t) + P * t.bitIndices.length := by omega
    rw [he, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]

#print axioms terminal_pair_fiber_bijection_and_clock_injectivity
#print axioms earliest_midpoint_terminal_time

end D5.S3.Observer.Budget.TerminalClockCompression

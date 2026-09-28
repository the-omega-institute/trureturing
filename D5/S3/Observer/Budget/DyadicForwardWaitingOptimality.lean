/- GID: D5/S3/Observer/Budget/DyadicForwardWaitingOptimality
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/DyadicForwardWaitingOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Saturated high-bit sensing forces midpoint phases and sharp forward waiting. -/

import D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.DyadicForwardWaitingOptimality

open WorstCaseDepthInformationLowerBound

/-- A controller can stop early, or wait a natural number of unit evolutions and
branch on one observed bit. Its index bounds the number of further queries. -/
inductive Protocol : Nat → Type
  | stop {d : Nat} (answer : Nat) : Protocol d
  | query {d : Nat} (wait : Nat) (next : Fin 2 → Protocol d) : Protocol (d + 1)

/-- The physical high bit, with the initial high bit retained separately. -/
def rawBit (P : Nat) (b : Fin 2) (n r : Nat) : Fin 2 :=
  ⟨((b.val * P + r + n) / P) % 2, Nat.mod_lt _ (by decide)⟩

/-- Relabel a bit using only the known initial bit and elapsed clock. -/
def parityFlip (P : Nat) (b : Fin 2) (n : Nat) (bit : Fin 2) : Fin 2 :=
  ⟨(bit.val + b.val + n / P) % 2, Nat.mod_lt _ (by decide)⟩

/-- The known initial bit and elapsed whole-period parity decode the raw bit. -/
def sensor (P : Nat) (b : Fin 2) (n r : Nat) : Fin 2 :=
  parityFlip P b n (rawBit P b n r)

/-- The threshold associated to an actual elapsed time. Phase zero is constant. -/
def threshold (P n r : Nat) : Fin 2 := if r < P - n % P then 0 else 1

/-- Execution returns the recovered original residue and the final elapsed time. -/
def execute (read : Nat → Nat → Fin 2) {d : Nat} : Protocol d → Nat → Nat → Nat × Nat
  | .stop answer, now, _ => (answer, now)
  | .query wait next, now, r => execute read (next (read (now + wait) r)) (now + wait) r

/-- Exact recovery throughout a consecutive interval of original residues. -/
def CorrectOn (read : Nat → Nat → Fin 2) {d : Nat}
    (p : Protocol d) (now a length : Nat) : Prop :=
  ∀ r, a ≤ r → r < a + length → (execute read p now r).1 = r

/-- Forget the clock and leaf labels, retaining the actual binary question tree. -/
def questionTree {X : Type} (read : Nat → X → Fin 2) {d : Nat} :
    Protocol d → Nat → AdaptiveProtocol X 2 d
  | .stop _, _ => .leaf
  | .query wait next, now => .query (read (now + wait))
      (fun bit => questionTree read (next bit) (now + wait))

/-- Capacity saturation forces an actual sensor's cut to be the interval midpoint. -/
private theorem forced_midpoint {P d a now wait : Nat}
    {read : Nat → Nat → Fin 2} (next : Fin 2 → Protocol d)
    (law : ∀ n r, r < P → read n r = threshold P n r)
    (hi : a + 2 ^ (d + 1) ≤ P)
    (hc : CorrectOn read (.query wait next) now a (2 ^ (d + 1))) :
    P - (now + wait) % P = a + 2 ^ d ∧
      CorrectOn read (next 0) (now + wait) a (2 ^ d) ∧
      CorrectOn read (next 1) (now + wait) (a + 2 ^ d) (2 ^ d) := by
  have interval_capacity (read : Nat → Nat → Fin 2) {d : Nat}
      (p : Protocol d) (now a length : Nat) (hc : CorrectOn read p now a length) :
      length ≤ 2 ^ d := by
    let read' : Nat → Fin length → Fin 2 := fun n r => read n (a + r.val)
    have uses : ∀ {k} (p : Protocol k) n,
        UsesReadoutFamily (id : (Fin length → Fin 2) → Fin length → Fin 2)
          (questionTree read' p n) := by
      intro k p
      induction p with
      | stop answer => intro n; trivial
      | query wait next ih =>
          intro n
          exact ⟨⟨read' (n + wait), rfl⟩, fun bit => ih bit (n + wait)⟩
    have same_output : ∀ {k} (p : Protocol k) n (x y : Fin length),
        adaptiveTranscript (questionTree read' p n) x =
          adaptiveTranscript (questionTree read' p n) y →
        (execute read p n (a + x.val)).1 = (execute read p n (a + y.val)).1 := by
      intro k p
      induction p with
      | stop answer => intros; rfl
      | query wait next ih =>
          intro n x y h
          simp only [questionTree, adaptiveTranscript, List.cons.injEq] at h
          simp only [execute]
          change (execute read (next (read' (n + wait) x)) (n + wait) (a + x.val)).1 =
            (execute read (next (read' (n + wait) y)) (n + wait) (a + y.val)).1
          rw [← h.1]
          apply ih _ _ x y
          simpa only [← h.1] using h.2
    have inj : Function.Injective (adaptiveTranscript (questionTree read' p now)) := by
      intro x y h
      have ho := same_output p now x y h
      rw [hc _ (by omega) (by omega), hc _ (by omega) (by omega)] at ho
      exact Fin.ext (by omega)
    have bound := exact_identification_card_le_pow
      (id : (Fin length → Fin 2) → Fin length → Fin 2) (by decide)
      ⟨questionTree read' p now, uses p now, inj⟩
    simpa only [Fintype.card_fin] using bound
  have hp : 0 < 2 ^ d := Nat.two_pow_pos d
  have he : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by omega
  have split : P - (now + wait) % P = a + 2 ^ d := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hbranch : CorrectOn read (next 1) (now + wait)
          (a + 2 ^ d - 1) (2 ^ d + 1) := by
        intro r hlo hhi
        have hr : r < P := by omega
        have hs : read (now + wait) r = 1 := by
          rw [law _ _ hr, threshold, if_neg (by omega)]
        have h := hc r (by omega) (by omega)
        simpa only [execute, hs] using h
      have h := interval_capacity read (next 1) (now + wait)
        (a + 2 ^ d - 1) (2 ^ d + 1) hbranch
      omega
    · have hbranch : CorrectOn read (next 0) (now + wait) a (2 ^ d + 1) := by
        intro r hlo hhi
        have hr : r < P := by omega
        have hs : read (now + wait) r = 0 := by
          rw [law _ _ hr, threshold, if_pos (by omega)]
        have h := hc r hlo (by omega)
        simpa only [execute, hs] using h
      have h := interval_capacity read (next 0) (now + wait) a (2 ^ d + 1) hbranch
      omega
  refine ⟨split, ?_, ?_⟩
  · intro r hlo hhi
    have hs : read (now + wait) r = 0 := by
      rw [law _ _ (by omega), threshold, split, if_pos hhi]
    simpa only [execute, hs] using hc r hlo (by omega)
  · intro r hlo hhi
    have hs : read (now + wait) r = 1 := by
      rw [law _ _ (by omega), threshold, split, if_neg (by omega)]
    simpa only [execute, hs] using hc r (by omega) (by omega)

private theorem rightmost_path_bound {P : Nat} {read : Nat → Nat → Fin 2}
    (law : ∀ n r, r < P → read n r = threshold P n r) {d : Nat}
    (p : Protocol d) : ∀ now, 2 ^ d ≤ P →
    CorrectOn read p now (P - 2 ^ d) (2 ^ d) →
    d = 0 ∨ ∃ t, now ≤ t ∧ t % P = 2 ^ (d - 1) ∧
      (t / P + (d - 1)) * P + 1 ≤ (execute read p now (P - 1)).2 := by
  have mono : ∀ {k} (p : Protocol k) n r, n ≤ (execute read p n r).2 := by
    intro k p
    induction p with
    | stop answer => intros; exact Nat.le_refl _
    | query wait next ih =>
        intro n r
        exact (Nat.le_add_right n wait).trans (ih _ _ _)
  induction p with
  | @stop d answer =>
      intro now hp hc
      cases d with
      | zero => exact Or.inl rfl
      | succ d =>
          have hpos := Nat.two_pow_pos d
          have h0 := hc (P - 2 ^ (d + 1)) (by omega) (by omega)
          have h1 := hc (P - 2 ^ (d + 1) + 1) (by omega) (by omega)
          simp only [execute] at h0 h1
          omega
  | @query d wait next ih =>
      intro now hp hc
      have hpos := Nat.two_pow_pos d
      have hP : 0 < P := by omega
      have he : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by omega
      obtain ⟨cut, _, right⟩ := forced_midpoint next law (by omega) hc
      have phase : (now + wait) % P = 2 ^ d := by
        have := Nat.mod_lt (now + wait) hP
        omega
      have childStart : P - 2 ^ (d + 1) + 2 ^ d = P - 2 ^ d := by omega
      rw [childStart] at right
      have answer : read (now + wait) (P - 1) = 1 := by
        rw [law _ _ (by omega), threshold, phase, if_neg (by omega)]
      refine Or.inr ⟨now + wait, by omega, ?_, ?_⟩
      · simpa only [Nat.add_sub_cancel] using phase
      simp only [Nat.add_sub_cancel, execute, answer]
      by_cases hd : d = 0
      · subst d
        have ht := Nat.mod_add_div (now + wait) P
        have hm := mono (next 1) (now + wait) (P - 1)
        simp only [Nat.pow_zero, Nat.add_zero, Nat.mul_comm P] at phase ht ⊢
        omega
      · rcases ih 1 (now + wait) (by omega) right with hz | ⟨u, hu, uphase, cost⟩
        · exact False.elim (hd hz)
        have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        have smaller : 2 ^ (d - 1) < 2 ^ d := by
          apply Nat.pow_lt_pow_right (by decide)
          omega
        have quot : (now + wait) / P + 1 ≤ u / P := by
          have hq := Nat.div_le_div_right (c := P) hu
          have ht := Nat.mod_add_div (now + wait) P
          have hut := Nat.mod_add_div u P
          by_contra hn
          have eq : (now + wait) / P = u / P := by omega
          rw [eq] at ht
          omega
        calc
          ((now + wait) / P + d) * P + 1 ≤ (u / P + (d - 1)) * P + 1 := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right P (by omega)) 1
          _ ≤ _ := cost

/-- Choose the first nonnegative waiting increment reaching the midpoint phase. -/
def midpoint (P : Nat) : (d : Nat) → Nat → Nat → Protocol d
  | 0, a, _ => .stop a
  | d + 1, a, now =>
      let m := a + 2 ^ d
      let wait := (P - m + P - now % P) % P
      .query wait (fun bit => midpoint P d (if bit = 0 then a else m) (now + wait))

private theorem midpoint_correct_cost {P : Nat} {read : Nat → Nat → Fin 2}
    (law : ∀ n r, r < P → read n r = threshold P n r) (d : Nat) :
    ∀ a now, a + 2 ^ d ≤ P →
    (now % P = (P - a) % P ∨ now % P = (P - (a + 2 ^ d)) % P) →
    CorrectOn read (midpoint P d a now) now a (2 ^ d) ∧
      ∀ r, a ≤ r → r < a + 2 ^ d →
        (execute read (midpoint P d a now) now r).2 + 2 ^ d ≤ now + d * P + 1 := by
  induction d with
  | zero =>
      intro a now hi halign
      constructor
      · intro r hlo hhi; simp only [midpoint, execute]; simp only [Nat.pow_zero] at hhi; omega
      · intros; simp only [midpoint, execute, Nat.pow_zero, Nat.zero_mul, Nat.add_zero]
        exact Nat.le_refl _
  | succ d ih =>
      intro a now hi halign
      have hpos := Nat.two_pow_pos d
      have he : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by omega
      have hP : 0 < P := by omega
      let w := (P - (a + 2 ^ d) + P - now % P) % P
      have geom : w ≤ P - 2 ^ d ∧ (now + w) % P = P - (a + 2 ^ d) := by
        have sm := Nat.mod_lt now hP
        have ph : P - (a + 2 ^ d) < P := by omega
        have hhalf : 2 ^ d < P := by omega
        rcases halign with hl | hr
        · by_cases ha : a = 0
          · subst a
            simp only [Nat.sub_zero, Nat.mod_self] at hl
            have hw : w = P - 2 ^ d := by
              dsimp [w]
              simp only [hl, Nat.sub_zero, Nat.zero_add, Nat.add_mod_right,
                Nat.mod_eq_of_lt (show P - 2 ^ d < P by omega)]
            rw [hw]
            refine ⟨le_rfl, ?_⟩
            rw [Nat.add_mod, hl, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
            omega
          · have pa : P - a < P := by omega
            rw [Nat.mod_eq_of_lt pa] at hl
            have hw : w = P - 2 ^ d := by
              dsimp [w]
              rw [hl, show P - (a + 2 ^ d) + P - (P - a) = P - 2 ^ d by omega,
                Nat.mod_eq_of_lt (by omega)]
            rw [hw]
            refine ⟨le_rfl, ?_⟩
            rw [Nat.add_mod, hl, Nat.mod_eq_of_lt (show P - 2 ^ d < P by omega),
              show P - a + (P - 2 ^ d) = P + (P - (a + 2 ^ d)) by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt ph]
        · have pa : P - (a + 2 ^ (d + 1)) < P := by omega
          rw [Nat.mod_eq_of_lt pa] at hr
          have hw : w = 2 ^ d := by
            dsimp [w]
            rw [hr, show P - (a + 2 ^ d) + P - (P - (a + 2 ^ (d + 1))) = P + 2 ^ d by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt hhalf]
          rw [hw]
          refine ⟨by omega, ?_⟩
          rw [Nat.add_mod, hr, Nat.mod_eq_of_lt hhalf,
            show P - (a + 2 ^ (d + 1)) + 2 ^ d = P - (a + 2 ^ d) by omega,
            Nat.mod_eq_of_lt ph]
      have left := ih a (now + w) (by omega) (Or.inr (by rw [geom.2, Nat.mod_eq_of_lt (by omega)]))
      have right := ih (a + 2 ^ d) (now + w) (by omega)
        (Or.inl (by rw [geom.2, Nat.mod_eq_of_lt (by omega)]))
      have both : ∀ r, a ≤ r → r < a + 2 ^ (d + 1) →
          (execute read (midpoint P (d + 1) a now) now r).1 = r ∧
          (execute read (midpoint P (d + 1) a now) now r).2 + 2 ^ (d + 1) ≤
            now + (d + 1) * P + 1 := by
        intro r hlo hhi
        have sr : read (now + w) r = if r < a + 2 ^ d then 0 else 1 := by
          rw [law _ _ (by omega), threshold, geom.2,
            Nat.sub_sub_self (show a + 2 ^ d ≤ P by omega)]
        change let out := execute read (.query w (fun bit => midpoint P d
          (if bit = 0 then a else a + 2 ^ d) (now + w))) now r
          out.1 = r ∧ out.2 + 2 ^ (d + 1) ≤ now + (d + 1) * P + 1
        dsimp only
        by_cases hr : r < a + 2 ^ d
        · simp only [execute, sr, if_pos hr, ite_true] at ⊢
          have hc := left.2 r hlo hr
          refine ⟨left.1 r hlo hr, ?_⟩
          simp only [Nat.add_mul, Nat.one_mul] at ⊢
          omega
        · have h10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [execute, sr, if_neg hr, if_neg h10] at ⊢
          have hc := right.2 r (by omega) (by omega)
          refine ⟨right.1 r (by omega) (by omega), ?_⟩
          simp only [Nat.add_mul, Nat.one_mul] at ⊢
          omega
      exact ⟨fun r hlo hhi => (both r hlo hhi).1, fun r hlo hhi => (both r hlo hhi).2⟩

/-- Transport a controller between raw and decoded bit labels, retaining its clock. -/
def transport (P : Nat) (b : Fin 2) {d : Nat} : Protocol d → Nat → Protocol d
  | .stop answer, _ => .stop answer
  | .query wait next, now => .query wait (fun bit =>
      transport P b (next (parityFlip P b (now + wait) bit)) (now + wait))

private theorem transport_execute (P : Nat) (b : Fin 2) {d : Nat} (p : Protocol d) :
    ∀ now r,
    execute (rawBit P b) (transport P b p now) now r = execute (sensor P b) p now r ∧
    execute (sensor P b) (transport P b p now) now r = execute (rawBit P b) p now r := by
  induction p with
  | stop answer => intros; exact ⟨rfl, rfl⟩
  | query wait next ih =>
      intro now r
      have flip : parityFlip P b (now + wait) (sensor P b (now + wait) r) =
          rawBit P b (now + wait) r := by
        apply Fin.ext
        change (((rawBit P b (now + wait) r).val + b.val + (now + wait) / P) % 2 +
          b.val + (now + wait) / P) % 2 = (rawBit P b (now + wait) r).val
        have hr := (rawBit P b (now + wait) r).isLt
        omega
      constructor
      · change execute (rawBit P b)
          (transport P b (next (sensor P b (now + wait) r)) (now + wait)) (now + wait) r = _
        exact (ih _ _ _).1
      · simp only [transport, execute, flip]
        exact (ih _ _ _).2

/-- The midpoint controller operating on actual raw high-bit observations. -/
def rawMidpoint (P : Nat) (b : Fin 2) (j : Nat) : Protocol j :=
  transport P b (midpoint P j 0 0) 0

/-- Bounds attained by exact controllers, with cost measured on every actual source. -/
def waitingBounds (P d : Nat) (read : Nat → Nat → Fin 2) : Set Nat :=
  {W | ∃ p : Protocol d, CorrectOn read p 0 0 P ∧
    ∀ r, r < P → (execute read p 0 r).2 ≤ W}

/-- The zero-budget singleton and the positive-depth sharp waiting value. -/
def sharpWait (j : Nat) : Nat := if j = 0 then 0 else (j - 1) * 2 ^ j + 1

/-- Both initial high-bit fibers have the same attained optimal forward waiting.
The displayed sensor law uses the actual elapsed clock; midpoint controllers recover
every original residue without an interface that can inspect it in advance. -/
theorem dyadic_forward_waiting_optimality (j : Nat) (b : Fin 2) :
    let P := 2 ^ j
    let read := rawBit P b
    (∀ n r, r < P →
      (read n r).val = (b.val + n / P + (threshold P n r).val) % 2 ∧
      sensor P b n r = threshold P n r) ∧
    IsLeast (waitingBounds P j read) (sharpWait j) ∧
    CorrectOn read (rawMidpoint P b j) 0 0 P ∧
    ∀ r, r < P → (execute read (rawMidpoint P b j) 0 r).2 ≤ sharpWait j := by
  dsimp only
  let P := 2 ^ j
  have hP : 0 < P := Nat.two_pow_pos j
  have rawlaw (n r : Nat) (hr : r < P) :
      (rawBit P b n r).val = (b.val + n / P + (threshold P n r).val) % 2 := by
    have hs := Nat.mod_lt n hP
    have carry : (r + n % P) / P = (threshold P n r).val := by
      unfold threshold
      split_ifs with h
      · exact Nat.div_eq_of_lt (by omega)
      · apply Nat.div_eq_of_lt_le (by omega)
        omega
    have clock := Nat.mod_add_div n P
    have rearrange : b.val * P + r + n = (r + n % P) + P * (b.val + n / P) := by
      simp only [Nat.add_mul, Nat.mul_comm P] at *
      omega
    change ((b.val * P + r + n) / P) % 2 = _
    rw [rearrange, Nat.add_mul_div_left _ _ hP, carry]
    congr 1
    omega
  have law (n r : Nat) (hr : r < P) : sensor P b n r = threshold P n r := by
    apply Fin.ext
    change ((rawBit P b n r).val + b.val + n / P) % 2 = (threshold P n r).val
    rw [rawlaw n r hr]
    have ht := (threshold P n r).isLt
    omega
  have upper := midpoint_correct_cost law j 0 0 (by change 0 + 2 ^ j ≤ 2 ^ j; omega)
    (Or.inl (by simp only [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]))
  have bound (r : Nat) (hr : r < P) :
      (execute (sensor P b) (midpoint P j 0 0) 0 r).2 ≤ sharpWait j := by
    have hu := upper.2 r (Nat.zero_le _) (by simpa only [Nat.zero_add] using hr)
    by_cases hj : j = 0
    · subst j
      simp [midpoint, execute, sharpWait]
    · have hm : j * P = (j - 1) * P + P := by
        conv_lhs => rw [show j = (j - 1) + 1 by omega]
        rw [Nat.add_mul, Nat.one_mul]
      change _ ≤ if j = 0 then 0 else (j - 1) * P + 1
      rw [if_neg hj]
      change (execute (sensor P b) (midpoint P j 0 0) 0 r).2 + P ≤ 0 + j * P + 1 at hu
      rw [hm] at hu
      omega
  have correctRaw : CorrectOn (rawBit P b) (rawMidpoint P b j) 0 0 P := by
    intro r hlo hhi
    rw [rawMidpoint, (transport_execute P b (midpoint P j 0 0) 0 r).1]
    exact upper.1 r hlo hhi
  have boundRaw (r : Nat) (hr : r < P) :
      (execute (rawBit P b) (rawMidpoint P b j) 0 r).2 ≤ sharpWait j := by
    rw [rawMidpoint, (transport_execute P b (midpoint P j 0 0) 0 r).1]
    exact bound r hr
  refine ⟨fun n r hr => ⟨rawlaw n r hr, law n r hr⟩, ?_, correctRaw, boundRaw⟩
  refine ⟨⟨rawMidpoint P b j, correctRaw, boundRaw⟩, ?_⟩
  intro W hW
  obtain ⟨p, hc, cost⟩ := hW
  by_cases hj : j = 0
  · simp only [sharpWait, if_pos hj, Nat.zero_le]
  · have decoded : CorrectOn (sensor P b) (transport P b p 0) 0 0 P := by
      intro r hlo hhi
      rw [(transport_execute P b p 0 r).2]
      exact hc r hlo hhi
    have lower := rightmost_path_bound law (transport P b p 0) 0 (by rfl)
      (by simpa only [P, Nat.sub_self] using decoded)
    rcases lower with hz | ⟨t, _, _, ht⟩
    · exact False.elim (hj hz)
    rw [(transport_execute P b p 0 (P - 1)).2] at ht
    have last := cost (P - 1) (by omega)
    apply le_trans _ (ht.trans last)
    change (if j = 0 then 0 else (j - 1) * P + 1) ≤ _
    rw [if_neg hj]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right P (Nat.le_add_left _ _)) 1

#print axioms dyadic_forward_waiting_optimality

end D5.S3.Observer.Budget.DyadicForwardWaitingOptimality

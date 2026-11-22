/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSharpness
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact unary Moore witness pairs and the least uniform separating prefix for a state bound. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation

/-! For each shorter cut, advance a cycle and a transient-plus-cycle machine
along their own transitions until their first disagreement occurs at that cut. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness

open UnaryMooreSeparation (Machine observations unary_moore_separation_and_synthesis)

private theorem source_emit {Q : Type} (m : Machine Q) (i : Nat) :
    m.emit i = m.label (m.transition^[i] m.start) :=
  (unary_moore_separation_and_synthesis 1 (by decide)).2.2.2.1 Q m i

private def advance {Q : Type} (m : Machine Q) (n : Nat) : Machine Q :=
  { m with start := m.transition^[n] m.start }

private theorem advance_emit {Q : Type} (m : Machine Q) (n i : Nat) :
    (advance m n).emit i = m.emit (i+n) := by
  rw [source_emit, source_emit, Function.iterate_add_apply]
  rfl

private theorem observations_agree {Q R : Type} (m : Machine Q) (m' : Machine R)
    (n : Nat) (h : ∀ i < n, m.emit i = m'.emit i) :
    observations m n = observations m' n := by
  induction n generalizing m m' with
  | zero => rfl
  | succ n ih =>
    change m.emit 0 :: observations (advance m 1) n =
      m'.emit 0 :: observations (advance m' 1) n
    rw [h 0 (by omega), ih (advance m 1) (advance m' 1)]
    intro i hi
    rw [advance_emit, advance_emit]
    exact h (i+1) (by omega)

private def zero (k : Nat) (hk : 1 ≤ k) : Fin k := ⟨0,hk⟩

private def cycleStep (k : Nat) (hk : 2 ≤ k) (q : Fin k) : Fin k :=
  ⟨(q.val+1) % k, Nat.mod_lt _ (by omega)⟩

private def transientStep (k : Nat) (hk : 2 ≤ k) (q : Fin k) : Fin k :=
  ⟨1+q.val % (k-1), by have := Nat.mod_lt q.val (show 0 < k-1 by omega); omega⟩

private def lastLabel (k : Nat) (q : Fin k) : Bool := decide (q.val = k-1)

private def cycleMachine (k : Nat) (hk : 2 ≤ k) : Machine (Fin k) :=
  ⟨cycleStep k hk, lastLabel k, zero k (by omega)⟩

private def transientMachine (k : Nat) (hk : 2 ≤ k) : Machine (Fin k) :=
  ⟨transientStep k hk, lastLabel k, zero k (by omega)⟩

private theorem cycle_state (k : Nat) (hk : 2 ≤ k) (i : Nat) :
    ((cycleStep k hk)^[i] (zero k (by omega))).val = i % k := by
  induction i with
  | zero => simp [zero]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change (((cycleStep k hk)^[i] (zero k (by omega))).val + 1) % k = (i+1) % k
    rw [ih, Nat.mod_add_mod]

private theorem transient_state (k : Nat) (hk : 2 ≤ k) (i : Nat) :
    ((transientStep k hk)^[i+1] (zero k (by omega))).val = 1+i % (k-1) := by
  induction i with
  | zero => simp [transientStep, zero]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change 1+((transientStep k hk)^[i+1] (zero k (by omega))).val % (k-1) =
      1+(i+1) % (k-1)
    rw [ih, Nat.add_comm 1 (i % (k-1)), Nat.mod_add_mod]

private theorem cycle_emit (k : Nat) (hk : 2 ≤ k) (i : Nat) :
    (cycleMachine k hk).emit i = decide (i % k = k-1) := by
  rw [source_emit]
  change decide (((cycleStep k hk)^[i] (zero k (by omega))).val = k-1) = _
  rw [cycle_state]

private theorem transient_emit_zero (k : Nat) (hk : 2 ≤ k) :
    (transientMachine k hk).emit 0 = false := by
  rw [source_emit]
  have h : 0 ≠ k-1 := by omega
  simp [transientMachine,lastLabel,zero,h]

private theorem transient_emit (k : Nat) (hk : 2 ≤ k) (i : Nat) :
    (transientMachine k hk).emit (i+1) = decide (1+i % (k-1) = k-1) := by
  rw [source_emit]
  change decide (((transientStep k hk)^[i+1] (zero k (by omega))).val = k-1) = _
  rw [transient_state]

private theorem mod_once (i k : Nat) (h₁ : k ≤ i) (h₂ : i < 2*k) : i % k = i-k := by
  calc
    i % k = ((i-k)+k) % k := congrArg (· % k) (by omega)
    _ = (i-k) % k := Nat.add_mod_right _ _
    _ = i-k := Nat.mod_eq_of_lt (by omega)

private theorem base_agree (k : Nat) (hk : 2 ≤ k) (i : Nat) (hi : i < 2*k-2) :
    (cycleMachine k hk).emit i = (transientMachine k hk).emit i := by
  cases i with
  | zero =>
    have h : 0 ≠ k-1 := by omega
    simp [cycle_emit, transient_emit_zero, h]
  | succ j =>
    rw [cycle_emit, transient_emit]
    by_cases h : j+1 < k
    · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (a := j) (b := k-1) (by omega)]
      rw [Nat.add_comm 1 j]
    · rw [mod_once (j+1) k (by omega) (by omega), mod_once j (k-1) (by omega) (by omega)]
      have h₁ : j+1-k ≠ k-1 := by omega
      have h₂ : 1+(j-(k-1)) ≠ k-1 := by omega
      simp [h₁,h₂]

private theorem base_split (k : Nat) (hk : 2 ≤ k) :
    (cycleMachine k hk).emit (2*k-2) = false ∧
    (transientMachine k hk).emit (2*k-2) = true := by
  constructor
  · rw [cycle_emit, mod_once (2*k-2) k (by omega) (by omega)]
    have h : 2*k-2-k ≠ k-1 := by omega
    simp [h]
  · have he : 2*k-2 = (2*k-3)+1 := by omega
    rw [he, transient_emit, mod_once (2*k-3) (k-1) (by omega) (by omega)]
    have h : 1+(2*k-3-(k-1)) = k-1 := by omega
    simp [h]

/-- Two physical unary Moore tables on the positive carrier Fin (n+1).
At n=0 they are opposite constants; otherwise move the starts of the
cycle and transient-plus-cycle table along their own real transitions. -/
def witnesses : (n v : Nat) → Machine (Fin (n+1)) × Machine (Fin (n+1))
  | 0, _ => (⟨id, fun _ => false, 0⟩, ⟨id, fun _ => true, 0⟩)
  | n+1, v =>
    (advance (cycleMachine (n+2) (by omega)) (2*(n+2)-2-v),
      advance (transientMachine (n+2) (by omega)) (2*(n+2)-2-v))

/-- Read the chosen actual emitted bit at the requested divergent index. -/
def witnessOutput (K v : Nat) (side : Bool) : Bool :=
  if side then (witnesses (K-1) v).2.emit v else (witnesses (K-1) v).1.emit v

/-- The length works simultaneously for all machines whose carriers have size at most K. -/
def UniformlySeparates (K v : Nat) : Prop :=
  ∀ (Q R : Type) [Fintype Q] [Fintype R] (m : Machine Q) (m' : Machine R),
    Fintype.card Q ≤ K → Fintype.card R ≤ K →
    (∀ i < v, m.emit i = m'.emit i) → ∀ i, m.emit i = m'.emit i

private theorem witness_data (n v : Nat) (hv : v < 2*(n+1)-1) :
    (∀ i < v, (witnesses n v).1.emit i = (witnesses n v).2.emit i) ∧
    (witnesses n v).1.emit v = false ∧ (witnesses n v).2.emit v = true := by
  cases n with
  | zero =>
    have h : v = 0 := by omega
    subst v
    simp [witnesses, source_emit]
  | succ n =>
    have hk : 2 ≤ n+2 := by omega
    have hcut : v + (2*(n+2)-2-v) = 2*(n+2)-2 := by omega
    constructor
    · intro i hi
      simp only [witnesses, advance_emit]
      exact base_agree (n+2) hk _ (by omega)
    · simp only [witnesses, advance_emit, hcut]
      exact base_split (n+2) hk

/-- Every shorter length has lawful unary witness machines, and 2K−1
is the least uniform sufficient prefix length. -/
theorem unary_moore_sharpness (K : Nat) (hK : 1 ≤ K) :
    (∀ (v : Nat), v < 2*K-1 →
      (∀ side : Bool, witnessOutput K v side = side) ∧
      Fintype.card (Fin (K-1+1)) ≤ K ∧
      (∀ i < v, (witnesses (K-1) v).1.emit i = (witnesses (K-1) v).2.emit i) ∧
      (witnesses (K-1) v).1.emit v ≠ (witnesses (K-1) v).2.emit v) ∧
    (∀ v : Nat, UniformlySeparates K v ↔ 2*K-1 ≤ v) := by
  have hcap : Fintype.card (Fin (K-1+1)) ≤ K := by rw [Fintype.card_fin]; omega
  constructor
  · intro v hv
    obtain ⟨ha, h₀, h₁⟩ := witness_data (K-1) v (by omega)
    refine ⟨?_, hcap, ha, by rw [h₀, h₁]; decide⟩
    intro side
    cases side
    · simpa only [witnessOutput, Bool.false_eq_true, ite_false] using h₀
    · simpa only [witnessOutput, ite_true] using h₁
  · intro v
    constructor
    · intro h
      by_contra! hv
      obtain ⟨ha, h₀, h₁⟩ := witness_data (K-1) v (by omega)
      have he := h _ _ (witnesses (K-1) v).1 (witnesses (K-1) v).2 hcap hcap ha v
      rw [h₀, h₁] at he
      cases he
    · intro hv Q R _ _ m m' hm hm' hs
      apply (unary_moore_separation_and_synthesis K hK).2.1 Q R m m' hm hm'
      exact observations_agree m m' _ (fun i hi => hs i (lt_of_lt_of_le hi hv))

#print axioms unary_moore_sharpness

end D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness

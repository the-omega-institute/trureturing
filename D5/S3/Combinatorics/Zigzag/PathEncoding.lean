/- GID: D5/S3/Combinatorics/Zigzag/PathEncoding
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/PathEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal class-order encoding of signed retirement paths. -/

import D5.S3.Combinatorics.Zigzag.Retirement
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

def evenTailLowForms {h : Half} : {m : Nat} -> {s : State} ->
    EvenTail h m s -> List Form
  | 0, _, e => [(evenTerminalValue (h := h) e).low]
  | _ + 1, _, ⟨i, p⟩ => (stepValue (h := h) i).low :: evenTailLowForms p

def evenTailHighForms {h : Half} : {m : Nat} -> {s : State} ->
    EvenTail h m s -> List Form
  | 0, _, e => [(evenTerminalValue (h := h) e).high]
  | _ + 1, _, ⟨i, p⟩ => (stepValue (h := h) i).high :: evenTailHighForms p

def oddTailLowForms {h : Half} : {m : Nat} -> {s : State} ->
    OddTail h m s -> List Form
  | 0, _, e => [(oddTerminalValue (h := h) e).label]
  | _ + 1, _, ⟨i, p⟩ => (stepValue (h := h) i).low :: oddTailLowForms p

def oddTailHighForms {h : Half} : {m : Nat} -> {s : State} ->
    OddTail h m s -> List Form
  | 0, _, _ => []
  | _ + 1, _, ⟨i, p⟩ => (stepValue (h := h) i).high :: oddTailHighForms p

def evenPathForms {h : Half} {m : Nat} (p : EvenPath h m) : List Form :=
  (startValue (h := h) p.1).label ::
    (evenTailLowForms p.2 ++ (evenTailHighForms p.2).reverse)

def oddPathForms {h : Half} {m : Nat} (p : OddPath h m) : List Form :=
  (startValue (h := h) p.1).label ::
    (oddTailLowForms p.2 ++ (oddTailHighForms p.2).reverse)

def formsFlow (n k : Nat) : List Form -> Flow n
  | [] => 0
  | f :: fs => edgeFlow n k f + formsFlow n (k + 1) fs

@[simp] theorem formsFlow_append (n k : Nat) (xs ys : List Form) :
    formsFlow n k (xs ++ ys) =
      formsFlow n k xs + formsFlow n (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [formsFlow]
  | cons x xs ih =>
      simp [formsFlow, ih, Nat.add_assoc]
      abel_nf

@[simp] theorem evenTailLowForms_length {h : Half} {m : Nat} {s : State}
    (p : EvenTail h m s) : (evenTailLowForms p).length = m + 1 := by
  induction m generalizing s with
  | zero => simp [evenTailLowForms]
  | succ m ih =>
      rcases p with ⟨i, p⟩
      simp [evenTailLowForms, ih p, Nat.add_assoc]

@[simp] theorem evenTailHighForms_length {h : Half} {m : Nat} {s : State}
    (p : EvenTail h m s) : (evenTailHighForms p).length = m + 1 := by
  induction m generalizing s with
  | zero => simp [evenTailHighForms]
  | succ m ih =>
      rcases p with ⟨i, p⟩
      simp [evenTailHighForms, ih p, Nat.add_assoc]

@[simp] theorem oddTailLowForms_length {h : Half} {m : Nat} {s : State}
    (p : OddTail h m s) : (oddTailLowForms p).length = m + 1 := by
  induction m generalizing s with
  | zero => simp [oddTailLowForms]
  | succ m ih =>
      rcases p with ⟨i, p⟩
      simp [oddTailLowForms, ih p, Nat.add_assoc]

@[simp] theorem oddTailHighForms_length {h : Half} {m : Nat} {s : State}
    (p : OddTail h m s) : (oddTailHighForms p).length = m := by
  induction m generalizing s with
  | zero => simp [oddTailHighForms]
  | succ m ih =>
      rcases p with ⟨i, p⟩
      simp [oddTailHighForms, ih p]

private def evenTailForms {h : Half} {m : Nat} {s : State}
    (p : EvenTail h m s) : List Form :=
  evenTailLowForms p ++ (evenTailHighForms p).reverse

private def oddTailForms {h : Half} {m : Nat} {s : State}
    (p : OddTail h m s) : List Form :=
  oddTailLowForms p ++ (oddTailHighForms p).reverse

def evenTailFlow (n j : Nat) {h : Half} : {m : Nat} -> {s : State} ->
    EvenTail h m s -> Flow n
  | 0, _, e => pairedFlow n j (evenTerminalValue e).low (evenTerminalValue e).high
  | _ + 1, _, ⟨i, p⟩ =>
      pairedFlow n j (stepValue (h := h) i).low (stepValue (h := h) i).high +
        evenTailFlow n (j + 1) p

def oddTailFlow (n j : Nat) {h : Half} : {m : Nat} -> {s : State} ->
    OddTail h m s -> Flow n
  | 0, _, e => edgeFlow n j (oddTerminalValue e).label
  | _ + 1, _, ⟨i, p⟩ =>
      pairedFlow n j (stepValue (h := h) i).low (stepValue (h := h) i).high +
        oddTailFlow n (j + 1) p

private theorem evenTailForms_flow {h : Half} {m n j : Nat} {s : State}
    (p : EvenTail h m s) (hn : n = 2 * (j + m)) :
    formsFlow n j (evenTailForms p) = evenTailFlow n j p := by
  induction m generalizing j s with
  | zero =>
      simp [evenTailForms, evenTailLowForms, evenTailHighForms,
        formsFlow, evenTailFlow, pairedFlow, highClass]
      subst n
      congr 2
      omega
  | succ m ih =>
      rcases p with ⟨i, p⟩
      have hforms : evenTailForms (m := m + 1) ⟨i, p⟩ =
          (stepValue (h := h) i).low ::
            (evenTailForms p ++ [(stepValue (h := h) i).high]) := by
        simp [evenTailForms, evenTailLowForms, evenTailHighForms, List.append_assoc]
      have hlen : (evenTailForms p).length = 2 * m + 2 := by
        unfold evenTailForms
        rw [List.length_append, List.length_reverse,
          evenTailLowForms_length, evenTailHighForms_length]
        omega
      rw [hforms]
      simp only [formsFlow, formsFlow_append, hlen, List.length_singleton]
      rw [ih p (by omega)]
      simp [evenTailFlow, pairedFlow, highClass]
      have hk : j + 1 + (2 * m + 2) = n + 1 - j := by omega
      rw [hk]
      abel

private theorem oddTailForms_flow {h : Half} {m n j : Nat} {s : State}
    (p : OddTail h m s) (hn : n = 2 * (j + m) - 1) :
    formsFlow n j (oddTailForms p) = oddTailFlow n j p := by
  induction m generalizing j s with
  | zero => simp [oddTailForms, oddTailLowForms, oddTailHighForms,
      formsFlow, oddTailFlow]
  | succ m ih =>
      rcases p with ⟨i, p⟩
      have hforms : oddTailForms (m := m + 1) ⟨i, p⟩ =
          (stepValue (h := h) i).low ::
            (oddTailForms p ++ [(stepValue (h := h) i).high]) := by
        simp [oddTailForms, oddTailLowForms, oddTailHighForms, List.append_assoc]
      have hlen : (oddTailForms p).length = 2 * m + 1 := by
        unfold oddTailForms
        rw [List.length_append, List.length_reverse,
          oddTailLowForms_length, oddTailHighForms_length]
        omega
      rw [hforms]
      simp only [formsFlow, formsFlow_append, hlen, List.length_singleton]
      rw [ih p (by omega)]
      simp [oddTailFlow, pairedFlow, highClass]
      have hk : j + 1 + (2 * m + 1) = n + 1 - j := by omega
      rw [hk]
      abel

def evenPathFlow (r : Nat) {h : Half} (p : EvenPath h (3 * r - 3)) : Flow (3 * (2 * r)) :=
  edgeFlow (3 * (2 * r)) 2 (startValue p.1).label +
    evenTailFlow (3 * (2 * r)) 3 p.2

def oddPathFlow (r : Nat) {h : Half} (p : OddPath h (3 * r - 1)) :
    Flow (3 * (2 * r + 1)) :=
  edgeFlow (3 * (2 * r + 1)) 2 (startValue p.1).label +
    oddTailFlow (3 * (2 * r + 1)) 3 p.2

theorem evenPathForms_flow (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : EvenPath h (3 * r - 3)) :
    formsFlow (3 * (2 * r)) 2 (evenPathForms p) = evenPathFlow r p := by
  rcases p with ⟨i, p⟩
  simp only [evenPathForms, evenPathFlow, formsFlow]
  change edgeFlow (3 * (2 * r)) 2 (startValue i).label +
      formsFlow (3 * (2 * r)) 3 (evenTailForms p) = _
  rw [evenTailForms_flow p (by omega)]

theorem oddPathForms_flow (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : OddPath h (3 * r - 1)) :
    formsFlow (3 * (2 * r + 1)) 2 (oddPathForms p) = oddPathFlow r p := by
  rcases p with ⟨i, p⟩
  simp only [oddPathForms, oddPathFlow, formsFlow]
  change edgeFlow (3 * (2 * r + 1)) 2 (startValue i).label +
      formsFlow (3 * (2 * r + 1)) 3 (oddTailForms p) = _
  rw [oddTailForms_flow p (by omega)]

private theorem evenTailFlow_boundary (r : Nat) (hr : 1 ≤ r) (h : Half) :
    {m : Nat} -> {s : State} -> (p : EvenTail h m s) -> (j : Nat) -> (q : Int) ->
    3 ≤ j -> j + m = 3 * r ->
    configurationFlow (3 * (2 * r)) h s (j - 1) q +
      evenTailFlow (3 * (2 * r)) j p =
      boundaryFlow (3 * (2 * r)) (q + evenTailCharge p)
  | 0, s, p, j, q, _, hj => by
      have hjeq : j = 3 * r := by omega
      subst j
      simpa [evenTailFlow, evenTailCharge] using even_terminal_flow r hr h s p q
  | m + 1, s, ⟨i, p⟩, j, q, hjlow, hj => by
      rw [evenTailFlow]
      simp only [evenTailCharge]
      rw [← add_assoc]
      rw [transition_flow (3 * (2 * r)) j (by omega) (by omega) h s i q]
      change configurationFlow (3 * (2 * r)) h (stepTarget i) j
          (q + (stepValue (h := h) i).charge) +
        evenTailFlow (3 * (2 * r)) (j + 1) p = _
      have hrec := evenTailFlow_boundary r hr h p (j + 1)
        (q + (stepValue (h := h) i).charge) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hrec
      rw [hrec]
      apply congrArg (boundaryFlow (3 * (2 * r)))
      omega

private theorem oddTailFlow_boundary (r : Nat) (hr : 1 ≤ r) (h : Half) :
    {m : Nat} -> {s : State} -> (p : OddTail h m s) -> (j : Nat) -> (q : Int) ->
    3 ≤ j -> j + m = 3 * r + 2 ->
    configurationFlow (3 * (2 * r + 1)) h s (j - 1) q +
      oddTailFlow (3 * (2 * r + 1)) j p =
      boundaryFlow (3 * (2 * r + 1)) (q + oddTailCharge p)
  | 0, s, p, j, q, _, hj => by
      have hjeq : j = 3 * r + 2 := by omega
      subst j
      simpa [oddTailFlow, oddTailCharge] using odd_terminal_flow r h s p q
  | m + 1, s, ⟨i, p⟩, j, q, hjlow, hj => by
      rw [oddTailFlow]
      simp only [oddTailCharge]
      rw [← add_assoc]
      rw [transition_flow (3 * (2 * r + 1)) j (by omega) (by omega) h s i q]
      change configurationFlow (3 * (2 * r + 1)) h (stepTarget i) j
          (q + (stepValue (h := h) i).charge) +
        oddTailFlow (3 * (2 * r + 1)) (j + 1) p = _
      have hrec := oddTailFlow_boundary r hr h p (j + 1)
        (q + (stepValue (h := h) i).charge) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hrec
      rw [hrec]
      apply congrArg (boundaryFlow (3 * (2 * r + 1)))
      omega

theorem evenPathFlow_eq_boundary (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : EvenPath h (3 * r - 3)) :
    evenPathFlow r p = boundaryFlow (3 * (2 * r)) (evenPathCharge p) := by
  rcases p with ⟨i, p⟩
  have hs : edgeFlow (3 * (2 * r)) 2 (startValue (h := h) i).label =
      configurationFlow (3 * (2 * r)) h (startTarget i) 2
        (startValue (h := h) i).charge := by
    cases h
    · fin_cases i
      · have hv : (1 - (2 : ZMod (3 * (2 * r)))) = -1 := by ring
        simp [edgeFlow, formPair, configurationFlow, halfSign,
          statePositive, stateNegative, startValue, starts, startTarget, startTargets,
          State.A, State.D, Form.II, Form.IV, hv]
        module
      · have hv : ((2 : ZMod (3 * (2 * r))) - 1) = 1 := by ring
        simp [edgeFlow, formPair, configurationFlow, halfSign,
          statePositive, stateNegative, startValue, starts, startTarget, startTargets,
          State.A, State.D, Form.II, Form.IV, hv]
        module
    · fin_cases i <;>
      simp [edgeFlow, formPair, configurationFlow, halfSign,
        statePositive, stateNegative, startValue, starts, startTarget, startTargets,
        State.A, State.D, Form.III, Form.V] <;> abel
  change edgeFlow (3 * (2 * r)) 2 (startValue (h := h) i).label +
      evenTailFlow (3 * (2 * r)) 3 p = _
  rw [hs]
  rw [evenTailFlow_boundary r hr h p 3 (startValue (h := h) i).charge
    (by omega) (by omega)]
  rfl

theorem oddPathFlow_eq_boundary (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : OddPath h (3 * r - 1)) :
    oddPathFlow r p = boundaryFlow (3 * (2 * r + 1)) (oddPathCharge p) := by
  rcases p with ⟨i, p⟩
  have hs : edgeFlow (3 * (2 * r + 1)) 2 (startValue (h := h) i).label =
      configurationFlow (3 * (2 * r + 1)) h (startTarget i) 2
        (startValue (h := h) i).charge := by
    cases h
    · fin_cases i
      · have hv : (1 - (2 : ZMod (3 * (2 * r + 1)))) = -1 := by ring
        simp [edgeFlow, formPair, configurationFlow, halfSign,
          statePositive, stateNegative, startValue, starts, startTarget, startTargets,
          State.A, State.D, Form.II, Form.IV, hv]
        module
      · have hv : ((2 : ZMod (3 * (2 * r + 1))) - 1) = 1 := by ring
        simp [edgeFlow, formPair, configurationFlow, halfSign,
          statePositive, stateNegative, startValue, starts, startTarget, startTargets,
          State.A, State.D, Form.II, Form.IV, hv]
        module
    · fin_cases i <;>
      simp [edgeFlow, formPair, configurationFlow, halfSign,
        statePositive, stateNegative, startValue, starts, startTarget, startTargets,
        State.A, State.D, Form.III, Form.V] <;> abel
  change edgeFlow (3 * (2 * r + 1)) 2 (startValue (h := h) i).label +
      oddTailFlow (3 * (2 * r + 1)) 3 p = _
  rw [hs]
  rw [oddTailFlow_boundary r hr h p 3 (startValue (h := h) i).charge
    (by omega) (by omega)]
  rfl

@[simp] theorem evenPathForms_length {h : Half} {m : Nat} (p : EvenPath h m) :
    (evenPathForms p).length = 2 * m + 3 := by
  rcases p with ⟨i, p⟩
  simp [evenPathForms]
  omega

@[simp] theorem oddPathForms_length {h : Half} {m : Nat} (p : OddPath h m) :
    (oddPathForms p).length = 2 * m + 2 := by
  rcases p with ⟨i, p⟩
  simp [oddPathForms]
  omega

private def choicesFromForms (t : Nat) (xs : List Form)
    (hlen : xs.length = 3 * t - 3)
    (hstart : forall hz : 0 < xs.length, (xs.get ⟨0, hz⟩).allowedAtTwo) : Choices t :=
  ⟨fun i => xs.get ⟨i.val, by simpa [hlen] using i.isLt⟩, by
    intro i hi
    have hz : 0 < xs.length := by rw [hlen]; omega
    have heq : (⟨i.val, by simpa [hlen] using i.isLt⟩ : Fin xs.length) = ⟨0, hz⟩ :=
      Fin.ext hi
    simpa only [heq] using hstart hz⟩

/-- Decode every signed even path into the literal labelled choices, in source
class order.  Reflected high classes occur in reverse retirement order. -/
def evenPathChoices (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : EvenPath h (3 * r - 3)) : Choices (2 * r) :=
  choicesFromForms (2 * r) (evenPathForms p) (by
    rw [evenPathForms_length]
    omega) (by
      rcases p with ⟨i, p⟩
      cases h <;> fin_cases i <;>
        simp [evenPathForms, startValue, starts, Form.allowedAtTwo])

/-- Decode every signed odd path into the literal labelled choices, with the
singleton between the low and reflected-high blocks. -/
def oddPathChoices (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : OddPath h (3 * r - 1)) : Choices (2 * r + 1) :=
  choicesFromForms (2 * r + 1) (oddPathForms p) (by
    rw [oddPathForms_length]
    omega) (by
      rcases p with ⟨i, p⟩
      cases h <;> fin_cases i <;>
        simp [oddPathForms, startValue, starts, Form.allowedAtTwo])

end D5.S3.Combinatorics.Zigzag

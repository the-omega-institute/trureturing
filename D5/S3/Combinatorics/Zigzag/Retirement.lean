/- GID: D5/S3/Combinatorics/Zigzag/Retirement
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/Retirement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Source-specific flow identities for literal zigzag node retirement. -/

import D5.S3.Combinatorics.Zigzag.PathData
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

/-- Distinct vertices at the even antipodal boundary. -/
def evenBoundaryVertex (r : Nat) : Fin 6 -> ZMod (3 * (2 * r))
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => (3 * r : ZMod (3 * (2 * r))) - 1
  | ⟨4, _⟩ => 1 - (3 * r : ZMod (3 * (2 * r)))
  | ⟨5, _⟩ => (3 * r : ZMod (3 * (2 * r)))

def evenBoundaryInteger (r : Nat) : Fin 6 -> Int
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => 3 * r - 1
  | ⟨4, _⟩ => 1 - 3 * r
  | ⟨5, _⟩ => 3 * r

theorem evenBoundaryVertex_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (evenBoundaryVertex r) := by
  intro a b hab
  have hcast (x : Fin 6) : evenBoundaryVertex r x =
      (evenBoundaryInteger r x : ZMod (3 * (2 * r))) := by
    fin_cases x <;> simp [evenBoundaryVertex, evenBoundaryInteger]
  rw [hcast, hcast] at hab
  have hd : (3 * (2 * r) : Int) ∣
      evenBoundaryInteger r b - evenBoundaryInteger r a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hab
  have habs : |evenBoundaryInteger r b - evenBoundaryInteger r a| <
      (3 * (2 * r) : Int) := by
    fin_cases a <;> fin_cases b <;>
      simp [evenBoundaryInteger, abs_lt] <;> omega
  have heq : evenBoundaryInteger r a = evenBoundaryInteger r b := by
    have hz := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  fin_cases a <;> fin_cases b <;>
    simp [evenBoundaryInteger] at heq ⊢ <;> omega

/-- Integer flow on the literal residue vertices. -/
abbrev Flow (n : Nat) := ZMod n -> Int

def vertexFlow (n : Nat) (x : ZMod n) : Flow n :=
  fun v => if x = v then 1 else 0

def edgeFlow (n k : Nat) (f : Form) : Flow n :=
  vertexFlow n (formPair n k f).1 - vertexFlow n (formPair n k f).2

def statePositive : State -> Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -2
  | ⟨4, _⟩ => 0

def stateNegative : State -> Int
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 2

def halfSign : Half -> Int
  | .positive => 1
  | .negative => -1

/-- A processed prefix has charge `q` at `+1`, the displayed signed frontier
state at `±j`, and the forced residual charge at `-1`. -/
def configurationFlow (n : Nat) (h : Half) (s : State) (j : Nat)
    (q : Int) : Flow n :=
  q • vertexFlow n 1 +
    (halfSign h * statePositive s) • vertexFlow n (j : ZMod n) +
    (halfSign h * stateNegative s) • vertexFlow n (-(j : ZMod n)) +
    (-q - halfSign h * (statePositive s + stateNegative s)) • vertexFlow n (-1)

def boundaryFlow (n : Nat) (q : Int) : Flow n :=
  q • vertexFlow n 1 + (-q) • vertexFlow n (-1)

/-- Flow contributed by one low/reflected-high class pair. -/
def pairedFlow (n j : Nat) (low high : Form) : Flow n :=
  edgeFlow n j low + edgeFlow n (highClass n j) high

/-- Every allowed class-two label is exactly one of the four signed starts. -/
theorem start_classification (n : Nat) (f : Form) (hf : f.allowedAtTwo) :
    ∃ (h : Half) (i : StartIndex h),
      f = (startValue i).label ∧
      edgeFlow n 2 f = configurationFlow n h (startTarget i) 2
        (startValue i).charge := by
  fin_cases f <;> simp [Form.allowedAtTwo, Form.I, Form.II, Form.III, Form.IV,
    Form.V, Form.VI] at hf
  · exact ⟨.positive, 0, rfl, by
      have h : (1 - (2 : ZMod n)) = -1 := by ring
      simp [edgeFlow, formPair, configurationFlow, halfSign,
        statePositive, stateNegative, startValue, starts, startTarget, startTargets,
        State.A, h]
      module⟩
  · exact ⟨.negative, 0, rfl, by
      simp [edgeFlow, formPair, configurationFlow, halfSign,
        statePositive, stateNegative, startValue, starts, startTarget, startTargets,
        State.A]
      abel⟩
  · exact ⟨.positive, 1, rfl, by
      have h : ((2 : ZMod n) - 1) = 1 := by ring
      simp [edgeFlow, formPair, configurationFlow, halfSign,
        statePositive, stateNegative, startValue, starts, startTarget, startTargets,
        State.D, h]
      module⟩
  · exact ⟨.negative, 1, rfl, by
      simp [edgeFlow, formPair, configurationFlow, halfSign,
        statePositive, stateNegative, startValue, starts, startTarget, startTargets,
        State.D]
      abel⟩

/-- A selected table entry advances the literal residue flow by one retirement
level.  The proof checks the actual low and reflected-high endpoint formulas. -/
theorem transition_flow (n j : Nat) (hj0 : 1 ≤ j) (hj1 : j ≤ n + 1)
    (h : Half) (s : State)
    (i : StepIndex s) (q : Int) :
    configurationFlow n h s (j - 1) q +
      pairedFlow n j (stepValue (h := h) i).low (stepValue (h := h) i).high =
      configurationFlow n h (stepValue (h := h) i).target j
        (q + (stepValue (h := h) i).charge) := by
  have hjm : (((j - 1 : Nat) : ZMod n)) = (j : ZMod n) - 1 := by
    rw [Nat.cast_sub hj0]
    push_cast
    rfl
  have hnegjm : (-((j - 1 : Nat) : ZMod n)) = 1 - (j : ZMod n) := by
    rw [hjm]
    ring
  have hhigh : ((highClass n j : Nat) : ZMod n) = 1 - (j : ZMod n) := by
    unfold highClass
    rw [Nat.cast_sub hj1]
    push_cast
    simp [ZMod.natCast_self]
  have hhighSub : ((highClass n j : ZMod n) - 1) = -(j : ZMod n) := by
    rw [hhigh]
    ring
  have honeHigh : (1 - (highClass n j : ZMod n)) = (j : ZMod n) := by
    rw [hhigh]
    ring
  have hnegHigh : (-(highClass n j : ZMod n)) = (j : ZMod n) - 1 := by
    rw [hhigh]
    ring
  cases h <;> fin_cases s <;> fin_cases i <;>
    simp [configurationFlow, pairedFlow, edgeFlow, formPair,
      stepValue, positiveStepLabel, negativeStepLabel, stepTarget, stepTargets, halfSign,
      statePositive, stateNegative, State.A, State.D, State.E, State.H, State.I,
      Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI,
      hjm, hnegjm, hhigh, hhighSub, honeHigh, hnegHigh] <;>
    ring

/-- The even antipodal table resolves the final frontier. -/
theorem even_terminal_flow (r : Nat) (hr : 1 ≤ r) (h : Half) (s : State)
    (i : EvenTerminalIndex h s) (q : Int) :
    configurationFlow (3 * (2 * r)) h s (3 * r - 1) q +
      pairedFlow (3 * (2 * r)) (3 * r)
        (evenTerminalValue i).low (evenTerminalValue i).high =
      boundaryFlow (3 * (2 * r)) (q + (evenTerminalValue i).charge) := by
  have hsub : (((3 * r - 1 : Nat) : ZMod (3 * (2 * r)))) =
      (3 * r : ZMod (3 * (2 * r))) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hanti : ((3 * r : Nat) : ZMod (3 * (2 * r))) =
      -((3 * r : Nat) : ZMod (3 * (2 * r))) := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
    have heq : 3 * r + 3 * r = 3 * (2 * r) := by omega
    rw [heq]
    exact ZMod.natCast_self (3 * (2 * r))
  have hantiMul : (3 : ZMod (3 * (2 * r))) * r =
      -((3 : ZMod (3 * (2 * r))) * r) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hanti
  have hanti' : ((r : ZMod (3 * (2 * r))) * 3) =
      -((r : ZMod (3 * (2 * r))) * 3) := by
    simpa only [mul_comm] using hantiMul
  have hhigh : ((highClass (3 * (2 * r)) (3 * r) : Nat) :
      ZMod (3 * (2 * r))) = 1 - (3 * r : ZMod (3 * (2 * r))) := by
    unfold highClass
    have heq : 3 * (2 * r) + 1 - 3 * r = 3 * r + 1 := by omega
    rw [heq]
    push_cast
    calc
      3 * (r : ZMod (3 * (2 * r))) + 1 =
          -(3 * (r : ZMod (3 * (2 * r)))) + 1 :=
        congrArg (fun x => x + 1) hantiMul
      _ = 1 - 3 * (r : ZMod (3 * (2 * r))) := by ring
  have hvanti := congrArg (vertexFlow (3 * (2 * r))) hanti
  have hvanti' := congrArg (vertexFlow (3 * (2 * r))) hanti'
  have hnegHigh : (-(highClass (3 * (2 * r)) (3 * r) :
      ZMod (3 * (2 * r)))) = (3 * r : ZMod (3 * (2 * r))) - 1 := by
    rw [hhigh]
    ring
  cases h <;> fin_cases s
  all_goals first | exact Fin.elim0 i | skip
  all_goals fin_cases i
  all_goals
    simp [configurationFlow, boundaryFlow, pairedFlow, edgeFlow, formPair,
      evenTerminalValue,
      halfSign, statePositive, stateNegative, State.A, State.D,
      Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI,
      hsub, hhigh, hnegHigh]
    ring_nf
    rw [hvanti'.symm]
    ring

/-- The odd singleton table resolves the final frontier independently. -/
theorem odd_terminal_flow (r : Nat) (h : Half) (s : State)
    (i : OddTerminalIndex h s) (q : Int) :
    configurationFlow (3 * (2 * r + 1)) h s (3 * r + 1) q +
      edgeFlow (3 * (2 * r + 1)) (3 * r + 2) (oddTerminalValue i).label =
      boundaryFlow (3 * (2 * r + 1)) (q + (oddTerminalValue i).charge) := by
  have hplus : ((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) =
      -((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
    have heq : 3 * r + 2 + (3 * r + 1) = 3 * (2 * r + 1) := by omega
    rw [heq]
    exact ZMod.natCast_self (3 * (2 * r + 1))
  have hminus : (-((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1)))) =
      ((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := by rw [hplus, neg_neg]
  have hplus' : (2 + (r : ZMod (3 * (2 * r + 1))) * 3) =
      (-1 - (r : ZMod (3 * (2 * r + 1))) * 3) := by
    calc
      2 + (r : ZMod (3 * (2 * r + 1))) * 3 =
          ((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) := by push_cast; ring
      _ = -((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := hplus
      _ = -1 - (r : ZMod (3 * (2 * r + 1))) * 3 := by push_cast; ring
  have hminus' : (-2 - (r : ZMod (3 * (2 * r + 1))) * 3) =
      (1 + (r : ZMod (3 * (2 * r + 1))) * 3) := by
    calc
      -2 - (r : ZMod (3 * (2 * r + 1))) * 3 =
          -((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) := by push_cast; ring
      _ = ((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := hminus
      _ = 1 + (r : ZMod (3 * (2 * r + 1))) * 3 := by push_cast; ring
  have hvplus' := congrArg (vertexFlow (3 * (2 * r + 1))) hplus'
  have hvminus' := congrArg (vertexFlow (3 * (2 * r + 1))) hminus'
  have hsub : (((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) - 1) =
      ((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := by
    push_cast
    ring
  have honeSub : (1 - ((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1)))) =
      -((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := by
    push_cast
    ring
  cases h <;> fin_cases s
  all_goals first | exact Fin.elim0 i | skip
  all_goals fin_cases i
  all_goals simp [configurationFlow, boundaryFlow, edgeFlow, formPair,
    oddTerminalValue,
    halfSign, statePositive, stateNegative, State.A, State.D,
    Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI,
    hplus, hminus, hplus', hminus', hsub, honeSub]
  all_goals ring_nf
  all_goals
    first
    | rw [hvminus']; ring
    | rw [hvplus']; ring

end D5.S3.Combinatorics.Zigzag

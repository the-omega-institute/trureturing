/- GID: D5/S3/Combinatorics/Zigzag/ChoiceClassification
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/ChoiceClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Converse retirement classification for literal labelled choices. -/

import D5.S3.Combinatorics.Zigzag.Retirement
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

/-- A future literal class cannot touch either node already retired at level
`j`.  This is the no-future-touch statement used by the all-level parser. -/
theorem edgeFlow_future_zero (n j k : Nat) (f : Form)
    (hj : 3 ≤ j) (hjk : j < k) (hk : k ≤ n - j) :
    edgeFlow n k f ((j - 1 : Nat) : ZMod n) = 0 ∧
      edgeFlow n k f (-((j - 1 : Nat) : ZMod n)) = 0 := by
  have hkn : k < n := by omega
  have hjm : (((j - 1 : Nat) : ZMod n)) = ((j : Int) - 1 : Int) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hnegjm : (-((j - 1 : Nat) : ZMod n)) = (1 - (j : Int) : Int) := by
    rw [hjm]
    push_cast
    ring
  have neCast (a b : Int) (hne : a ≠ b)
      (hl : -(n : Int) < b - a) (hu : b - a < (n : Int)) :
      (a : ZMod n) ≠ (b : ZMod n) := by
    intro heq
    have hd : (n : Int) ∣ b - a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub a b n).mp heq
    have habs : |b - a| < (n : Int) := (abs_lt).2 ⟨hl, hu⟩
    have hz : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hd habs
    exact hne (by omega)
  have h1p : (1 : ZMod n) ≠ (j : ZMod n) - 1 := by
    simpa using neCast 1 ((j : Int) - 1) (by omega) (by omega) (by omega)
  have h1m : (1 : ZMod n) ≠ 1 - (j : ZMod n) := by
    simpa using neCast 1 (1 - (j : Int)) (by omega) (by omega) (by omega)
  have hkm1p : (k : ZMod n) - 1 ≠ (j : ZMod n) - 1 := by
    simpa using neCast ((k : Int) - 1) ((j : Int) - 1)
      (by omega) (by omega) (by omega)
  have hkm1m : (k : ZMod n) - 1 ≠ 1 - (j : ZMod n) := by
    simpa using neCast ((k : Int) - 1) (1 - (j : Int))
      (by omega) (by omega) (by omega)
  have hkp : (k : ZMod n) ≠ (j : ZMod n) - 1 := by
    simpa using neCast (k : Int) ((j : Int) - 1) (by omega) (by omega) (by omega)
  have hkm : (k : ZMod n) ≠ 1 - (j : ZMod n) := by
    simpa using neCast (k : Int) (1 - (j : Int)) (by omega) (by omega) (by omega)
  have hn1p : (-1 : ZMod n) ≠ (j : ZMod n) - 1 := by
    simpa using neCast (-1) ((j : Int) - 1) (by omega) (by omega) (by omega)
  have hn1m : (-1 : ZMod n) ≠ 1 - (j : ZMod n) := by
    simpa using neCast (-1) (1 - (j : Int)) (by omega) (by omega) (by omega)
  have h1mkp : 1 - (k : ZMod n) ≠ (j : ZMod n) - 1 := by
    simpa using neCast (1 - (k : Int)) ((j : Int) - 1)
      (by omega) (by omega) (by omega)
  have h1mkm : 1 - (k : ZMod n) ≠ 1 - (j : ZMod n) := by
    simpa using neCast (1 - (k : Int)) (1 - (j : Int))
      (by omega) (by omega) (by omega)
  have hnkp : -(k : ZMod n) ≠ (j : ZMod n) - 1 := by
    simpa using neCast (-(k : Int)) ((j : Int) - 1)
      (by omega) (by omega) (by omega)
  have hnkm : -(k : ZMod n) ≠ 1 - (j : ZMod n) := by
    simpa using neCast (-(k : Int)) (1 - (j : Int))
      (by omega) (by omega) (by omega)
  fin_cases f <;>
    simp [edgeFlow, vertexFlow, formPair, hjm, hnegjm, h1p, h1m, hkm1p,
      hkm1m, hkp, hkm, hn1p, hn1m, h1mkp, h1mkm, hnkp, hnkm]

/-- The six live residues at one strict interior retirement level. -/
def frontierVertex (n j : Nat) : Fin 6 -> ZMod n
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => (j : ZMod n) - 1
  | ⟨3, _⟩ => 1 - (j : ZMod n)
  | ⟨4, _⟩ => j
  | ⟨5, _⟩ => -(j : ZMod n)

private def frontierInteger (j : Nat) : Fin 6 -> Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => (j : Int) - 1
  | ⟨3, _⟩ => 1 - (j : Int)
  | ⟨4, _⟩ => j
  | ⟨5, _⟩ => -(j : Int)

/-- Strictly before the parity boundary, the six live residues are distinct. -/
theorem frontierVertex_injective (n j : Nat) (hj : 3 ≤ j) (hjn : 2 * j < n) :
    Function.Injective (frontierVertex n j) := by
  intro a b hab
  have hcast (x : Fin 6) :
      frontierVertex n j x = (frontierInteger j x : ZMod n) := by
    fin_cases x <;> simp [frontierVertex, frontierInteger]
  rw [hcast, hcast] at hab
  have hd : (n : Int) ∣ frontierInteger j b - frontierInteger j a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hab
  have habs : |frontierInteger j b - frontierInteger j a| < (n : Int) := by
    fin_cases a <;> fin_cases b <;> simp [frontierInteger, abs_lt] <;> omega
  have heq : frontierInteger j a = frontierInteger j b := by
    have hz := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  fin_cases a <;> fin_cases b <;> simp [frontierInteger] at heq ⊢ <;> omega

def lowRetiredPositive : Form -> Int
  | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1 | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 0

def lowRetiredNegative : Form -> Int
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0 | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 1

def highRetiredPositive : Form -> Int
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => -1 | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 0

def highRetiredNegative : Form -> Int
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => 0 | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 0

theorem pairedFlow_retiredPositive (n j : Nat) (hj0 : 1 ≤ j) (hj : j ≤ n + 1)
    (hinj : Function.Injective (frontierVertex n j)) (low high : Form) :
    pairedFlow n j low high ((j - 1 : Nat) : ZMod n) =
      lowRetiredPositive low + highRetiredPositive high := by
  have hjm : (((j - 1 : Nat) : ZMod n)) = (j : ZMod n) - 1 := by
    rw [Nat.cast_sub hj0]
    push_cast
    rfl
  have hhigh : ((highClass n j : Nat) : ZMod n) = 1 - (j : ZMod n) := by
    unfold highClass
    rw [Nat.cast_sub hj]
    push_cast
    simp
  have hhighSub : ((highClass n j : ZMod n) - 1) = -(j : ZMod n) := by
    rw [hhigh]
    ring
  have honeHigh : (1 - (highClass n j : ZMod n)) = (j : ZMod n) := by
    rw [hhigh]
    ring
  have hnegHigh : (-(highClass n j : ZMod n)) = (j : ZMod n) - 1 := by
    rw [hhigh]
    ring
  have hne (a b : Fin 6) (hab : a ≠ b) :
      frontierVertex n j a ≠ frontierVertex n j b := fun e => hab (hinj e)
  have h02 := hne 0 2 (by decide)
  have h12 := hne 1 2 (by decide)
  have h32 := hne 3 2 (by decide)
  have h42 := hne 4 2 (by decide)
  have h52 := hne 5 2 (by decide)
  simp [frontierVertex] at h02 h12 h32 h42 h52
  fin_cases low <;> fin_cases high <;>
    simp [pairedFlow, edgeFlow, vertexFlow, formPair, lowRetiredPositive,
      highRetiredPositive, hjm, hhigh, hhighSub, honeHigh,
      hnegHigh, h02, h12, h32, h42, h52]

theorem pairedFlow_retiredNegative (n j : Nat) (hj0 : 1 ≤ j) (hj : j ≤ n + 1)
    (hinj : Function.Injective (frontierVertex n j)) (low high : Form) :
    pairedFlow n j low high (-((j - 1 : Nat) : ZMod n)) =
      lowRetiredNegative low + highRetiredNegative high := by
  have hjm : (((j - 1 : Nat) : ZMod n)) = (j : ZMod n) - 1 := by
    rw [Nat.cast_sub hj0]
    push_cast
    rfl
  have hnegjm : (-((j - 1 : Nat) : ZMod n)) = 1 - (j : ZMod n) := by
    rw [hjm]
    ring
  have hhigh : ((highClass n j : Nat) : ZMod n) = 1 - (j : ZMod n) := by
    unfold highClass
    rw [Nat.cast_sub hj]
    push_cast
    simp
  have hhighSub : ((highClass n j : ZMod n) - 1) = -(j : ZMod n) := by
    rw [hhigh]
    ring
  have honeHigh : (1 - (highClass n j : ZMod n)) = (j : ZMod n) := by
    rw [hhigh]
    ring
  have hnegHigh : (-(highClass n j : ZMod n)) = (j : ZMod n) - 1 := by
    rw [hhigh]
    ring
  have hne (a b : Fin 6) (hab : a ≠ b) :
      frontierVertex n j a ≠ frontierVertex n j b := fun e => hab (hinj e)
  have h03 := hne 0 3 (by decide)
  have h13 := hne 1 3 (by decide)
  have h23 := hne 2 3 (by decide)
  have h43 := hne 4 3 (by decide)
  have h53 := hne 5 3 (by decide)
  simp [frontierVertex] at h03 h13 h23 h43 h53
  fin_cases low <;> fin_cases high <;>
    simp [pairedFlow, edgeFlow, vertexFlow, formPair, lowRetiredNegative,
      highRetiredNegative, hjm, hnegjm, hhigh, hhighSub,
      honeHigh, hnegHigh, h03, h13, h23, h43, h53]

/-- The complete 36-pair local converse.  The caller obtains the two integer
ledger equations by evaluating literal balance at the retired nodes. -/
theorem transition_labels_of_local_balance
    (h : Half) (s : State) (low high : Form)
    (hp : halfSign h * statePositive s + lowRetiredPositive low +
      highRetiredPositive high = 0)
    (hn : halfSign h * stateNegative s + lowRetiredNegative low +
      highRetiredNegative high = 0) :
    ∃ i : StepIndex s, low = (stepValue (h := h) i).low ∧
      high = (stepValue (h := h) i).high := by
  cases h <;> fin_cases s <;> fin_cases low <;> fin_cases high
  all_goals norm_num [lowRetiredPositive, lowRetiredNegative,
    highRetiredPositive, highRetiredNegative, halfSign,
    statePositive, stateNegative, StepIndex, stepTargets, stepTarget, stepValue,
    positiveStepLabel, negativeStepLabel, State.A, State.D, State.E, State.H,
    State.I, Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI] at *
  all_goals first | exact ⟨⟨0, by decide⟩, by decide⟩ |
    exact ⟨⟨1, by decide⟩, by decide⟩ |
    exact ⟨⟨2, by decide⟩, by decide⟩ |
    exact ⟨⟨3, by decide⟩, by decide⟩ |
    (simp only [← Fin.pos_iff_nonempty]; decide)

end D5.S3.Combinatorics.Zigzag

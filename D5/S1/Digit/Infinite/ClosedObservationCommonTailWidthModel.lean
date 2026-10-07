/- GID: D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual legal addresses and the complete closed endpoint graph model. -/

import D5.S1.Digit.Infinite.WindowCylinderPartition
import D5.S1.Scale.Embedding
import D5.S0.Carrier.Units
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Int.Interval

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.SignedSeriesRange (alpha signedValue signed_series_range)
open D5.S0.Carrier (GoldenInt conj conjEquiv phiUnit)
open D5.S1.Scale (embedding embedding_injective)
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres
open scoped Topology

/-- The reciprocal golden ratio. -/
noncomputable abbrev t : ℝ := alpha
/-- The contraction magnitude for exactly three deleted bits. -/
noncomputable def g : ℝ := t ^ 3
/-- The critical observation radius. -/
noncomputable def lambda : ℝ := t ^ 2 / 10
/-- Guard-relative scalar intervals; true denotes incoming guard one. -/
noncomputable def stateInterval (s : Bool) : Set ℝ :=
  Set.Icc (-1) (if s then t else 1 + t)
/-- The actual address restriction imposed by the incoming guard. -/
def stateAddress (s : Bool) (x : LegalDigits) : Prop := s = true → x.val 0 = false
/-- Shift an actual address by the specified number of individual bits. -/
def bitShift (x : LegalDigits) (n : ℕ) : LegalDigits :=
  ⟨fun j => x.val (j + n), fun j => by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using x.property (j + n)⟩
/-- The original deletion removes three bits, regardless of cylinder padding. -/
def originalT (x : LegalDigits) : LegalDigits := bitShift x 3
/-- The incoming guard after each actual three-bit deletion. -/
def actualGuard (s : Bool) (x : LegalDigits) (j : ℕ) : Bool :=
  if j = 0 then s else x.val (3 * j - 1)
/-- A legal three-bit window, in low-to-high order. -/
abbrev Label := D5.S1.Digit.Infinite.WindowSuccessorGraph.X 3
/-- The actual window at time j. -/
def window (x : LegalDigits) (j : ℕ) : Label :=
  D5.S1.Digit.Infinite.WindowSuccessorGraph.P 3 (bitShift x (3 * j))
/-- The empty window 000. -/
def nullLabel : Label := ⟨fun _ => false, by simp⟩
/-- The window 010, whose source label is three. -/
def threeLabel : Label := ⟨fun i => decide (i.val = 1), by
  intro j hj
  simp only [decide_eq_true_eq]
  omega⟩
/-- The window 100, whose source label is two. -/
def twoLabel : Label := ⟨fun i => decide (i.val = 0), by
  intro j hj
  simp only [decide_eq_true_eq]
  omega⟩
/-- The window 001, whose source label is five. -/
def fiveLabel : Label := ⟨fun i => decide (i.val = 2), by
  intro j hj
  simp only [decide_eq_true_eq]
  omega⟩
/-- The single window 101, whose source label is twenty-five. -/
def twoFiveLabel : Label := ⟨fun i => decide (i.val ≠ 1), by
  intro j hj
  simp only [decide_eq_true_eq]
  omega⟩
/-- The translation of a legal window: 0, 1, -t, 2-t, or t squared. -/
noncomputable def offset (l : Label) : ℝ :=
  (if l.val 0 then 1 else 0) - t * (if l.val 1 then 1 else 0) +
    t ^ 2 * (if l.val 2 then 1 else 0)
/-- The same window translation in the integral basis one, phi. -/
def offsetInteger (l : Label) : GoldenInt := ⟨
  (if l.val 0 then 1 else 0) + (if l.val 1 then 1 else 0) +
    2 * (if l.val 2 then 1 else 0),
  -(if l.val 1 then 1 else 0) - (if l.val 2 then 1 else 0)⟩
/-- The literal grouped-window series of the original address. -/
noncomputable def kappa (x : LegalDigits) : ℝ :=
  ∑' j : ℕ, (-g) ^ j * offset (window x j)
/-- A window changes the guard to its highest bit. -/
def outgoing (l : Label) : Bool := l.val 2
/-- The original legal guard graph, retaining the incoming restriction. -/
def lawful (s : Bool) (l : Label) (s' : Bool) : Prop :=
  (s = true → l.val 0 = false) ∧ s' = outgoing l
/-- A closed forward branch. -/
noncomputable def branch (l : Label) (y : ℝ) : ℝ := offset l - g * y
/-- The inverse branch used by the endpoint graph. -/
noncomputable def inverseBranch (l : Label) (x : ℝ) : ℝ := (offset l - x) / g
/-- A finite source is an actual address that is eventually zero. -/
def finiteTail (x : LegalDigits) : Prop := ∃ N, ∀ j, N ≤ j → x.val j = false
/-- The five fixed cuts of the six-cell instrument. -/
noncomputable def cuts (i : Fin 5) : ℝ :=
  match i.val with
  | 0 => -t ^ 2 - lambda
  | 1 => g - 3 * lambda
  | 2 => t - 5 * lambda
  | 3 => 2 * t - 7 * lambda
  | _ => 2 * t + lambda
/-- The unexpanded lower and upper endpoints, with the support endpoints retained. -/
noncomputable def cellLower (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => -1
  | 1 => cuts 0
  | 2 => cuts 1
  | 3 => cuts 2
  | 4 => cuts 3
  | _ => cuts 4
noncomputable def cellUpper (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => cuts 0
  | 1 => cuts 1
  | 2 => cuts 2
  | 3 => cuts 3
  | 4 => cuts 4
  | _ => 1 + t
/-- The complete closed expansion clipped to the support. -/
noncomputable def observation (b0 : ℝ) (i : Fin 6) : Set ℝ :=
  Set.Icc (max (-1) (cellLower i - b0)) (min (1 + t) (cellUpper i + b0))
/-- One fixed endpoint assignment for the instrument. -/
def instrument (Q : ℝ → Fin 6) : Prop :=
  ∀ x ∈ stateInterval false, x ∈ Set.Icc (cellLower (Q x)) (cellUpper (Q x))
/-- The exact, actually attainable closed-budget observation relation. -/
noncomputable def exactObservation (Q : ℝ → Fin 6) (b0 : ℝ) (i : Fin 6) : Set ℝ :=
  {x | x ∈ stateInterval false ∧ ∃ y ∈ stateInterval false, Q y = i ∧ |x - y| ≤ b0}
/-- The coefficient field is represented by its two rational coefficients. -/
def inCoefficientField (x : ℝ) : Prop := ∃ a b : ℚ, x = (a : ℝ) + b * t
/-- The original bounded-conjugate endpoint set, in the integral golden basis. -/
noncomputable def endpoints (q : ℕ) (R : ℝ) : Set ℝ :=
  {x | x ∈ stateInterval false ∧ ∃ z : GoldenInt,
    x = embedding z / q ∧ |embedding (conj z) / q| ≤ R}
/-- All effective observation endpoints and all guard and root-domain endpoints. -/
noncomputable def seeds (b0 : ℝ) : Set ℝ :=
  {-1, 1 + t, t, -t ^ 2, g, 2 * t} ∪
    Set.range (fun i : Fin 6 => max (-1) (cellLower i - b0)) ∪
    Set.range (fun i : Fin 6 => min (1 + t) (cellUpper i + b0))
/-- Numerical parameters for the original construction, with no lifting assumptions. -/
def endpointParameters (b0 : ℝ) (q : ℕ) (R : ℝ) : Prop :=
  1 ≤ q ∧ 0 ≤ R ∧ seeds b0 ⊆ endpoints q R ∧
    ∀ l : Label, |embedding (conj (offsetInteger l))| *
        g ≤ (1 - g) * R
/-- A basic closed piece is a singleton or the whole interval between adjacent endpoints. -/
def basicPiece (q : ℕ) (R : ℝ) (s : Bool) (a b : ℝ) : Prop :=
  a ∈ endpoints q R ∧ b ∈ endpoints q R ∧ a ∈ stateInterval s ∧
    b ∈ stateInterval s ∧ a ≤ b ∧
    (a = b ∨ ∀ c ∈ endpoints q R, a < c → c < b → False)
/-- Every guard-typed singleton and whole adjacent interval is a vertex. -/
def Vertex (q : ℕ) (R : ℝ) :=
  {v : Bool × ℝ × ℝ // basicPiece q R v.1 v.2.1 v.2.2}
/-- The whole closed set carried by a vertex. -/
noncomputable def piece {q : ℕ} {R : ℝ} (v : Vertex q R) : Set ℝ :=
  Set.Icc v.val.2.1 v.val.2.2
/-- The exact all-containment rule of the original endpoint graph. -/
noncomputable def edge {q : ℕ} {R : ℝ} (v : Vertex q R) (l : Label)
    (u : Vertex q R) : Prop :=
  lawful v.val.1 l u.val.1 ∧
    piece v ⊆ branch l '' stateInterval u.val.1 ∧
    piece u ⊆ inverseBranch l '' piece v
/-- A color is permitted only when the entire piece belongs to its expansion. -/
def permits {q : ℕ} {R : ℝ} (b0 : ℝ) (v : Vertex q R) (i : Fin 6) : Prop :=
  piece v ⊆ observation b0 i
/-- Finite observed paths have one fewer source edges than colors. -/
inductive ClosedPath {q : ℕ} {R : ℝ} (b0 : ℝ) :
    List (Fin 6) → List (Vertex q R) → List Label → Prop
  | point (i) (v) : permits b0 v i → ClosedPath b0 [i] [v] []
  | step (i) (r) (v u) (vs) (l) (w) :
      permits b0 v i → edge v l u → ClosedPath b0 r (u :: vs) w →
        ClosedPath b0 (i :: r) (v :: u :: vs) (l :: w)
/-- Joint realization uses the successive tails of one actual address. -/
noncomputable def addressChain {q : ℕ} {R : ℝ} (x : LegalDigits) :
    List (Vertex q R) → List Label → Prop
  | [v], [] => stateAddress v.val.1 x ∧ kappa x ∈ piece v
  | v :: u :: vs, l :: w => stateAddress v.val.1 x ∧ kappa x ∈ piece v ∧
      window x 0 = l ∧ addressChain (originalT x) (u :: vs) w
  | _, _ => False
/-- All distinct terminal-vertex/source-word pairs, including no-color initialization. -/
def histories {q : ℕ} {R : ℝ} (b0 : ℝ) (r : List (Fin 6)) :
    Set (Vertex q R × List Label) :=
  if r = [] then {vw | vw.1.val.1 = false ∧ vw.2 = []} else
    {vw | ∃ v vs, v.val.1 = false ∧ (v :: vs).getLast? = some vw.1 ∧
      ClosedPath b0 r (v :: vs) vw.2}
/-- A single global longest common prefix; the empty candidate family has empty prefix. -/
noncomputable def globalLCP {q : ℕ} {R : ℝ} (H : Set (Vertex q R × List Label)) :
    List Label := by
  classical
  exact if h : H.Nonempty then
    let w := (Classical.choose h).2
    w.take (Nat.findGreatest (fun n => ∀ vw ∈ H, w.take n <+: vw.2) w.length)
  else []
/-- Delete that same global prefix from every distinct candidate pair. -/
noncomputable def residuals {q : ℕ} {R : ℝ} (b0 : ℝ) (r : List (Fin 6)) :
    Set (Vertex q R × List Label) :=
  (fun vw => (vw.1, vw.2.drop
    (globalLCP (histories (q := q) (R := R) b0 r)).length)) '' histories b0 r

end D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel

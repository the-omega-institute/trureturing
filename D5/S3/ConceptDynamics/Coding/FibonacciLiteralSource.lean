/- GID: D5/S3/ConceptDynamics/Coding/FibonacciLiteralSource
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciLiteralSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal five-label Fibonacci sources retain one suffix coordinate at every occurrence. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

noncomputable def t : ℝ := (Real.sqrt 5 - 1) / 2
noncomputable def g : ℝ := 2 * t - 1
noncomputable def phi : ℝ := 1 + t
noncomputable def T2 : ℝ := 1 - t
noncomputable def lam : ℝ := T2 / 10
noncomputable def c0 : ℝ := 2 * t / 5
noncomputable def rho : ℝ := g ^ 6
noncomputable def chi : ℝ := g ^ 20

inductive Label | L3 | L0 | L5 | L2 | L25
  deriving DecidableEq, Repr
inductive Guard | G0 | G1
  deriving DecidableEq, Repr
inductive Side | high | low
  deriving DecidableEq, Repr
inductive Model | original | anchored
  deriving DecidableEq, Repr
abbrev Color := Fin 6
abbrev Ownership := Fin 5 → Bool

def nextGuard : Guard → Label → Option Guard
  | .G0, .L3 | .G0, .L0 | .G0, .L2 => some .G0
  | .G0, .L5 | .G0, .L25 => some .G1
  | .G1, .L3 | .G1, .L0 => some .G0
  | .G1, .L5 => some .G1
  | .G1, .L2 | .G1, .L25 => none

def walk : Guard → List Label → Option Guard
  | s, [] => some s
  | s, l :: w => (nextGuard s l).bind (fun s' => walk s' w)

def LegalWord (s e : Guard) (w : List Label) : Prop := walk s w = some e

noncomputable def supportUpper : Guard → ℝ
  | .G0 => phi
  | .G1 => t

def InSupport (s : Guard) (x : ℝ) : Prop := -1 ≤ x ∧ x ≤ supportUpper s

noncomputable def shift : Label → ℝ
  | .L3 => -t
  | .L0 => 0
  | .L5 => T2
  | .L2 => 1
  | .L25 => 2 - t

noncomputable def branch (l : Label) (x : ℝ) : ℝ := shift l - g * x

noncomputable def compose : List Label → ℝ → ℝ
  | [], x => x
  | l :: w, x => branch l (compose w x)

/-- A finite literal prefix followed by the empty-window label forever. -/
def address (w : List Label) (p : ℕ) : Label := w[p]?.getD .L0

/-- The complete remaining literal suffix, with the zero tail interpreted at zero. -/
noncomputable def coordinate (w : List Label) (p : ℕ) : ℝ := compose (w.drop p) 0

def repeatWord (w : List Label) : ℕ → List Label
  | 0 => []
  | n + 1 => w ++ repeatWord w n

def U : List Label := [.L5, .L0, .L3, .L0, .L3, .L3]
def V : List Label := [.L0, .L3, .L3, .L5, .L0, .L3]
def C : List Label :=
  [.L5, .L5, .L3, .L2, .L2, .L0, .L3, .L3, .L3, .L25,
   .L5, .L0, .L0, .L2, .L2, .L25, .L3, .L3, .L0, .L5]
def colorsD : List Color := [2, 1, 0, 2, 1, 0]
def colorsE : List Color := [2, 3, 0, 3, 4, 2, 0, 1, 0, 5, 2, 1, 1, 3, 3, 5, 0, 0, 1, 2]
def block : Side → List Label | .high => U | .low => V
def stem (j : Side) : List Label := block j ++ C

/-- All positive returns are source words; no budget cap is built into the carrier. -/
structure Return where
  m : ℕ
  r : ℕ
  m_pos : 0 < m
  r_pos : 0 < r
  deriving DecidableEq

def returnWord (j : Side) (a : Return) : List Label :=
  repeatWord (block j) a.m ++ repeatWord C a.r
def returnColors (a : Return) : List Color :=
  (List.replicate a.m colorsD).flatten ++ (List.replicate a.r colorsE).flatten
def externalWord (j : Side) (execution : List Return) : List Label :=
  (execution.reverse.map (returnWord j)).flatten
def anchor (j : Side) : Model → List Label
  | .original => []
  | .anchored => stem j
def observedPrefix (j : Side) (model : Model) (execution : List Return) : List Label :=
  stem j ++ externalWord j execution ++ anchor j model
def history (model : Model) (execution : List Return) : List Color :=
  colorsD ++ colorsE ++ (execution.reverse.map returnColors).flatten ++
    (match model with | .original => [] | .anchored => colorsD ++ colorsE)

/-- The final zero is part of a finite representation of the same eventually-zero tail. -/
def exitPrefix : Side → List Label | .high => [.L5, .L0] | .low => [.L0]
def tailPrefix (j : Side) : List Label :=
  block j ++ repeatWord C 3 ++ exitPrefix j
def sourcePrefix (j : Side) (model : Model) (execution : List Return) : List Label :=
  observedPrefix j model execution ++ tailPrefix j
def source (j : Side) (model : Model) (execution : List Return) : ℕ → Label :=
  address (sourcePrefix j model execution)

noncomputable def hSide : Side → ℝ
  | .high => (39 - 6 * g) / 380
  | .low => (46 + 31 * g) / 380
noncomputable def eSide : Side → ℝ | .high => T2 - c0 | .low => c0
noncomputable def aSide (j : Side) : ℝ := (1 - rho) * hSide j
noncomputable def xSide (j : Side) : ℝ := aSide j + rho * chi ^ 3 * eSide j
noncomputable def ySide (j : Side) : ℝ := aSide j + rho * chi * xSide j
noncomputable def sign : Side → ℝ | .high => 1 | .low => -1
noncomputable def returnMap (j : Side) (a : Return) (D : ℝ) : ℝ :=
  hSide j - rho ^ a.m * (hSide j - chi ^ a.r * D)
noncomputable def initial (j : Side) : Model → ℝ
  | .original => xSide j
  | .anchored => ySide j
noncomputable def execute (j : Side) : List Return → ℝ → ℝ
  | [], D => D
  | a :: rest, D => execute j rest (returnMap j a D)

def listWeight : List Return → ℕ
  | [] => 0
  | a :: rest => 6 * a.m + 20 * a.r + listWeight rest
def observationOffset : Model → ℕ | .original => 26 | .anchored => 52

def GuardTrace (K : ℕ) (d : ℝ) (strict : Bool) (j : Side) :
    List Return → ℝ → Prop
  | [], _ => True
  | a :: rest, D => a.r ≤ K ∧
      (a.r = K → if strict then d < D else d ≤ D) ∧
      GuardTrace K d strict j rest (returnMap j a D)

noncomputable def cut : ℕ → ℝ
  | 0 => -1
  | 1 => -T2 - lam
  | 2 => g - 3 * lam
  | 3 => t - 5 * lam
  | 4 => 2 * t - 7 * lam
  | 5 => 2 * t + lam
  | _ => phi

noncomputable def readout (o : Ownership) (x : ℝ) : Color :=
  if x < cut 1 then 0 else if x = cut 1 then (if o 0 then 1 else 0) else
  if x < cut 2 then 1 else if x = cut 2 then (if o 1 then 2 else 1) else
  if x < cut 3 then 2 else if x = cut 3 then (if o 2 then 3 else 2) else
  if x < cut 4 then 3 else if x = cut 4 then (if o 3 then 4 else 3) else
  if x < cut 5 then 4 else if x = cut 5 then (if o 4 then 5 else 4) else 5

def Cell (o : Ownership) (i : Color) (x : ℝ) : Prop :=
  InSupport .G0 x ∧ readout o x = i
def ClosedCell (i : Color) (x : ℝ) : Prop := cut i.val ≤ x ∧ x ≤ cut (i.val + 1)
noncomputable def clip (x : ℝ) : ℝ := max (-1) (min phi x)
noncomputable def observe (o : Ownership) (x error : ℝ) : Color := readout o (clip (x + error))

inductive Contract | closed | strict | recordMargin
  deriving DecidableEq, Repr
def ErrorBound (b : ℝ) : Contract → (ℕ → ℝ) → Prop
  | .closed, err => ∀ p, |err p| ≤ b
  | .strict, err => ∀ p, |err p| < b
  | .recordMargin, err => ∃ eps > 0, ∀ p, |err p| ≤ b - eps

/-- A readout/error relation on the two fixed sources, including their zero-error futures. -/
def ActualPairSupply (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (execution : List Return) : Prop :=
  ∀ j : Side, ∃ err : ℕ → ℝ, ErrorBound b contract err ∧
    (∀ p (hp : p < (history model execution).length),
      observe o (coordinate (sourcePrefix j model execution) p) (err p) =
        (history model execution)[p]) ∧
    (∀ p, (history model execution).length ≤ p → err p = 0) ∧
    (∀ p, observe o (coordinate (sourcePrefix j model execution)
        ((observedPrefix j model execution).length + p))
        (err ((observedPrefix j model execution).length + p)) =
      observe o (coordinate (tailPrefix j) p) 0)

/-- Legal branch supports and the affine law are derived from the literal source.
The occurrence formula uses the complete right suffix at that very occurrence. -/
theorem literal_source_geometry :
    (∀ (s e : Guard) (w : List Label) (z : ℝ), LegalWord s e w → InSupport e z →
      InSupport s (compose w z)) ∧
    (∀ (left B right : List Label) (p : ℕ), p ≤ B.length →
      coordinate (left ++ B ++ right) (left.length + p) =
        compose (B.drop p) c0 + (-g) ^ (B.length - p) * (coordinate right 0 - c0)) ∧
    (∀ (w : List Label) (n p : ℕ), coordinate (w ++ List.replicate n Label.L0) p =
      coordinate w p) ∧
    (∀ (w : List Label) (x y : ℝ),
      compose w (x + y) = compose w x + (-g) ^ w.length * y) ∧
    (∀ (w v : List Label) (z : ℝ), compose (w ++ v) z = compose w (compose v z)) := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsqrt0 := Real.sqrt_nonneg (5 : ℝ)
  have ht : t ^ 2 = 1 - t := by dsimp [t]; nlinarith
  have htlo : 0 < t := by dsimp [t]; nlinarith
  have hthi : t < 1 := by dsimp [t]; nlinarith
  have hg : 0 < g := by dsimp [g, t]; nlinarith
  have edge_support : ∀ (s e : Guard) (l : Label) (z : ℝ),
      nextGuard s l = some e → InSupport e z → InSupport s (branch l z) := by
    intro s e l z hedge hz
    have hlo := mul_nonneg hg.le (sub_nonneg.mpr hz.1)
    have hhi := mul_nonneg hg.le (sub_nonneg.mpr hz.2)
    cases s <;> cases e <;> cases l <;>
      simp_all [nextGuard, InSupport, supportUpper, branch, shift, phi, T2, g] <;>
      constructor <;> nlinarith
  have affine : ∀ (w : List Label) (x y : ℝ),
      compose w (x + y) = compose w x + (-g) ^ w.length * y := by
    intro w
    induction w with
    | nil => intro x y; simp [compose]
    | cons l w ih =>
      intro x y
      simp only [compose, List.length_cons, ih, branch, pow_succ]
      ring
  have append_compose : ∀ (w v : List Label) (z : ℝ),
      compose (w ++ v) z = compose w (compose v z) := by
    intro w
    induction w with
    | nil => intro v z; rfl
    | cons l w ih => intro v z; simp [compose, ih]
  have zero_tail : ∀ n, compose (List.replicate n Label.L0) 0 = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, compose, branch, shift, ih]
  refine ⟨?_, ?_, ?_, affine, append_compose⟩
  · intro s e w
    induction w generalizing s with
    | nil =>
      intro z hw hz
      have he : s = e := by simpa [LegalWord, walk] using hw
      simpa [compose, he] using hz
    | cons l w ih =>
      intro z hw hz
      cases hnext : nextGuard s l with
      | none => simp [LegalWord, walk, hnext] at hw
      | some s' =>
        have hrest : LegalWord s' e w := by simpa [LegalWord, walk, hnext] using hw
        exact edge_support s s' l (compose w z) hnext (ih s' z hrest hz)
  · intro left B right p hp
    unfold coordinate
    rw [show (left ++ B ++ right).drop (left.length + p) = B.drop p ++ right by
      rw [List.append_assoc, List.drop_append]
      simp only [List.drop_eq_nil_of_le (Nat.le_add_right left.length p),
        Nat.add_sub_cancel_left, List.nil_append]
      exact List.drop_append_of_le_length hp]
    rw [append_compose]
    have h := affine (B.drop p) c0 (compose right 0 - c0)
    rw [show c0 + (compose right 0 - c0) = compose right 0 by ring] at h
    simpa only [add_sub_cancel_left, List.length_drop, List.drop_zero] using h
  · intro w n p
    unfold coordinate
    by_cases hp : p ≤ w.length
    · rw [List.drop_append_of_le_length hp, append_compose, zero_tail]
    · have hp' : w.length ≤ p := le_of_not_ge hp
      simp [List.drop_append, List.drop_eq_nil_of_le hp', List.drop_replicate, zero_tail, compose]

set_option maxHeartbeats 6000000 in
-- The twenty-label affine calculation requires exact polynomial normalization.
/-- Reversed execution reconstructs the prescribed literal sources. Every positive
return is legal, and the boundary displacement is calculated from that source. -/
theorem paired_source_reconstruction (j : Side) (model : Model) (execution : List Return) :
    LegalWord .G0 .G0 (sourcePrefix j model execution) ∧
    (∀ p, source j model execution ((observedPrefix j model execution).length + p) =
      address (tailPrefix j) p) ∧
    (∀ p, coordinate (sourcePrefix j model execution)
        ((observedPrefix j model execution).length + p) = coordinate (tailPrefix j) p) ∧
    coordinate (externalWord j execution ++ anchor j model ++ tailPrefix j) 0 =
      c0 + sign j * execute j execution (initial j model) ∧
    (observedPrefix j model execution).length = observationOffset model + listWeight execution ∧
    (history model execution).length = observationOffset model + listWeight execution ∧
    (∀ D, compose C (c0 + sign j * D) = c0 + sign j * (chi * D)) ∧
    (∀ D, compose (block j) (c0 + sign j * D) =
      c0 + sign j * (aSide j + rho * D)) ∧
    (∀ (a : Return) D, compose (returnWord j a) (c0 + sign j * D) =
      c0 + sign j * returnMap j a D) ∧
    (∀ (xs : List Return) D, compose (externalWord j xs) (c0 + sign j * D) =
      c0 + sign j * execute j xs D) ∧
    compose (tailPrefix j) 0 = c0 + sign j * xSide j := by
  have affine := literal_source_geometry.2.2.2.1
  have app := literal_source_geometry.2.2.2.2
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have ht : t ^ 2 = 1 - t := by dsimp [t]; nlinarith only [hsqrt, Real.sqrt_nonneg (5 : ℝ)]
  have htg : t = (1 + g) / 2 := by dsimp [g]; ring
  have hg2 : g ^ 2 = 1 - 4 * g := by dsimp [g]; nlinarith only [ht]
  have hg3 : g ^ 3 = 17 * g - 4 := by rw [pow_succ, hg2]; nlinarith only [hg2]
  have hg4 : g ^ 4 = 17 - 72 * g := by rw [pow_succ, hg3]; nlinarith only [hg2]
  have hg5 : g ^ 5 = 305 * g - 72 := by rw [pow_succ, hg4]; nlinarith only [hg2]
  have hg6 : g ^ 6 = 305 - 1292 * g := by rw [pow_succ, hg5]; nlinarith only [hg2]
  have hg7 : g ^ 7 = 5473 * g - 1292 := by rw [pow_succ, hg6]; nlinarith only [hg2]
  have centerC : compose C c0 = c0 := by
    have s19 : branch .L5 c0 = (3 + g) / 10 := by
      dsimp [branch, shift, T2, c0]; rw [htg]; nlinarith only [hg2]
    have s18 : branch .L0 ((3 + g) / 10) = (-1 + g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s17 : branch .L3 ((-1 + g) / 10) = -6 / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s16 : branch .L3 (-6 / 10) = (-5 + g) / 10 := by
      dsimp [branch, shift]; rw [htg]; ring
    have s15 : branch .L25 ((-5 + g) / 10) = (14 + 4 * g) / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s14 : branch .L2 ((14 + 4 * g) / 10) = (6 + 2 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s13 : branch .L2 ((6 + 2 * g) / 10) = (8 + 2 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s12 : branch .L0 ((8 + 2 * g) / 10) = -2 / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s11 : branch .L0 (-2 / 10) = (2 * g) / 10 := by
      dsimp [branch, shift]; ring
    have s10 : branch .L5 ((2 * g) / 10) = (3 + 3 * g) / 10 := by
      dsimp [branch, shift, T2]; rw [htg]; nlinarith only [hg2]
    have s9 : branch .L25 ((3 + 3 * g) / 10) = (12 + 4 * g) / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s8 : branch .L3 ((12 + 4 * g) / 10) = (-9 - g) / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s7 : branch .L3 ((-9 - g) / 10) = -4 / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s6 : branch .L3 (-4 / 10) = (-5 - g) / 10 := by
      dsimp [branch, shift]; rw [htg]; ring
    have s5 : branch .L0 ((-5 - g) / 10) = (1 + g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s4 : branch .L2 ((1 + g) / 10) = (9 + 3 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s3 : branch .L2 ((9 + 3 * g) / 10) = (7 + 3 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s2 : branch .L3 ((7 + 3 * g) / 10) = -8 / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s1 : branch .L5 (-8 / 10) = (5 + 3 * g) / 10 := by
      dsimp [branch, shift, T2]; rw [htg]; ring
    have s0 : branch .L5 ((5 + 3 * g) / 10) = c0 := by
      dsimp [branch, shift, T2, c0]; rw [htg]; nlinarith only [hg2]
    simp only [C, compose, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10,
      s9, s8, s7, s6, s5, s4, s3, s2, s1, s0]
  have centerBlock : compose (block j) c0 = c0 + sign j * aSide j := by
    cases j <;> dsimp [block, U, V, compose, branch, shift, T2, c0, sign, aSide,
      rho, hSide] <;> rw [htg] <;> ring_nf <;> linarith only [hg2, hg3, hg4, hg5, hg6, hg7]
  have actC (D : ℝ) : compose C (c0 + sign j * D) = c0 + sign j * (chi * D) := by
    rw [affine, centerC]
    norm_num [C, chi, neg_pow]
    ring
  have actBlock (D : ℝ) : compose (block j) (c0 + sign j * D) =
      c0 + sign j * (aSide j + rho * D) := by
    rw [affine, centerBlock]
    have hlen : (block j).length = 6 := by cases j <;> rfl
    rw [hlen]
    norm_num [rho, neg_pow]
    ring
  have copiesC : ∀ n (D : ℝ), compose (repeatWord C n) (c0 + sign j * D) =
      c0 + sign j * (chi ^ n * D) := by
    intro n
    induction n with
    | zero => intro D; simp [repeatWord, compose]
    | succ n ih =>
      intro D
      rw [repeatWord, app, ih, actC, pow_succ]
      ring
  have copiesBlock : ∀ n (D : ℝ), compose (repeatWord (block j) n) (c0 + sign j * D) =
      c0 + sign j * (hSide j - rho ^ n * (hSide j - D)) := by
    intro n
    induction n with
    | zero => intro D; simp [repeatWord, compose]
    | succ n ih =>
      intro D
      rw [repeatWord, app, ih, actBlock, pow_succ]
      dsimp [aSide]
      ring
  have actReturn (a : Return) (D : ℝ) :
      compose (returnWord j a) (c0 + sign j * D) = c0 + sign j * returnMap j a D := by
    rw [returnWord, app, copiesC, copiesBlock]
    rfl
  have external_cons (a : Return) (rest : List Return) :
      externalWord j (a :: rest) = externalWord j rest ++ returnWord j a := by
    simp [externalWord, List.reverse_cons, List.map_append, List.flatten_append]
  have actExternal : ∀ (xs : List Return) (D : ℝ),
      compose (externalWord j xs) (c0 + sign j * D) = c0 + sign j * execute j xs D := by
    intro xs
    induction xs with
    | nil => intro D; rfl
    | cons a rest ih => intro D; rw [external_cons, app, actReturn, ih]; rfl
  have actTail : compose (tailPrefix j) 0 = c0 + sign j * xSide j := by
    have hexit (j' : Side) : compose (exitPrefix j') 0 = c0 + sign j' * eSide j' := by
      cases j' <;> simp only [exitPrefix, compose, branch, shift, sign, eSide,
        mul_zero, sub_zero] <;> ring
    rw [tailPrefix, app, app, hexit j, copiesC, actBlock]
    dsimp [xSide]
    ring
  have actAnchorTail : compose (anchor j model ++ tailPrefix j) 0 =
      c0 + sign j * initial j model := by
    cases model with
    | original => simpa [anchor, initial, compose] using actTail
    | anchored =>
      rw [anchor, app, actTail, stem, app, actC, actBlock]
      dsimp [initial, ySide]
      ring
  have walk_app : ∀ (w v : List Label) (s : Guard), walk s (w ++ v) =
      (walk s w).bind (fun e => walk e v) := by
    intro w
    induction w with
    | nil => intro v s; rfl
    | cons l w ih =>
      intro v s
      cases hn : nextGuard s l <;> simp [walk, hn, ih]
  have walkBlock (s : Guard) : walk s (block j) = some .G0 := by
    cases s <;> cases j <;> rfl
  have walkC (s : Guard) : walk s C = some .G1 := by cases s <;> rfl
  have walkCopiesBlock : ∀ n (s : Guard), walk s (repeatWord (block j) (n + 1)) = some .G0 := by
    intro n
    induction n with
    | zero => intro s; simpa only [repeatWord, List.append_nil] using walkBlock s
    | succ n ih =>
      intro s
      rw [repeatWord, walk_app, walkBlock]
      exact ih .G0
  have walkCopiesC : ∀ n (s : Guard), walk s (repeatWord C (n + 1)) = some .G1 := by
    intro n
    induction n with
    | zero => intro s; simpa only [repeatWord, List.append_nil] using walkC s
    | succ n ih =>
      intro s
      rw [repeatWord, walk_app, walkC]
      exact ih .G1
  have walkReturn (a : Return) (s : Guard) : walk s (returnWord j a) = some .G1 := by
    obtain ⟨m, r, hm, hr⟩ := a
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    simp [returnWord, walk_app, walkCopiesBlock, walkCopiesC]
  have walkExternal : ∀ xs, walk .G1 (externalWord j xs) = some .G1 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih => simp [external_cons, walk_app, ih, walkReturn]
  have walkStem (s : Guard) : walk s (stem j) = some .G1 := by
    simp [stem, walk_app, walkBlock, walkC]
  have walkAnchor : walk .G1 (anchor j model) = some .G1 := by
    cases model <;> simp [anchor, walkStem, walk]
  have walkTail : walk .G1 (tailPrefix j) = some .G0 := by cases j <;> rfl
  have repeatLength : ∀ (w : List Label) n, (repeatWord w n).length = w.length * n := by
    intro w n
    induction n with
    | zero => rfl
    | succ n ih => simp [repeatWord, ih, Nat.mul_succ, Nat.add_comm]
  have returnLength (a : Return) : (returnWord j a).length = 6 * a.m + 20 * a.r := by
    cases j <;> simp [returnWord, repeatLength, block, U, V, C]
  have externalLength : ∀ xs, (externalWord j xs).length = listWeight xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih => simp [external_cons, returnLength, ih, listWeight, Nat.add_comm]
  have colorsLength (a : Return) : (returnColors a).length = 6 * a.m + 20 * a.r := by
    simp [returnColors, List.length_flatten, colorsD, colorsE, Nat.mul_comm]
  have historyVariableLength : ∀ xs : List Return,
      (xs.reverse.map returnColors).flatten.length = listWeight xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.reverse_cons, List.map_append, List.flatten_append, List.length_append,
        List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [ih, colorsLength]
      simp only [listWeight, Nat.add_comm]
  have stemLength : (stem j).length = 26 := by cases j <;> rfl
  have lenCalc (md : Model) (n : ℕ) :
      26 + n + (anchor j md).length = observationOffset md + n := by
    cases md <;> simp only [anchor, List.length_nil, stemLength, observationOffset] <;> omega
  have colorAnchorLength (md : Model) :
      (match md with | .original => [] | .anchored => colorsD ++ colorsE).length =
        (anchor j md).length := by
    cases md <;> simp only [anchor, List.length_nil, stemLength]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, actC, actBlock, actReturn, actExternal, actTail⟩
  · simp [LegalWord, sourcePrefix, observedPrefix, walk_app, walkStem, walkExternal,
      walkAnchor, walkTail]
  · intro p
    simp [source, sourcePrefix, address, List.getElem?_append_right]
  · intro p
    simp only [coordinate, sourcePrefix, List.drop_append, Nat.add_sub_cancel_left,
      List.drop_eq_nil_of_le (Nat.le_add_right (observedPrefix j model execution).length p),
      List.nil_append]
  · simp only [coordinate, List.drop_zero, List.append_assoc]
    rw [app, actAnchorTail, actExternal]
  · simp only [observedPrefix, List.length_append, stemLength, externalLength]
    exact lenCalc model (listWeight execution)
  · have hd : colorsD.length = 6 := rfl
    have he : colorsE.length = 20 := rfl
    simp only [history, List.length_append, hd, he, historyVariableLength, colorAnchorLength]
    exact lenCalc model (listWeight execution)

/-- The legal finite prefix constructs the guard itinerary and coordinate path
of its eventually-empty address, including all zero-tail departure positions. -/
theorem literal_address_path (s e : Guard) (w : List Label) (hw : LegalWord s e w) :
    ∃ path : ℕ → Guard, path 0 = s ∧
      (∀ p, nextGuard (path p) (address w p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (coordinate w p)) ∧
      (∀ p, coordinate w p = branch (address w p) (coordinate w (p + 1))) := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have ht : 0 ≤ t := by dsimp [t]; nlinarith only [hsqrt, Real.sqrt_nonneg (5 : ℝ)]
  have zeroSupport (q : Guard) : InSupport q 0 := by
    cases q <;> simp only [InSupport, supportUpper, phi] <;> constructor <;> linarith
  induction w generalizing s with
  | nil =>
    refine ⟨fun p => if p = 0 then s else .G0, by simp, ?_, ?_, ?_⟩
    · intro p
      cases p with
      | zero => cases s <;> rfl
      | succ p => simp [address, nextGuard]
    · intro p
      simpa only [coordinate, List.drop_nil, compose] using
        zeroSupport (if p = 0 then s else .G0)
    · intro p
      simp [coordinate, address, compose, branch, shift]
  | cons l w ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord, walk, hn] at hw
    | some q =>
      have hr : LegalWord q e w := by simpa [LegalWord, walk, hn] using hw
      obtain ⟨path, hzero, hleg, hsupp, hrec⟩ := ih q hr
      refine ⟨fun p => match p with | 0 => s | p + 1 => path p, rfl, ?_, ?_, ?_⟩
      · intro p
        cases p with
        | zero => simpa [address, hzero] using hn
        | succ p => simpa [address, Nat.add_assoc] using hleg p
      · intro p
        cases p with
        | zero => exact literal_source_geometry.1 s e (l :: w) 0 hw (zeroSupport e)
        | succ p => simpa [coordinate] using hsupp p
      · intro p
        cases p with
        | zero => simp [coordinate, address, compose]
        | succ p => simpa [coordinate, address, Nat.add_assoc] using hrec p


/-- Acquisition at every original six- and twenty-slot departure coordinate.
The active slot uses the actual endpoint flag; all other flags remain arbitrary. -/
def BlockSupply (o : Ownership) (b : ℝ) (strict : Bool)
    (w : List Label) (cs : List Color) (z : ℝ) : Prop :=
  ∀ p (hp : p < cs.length), ∃ error : ℝ,
    (if strict then |error| < b else |error| ≤ b) ∧
    observe o (compose (w.drop p) z) error = cs[p]

set_option maxHeartbeats 4000000 in
-- Finite slot certificates include all six and twenty original departure positions.
theorem literal_full_slot_readout (o : Ownership) (b : ℝ) (hb : lam - rho < b) :
    (∀ (j : Side) (D : ℝ), 0 < D → D ≤ eSide j →
      (BlockSupply o b true (block j) colorsD (c0 + sign j * D) ↔
        lam - g ^ 2 * D < b)) ∧
    (∀ (j : Side) (D : ℝ), 0 < D → D ≤ eSide j →
      (BlockSupply o b false (block j) colorsD (c0 + sign j * D) ↔
        lam - g ^ 2 * D < b ∨
          (lam - g ^ 2 * D = b ∧
            (match j with | .high => o 0 = true | .low => o 1 = false)))) ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ T2 → BlockSupply o b true C colorsE z) := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hg2 : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have hg0 : 0 < g := by dsimp [g, t]; nlinarith
  have htg : t = (1 + g) / 2 := by dsimp [g]; ring
  have hglo : 4 / 17 < g := by nlinarith
  have hghi : g < 17 / 72 := by nlinarith
  have hgquarter : g < 1 / 4 := by linarith
  have hgprecise : 59 / 250 < g := by nlinarith only [hg2, hg0]
  have hrho : rho < 1 / 4096 := by
    have h := pow_lt_pow_left₀ hgquarter hg0.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at h ⊢
    exact h
  have hlam : 3 / 80 < lam := by dsimp [lam, T2]; rw [htg]; linarith
  have hb0 : 0 < b := by linarith
  have hT : 0 < T2 ∧ T2 < 2 / 5 := by dsimp [T2]; rw [htg]; constructor <;> linarith
  have hE (j : Side) : 0 < eSide j ∧ eSide j < 2 / 5 := by
    cases j <;> dsimp [eSide, T2, c0] <;> rw [htg] <;> constructor <;> linarith
  have cuts : cut 0 < cut 1 ∧ cut 1 < cut 2 ∧ cut 2 < cut 3 ∧
      cut 3 < cut 4 ∧ cut 4 < cut 5 ∧ cut 5 < cut 6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [cut, lam, T2, phi] <;> try simp only [htg] <;> linarith
  have interior (i : Color) (y : ℝ) (hlo : cut i.val < y)
      (hhi : y < cut (i.val + 1)) : observe o y 0 = i := by
    have hs : -1 ≤ y ∧ y ≤ phi := by
      fin_cases i <;> norm_num [cut, lam, T2, phi] at hlo hhi ⊢ <;>
        simp only [htg] at hlo hhi ⊢ <;> constructor <;> linarith
    simp only [observe, add_zero, clip, min_eq_right hs.2, max_eq_right hs.1]
    fin_cases i <;> simp only [readout] <;> split_ifs <;> try rfl
    all_goals norm_num at *
    all_goals linarith [cuts.1, cuts.2.1, cuts.2.2.1, cuts.2.2.2.1,
        cuts.2.2.2.2.1, cuts.2.2.2.2.2]
  have acquire (i : Color) (x : ℝ) (hlo : cut i.val - b < x)
      (hhi : x < cut (i.val + 1) + b) :
      ∃ error : ℝ, |error| < b ∧ observe o x error = i := by
    have hc : cut i.val < cut (i.val + 1) := by
      fin_cases i <;> first
      | exact cuts.1
      | exact cuts.2.1
      | exact cuts.2.2.1
      | exact cuts.2.2.2.1
      | exact cuts.2.2.2.2.1
      | exact cuts.2.2.2.2.2
    have hint : max (cut i.val) (x - b) < min (cut (i.val + 1)) (x + b) := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      constructor <;> constructor <;> linarith
    obtain ⟨y, hyl, hyr⟩ := exists_between hint
    have hylo := (lt_of_le_of_lt (le_max_left _ _) hyl)
    have hyhi := (lt_of_lt_of_le hyr (min_le_left _ _))
    refine ⟨y - x, abs_lt.mpr ⟨?_, ?_⟩, ?_⟩
    · have := lt_of_le_of_lt (le_max_right _ _) hyl; linarith
    · have := lt_of_lt_of_le hyr (min_le_right _ _); linarith
    · have he : x + (y - x) = y := by ring
      simpa only [observe, he, add_zero] using interior i y hylo hyhi
  have colorOne (y : ℝ) (h : readout o y = 1) : cut 1 ≤ y ∧ y ≤ cut 2 := by
    unfold readout at h
    split_ifs at h <;> try { have hv := congrArg Fin.val h; norm_num at hv }
    all_goals constructor <;> linarith
  have clipq1 : clip (cut 1) = cut 1 := by
    have hlo : -1 ≤ cut 1 := by simpa only [cut] using cuts.1.le
    have hhi : cut 1 ≤ phi := by
      have hh := le_trans cuts.2.1.le (le_trans cuts.2.2.1.le
        (le_trans cuts.2.2.2.1.le (le_trans cuts.2.2.2.2.1.le cuts.2.2.2.2.2.le)))
      simpa only [cut] using hh
    simp only [clip, min_eq_right hhi, max_eq_right hlo]
  have clipq2 : clip (cut 2) = cut 2 := by
    have hlo : -1 ≤ cut 2 := by simpa only [cut] using (le_trans cuts.1.le cuts.2.1.le)
    have hhi : cut 2 ≤ phi := by
      have hh := le_trans cuts.2.2.1.le (le_trans cuts.2.2.2.1.le
        (le_trans cuts.2.2.2.2.1.le cuts.2.2.2.2.2.le))
      simpa only [cut] using hh
    simp only [clip, min_eq_right hhi, max_eq_right hlo]
  have q1Read : readout o (cut 1) = 1 ↔ o 0 = true := by
    cases ho : o 0 <;> simp [readout, ho, ne_of_lt cuts.2.1, cuts.2.1]
  have q2Read : readout o (cut 2) = 1 ↔ o 1 = false := by
    cases ho : o 1 <;> simp [readout, ho, not_lt.mpr cuts.2.1.le,
      ne_of_gt cuts.2.1, cuts.2.2.1]
  have clipOne (x error : ℝ) (h : observe o x error = 1) :
      cut 1 ≤ x + error ∧ x + error ≤ cut 2 := by
    have hy := colorOne (clip (x + error)) h
    have hq1 : -1 < cut 1 := cuts.1
    have hq2 : cut 2 < phi := lt_trans cuts.2.2.1
      (lt_trans cuts.2.2.2.1 (lt_trans cuts.2.2.2.2.1 cuts.2.2.2.2.2))
    simp only [clip] at hy
    constructor
    · by_contra hn
      have hh : x + error < cut 1 := lt_of_not_ge hn
      have := max_lt hq1 (lt_of_le_of_lt (min_le_right phi (x + error)) hh)
      linarith
    · by_contra hn
      have hh : cut 2 < x + error := lt_of_not_ge hn
      have := lt_of_lt_of_le (lt_min hq2 hh) (le_max_right (-1) (min phi (x + error)))
      linarith
  let pointsU : ℕ → ℝ := fun p => match p with
    | 0 => (-257 / 5) + (1096 / 5) * g
    | 1 => (-121 / 10) + (519 / 10) * g
    | 2 => (-7 / 2) + (121 / 10) * g
    | 3 => (-3 / 5) + 3 * g
    | 4 => (-3 / 5) + (3 / 5) * g
    | 5 => (-7 / 10) + (1 / 10) * g
    | _ => c0
  let pointsV : ℕ → ℝ := fun p => match p with
    | 0 => (-342 / 5) + (1451 / 5) * g
    | 1 => (-83 / 5) + (342 / 5) * g
    | 2 => (-9 / 2) + (161 / 10) * g
    | 3 => (-3 / 5) + 4 * g
    | 4 => (-1 / 10) + (11 / 10) * g
    | 5 => (-7 / 10) + (1 / 10) * g
    | _ => c0
  let pointsC : ℕ → ℝ := fun p => match p with
    | 0 => (1 / 5) + (1 / 5) * g
    | 1 => (1 / 2) + (3 / 10) * g
    | 2 => (-4 / 5) + 0 * g
    | 3 => (7 / 10) + (3 / 10) * g
    | 4 => (9 / 10) + (3 / 10) * g
    | 5 => (1 / 10) + (1 / 10) * g
    | 6 => (-1 / 2) + (-1 / 10) * g
    | 7 => (-2 / 5) + 0 * g
    | 8 => (-9 / 10) + (-1 / 10) * g
    | 9 => (6 / 5) + (2 / 5) * g
    | 10 => (3 / 10) + (3 / 10) * g
    | 11 => 0 + (1 / 5) * g
    | 12 => (-1 / 5) + 0 * g
    | 13 => (4 / 5) + (1 / 5) * g
    | 14 => (3 / 5) + (1 / 5) * g
    | 15 => (7 / 5) + (2 / 5) * g
    | 16 => (-1 / 2) + (1 / 10) * g
    | 17 => (-3 / 5) + 0 * g
    | 18 => (-1 / 10) + (1 / 10) * g
    | 19 => (3 / 10) + (1 / 10) * g
    | _ => c0

  have suffixTable (w : List Label) (n : ℕ) (points : ℕ → ℝ)
      (hlen : w.length = n) (hlast : points n = c0)
      (hstep : ∀ p (hp : p < n), points p = branch (w[p]'(by omega)) (points (p + 1))) :
      ∀ p, p ≤ n → compose (w.drop p) c0 = points p := by
    intro p hp
    refine Nat.decreasingInduction' (m := p) (n := n)
      (P := fun k => compose (w.drop k) c0 = points k) ?_ hp ?_
    · intro k hk _ ih
      rw [List.drop_eq_getElem_cons (by omega : k < w.length), compose, ih]
      exact (hstep k hk).symm
    · rw [List.drop_eq_nil_of_le (by omega), compose, hlast]
  have tableU : ∀ p, p ≤ 6 → compose (U.drop p) c0 = pointsU p := by
    apply suffixTable U 6 pointsU rfl (by simp [pointsU])
    intro p hp
    have hp' : p ∈ Finset.range 6 := Finset.mem_range.mpr hp
    fin_cases hp' <;> norm_num [pointsU, U, branch, shift, T2, c0]
    all_goals try simp only [htg]
    all_goals nlinarith only [hg2]
  have tableV : ∀ p, p ≤ 6 → compose (V.drop p) c0 = pointsV p := by
    apply suffixTable V 6 pointsV rfl (by simp [pointsV])
    intro p hp
    have hp' : p ∈ Finset.range 6 := Finset.mem_range.mpr hp
    fin_cases hp' <;> norm_num [pointsV, V, branch, shift, T2, c0]
    all_goals try simp only [htg]
    all_goals nlinarith only [hg2]
  have tableC : ∀ p, p ≤ 20 → compose (C.drop p) c0 = pointsC p := by
    apply suffixTable C 20 pointsC rfl (by simp [pointsC])
    intro p hp
    have hp' : p ∈ Finset.range 20 := Finset.mem_range.mpr hp
    fin_cases hp' <;> norm_num [pointsC, C, branch, shift, T2, c0]
    all_goals try simp only [htg]
    all_goals nlinarith only [hg2]
  have perturb (w : List Label) (p : ℕ) (z : ℝ) (hz : |z - c0| ≤ 2 / 5) :
      |compose (w.drop p) z - compose (w.drop p) c0| ≤
        (1 / 4 : ℝ) ^ (w.length - p) * (2 / 5) := by
    have hh := literal_source_geometry.2.2.2.1 (w.drop p) c0 (z - c0)
    rw [show c0 + (z - c0) = z by ring] at hh
    rw [hh, add_sub_cancel_left, abs_mul, abs_pow, abs_neg, abs_of_pos hg0, List.length_drop]
    exact mul_le_mul (pow_le_pow_left₀ hg0.le hgquarter.le _) hz (abs_nonneg _) (by positivity)
  have nonactive (j : Side) (D : ℝ) (hD : 0 < D) (hDE : D ≤ eSide j)
      (p : ℕ) (hp : p < 6) (hne : p ≠ 4) :
      ∃ error : ℝ, |error| < b ∧
        observe o (compose ((block j).drop p) (c0 + sign j * D)) error = colorsD[p] := by
    have hDmax : D < 2 / 5 := lt_of_le_of_lt hDE (hE j).2
    have hz : |c0 + sign j * D - c0| ≤ 2 / 5 := by
      cases j <;> simp [sign, abs_of_pos hD, abs_of_neg (neg_neg_of_pos hD)] <;> linarith
    have hpert := perturb (block j) p (c0 + sign j * D) hz
    have hlen : (block j).length = 6 := by cases j <;> rfl
    rw [hlen] at hpert
    obtain ⟨hl, hu⟩ := abs_le.mp hpert
    have hp' : p ∈ Finset.range 6 := Finset.mem_range.mpr hp
    cases j <;> fin_cases hp' <;> try contradiction
    all_goals
      apply acquire
      all_goals simp only [block] at hl hu ⊢
      all_goals first | rw [tableU _ (by omega)] at hl hu | rw [tableV _ (by omega)] at hl hu
      all_goals norm_num [pointsU, pointsV, colorsD, cut, lam, T2, phi] at hl hu ⊢
      all_goals try simp only [htg] at hl hu ⊢
      all_goals have hb' := hb; dsimp [lam, T2] at hb'; simp only [htg] at hb'
      all_goals linarith
  have activeCoord (j : Side) (D : ℝ) :
      compose ((block j).drop 4) (c0 + sign j * D) =
        match j with | .high => cut 1 - lam + g ^ 2 * D
                     | .low => cut 2 + lam - g ^ 2 * D := by
    cases j <;> norm_num [block, U, V, compose, branch, shift, cut, lam, T2, sign, c0]
    all_goals rw [htg]; nlinarith [hg2]
  have costPos (j : Side) (D : ℝ) (hD : 0 < D) (hDE : D ≤ eSide j) :
      0 < lam - g ^ 2 * D := by
    have hDmax : D < 2 / 5 := lt_of_le_of_lt hDE (hE j).2
    have hsq : g ^ 2 < 1 / 16 := by nlinarith
    have hm := mul_lt_mul_of_pos_left hDmax (sq_pos_of_pos hg0)
    nlinarith
  have activeStrict (j : Side) (D : ℝ) (hD : 0 < D) (hDE : D ≤ eSide j) :
      (∃ error : ℝ, |error| < b ∧
        observe o (compose ((block j).drop 4) (c0 + sign j * D)) error = 1) ↔
          lam - g ^ 2 * D < b := by
    rw [activeCoord]
    constructor
    · rintro ⟨error, he, hread⟩
      have hh := clipOne _ _ hread
      obtain ⟨hl, hu⟩ := abs_lt.mp he
      cases j <;> simp only at hh <;> linarith
    · intro hc
      cases j <;> apply acquire (1 : Color) <;> norm_num <;>
        have := costPos _ D hD hDE <;> linarith [cuts.2.1]
  have activeClosed (j : Side) (D : ℝ) (hD : 0 < D) (hDE : D ≤ eSide j) :
      (∃ error : ℝ, |error| ≤ b ∧
        observe o (compose ((block j).drop 4) (c0 + sign j * D)) error = 1) ↔
          lam - g ^ 2 * D < b ∨ (lam - g ^ 2 * D = b ∧
            (match j with | .high => o 0 = true | .low => o 1 = false)) := by
    rw [activeCoord]
    constructor
    · rintro ⟨error, he, hread⟩
      have hh := clipOne _ _ hread
      obtain ⟨hl, hu⟩ := abs_le.mp he
      have hcost : lam - g ^ 2 * D ≤ b := by cases j <;> simp only at hh <;> linarith
      rcases lt_or_eq_of_le hcost with hc | hc
      · exact Or.inl hc
      · refine Or.inr ⟨hc, ?_⟩
        cases j
        · have heq : cut 1 - lam + g ^ 2 * D + error = cut 1 := by simp only at hh; linarith
          simp only [observe, heq, clipq1] at hread
          exact q1Read.mp hread
        · have heq : cut 2 + lam - g ^ 2 * D + error = cut 2 := by simp only at hh; linarith
          simp only [observe, heq, clipq2] at hread
          exact q2Read.mp hread
    · rintro (hc | ⟨hc, ho⟩)
      · obtain ⟨error, he, hread⟩ := (activeStrict j D hD hDE).mpr hc
        exact ⟨error, he.le, by simpa only [activeCoord] using hread⟩
      · cases j
        · refine ⟨b, by simpa [abs_of_pos hb0], ?_⟩
          have heq : cut 1 - lam + g ^ 2 * D + b = cut 1 := by linarith
          simp only [observe, heq, clipq1]
          exact q1Read.mpr ho
        · refine ⟨-b, by simpa [abs_of_pos hb0], ?_⟩
          have heq : cut 2 + lam - g ^ 2 * D + -b = cut 2 := by linarith
          simp only [observe, heq, clipq2]
          exact q2Read.mpr ho
  refine ⟨?_, ?_, ?_⟩
  · intro j D hD hDE
    constructor
    · intro h
      have hh := h 4 (by norm_num [colorsD])
      norm_num [colorsD] at hh
      exact (activeStrict j D hD hDE).mp hh
    · intro hc p hp
      have hp6 : p < 6 := by simpa [colorsD] using hp
      by_cases h4 : p = 4
      · subst p; simpa [colorsD] using (activeStrict j D hD hDE).mpr hc
      · exact nonactive j D hD hDE p hp6 h4
  · intro j D hD hDE
    constructor
    · intro h
      have hh := h 4 (by norm_num [colorsD])
      norm_num [colorsD] at hh
      cases j <;> simpa only using (activeClosed _ D hD hDE).mp hh
    · intro hc p hp
      have hp6 : p < 6 := by simpa [colorsD] using hp
      by_cases h4 : p = 4
      · subst p; cases j <;> simpa [colorsD] using (activeClosed _ D hD hDE).mpr hc
      · obtain ⟨error, he, hread⟩ := nonactive j D hD hDE p hp6 h4
        exact ⟨error, he.le, hread⟩
  · intro z hz hzt p hp
    have hp20 : p < 20 := by simpa [colorsE] using hp
    by_cases h19 : p = 19
    · subst p
      refine ⟨0, by simpa using hb0, ?_⟩
      have hlo : cut 2 < compose (C.drop 19) z := by
        norm_num [C, compose, branch, shift, cut, lam, T2]
        rw [htg] at *; nlinarith [hg2]
      have hhi : compose (C.drop 19) z < cut 3 := by
        norm_num [C, compose, branch, shift, cut, lam, T2]
        rw [htg] at *; nlinarith [hg2]
      simpa [colorsE] using interior 2 _ hlo hhi
    · have hzabs : |z - c0| ≤ 2 / 5 := by
        rw [abs_le]; dsimp [c0]; rw [htg]; dsimp [T2] at hzt; rw [htg] at hzt
        constructor <;> linarith
      have hpert := perturb C p z hzabs
      have hlen : C.length = 20 := rfl
      rw [hlen, tableC p (by omega)] at hpert
      have hpow : (1 / 4 : ℝ) ^ (20 - p) ≤ (1 / 4 : ℝ) ^ 2 := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have herr : |pointsC p - compose (C.drop p) z| < b := by
        rw [abs_sub_comm]
        have hh := mul_le_mul_of_nonneg_right hpow (by norm_num : (0 : ℝ) ≤ 2 / 5)
        norm_num at hh
        linarith
      refine ⟨pointsC p - compose (C.drop p) z, herr, ?_⟩
      have heq : compose (C.drop p) z + (pointsC p - compose (C.drop p) z) = pointsC p := by ring
      have hp' : p ∈ Finset.range 20 := Finset.mem_range.mpr hp20
      have hlo : cut (colorsE[p].val) < pointsC p := by
        fin_cases hp' <;> norm_num [colorsE, pointsC, cut, lam, T2, phi, c0]
        all_goals try simp only [htg]
        all_goals linarith only [hg0, hglo, hghi]
      have hhi : pointsC p < cut (colorsE[p].val + 1) := by
        fin_cases hp' <;> norm_num [colorsE, pointsC, cut, lam, T2, phi, c0]
        all_goals try simp only [htg]
        all_goals linarith only [hg0, hglo, hghi]
      change observe o (compose (C.drop p) z) (pointsC p - compose (C.drop p) z) = colorsE[p]'hp
      unfold observe
      rw [heq]
      simpa only [observe, add_zero] using interior (colorsE[p]'hp) (pointsC p) hlo hhi

end D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

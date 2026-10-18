/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FibonacciLiteralSource
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FibonacciLiteralSource
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

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

noncomputable def phi : ℝ := 1 + t
noncomputable def c0 : ℝ := 2 * t / 5

inductive Label | L3 | L0 | L5 | L2 | L25
  deriving DecidableEq, Repr
inductive Guard | G0 | G1
  deriving DecidableEq, Repr

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
def block : Side → List Label | .high => U | .low => V
def stem (j : Side) : List Label := block j ++ C


def returnWord (j : Side) (a : Return) : List Label :=
  repeatWord (block j) a.m ++ repeatWord C a.r
def externalWord (j : Side) (execution : List Return) : List Label :=
  (execution.reverse.map (returnWord j)).flatten
def anchor (j : Side) : Model → List Label
  | .original => []
  | .anchored => stem j
def observedPrefix (j : Side) (model : Model) (execution : List Return) : List Label :=
  stem j ++ externalWord j execution ++ anchor j model

/-- The final zero is part of a finite representation of the same eventually-zero tail. -/
def exitPrefix : Side → List Label | .high => [.L5, .L0] | .low => [.L0]
def tailPrefix (j : Side) : List Label :=
  block j ++ repeatWord C 3 ++ exitPrefix j
def sourcePrefix (j : Side) (model : Model) (execution : List Return) : List Label :=
  observedPrefix j model execution ++ tailPrefix j
def source (j : Side) (model : Model) (execution : List Return) : ℕ → Label :=
  address (sourcePrefix j model execution)

noncomputable def eSide : Side → ℝ | .high => T2 - c0 | .low => c0
noncomputable def xSide (j : Side) : ℝ := aSide j + rho * chi ^ 3 * eSide j
noncomputable def ySide (j : Side) : ℝ := aSide j + rho * chi * xSide j
noncomputable def sign : Side → ℝ | .high => 1 | .low => -1
noncomputable def initial (j : Side) : Model → ℝ
  | .original => xSide j
  | .anchored => ySide j

def observationOffset : Model → ℕ | .original => 26 | .anchored => 52







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

section

-- The Model matchers share reducibility while the history-length equality elaborates.
set_option allowUnsafeReducibility true in
attribute [local reducible] instReprModel.repr.match_1 anchor.match_1

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

end





end D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

set_option maxHeartbeats 1000000 in
-- Uniform comparisons cover both starts, every prefix and all internal powers.
/-- Complete boundaries of both actual starts and the internal C/T inputs of the
same execution prefixes. Only complete boundaries have the lower bound A. -/
theorem actual_complete_boundary_geometry (model : Model) (execution : List Return) :
    (∀ (j : Side) (p : ℕ),
      aSide j < execute j (execution.take p) (initial j model) ∧
      execute j (execution.take p) (initial j model) < hSide j) ∧
    (∀ p : ℕ, execute .high (execution.take p) (initial .high model) <
      execute .low (execution.take p) (initial .low model)) ∧
    (∀ (j : Side) (p n k : ℕ),
      let D := execute j (execution.take p) (initial j model)
      let z := hSide j - rho ^ k * (hSide j - chi ^ n * D)
      0 < z ∧ z < hSide j ∧
      0 ≤ c0 + sign j * z ∧ c0 + sign j * z ≤ T2) ∧
    (∀ (p n k : ℕ),
      hSide .high - rho ^ k * (hSide .high - chi ^ n *
        execute .high (execution.take p) (initial .high model)) <
      hSide .low - rho ^ k * (hSide .low - chi ^ n *
        execute .low (execution.take p) (initial .low model))) ∧
    (∀ (j : Side) (p : ℕ),
      coordinate (sourcePrefix j model execution)
        ((stem j).length + listWeight (execution.drop p)) =
      c0 + sign j * execute j (execution.take p) (initial j model)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have tg : t = (1 + g) / 2 := by dsimp [g]; ring
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have rb : rho < 1 / 4096 := by
    have h := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at h ⊢
    exact h
  have cb : chi < 1 / 256 := by
    have h20 : g ^ 20 ≤ g ^ 4 :=
      pow_le_pow_of_le_one gp.le (by linarith) (by decide)
    have h4 := pow_lt_pow_left₀ gq gp.le (by decide : (4 : ℕ) ≠ 0)
    norm_num at h4
    exact lt_of_le_of_lt h20 h4
  have r1 : rho < 1 := by linarith
  have c1 : chi < 1 := by linarith
  have hb (j : Side) : 1 / 16 < hSide j ∧ hSide j < eSide j ∧
      0 < eSide j ∧ eSide j < 1 := by
    cases j <;> dsimp [hSide, eSide, c0, T2] <;> simp only [tg] <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [gp, gq]
  have ap (j : Side) : 0 < aSide j := by
    exact mul_pos (sub_pos.mpr r1) (by linarith [(hb j).1])
  have ah (j : Side) : aSide j < hSide j := by
    have := mul_pos rp (by linarith [(hb j).1] : 0 < hSide j)
    dsimp [aSide]; nlinarith
  have ceA (j : Side) : chi * eSide j < aSide j := by
    have hcE := mul_lt_mul_of_pos_left (hb j).2.2.2 cp
    have hAh := mul_lt_mul_of_pos_right (show (3 / 4 : ℝ) < 1 - rho by linarith)
      (show 0 < hSide j by linarith [(hb j).1])
    dsimp [aSide] at *
    nlinarith [(hb j).1]
  have xp (j : Side) : aSide j < xSide j ∧ xSide j < hSide j := by
    have c3p : 0 < chi ^ 3 := pow_pos cp 3
    have c3le : chi ^ 3 ≤ chi := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one cp.le c1.le (by decide : 1 ≤ (3 : ℕ)))
    have c3E : chi ^ 3 * eSide j < hSide j :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right c3le (hb j).2.2.1.le)
        (lt_trans (ceA j) (ah j))
    have hpos := mul_pos rp (mul_pos c3p (hb j).2.2.1)
    have hgap := mul_pos rp (sub_pos.mpr c3E)
    dsimp [xSide, aSide] at *
    constructor <;> nlinarith
  have step (j : Side) (a : Return) (D : ℝ) (hD : aSide j < D ∧ D < hSide j) :
      aSide j < returnMap j a D ∧ returnMap j a D < hSide j := by
    have Dp : 0 < D := lt_trans (ap j) hD.1
    have cm := pow_pos cp a.r
    have rm := pow_pos rp a.m
    have cle : chi ^ a.r ≤ 1 := pow_le_one₀ cp.le c1.le
    have rle : rho ^ a.m ≤ rho := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one rp.le r1.le a.m_pos)
    have cd : chi ^ a.r * D < hSide j :=
      lt_of_le_of_lt (by nlinarith) hD.2
    have gap : 0 < hSide j - chi ^ a.r * D := sub_pos.mpr cd
    have gain := mul_pos rp (mul_pos cm Dp)
    have upper := mul_pos rm gap
    have lower := mul_le_mul_of_nonneg_right rle gap.le
    dsimp [returnMap, aSide] at *
    constructor <;> nlinarith
  have ip (j : Side) (md : Model) : aSide j < initial j md ∧ initial j md < hSide j := by
    cases md with
    | original => exact xp j
    | anchored =>
      have h := step j ⟨1, 1, by decide, by decide⟩ (xSide j) (xp j)
      dsimp [initial, returnMap, ySide, aSide] at h ⊢
      constructor <;> nlinarith only [h.1, h.2]
  have hh : hSide .high < hSide .low := by dsimp [hSide]; linarith
  have ee : eSide .high < eSide .low := by dsimp [eSide, c0, T2]; rw [tg]; nlinarith
  have xx : xSide .high < xSide .low := by
    have ha := mul_pos (sub_pos.mpr r1) (sub_pos.mpr hh)
    have hx := mul_pos (mul_pos rp (pow_pos cp 3)) (sub_pos.mpr ee)
    dsimp [xSide, aSide] at *; nlinarith
  have ordered (a : Return) (DH DL : ℝ) (hD : DH < DL) :
      returnMap .high a DH < returnMap .low a DL := by
    have rm := pow_pos rp a.m
    have cm := pow_pos cp a.r
    have rlt := pow_lt_one₀ rp.le r1 (Nat.ne_of_gt a.m_pos)
    have hhg := mul_pos (sub_pos.mpr rlt) (sub_pos.mpr hh)
    have hdg := mul_pos (mul_pos rm cm) (sub_pos.mpr hD)
    dsimp [returnMap]; nlinarith
  have io (md : Model) : initial .high md < initial .low md := by
    cases md with
    | original => exact xx
    | anchored =>
      have h := ordered ⟨1, 1, by decide, by decide⟩ _ _ xx
      dsimp [initial, returnMap, ySide, aSide] at h ⊢
      nlinarith only [h]
  have run (j : Side) (xs : List Return) (D : ℝ)
      (hD : aSide j < D ∧ D < hSide j) :
      aSide j < execute j xs D ∧ execute j xs D < hSide j := by
    induction xs generalizing D with
    | nil => exact hD
    | cons a rest ih => exact ih _ (step j a D hD)
  have runOrder (xs : List Return) (DH DL : ℝ) (hD : DH < DL) :
      execute .high xs DH < execute .low xs DL := by
    induction xs generalizing DH DL with
    | nil => exact hD
    | cons a rest ih => exact ih _ _ (ordered a DH DL hD)
  refine ⟨fun j p => run j (execution.take p) _ (ip j model),
    fun p => runOrder (execution.take p) _ _ (io model), ?_, ?_, ?_⟩
  · intro j p n k
    dsimp only
    let D := execute j (execution.take p) (initial j model)
    change 0 < hSide j - rho ^ k * (hSide j - chi ^ n * D) ∧
      hSide j - rho ^ k * (hSide j - chi ^ n * D) < hSide j ∧
      0 ≤ c0 + sign j * (hSide j - rho ^ k * (hSide j - chi ^ n * D)) ∧
      c0 + sign j * (hSide j - rho ^ k * (hSide j - chi ^ n * D)) ≤ T2
    have hD := run j (execution.take p) _ (ip j model)
    change aSide j < D ∧ D < hSide j at hD
    have Dp := lt_trans (ap j) hD.1
    have cn := pow_pos cp n
    have rk := pow_pos rp k
    have cnle : chi ^ n ≤ 1 := pow_le_one₀ cp.le c1.le
    have rkle : rho ^ k ≤ 1 := pow_le_one₀ rp.le r1.le
    have z0 := mul_pos cn Dp
    have zh : chi ^ n * D < hSide j := lt_of_le_of_lt (by nlinarith) hD.2
    have zgap := mul_pos rk (sub_pos.mpr zh)
    have zl := mul_le_mul_of_nonneg_right rkle (sub_pos.mpr zh).le
    have zpos : 0 < hSide j - rho ^ k * (hSide j - chi ^ n * D) := by nlinarith
    have zhi : hSide j - rho ^ k * (hSide j - chi ^ n * D) < hSide j := by linarith
    refine ⟨zpos, zhi, ?_, ?_⟩
    all_goals have zE := lt_trans zhi (hb j).2.1
    all_goals cases j <;> dsimp [sign, eSide, c0, T2] at zE zpos ⊢ <;>
      simp only [tg] at zE zpos ⊢ <;> nlinarith
  · intro p n k
    have hd := runOrder (execution.take p) _ _ (io model)
    have cn := pow_pos cp n
    have rk := pow_pos rp k
    have rk1 : rho ^ k ≤ 1 := pow_le_one₀ rp.le r1.le
    have hgap := mul_nonneg (sub_nonneg.mpr rk1) (sub_pos.mpr hh).le
    have dgap := mul_pos (mul_pos rk cn) (sub_pos.mpr hd)
    nlinarith

  · intro j p
    have extLength (xs : List Return) : (externalWord j xs).length = listWeight xs := by
      have hl := (paired_source_reconstruction j .original xs).2.2.2.2.1
      have hst : (stem j).length = 26 := by cases j <;> rfl
      simp only [observedPrefix, List.length_append, anchor, List.length_nil,
        observationOffset, hst, Nat.add_zero] at hl
      exact Nat.add_left_cancel hl
    have extSplit : externalWord j execution =
        externalWord j (execution.drop p) ++ externalWord j (execution.take p) := by
      calc
        externalWord j execution = externalWord j (execution.take p ++ execution.drop p) :=
          congrArg (externalWord j) (List.take_append_drop p execution).symm
        _ = externalWord j (execution.drop p) ++ externalWord j (execution.take p) := by
          simp only [externalWord, List.reverse_append, List.map_append, List.flatten_append]
    have sourceSplit : sourcePrefix j model execution =
        (stem j ++ externalWord j (execution.drop p)) ++
        (externalWord j (execution.take p) ++ anchor j model ++ tailPrefix j) := by
      simp only [sourcePrefix, observedPrefix, extSplit, List.append_assoc]
    have index : (stem j).length + listWeight (execution.drop p) =
        (stem j ++ externalWord j (execution.drop p)).length := by
      simp only [List.length_append, extLength]
    rw [coordinate, sourceSplit, index]
    simp only [List.drop_append, List.drop_eq_nil_of_le le_rfl, Nat.sub_self,
      List.drop_zero, List.nil_append, Nat.zero_sub]
    simpa only [coordinate, List.drop_zero] using
      (paired_source_reconstruction j model (execution.take p)).2.2.2.1

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

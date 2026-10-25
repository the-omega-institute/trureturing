/- GID: D5/S3/Quantum/PureState/QutritDickePruningRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/QutritDickePruningRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/PureState/QutritDickePruningRefutation.claim; result=D5/S3/Quantum/PureState/QutritDickePruningRefutation.result; claim=D5/S3/Quantum/PureState/QutritDickePruningRefutation.claim
   digest: The pruned qutrit Dicke circuit loses a required amplitude at occupation (1,3,1). -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PureState.QutritDickePruningRefutation

noncomputable section

abbrev Word (n : ℕ) := D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word (Fin 3) n
abbrev State (n : ℕ) := Word n → ℝ
abbrev Occupation := Fin 3 → ℕ

/-- Wire numbers increase from right to left. Out-of-register reads are zero. -/
def wire {n : ℕ} (t : Word n) (r : ℕ) : Fin 3 :=
  if h : r < n then t ⟨r, h⟩ else 0

/-- An out-of-register update acts as the identity. -/
def put {n : ℕ} (t : Word n) (r : ℕ) (a : Fin 3) : Word n :=
  if h : r < n then Function.update t ⟨r, h⟩ a else t

def controlsHold {n : ℕ} (controls : List (ℕ × Fin 3)) (t : Word n) : Bool :=
  controls.all (fun p => decide (p.1 < n) && decide (wire t p.1 = p.2))

/-- Controlled exchange, acting by the inverse basis permutation. -/
def controlledX {n : ℕ} (target : ℕ) (controls : List (ℕ × Fin 3))
    (i j : Fin 3) (f : State n) : State n :=
  fun t => if controlsHold controls t then
    f (put t target (Equiv.swap i j (wire t target))) else f t

/-- The real rotation has rows `(c,-s)` and `(s,c)` in the `(i,j)` subspace. -/
def controlledR {n : ℕ} (target : ℕ) (controls : List (ℕ × Fin 3))
    (i j : Fin 3) (c s : ℝ) (f : State n) : State n :=
  fun t => if controlsHold controls t then
    if wire t target = i then c * f t - s * f (put t target j)
    else if wire t target = j then s * f (put t target i) + c * f t
    else f t
  else f t

/-- The three elementary operations in the paper's `V` circuit, in time order. -/
def V (n m l : ℕ) (i j : Fin 3) (f : State n) : State n :=
  let off := n - m
  let x := controlledX (off + l) [(off, j)] i j
  let cs := [(off + l, j)] ++
    (if 2 ≤ l then [(off + (l - 1), j)] else []) ++
    (if 0 < i.val ∧ l ≤ m - 2 then [(off + (m - 1), i)] else [])
  x (controlledR off cs i j (Real.sqrt ((l : ℝ) / m))
    (-Real.sqrt (1 - (l : ℝ) / m)) (x f))

def I (n m l : ℕ) (f : State n) : State n :=
  V n m l 1 2 (V n m l 0 2 (V n m l 0 1 f))

/-- Both rotations use the common controls, including their boundary omissions. -/
def II (n m l₁ l₂ : ℕ) (f : State n) : State n :=
  let off := n - m
  let x := controlledX (off + l₂) [(off, 2)] 1 2
  let y := controlledX (off + l₁) [(off, 1)] 0 1
  let cs := [(off + l₂, 2)] ++
    (if 2 ≤ l₂ then [(off + (l₂ - 1), 2)] else []) ++
    (if l₂ < l₁ - 1 then [(off + (l₁ - 1), 1)] else [])
  let r₁ := controlledR off ((off + l₁, 0) :: cs) 1 2
    (Real.sqrt ((l₂ : ℝ) / m)) (-Real.sqrt (1 - (l₂ : ℝ) / m))
  let r₂ := controlledR off ((off + l₁, 1) :: cs) 0 1
    (Real.sqrt (((l₁ - l₂ : ℕ) : ℝ) / (m - l₂ : ℕ)))
    (-Real.sqrt (1 - ((l₁ - l₂ : ℕ) : ℝ) / (m - l₂ : ℕ)))
  y (r₂ (y (x (r₁ (x f)))))

/-- Inclusive natural-number interval, with an empty reversed interval. -/
def increasingRange (lo hi : ℕ) : List ℕ := List.range' lo (hi + 1 - lo)

def prunedTilde (n m : ℕ) (k : Occupation) (f : State n) : State n :=
  let kt := if k 0 = 0 then k 2 else max (k 1) (k 2)
  (increasingRange (max (kt + m - n) 1) (min kt (m - 1))).foldl
    (fun g l => I n m l g) f

def prunedTildeTilde (n m : ℕ) (k : Occupation) (f : State n) : State n :=
  let l₁ := k 1 + k 2
  let l₂ := k 2
  (increasingRange (max (l₂ + m - n) 1) (min l₂ (m - 2))).foldl
    (fun g b => (increasingRange (max (l₁ + m - n) (b + 1)) (min l₁ (m - 1))).foldl
      (fun h a => II n m a b h) g) f

def prunedW (n m : ℕ) (k : Occupation) (f : State n) : State n :=
  prunedTildeTilde n m k (prunedTilde n m k f)

/-- The largest register block acts first. -/
def prunedU (n : ℕ) (k : Occupation) (f : State n) : State n :=
  (increasingRange 2 n).reverse.foldl (fun g m => prunedW n m k g) f

def initialWord (n : ℕ) (k : Occupation) : Word n :=
  fun w => if w.val < k 2 then 2 else if w.val < k 1 + k 2 then 1 else 0

def basisState {n : ℕ} (t : Word n) : State n := fun u => if u = t then 1 else 0

/-- The occupation counts use the existing multiset-of-letters representation. -/
def dicke (n : ℕ) (k : Occupation) : State n :=
  fun t => if ∀ s, (D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation t).count s = k s
    then 1 / Real.sqrt ((n.factorial / ((k 0).factorial * (k 1).factorial *
      (k 2).factorial) : ℕ) : ℝ) else 0

def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k₀ k₁ k₂ : ℕ, k₀ + k₁ + k₂ = n →
    prunedU n ![k₀, k₁, k₂] (basisState (initialWord n ![k₀, k₁, k₂])) =
      dicke n ![k₀, k₁, k₂]

private def witnessOccupation : Occupation := ![1, 3, 1]
private def inputWord : Word 5 := ![2, 1, 1, 1, 0]
private def branchWord : Word 5 := ![0, 2, 1, 1, 1]
private def targetWord : Word 5 := ![0, 1, 1, 1, 2]

private def project {n : ℕ} (r : ℕ) (a : Fin 3) (f : State n) : State n :=
  fun t => if wire t r = a then f t else 0

private theorem project_W5 :
    project 0 0 (prunedW 5 5 witnessOccupation (basisState inputWord)) =
      fun t => (1 / Real.sqrt 5) * basisState branchWord t := by
  sorry

private theorem W4_branch :
    prunedW 5 4 witnessOccupation (basisState branchWord) = basisState branchWord := by
  sorry

private theorem project_W4 (f : State 5) :
    project 0 0 (prunedW 5 4 witnessOccupation f) =
      prunedW 5 4 witnessOccupation (project 0 0 f) := by
  sorry

private theorem W4_scale (a : ℝ) (f : State 5) :
    prunedW 5 4 witnessOccupation (fun t => a * f t) =
      fun t => a * prunedW 5 4 witnessOccupation f t := by
  sorry

private theorem tail_zero (f : State 5)
    (h : ∀ t, wire t 0 = 0 → wire t 1 ≠ 2 → f t = 0) :
    prunedW 5 2 witnessOccupation (prunedW 5 3 witnessOccupation f) targetWord = 0 := by
  sorry

private theorem output_zero :
    prunedU 5 witnessOccupation (basisState (initialWord 5 witnessOccupation)) targetWord = 0 := by
  have hw5 := project_W5
  have hw4 := project_W4 (prunedW 5 5 witnessOccupation (basisState inputWord))
  rw [hw5, W4_scale, W4_branch] at hw4
  have h : ∀ t, wire t 0 = 0 → wire t 1 ≠ 2 →
      prunedW 5 4 witnessOccupation
        (prunedW 5 5 witnessOccupation (basisState inputWord)) t = 0 := by
    intro t h0 h1
    have ht := congrFun hw4 t
    have hb : t ≠ branchWord := by
      intro he
      subst t
      exact h1 rfl
    simpa [project, h0, basisState, hb] using ht
  have ht := tail_zero _ h
  have hi : initialWord 5 witnessOccupation = inputWord := by
    funext w
    fin_cases w <;> rfl
  rw [hi]
  simpa [prunedU, increasingRange, List.range', List.range'TR] using ht

private theorem target_nonzero : dicke 5 witnessOccupation targetWord ≠ 0 := by
  sorry

 theorem result : ¬ claim := by
  intro hc
  have he := congrFun (hc 5 (by decide) 1 3 1 (by decide)) targetWord
  change prunedU 5 witnessOccupation (basisState (initialWord 5 witnessOccupation)) targetWord =
    dicke 5 witnessOccupation targetWord at he
  exact target_nonzero (he.symm.trans output_zero)

end
end D5.S3.Quantum.PureState.QutritDickePruningRefutation

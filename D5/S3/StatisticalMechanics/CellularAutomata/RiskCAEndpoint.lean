/- GID: D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   digest: The highest active threshold of the deterministic RiskCA has a collision on complete boards. -/

import Lean.Elab.Tactic.Omega

/-!
# The highest active threshold in RiskCA

The deterministic finite-board local step is from María Teresa Arias Noguerales,
arXiv:2611.34784v1, §3.2 and Appendix B, Algorithm 1. The indexed transition
through 'step' is adapted from the author's MIT-licensed 'RiskCA/Model.lean'
at commit 67bb577bd35855cf605e4457ad8795ec0e923991.
-/

/-
MIT License

Copyright (c) 2026 María Teresa Arias Noguerales

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace D5.S3.StatisticalMechanics.CellularAutomata.RiskCAEndpoint

structure Board where
  N   : Nat
  nbr : Nat → List Nat

structure Params where
  Nmax : Nat
  g    : Nat
  θ    : Nat
  p    : Nat      -- ρ = p / q
  q    : Nat
  fortify : Bool := true

structure State where
  o : Nat → Nat
  n : Nat → Nat

/-- ⌈x / y⌉ for y > 0. -/
def ceilDiv (x y : Nat) : Nat := (x + y - 1) / y

/-- First element of `l` minimising `key` lexicographically. -/
def argminBy (key : Nat → Nat × Nat) : List Nat → Option Nat
  | [] => none
  | j :: js =>
    match argminBy key js with
    | none => some j
    | some k =>
      let a := key j; let b := key k
      if a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) then some j else some k

/-- Lexicographic "a is strictly better than b" for keys to be maximised in the
    first component and minimised in the second (larger force, lower priority). -/
def better (a b : Nat × Nat) : Bool := a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)

def argmaxBy (key : Nat → Nat × Nat) : List Nat → Option Nat
  | [] => none
  | j :: js =>
    match argmaxBy key js with
    | none => some j
    | some k => if better (key j) (key k) || key j == key k then some j else some k

variable (B : Board) (P : Params) (prio : Nat → Nat)

/-- (G) growth -/
def grow (s : State) : State := { s with n := fun i => min P.Nmax (s.n i + P.g) }

def hostile (o : Nat → Nat) (i : Nat) : List Nat := (B.nbr i).filter (fun j => o j != o i)

/-- (D) target: weakest hostile neighbour, ties by priority. -/
def target (s : State) (i : Nat) : Option Nat :=
  argminBy (fun j => (s.n j, prio j)) (hostile B s.o i)

/-- (D) i wants to attack its target. -/
def wants (s : State) (i : Nat) : Bool :=
  match target B prio s i with
  | some t => decide (s.n i ≥ 2) && decide (s.n i ≥ s.n t + P.θ)
  | none => false

/-- (R) attacker accepted at target j: largest committed force, ties by priority. -/
def accepted (s : State) (j : Nat) : Option Nat :=
  argmaxBy (fun i => (s.n i - 1, prio i))
    ((B.nbr j).filter (fun i => wants B P prio s i && target B prio s i == some j))

/-- i's own attack was accepted. -/
def committed (s : State) (i : Nat) : Bool :=
  match target B prio s i with
  | some t => wants B P prio s i && accepted B P prio s t == some i
  | none => false

/-- A battle realisation: (attacker, target, committed force a, defence d) ↦
    (attacker wins, survivors). For the deterministic operator it is `detBat`; for dice it is the
    outcome drawn with the random numbers of the step held fixed. -/
abbrev Bat := Nat → Nat → Nat → Nat → Bool × Nat

/-- The deterministic operator R_ρ, ρ = p/q. -/
def detBat : Bat := fun _ _ a d =>
  if P.p * a > P.q * d then (true, min P.Nmax (max 1 (a - ceilDiv (d * P.q) P.p)))
  else (false, max 1 (d - (P.p * a) / P.q))

/-- (R) resolution with battle realisation `bat`. Input: state after (G). -/
def resolve (bat : Bat) (s : State) : State :=
  let n1 : Nat → Nat := fun i => if committed B P prio s i then 1 else s.n i
  { o := fun j =>
      match accepted B P prio s j with
      | some i => if (bat i j (s.n i - 1) (n1 j)).1 then s.o i else s.o j
      | none => s.o j
    n := fun j =>
      match accepted B P prio s j with
      | some i => (bat i j (s.n i - 1) (n1 j)).2
      | none => n1 j }

def threat (o : Nat → Nat) (i : Nat) : Nat := (hostile B o i).length

/-- (F) destination of an interior cell: friendly neighbour of highest threat, ties by priority. -/
def dest (s : State) (i : Nat) : Option Nat :=
  argmaxBy (fun k => (threat B s.o k, prio k)) ((B.nbr i).filter (fun k => s.o k == s.o i))

/-- (F) units sent by cell i (0 if it does not send). -/
def sent (s : State) (i : Nat) : Nat :=
  if threat B s.o i == 0 then
    match dest B prio s i with
    | some k => if threat B s.o k > 0 then (s.n i - s.n k) / 2 else 0
    | none => 0
  else 0

def inflow (s : State) (k : Nat) : Nat :=
  ((B.nbr k).filter (fun i => dest B prio s i == some k)).foldl (fun acc i => acc + sent B prio s i) 0

/-- (F) fortification with overflow lost at the cap. -/
def fortify (s : State) : State :=
  if P.fortify then
    { s with n := fun k => min P.Nmax (s.n k - sent B prio s k + inflow B prio s k) }
  else s

/-- One synchronous step Φ = F ∘ R ∘ D ∘ G with battle realisation `bat`;
    the deterministic rule is `step B P prio (detBat P)`. -/
def step (bat : Bat) (s : State) : State :=
  fortify B P prio (resolve B P prio bat (grow P s))

/-- The full legal carrier. Each digit represents its value plus one. -/
abbrev Config (V : Type u) (owners cap : Nat) := V → Fin owners × Fin cap

/-- Index all the other board cells as neighbours. Outside the board the list is empty. -/
def completeBoard (N : Nat) : Board where
  N := N
  nbr i := if i < N then (List.range N).filter (fun j => j != i) else []

/-- Extend a legal configuration by owner digit zero and one unit off the board. -/
def encode {N owners cap : Nat} (x : Config (Fin N) owners cap) : State where
  o i := if hi : i < N then (x ⟨i, hi⟩).1.val else 0
  n i := if hi : i < N then (x ⟨i, hi⟩).2.val + 1 else 1

/-- Decode a legal board state. The finite constructors are saturated for raw states. -/
def decode {N owners cap : Nat} (howners : 0 < owners) (hcap : 0 < cap)
    (s : State) : Config (Fin N) owners cap :=
  fun i => (⟨min (owners - 1) (s.o i.val), by omega⟩,
    ⟨min (cap - 1) (s.n i.val - 1), by omega⟩)

def endpointParams (cap : Nat) (enabled : Bool) : Params :=
  { Nmax := cap, g := 0, θ := cap - 1, p := 3, q := 2, fortify := enabled }

/-- The author's indexed step on the paper's full finite product at zero growth. -/
def indexedStep {N owners cap : Nat} (howners : 0 < owners) (hcap : 0 < cap)
    (priority : Nat → Nat) (enabled : Bool) (bat : Bat) :
    Config (Fin N) owners cap → Config (Fin N) owners cap :=
  fun x => decode howners hcap
    (step (completeBoard N) (endpointParams cap enabled) priority bat (encode x))

def probeX : Config (Fin 2) 2 3 :=
  fun i => if i = 0 then (0, 2) else (1, 0)

def probeY : Config (Fin 2) 2 3 := fun _ => (0, 0)

/-- On the legal two-cell board both flags give the same exhibited collision. -/
theorem probe (enabled : Bool) :
    probeX ≠ probeY ∧
    indexedStep (by decide) (by decide) id enabled
      (detBat (endpointParams 3 enabled)) probeX = probeY ∧
    indexedStep (by decide) (by decide) id enabled
      (detBat (endpointParams 3 enabled)) probeY = probeY := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    change ((0, 2) : Fin 2 × Fin 3) = (0, 0) at h0
    exact (by decide : ((0, 2) : Fin 2 × Fin 3) ≠ (0, 0)) h0
  all_goals
    cases enabled <;> funext i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> decide

#print axioms probe

end D5.S3.StatisticalMechanics.CellularAutomata.RiskCAEndpoint

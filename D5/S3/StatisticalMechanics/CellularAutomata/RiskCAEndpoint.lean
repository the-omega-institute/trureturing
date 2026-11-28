/- GID: D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   digest: The highest active threshold of the deterministic RiskCA has a collision on complete boards. -/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.SimpleGraph.Basic
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
# The highest active threshold in RiskCA

The deterministic finite-board local step is from María Teresa Arias Noguerales,
arXiv:2611.34784v1, §3.2 and Appendix B, Algorithm 1. The indexed transition
through 'step' and the indicated lemmas are adapted from the author's
MIT-licensed Lean sources at commit 67bb577bd35855cf605e4457ad8795ec0e923991.
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

/-! The list-membership and homogeneous-state lemmas are from Prop4, Prop6 and Prop3. -/

private theorem foldl_add_zero (l : List Nat) (f : Nat → Nat) (hf : ∀ i, f i = 0) (init : Nat) :
    l.foldl (fun acc i => acc + f i) init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl, hf x, Nat.add_zero]; exact ih init

private theorem filter_false_nil (l : List Nat) : l.filter (fun _ => false) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [List.filter, ih]

/-- If no cell wants to attack, (R) leaves the state unchanged. -/
private theorem resolve_no_attacks (B : Board) (P : Params) (prio : Nat → Nat) (bat : Bat) (s : State)
    (h : ∀ i, wants B P prio s i = false) : resolve B P prio bat s = s := by
  have hacc : ∀ j, accepted B P prio s j = none := by
    intro j; unfold accepted; simp only [h, Bool.false_and]; rw [filter_false_nil]; rfl
  have hcom : ∀ i, committed B P prio s i = false := by
    intro i; unfold committed; split <;> simp [h]
  cases s with
  | mk o n => simp [resolve, hacc, hcom]

/-- If no cell sends, (F) leaves troops unchanged when they are already capped. -/
private theorem fortify_no_sends (B : Board) (P : Params) (prio : Nat → Nat) (s : State)
    (h : ∀ i, sent B prio s i = 0) (hcap : ∀ i, s.n i ≤ P.Nmax) : fortify B P prio s = s := by
  unfold fortify
  split
  · have hin : ∀ k, inflow B prio s k = 0 := by
      intro k; unfold inflow; exact foldl_add_zero _ _ h 0
    cases s with
    | mk o n =>
      simp only [State.mk.injEq, true_and]
      funext k
      simp only [h, hin, Nat.sub_zero, Nat.add_zero]
      exact Nat.min_eq_right (hcap k)
  · rfl

/-- Proposition 4(a): on a homogeneous configuration, (D)-(F) are inactive and a step is pure growth. -/
private theorem prop4a_homogeneous (B : Board) (P : Params) (prio : Nat → Nat) (bat : Bat) (s : State) (c : Nat)
    (hom : ∀ i, s.o i = c) : step B P prio bat s = grow P s := by
  have hhost : ∀ (t : State) i, (∀ j, t.o j = c) → hostile B t.o i = [] := by
    intro t i ht; unfold hostile; simp [ht]
  have hw : ∀ i, wants B P prio (grow P s) i = false := by
    intro i; unfold wants target
    rw [hhost (grow P s) i (by intro j; simp [grow, hom])]; rfl
  have hs : ∀ i, sent B prio (grow P s) i = 0 := by
    intro i; unfold sent threat
    rw [hhost (grow P s) i (by intro j; simp [grow, hom])]
    simp only [List.length_nil, beq_self_eq_true, if_true]
    split
    · rename_i k _
      rw [hhost (grow P s) k (by intro j; simp [grow, hom])]; rfl
    · rfl
  unfold step
  rw [resolve_no_attacks B P prio bat _ hw, fortify_no_sends B P prio _ hs (fun i => by simp [grow]; omega)]

private theorem argminBy_mem (key : Nat → Nat × Nat) : ∀ (l : List Nat) (x : Nat), argminBy key l = some x → x ∈ l
  | [], x, h => by simp [argminBy] at h
  | j :: js, x, h => by
    simp only [argminBy] at h
    cases hk : argminBy key js with
    | none => rw [hk] at h; cases h; exact List.mem_cons_self _ _
    | some k =>
      rw [hk] at h
      dsimp only at h
      split at h
      · cases h; exact List.mem_cons_self _ _
      · cases h; exact List.mem_cons_of_mem _ (argminBy_mem key js _ hk)

private theorem argmaxBy_mem (key : Nat → Nat × Nat) : ∀ (l : List Nat) (x : Nat), argmaxBy key l = some x → x ∈ l
  | [], x, h => by simp [argmaxBy] at h
  | j :: js, x, h => by
    simp only [argmaxBy] at h
    cases hk : argmaxBy key js with
    | none => rw [hk] at h; cases h; exact List.mem_cons_self _ _
    | some k =>
      rw [hk] at h
      dsimp only at h
      split at h
      · cases h; exact List.mem_cons_self _ _
      · cases h; exact List.mem_cons_of_mem _ (argmaxBy_mem key js _ hk)

/-- Adjacency lists without repetitions and with cells below N. -/
def WF (B : Board) : Prop := ∀ k, k < B.N → (B.nbr k).Nodup ∧ ∀ j ∈ B.nbr k, j < B.N

private def Symm (B : Board) : Prop := ∀ i j, j ∈ B.nbr i → i ∈ B.nbr j

private theorem target_mem (B : Board) (prio : Nat → Nat) (s : State) (i j : Nat)
    (h : target B prio s i = some j) : j ∈ hostile B s.o i :=
  argminBy_mem _ _ _ h

private theorem hostile_sub_nbr (B : Board) (o : Nat → Nat) (i j : Nat)
    (h : j ∈ hostile B o i) : j ∈ B.nbr i :=
  (List.mem_filter.mp h).1

private theorem argminBy_all (key : Nat → Nat × Nat) (l : List Nat) (u : Nat)
    (hmem : u ∈ l) (hall : ∀ x ∈ l, x = u) : argminBy key l = some u := by
  cases l with
  | nil => simp at hmem
  | cons j js =>
    have hj := hall j (by simp)
    simp only [argminBy]
    split
    · simp [hj]
    · rename_i k hk
      have hku := hall k (List.mem_cons_of_mem _ (argminBy_mem _ _ _ hk))
      simp [hj, hku]

private theorem argmaxBy_all (key : Nat → Nat × Nat) (l : List Nat) (u : Nat)
    (hmem : u ∈ l) (hall : ∀ x ∈ l, x = u) : argmaxBy key l = some u := by
  cases l with
  | nil => simp at hmem
  | cons j js =>
    have hj := hall j (by simp)
    simp only [argmaxBy]
    split
    · simp [hj]
    · rename_i k hk
      have hku := hall k (List.mem_cons_of_mem _ (argmaxBy_mem _ _ _ hk))
      simp [hj, hku, better]

section
variable (B : Board) (P : Params) (prio : Nat → Nat) (bat : Bat)

private theorem accepted_spec (a : State) (j i : Nat) (h : accepted B P prio a j = some i) :
    wants B P prio a i = true ∧ target B prio a i = some j ∧ i ∈ B.nbr j := by
  have hmem := argmaxBy_mem _ _ _ h
  have ⟨hi, hf⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  exact ⟨hf.1, hf.2, hi⟩

/-! The single-request resolution lemma is from Prop2. -/

/-- (R) when exactly one cell u of the board wants to attack, and its target is v. -/
private theorem single_attack (hB : WF B) (hs : Symm B) (a : State) (u v : Nat) (hu : u < B.N)
    (ht : target B prio a u = some v) (hw : wants B P prio a u = true)
    (hno : ∀ i, i < B.N → i ≠ u → wants B P prio a i = false) (x : Nat) (hx : x < B.N) :
    (resolve B P prio bat a).o x =
      (if x = v then (if (bat u v (a.n u - 1) (a.n v)).1 then a.o u else a.o v) else a.o x) ∧
    (resolve B P prio bat a).n x =
      (if x = v then (bat u v (a.n u - 1) (a.n v)).2 else if x = u then 1 else a.n x) := by
  have hvh := target_mem B prio a u v ht
  have hvn : v ∈ B.nbr u := hostile_sub_nbr B a.o u v hvh
  have hvN : v < B.N := (hB u hu).2 v hvn
  have hvu : v ≠ u := by
    intro e; have := (List.mem_filter.mp hvh).2; rw [e] at this; simp at this
  have hacc : ∀ j, j < B.N → accepted B P prio a j = if j = v then some u else none := by
    intro j hj
    unfold accepted
    by_cases hjv : j = v
    · rw [if_pos hjv, hjv]
      apply argmaxBy_all
      · exact List.mem_filter.mpr ⟨hs u v hvn, by simp [hw, ht]⟩
      · intro i hi
        have ⟨hin, hc⟩ := List.mem_filter.mp hi
        by_cases hiu : i = u
        · exact hiu
        · rw [hno i ((hB v hvN).2 i hin) hiu] at hc; simp at hc
    · rw [if_neg hjv]
      have : (B.nbr j).filter (fun i => wants B P prio a i && target B prio a i == some j) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro i hi
        by_cases hiu : i = u
        · rw [hiu, ht]
          have : (some v == some j) = false := by simp [Ne.symm hjv]
          simp [this]
        · rw [hno i ((hB j hj).2 i hi) hiu]; simp
      rw [this]; rfl
  have hcom : ∀ i, i < B.N → committed B P prio a i = decide (i = u) := by
    intro i hi
    by_cases hiu : i = u
    · rw [hiu]; simp [committed, ht, hw, hacc v hvN]
    · unfold committed; split
      · rw [hno i hi hiu]; simp [hiu]
      · simp [hiu]
  by_cases hxv : x = v
  · rw [hxv]
    have hc := hcom v hvN
    simp only [decide_eq_true_eq, hvu, decide_False] at hc
    simp [resolve, hacc v hvN, hc]
  · have hc := hcom x hx
    by_cases hxu : x = u
    · have : committed B P prio a x = true := by rw [hc]; simp [hxu]
      rw [hxu] at this hxv hx ⊢
      simp [resolve, hacc u hx, hxv, this]
    · have : committed B P prio a x = false := by rw [hc]; simp [hxu]
      simp [resolve, hacc x hx, hxv, hxu, this]

end

/-- Faction 1 at v, faction 0 elsewhere; m units at u, d0 at v, one elsewhere. -/
def edgeState (u v m d0 : Nat) : State :=
  { o := fun x => if x = v then 1 else 0, n := fun x => if x = u then m else if x = v then d0 else 1 }

private theorem mem_completeBoard {N i j : Nat} :
    j ∈ (completeBoard N).nbr i ↔ i < N ∧ j < N ∧ j ≠ i := by
  by_cases hi : i < N <;> simp [completeBoard, hi]

private theorem completeBoard_wf (N : Nat) : WF (completeBoard N) := by
  intro i hi
  exact ⟨by simpa [completeBoard, hi] using (List.nodup_range (n := N)).filter _,
    fun _ hj => (mem_completeBoard.mp hj).2.1⟩

private theorem completeBoard_symm (N : Nat) : Symm (completeBoard N) := by
  intro i j h
  obtain ⟨hi, hj, hji⟩ := mem_completeBoard.mp h
  exact mem_completeBoard.mpr ⟨hj, hi, Ne.symm hji⟩

private theorem grow_zero (s : State) (cap : Nat) (enabled : Bool)
    (hb : ∀ i, s.n i ≤ cap) : grow (endpointParams cap enabled) s = s := by
  cases s
  congr
  funext i
  simpa [grow, endpointParams] using Nat.min_eq_right (hb i)

private theorem fortify_complete (N cap : Nat) (enabled : Bool) (prio : Nat → Nat)
    (s : State) (hb : ∀ i, s.n i ≤ cap) :
    fortify (completeBoard N) (endpointParams cap enabled) prio s = s := by
  apply fortify_no_sends _ _ _ s _ hb
  intro i
  by_cases hi : i < N
  · unfold sent
    split
    · rename_i hint
      have hhost : hostile (completeBoard N) s.o i = [] :=
        List.eq_nil_of_length_eq_zero (by simpa [threat] using hint)
      have howner (j : Nat) (hj : j < N) : s.o j = s.o i := by
        by_cases hji : j = i
        · simp [hji]
        · have hjn := mem_completeBoard.mpr (N := N) ⟨hi, hj, hji⟩
          have hh := List.filter_eq_nil_iff.mp hhost j hjn
          simpa using hh
      split
      · rename_i k hk
        have hkn : k ∈ (completeBoard N).nbr i :=
          (List.mem_filter.mp (argmaxBy_mem _ _ _ hk)).1
        have hkN := (mem_completeBoard.mp hkn).2.1
        have hz : hostile (completeBoard N) s.o k = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro j hj
          rw [howner j (mem_completeBoard.mp hj).2.1, howner k hkN]
          simp
        simp [threat, hz]
      · rfl
    · rfl
  · simp [sent, dest, completeBoard, hi, argmaxBy, threat, hostile]

/-- The paper's strict real comparison and its two survivor formulas. -/
noncomputable def realDetBat (ρ : ℝ) : Bat :=
  fun _ _ a d =>
    if (d : ℝ) < ρ * (a : ℝ) then (true, max 1 (a - ⌈(d : ℝ) / ρ⌉₊))
    else (false, max 1 (d - ⌊ρ * (a : ℝ)⌋₊))

private theorem real_endpoint_battle (cap : Nat) (hcap : 3 ≤ cap)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (i j : Nat) :
    realDetBat ρ i j (cap - 1) 1 = (true, cap - 2) := by
  have hc : 1 < ((cap - 1 : Nat) : ℝ) := by exact_mod_cast (show 1 < cap - 1 by omega)
  have hwin : (1 : ℝ) < ρ * ((cap - 1 : Nat) : ℝ) :=
    hc.trans_le (le_mul_of_one_le_left (le_of_lt (zero_lt_one.trans hc)) hρ)
  have hpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hceil : ⌈(1 : ℝ) / ρ⌉₊ = 1 := by
    apply (Nat.ceil_eq_iff one_ne_zero).mpr
    simpa using And.intro (div_pos zero_lt_one hpos) ((div_le_one hpos).mpr hρ)
  simp [realDetBat, hwin, hceil]
  omega

private theorem rational_endpoint_battle (cap : Nat) (hcap : 3 ≤ cap) (enabled : Bool)
    (i j : Nat) : detBat (endpointParams cap enabled) i j (cap - 1) 1 = (true, cap - 2) := by
  have hwin : 2 < 3 * (cap - 1) := by omega
  simp [detBat, endpointParams, hwin, ceilDiv]
  omega

private theorem accepted_endpoint (B : Board) (cap : Nat) (enabled : Bool)
    (prio : Nat → Nat) (s : State) (hvalid : ∀ i, 1 ≤ s.n i) (hbound : ∀ i, s.n i ≤ cap)
    {i j : Nat} (h : accepted B (endpointParams cap enabled) prio s j = some i) :
    s.n i - 1 = cap - 1 ∧ (if committed B (endpointParams cap enabled) prio s j
      then 1 else s.n j) = 1 := by
  obtain ⟨hw, ht, _⟩ := accepted_spec B (endpointParams cap enabled) prio s j i h
  have hgap : s.n j + (cap - 1) ≤ s.n i := by
    simpa [wants, ht, endpointParams] using (Bool.and_eq_true.mp
      (show (decide (2 ≤ s.n i) && decide (s.n j + (cap - 1) ≤ s.n i)) = true from
        by simpa only [wants, ht, endpointParams] using hw)).2
  have hi := hbound i
  have hj := hvalid j
  have hj1 : s.n j = 1 := by omega
  exact ⟨by omega, by simp [hj1]⟩

private theorem resolve_endpoint_congr (B : Board) (cap : Nat) (enabled : Bool)
    (prio : Nat → Nat) (s : State) (hvalid : ∀ i, 1 ≤ s.n i) (hbound : ∀ i, s.n i ≤ cap)
    (a b : Bat) (hbat : ∀ i j, a i j (cap - 1) 1 = b i j (cap - 1) 1) :
    resolve B (endpointParams cap enabled) prio a s =
      resolve B (endpointParams cap enabled) prio b s := by
  simp only [resolve, State.mk.injEq]
  constructor <;> funext j <;> split
  all_goals try rfl
  all_goals
    rename_i i ha
    obtain ⟨hforce, hdefence⟩ := accepted_endpoint B cap enabled prio s hvalid hbound ha
    rw [hforce, hdefence, hbat i j]

private theorem encode_legal {N owners cap : Nat} (hp : 0 < owners) (hm : 0 < cap)
    (x : Config (Fin N) owners cap) (i : Nat) :
    (encode x).o i < owners ∧ 1 ≤ (encode x).n i ∧ (encode x).n i ≤ cap := by
  by_cases hi : i < N
  · have ho := (x ⟨i, hi⟩).1.isLt
    have hn := (x ⟨i, hi⟩).2.isLt
    simp only [encode, dif_pos hi]
    omega
  · simp [encode, hi]
    omega

private theorem resolve_endpoint_legal (B : Board) (owners cap : Nat) (hcap : 3 ≤ cap)
    (enabled : Bool) (prio : Nat → Nat) (bat : Bat)
    (hbat : ∀ i j, bat i j (cap - 1) 1 = (true, cap - 2)) (s : State)
    (hs : ∀ i, s.o i < owners ∧ 1 ≤ s.n i ∧ s.n i ≤ cap) (j : Nat) :
    (resolve B (endpointParams cap enabled) prio bat s).o j < owners ∧
    1 ≤ (resolve B (endpointParams cap enabled) prio bat s).n j ∧
    (resolve B (endpointParams cap enabled) prio bat s).n j ≤ cap := by
  simp only [resolve]
  cases ha : accepted B (endpointParams cap enabled) prio s j with
  | none =>
    rw [ha]
    obtain ⟨ho, hn, hc⟩ := hs j
    split <;> omega
  | some i =>
    obtain ⟨hforce, hdefence⟩ :=
      accepted_endpoint B cap enabled prio s (fun k => (hs k).2.1) (fun k => (hs k).2.2) ha
    rw [ha, hforce, hdefence, hbat i j]
    have ho := (hs i).1
    simp
    omega

private theorem decode_at {N owners cap : Nat} (hp : 0 < owners) (hm : 0 < cap)
    (s : State) (i : Fin N) (ho : s.o i < owners) (hn : 1 ≤ s.n i) (hb : s.n i ≤ cap) :
    ((decode hp hm s i).1.val, (decode hp hm s i).2.val + 1) = (s.o i, s.n i) := by
  simp only [decode, Prod.mk.injEq]
  omega

/-- The on-board values recovered after a real step are the raw output values.
In particular the finite constructors never clip the raw output of a legal input. -/
theorem indexed_real_step_values {N owners cap : Nat} (hp : 0 < owners) (hcap : 3 ≤ cap)
    (prio : Nat → Nat) (enabled : Bool) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (x : Config (Fin N) owners cap) (i : Fin N) :
    let y := indexedStep hp (by omega) prio enabled (realDetBat ρ) x
    let s := step (completeBoard N) (endpointParams cap enabled) prio (realDetBat ρ) (encode x)
    ((y i).1.val, (y i).2.val + 1) = (s.o i, s.n i) := by
  have hs := encode_legal hp (by omega) x
  let r := resolve (completeBoard N) (endpointParams cap enabled) prio (realDetBat ρ) (encode x)
  have hr := resolve_endpoint_legal (completeBoard N) owners cap hcap enabled prio _
    (real_endpoint_battle cap hcap ρ hρ) (encode x) hs
  have heq : step (completeBoard N) (endpointParams cap enabled) prio (realDetBat ρ) (encode x) = r := by
    unfold step
    rw [grow_zero _ cap enabled (fun i => (hs i).2.2)]
    exact fortify_complete N cap enabled prio r (fun i => (hr i).2.2)
  change ((decode hp (by omega) _ i).1.val, (decode hp (by omega) _ i).2.val + 1) = _
  rw [heq]
  exact decode_at hp (by omega) r i (hr i).1 (hr i).2.1 (hr i).2.2

/-- On every legal indexed input, the real step agrees with the fixed rational step. -/
theorem indexed_real_eq_rational {N owners cap : Nat} (hp : 0 < owners) (hcap : 3 ≤ cap)
    (prio : Nat → Nat) (enabled : Bool) (ρ : ℝ) (hρ : 1 ≤ ρ) (x : Config (Fin N) owners cap) :
    indexedStep hp (by omega) prio enabled (realDetBat ρ) x =
    indexedStep hp (by omega) prio enabled (detBat (endpointParams cap enabled)) x := by
  let B := completeBoard N
  let K := endpointParams cap enabled
  have hs := encode_legal hp (by omega) x
  have heq := resolve_endpoint_congr B cap enabled prio (encode x)
    (fun i => (hs i).2.1) (fun i => (hs i).2.2)
    (realDetBat ρ) (detBat K) (fun i j =>
      (real_endpoint_battle cap hcap ρ hρ i j).trans
        (rational_endpoint_battle cap hcap enabled i j).symm)
  unfold indexedStep step
  rw [grow_zero _ cap enabled (fun i => (hs i).2.2), heq]

end D5.S3.StatisticalMechanics.CellularAutomata.RiskCAEndpoint

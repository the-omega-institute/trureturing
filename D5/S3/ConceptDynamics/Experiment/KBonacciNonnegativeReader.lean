/- GID: D5/S3/ConceptDynamics/Experiment/KBonacciNonnegativeReader
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/KBonacciNonnegativeReader
   mirror-E: none(waiver:exact-symbolic-obstruction)
   anchors: []
   utility: none
   digest: Nonnegative readers obstruct one preparation for unrestricted actual-window protocols. -/

import D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators
import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

/-! Exact irreversible acquisition with an unknown nonnegative fixed reader. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader

open D5.S0.Automata.TypedPartialDFAOOverBase
open PassivePolicyNormalization (Hist execute execute_transfer execute_mono)
open scoped Matrix BigOperators

noncomputable section

abbrev Vec := Fin 2 → ℝ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- Both initial vectors are unknown; the reader may have an unknown zero coordinate. -/
structure World where
  c : Vec
  ell : Vec
  c_pos : ∀ i, 0 < c i
  ell_nonneg : ∀ i, 0 ≤ ell i
  ell_nonzero : 0 < ell 0 + ell 1

def target (w : World) : Mat := Matrix.vecMulVec w.c w.ell

/-- The original live-tail automaton, specialized to dimension two. -/
def base : PartialDFA Bool (Fin 2) :=
  { start := 0
    step := fun s b => if b then
      if h : s.val + 1 < 2 then some ⟨s.val + 1, h⟩ else none
      else some 0 }

def live (word : List Bool) : Mat := fun i s =>
  if base.evalFrom s word = some i then 1 else 0

def endpoint (p t : Fin 2) : Mat := fun i s =>
  if i = t ∧ s.val + p.val < 2 then 1 else 0

/-- Actual words of length three with no internal forbidden pair of ones.
Legality starts the internal-word automaton at zero, not at the current object. -/
abbrev Window := {word : List Bool // word.length = 3 ∧ base.evalFrom 0 word ≠ none}

/-- `none` prepares the same initial object; `some word` applies a complete window. -/
abbrev Action := Option Window

/-- A query retains the preceding literal action list and its next actual action. -/
abbrev Query := List Action × Action
abbrev History := Hist (fun _ : Query => ℝ)

def advance (w : World) (x : Option Vec) (a : Action) : Option Vec :=
  match a with
  | none => some w.c
  | some word => x.map (fun v => live word.val *ᵥ v)

/-- A preparation discards the previous object. No action can return to it. -/
def state (w : World) (actions : List Action) : Option Vec :=
  actions.foldl (advance w) none

def observe (w : World) (x : Option Vec) : ℝ :=
  match x with
  | none => 0
  | some v => w.ell ⬝ᵥ v

/-- Every action has exactly one forced exact read, including every zero read. -/
def read (q : Query) (w : World) : ℝ :=
  observe w (state w (q.1 ++ [q.2]))

/-- A window needs a prepared object. Prefixes retain all past actions, including
discarded runs; only their last preparation supplies the current object. -/
def Chronological : List Action → History → Prop
  | _, [] => True
  | prior, a :: h => a.1.1 = prior ∧
      (a.1.2 ≠ none → none ∈ prior) ∧ Chronological (prior ++ [a.1.2]) h

def preparations (h : History) : ℕ := h.countP (fun a => a.1.2.isNone)
def windows (h : History) : ℕ := h.countP (fun a => a.1.2.isSome)
def paidReads (h : History) : ℕ := h.length

/-- Arbitrary full-history choice, stop and output functions, with an actual finite
execution separately on each world. No common fuel or resource bound is supplied. -/
structure Protocol where
  policy : History → Sum Query Mat
  history : World → History
  output : World → Mat
  terminates : ∀ w, ∃ n, execute read policy n [] w = some (history w, output w)
  lawful : ∀ w, Chronological [] (history w)

def Correct (π : Protocol) : Prop := ∀ w, π.output w = target w

def worstPreparations (π : Protocol) : ENNReal :=
  ⨆ w : World, (preparations (π.history w) : ENNReal)

/-- The empty correct-protocol class has infimum positive infinity. -/
def preparationValue : ENNReal := ⨅ π : {π : Protocol // Correct π}, worstPreparations π.val

private theorem window_endpoint (word : Window) :
    ∃ p t : Fin 2, (word.val.takeWhile id).length = p.val ∧
      live word.val = endpoint p t := by
  have h := D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators.actual_endpoint_operators
    (K := ℝ) 2 (by decide)
  have hf := h.2.2.2.2.2.2.1 word.val (by omega) word.property.2
  obtain ⟨p, t, hp, _, _, _, he⟩ := h.2.2.2.2.1 word.val hf word.property.2
  exact ⟨p, t, hp, he⟩

private theorem all_endpoints : ∀ p t : Fin 2,
    ∃ word : Window, live word.val = endpoint p t := by
  intro p t
  have h := D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators.actual_endpoint_operators
    (K := ℝ) 2 (by decide)
  have hw := h.2.2.2.2.2.2.2.2.2.2.1 p t (by omega)
  have hn : base.evalFrom 0 _ = some t := hw.2.2.2.1
  exact ⟨⟨_, hw.1, by rw [hn]; simp⟩, hw.2.2.2.2⟩

private theorem state_snoc (w : World) (prior : List Action) (a : Action) :
    state w (prior ++ [a]) = advance w (state w prior) a := by
  simp [state, List.foldl_append]

private theorem charges (h : History) : paidReads h = preparations h + windows h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    simp only [paidReads, List.length_cons, preparations, windows, List.countP_cons] at ih ⊢
    cases ha : a.1.2 <;>
      simp only [ha, Option.isNone, Option.isSome, Bool.false_eq_true, ite_false,
        ite_true] <;> omega

private theorem terminal_unique (π : Protocol) (w : World) (n : ℕ) (h : History) (R : Mat)
    (hr : execute read π.policy n [] w = some (h, R)) :
    π.history w = h ∧ π.output w = R := by
  obtain ⟨m, hm⟩ := π.terminates w
  have hn := execute_mono read π.policy n (max n m) [] w h R (le_max_left ..) hr
  have hm' := execute_mono read π.policy m (max n m) [] w _ _ (le_max_right ..) hm
  rw [hn] at hm'
  have he := Prod.mk.inj (Option.some.inj hm')
  exact ⟨he.1.symm, he.2.symm⟩

private theorem query_tail (policy : History → Sum Query Mat) (w : World)
    (n : ℕ) (pre h : History) (R : Mat) (q : Query)
    (hp : policy pre = .inl q) (hr : execute read policy n pre w = some (h, R)) :
    ∃ m tail, execute read policy m (pre ++ [⟨q, read q w⟩]) w = some (tail, R) ∧
      h = ⟨q, read q w⟩ :: tail := by
  cases n with
  | zero => simp [execute] at hr
  | succ n =>
    simp only [execute, hp] at hr
    obtain ⟨⟨tail, l⟩, ht, he⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    exact ⟨n, tail, ht, rfl⟩

/-- Once the actual objects and fixed readers agree, every subsequent complete
window has the same paid read, with no exclusion for killed or repeated zero states. -/
private theorem continuation_read_eq (u v : World) (prior : List Action) (h : History)
    (hell : u.ell = v.ell) (hs : state u prior = state v prior)
    (hc : Chronological prior h) (hp : preparations h = 0) :
    ∀ a ∈ h, read a.1 u = read a.1 v := by
  induction h generalizing prior with
  | nil => simp
  | cons a h ih =>
    rcases hc with ⟨ha, _, hc⟩
    have hzero : preparations h = 0 := by
      simp only [preparations, List.countP_cons] at hp ⊢
      split at hp <;> omega
    have hsome : ∃ word, a.1.2 = some word := by
      cases hact : a.1.2 with
      | none => simp [preparations, List.countP_cons, hact] at hp
      | some word => exact ⟨word, rfl⟩
    obtain ⟨word, hact⟩ := hsome
    have hs' : state u (prior ++ [a.1.2]) = state v (prior ++ [a.1.2]) := by
      rw [state_snoc, state_snoc, hact]
      simp only [advance, hs]
    have he : read a.1 u = read a.1 v := by
      simp only [read, ha, hs', observe]
      cases state v (prior ++ [a.1.2]) <;> simp [observe, hell]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact he
    · exact ih _ hs' hc hzero b hb

private def corner (other : Bool) : World where
  c := ![1, if other then 2 else 1]
  ell := ![1, 0]
  c_pos := by intro i; fin_cases i <;> cases other <;> norm_num
  ell_nonneg := by intro i; fin_cases i <;> norm_num
  ell_nonzero := by norm_num

private def interior (other : Bool) : World where
  c := if other then ![3/4, 1/4] else ![1/4, 3/4]
  ell := ![1, 1]
  c_pos := by intro i; fin_cases i <;> cases other <;> norm_num
  ell_nonneg := by intro i; fin_cases i <;> norm_num
  ell_nonzero := by norm_num

private theorem corner_initial (b : Bool) : read ([], none) (corner b) = 1 := by
  cases b <;> norm_num [read, state, advance, observe, corner, dotProduct, Fin.sum_univ_two]

private theorem corner_different : target (corner false) ≠ target (corner true) := by
  intro h
  have he := congrArg (fun R : Mat => R 1 0) h
  norm_num [target, corner, Matrix.vecMulVec_apply] at he

/-- The two source pairs agree after the selected first *actual* window. The
trailing endpoint is unrestricted, including the boundary reader's zero read. -/
private theorem first_window_collision (word : Window) :
    ∃ u v : World, u.ell = v.ell ∧ target u ≠ target v ∧
      read ([], none) u = 1 ∧ read ([], none) v = 1 ∧
      state u [none, some word] = state v [none, some word] := by
  obtain ⟨p, t, _, he⟩ := window_endpoint word
  fin_cases p
  · refine ⟨interior false, interior true, rfl, ?_, ?_, ?_, ?_⟩
    · intro ht
      have hf := congrArg (fun R : Mat => R 0 0) ht
      norm_num [target, interior, Matrix.vecMulVec_apply] at hf
    · norm_num [read, state, advance, observe, interior, dotProduct, Fin.sum_univ_two]
    · norm_num [read, state, advance, observe, interior, dotProduct, Fin.sum_univ_two]
    · change some (live word.val *ᵥ (interior false).c) =
        some (live word.val *ᵥ (interior true).c)
      rw [he]
      congr 1
      ext i
      fin_cases i <;> fin_cases t <;>
        norm_num [endpoint, interior, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨corner false, corner true, rfl, corner_different,
      corner_initial false, corner_initial true, ?_⟩
    change some (live word.val *ᵥ (corner false).c) =
      some (live word.val *ᵥ (corner true).c)
    rw [he]
    congr 1
    ext i
    fin_cases i <;> fin_cases t <;>
      norm_num [endpoint, corner, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end
end D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader

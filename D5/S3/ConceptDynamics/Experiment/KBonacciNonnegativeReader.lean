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
  simpa only [paidReads, preparations, windows, decide_not, Bool.decide_coe,
    Option.not_isNone] using
    (List.length_eq_countP_add_countP (fun a : Sigma (fun _ : Query => ℝ) => a.1.2.isNone)
      (l := h))

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
      | none => simp [preparations, hact] at hp
      | some word => exact ⟨word, rfl⟩
    obtain ⟨word, hact⟩ := hsome
    have hs' : state u (prior ++ [a.1.2]) = state v (prior ++ [a.1.2]) := by
      rw [state_snoc, state_snoc, hact]
      simp only [advance, hs]
    have he : read a.1 u = read a.1 v := by
      simp only [read, ha, hs', observe]
      cases state v (prior ++ [a.1.2]) <;> simp [hell]
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

private theorem collision_of_same_run (π : Protocol) (u v : World)
    (hne : target u ≠ target v) (n : ℕ) (h : History) (R : Mat)
    (hu : execute read π.policy n [] u = some (h, R))
    (hv : execute read π.policy n [] v = some (h, R)) :
    ∃ u v : World, target u ≠ target v ∧
      π.history u = π.history v ∧ π.output u = π.output v := by
  have eu := terminal_unique π u n h R hu
  have ev := terminal_unique π v n h R hv
  exact ⟨u, v, hne, eu.1.trans ev.1.symm, eu.2.trans ev.2.symm⟩

/-- A source-specific collision for every legal, pointwise finite, one-preparation
protocol. It neither assumes a collision certificate nor bounds the window tail. -/
private theorem one_preparation_terminal_collision (π : Protocol)
    (bound : ∀ w, preparations (π.history w) ≤ 1) :
    ∃ u v : World, target u ≠ target v ∧
      π.history u = π.history v ∧ π.output u = π.output v := by
  obtain ⟨n, hn⟩ := π.terminates (corner false)
  cases hp0 : π.policy [] with
  | inr R =>
    apply collision_of_same_run π (corner false) (corner true) corner_different 1 [] R
    · simp [execute, hp0]
    · simp [execute, hp0]
  | inl q =>
    obtain ⟨m, tail, ht, hh⟩ := query_tail π.policy (corner false) n [] _ _ q hp0 hn
    have hc := π.lawful (corner false)
    rw [hh] at hc
    have hq0 : q.1 = [] := hc.1
    have hqa : q.2 = none := by
      by_contra hne
      have hmem := hc.2.1 hne
      simp [hq0] at hmem
    have hq : q = ([], none) := Prod.ext hq0 hqa
    subst q
    simp only [corner_initial, List.nil_append] at ht hh
    have htail : Chronological [none] tail := hc.2.2
    have hpaid : preparations tail = 0 := by
      have hb := bound (corner false)
      rw [hh] at hb
      simpa [preparations] using hb
    cases hp1 : π.policy [⟨([], none), 1⟩] with
    | inr R =>
      apply collision_of_same_run π (corner false) (corner true) corner_different 2
        [⟨([], none), 1⟩] R
      · simp [execute, hp0, corner_initial, hp1]
      · simp [execute, hp0, corner_initial, hp1]
    | inl q =>
      obtain ⟨m', rest, ht', htail'⟩ := query_tail π.policy (corner false) m
        [⟨([], none), 1⟩] tail _ q hp1 ht
      rw [htail'] at htail
      have hq0 : q.1 = [none] := htail.1
      have hqa : ∃ word, q.2 = some word := by
        cases ha : q.2 with
        | some word => exact ⟨word, rfl⟩
        | none =>
          rw [htail'] at hpaid
          simp [preparations, ha] at hpaid
      obtain ⟨word, hqa⟩ := hqa
      have hq : q = ([none], some word) := Prod.ext hq0 hqa
      subst q
      obtain ⟨u, v, hell, hne, huD, hvD, hs⟩ := first_window_collision word
      obtain ⟨nu, hnu⟩ := π.terminates u
      obtain ⟨mu, tailu, htu, hhu⟩ := query_tail π.policy u nu [] _ _
        ([], none) hp0 hnu
      simp only [huD, List.nil_append] at htu hhu
      obtain ⟨mu', restu, htru, htailu⟩ := query_tail π.policy u mu
        [⟨([], none), 1⟩] tailu _ ([none], some word) hp1 htu
      have hwhole : π.history u = ⟨([], none), 1⟩ ::
          ⟨([none], some word), read ([none], some word) u⟩ :: restu := by
        rw [hhu, htailu]
      have hcrest : Chronological [none, some word] restu := by
        have hl := π.lawful u
        rw [hwhole] at hl
        exact hl.2.2.2.2
      have hprest : preparations restu = 0 := by
        have hb := bound u
        rw [hwhole] at hb
        simpa [preparations] using hb
      have hread : read ([none], some word) u = read ([none], some word) v := by
        change observe u (state u [none, some word]) =
          observe v (state v [none, some word])
        rw [hs]
        cases state v [none, some word] <;> simp [observe, hell]
      have heq : ∀ a ∈ π.history u, read a.1 u = read a.1 v := by
        rw [hwhole]
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact huD.trans hvD.symm
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hread
        · exact continuation_read_eq u v [none, some word] restu hell hs
            hcrest hprest a ha
      have transfer := execute_transfer read π.policy nu [] u _ _ hnu
      have hv : execute read π.policy nu [] v = some (π.history u, π.output u) :=
        transfer.2 v (fun a ha => (heq a ha).symm.trans (transfer.1 a ha))
      exact collision_of_same_run π u v hne nu (π.history u) (π.output u) hnu hv

private theorem initial_positive (w : World) : 0 < read ([], none) w := by
  change 0 < w.ell ⬝ᵥ w.c
  rw [dotProduct, Fin.sum_univ_two]
  have hpos : 0 < w.ell 0 ∨ 0 < w.ell 1 := by
    have := w.ell_nonzero
    by_contra h
    push Not at h
    linarith
  rcases hpos with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos h (w.c_pos 0))
      (mul_nonneg (w.ell_nonneg 1) (le_of_lt (w.c_pos 1)))
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (w.ell_nonneg 0) (le_of_lt (w.c_pos 0))) (mul_pos h (w.c_pos 1))

/-- The complete dimension-two obstruction for the original rank-one target.
Worst costs are extended suprema, and the infimum includes an empty protocol class.
Only the preparation equality and simultaneous resource law are excluded. -/
theorem complete_source_8_2 :
    let T : World → Mat := target
    let correct : Protocol → Prop := fun π => ∀ w, π.output w = T w
    let value : ENNReal := ⨅ π : {π : Protocol // correct π}, worstPreparations π.val
    (∀ word : Window, ∃ p t : Fin 2,
      (word.val.takeWhile id).length = p.val ∧ live word.val = endpoint p t) ∧
    (∀ p t : Fin 2, ∃ word : Window, live word.val = endpoint p t) ∧
    (∀ w : World, 0 < read ([], none) w) ∧
    (∀ (π : Protocol) (w : World), paidReads (π.history w) =
      preparations (π.history w) + windows (π.history w)) ∧
    (∀ π : Protocol, correct π → ¬ (∀ w, preparations (π.history w) ≤ 1)) ∧
    (∀ π : Protocol, correct π → (2 : ENNReal) ≤ worstPreparations π) ∧
    (2 : ENNReal) ≤ value ∧
    value ≠ 1 ∧
    ¬ (∃ π : Protocol, correct π ∧ ∀ w,
      preparations (π.history w) ≤ 1 ∧ windows (π.history w) ≤ 2 ∧
        paidReads (π.history w) ≤ 3) := by
  dsimp only
  have impossible (π : Protocol) (hc : Correct π)
      (hb : ∀ w, preparations (π.history w) ≤ 1) : False := by
    obtain ⟨u, v, hne, _, he⟩ := one_preparation_terminal_collision π hb
    exact hne ((hc u).symm.trans (he.trans (hc v)))
  have lower (π : Protocol) (hc : Correct π) :
      (2 : ENNReal) ≤ worstPreparations π := by
    have hex : ∃ w, 2 ≤ preparations (π.history w) := by
      by_contra h
      push Not at h
      exact impossible π hc (fun w => by have := h w; omega)
    obtain ⟨w, hw⟩ := hex
    exact le_trans (by exact_mod_cast hw) (le_iSup
      (fun w : World => (preparations (π.history w) : ENNReal)) w)
  have value : (2 : ENNReal) ≤ preparationValue := by
    exact le_iInf (fun π => lower π.val π.property)
  refine ⟨window_endpoint, all_endpoints, initial_positive, fun _ _ => charges _,
    impossible, lower, value, ?_, ?_⟩
  · intro he
    change preparationValue = 1 at he
    rw [he] at value
    norm_num at value
  · rintro ⟨π, hc, hb⟩
    exact impossible π hc (fun w => (hb w).1)

#print axioms complete_source_8_2

end
end D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader

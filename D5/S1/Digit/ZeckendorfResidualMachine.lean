/- GID: D5/S1/Digit/ZeckendorfResidualMachine
   generality: I
   mirror-B: none(waiver:source-arithmetic-bridge)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Complete padded Fibonacci residuals form a finite reachable partial output machine. -/

import D5.S1.Digit.ZeckendorfResidualCover
import D5.S0.Automata.TypedPartialDFAO
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfResidualMachine

open D5.S0.Automata.TypedPartialDFAO
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfResidualCover

/-- The previous-one flag gives the exact padded no11 language. -/
def sourceBase : BaseAutomaton (Fin 2) Bool where
  start := false
  step b a := if a = 0 then some false else if b then none else some true

/-- Only actual residuals of legal source prefixes are states; there is no sink. -/
def ResidualState (c : ℕ) :=
  {r : List (Fin 2) → Option Bool // ∃ w, NoAdjacentOnes w ∧ ZeckendorfRawWindow.residual c w = r}

/-- An admissible state count includes every reachable live state and the start.
The complete Option equation enforces outputs on all valid padded words and
undefined execution on every invalid word. -/
def Admissible (c k : ℕ) : Prop :=
  ∃ P : BaseAutomaton (Fin 2) (Fin k), ∃ output : Fin k → Bool,
    P.step P.start 0 = some P.start ∧
    (∀ w, (P.run w).map output = ZeckendorfRawWindow.residual c [] w) ∧
    (∀ s, ∃ w, P.run w = some s)

/-- Minimum over the exact finite source-full machine class. -/
noncomputable def minimumStates (c : ℕ) : ℕ := sInf {k | Admissible c k}

/-- The actual full ZeckendorfRawWindow.residual image is finite, and its exact cardinality is
realized by a source-full partial DFAO with every state reachable. -/
theorem finite_residual_realization (c : ℕ) :
    Finite (ResidualState c) ∧ Admissible c (Nat.card (ResidualState c)) := by
  classical
  let pack (L : ℕ) (f : Fin L → Fin 2) := List.ofFn f
  have hf (L : ℕ) : (Set.range (fun f : Fin L → Fin 2 => ZeckendorfRawWindow.residual c (pack L f))).Finite :=
    Set.finite_range _
  let H := c + 14
  have hH : 14 ≤ H := by omega
  have hc : c ≤ Nat.fib H := by
    have := Nat.le_fib_add_one H
    omega
  have finite_image : (Set.univ : Set (ResidualState c)).Finite := by
    have hs := (hf (H + 7)).subset (show
        {r | ∃ w, NoAdjacentOnes w ∧ ZeckendorfRawWindow.residual c w = r} ⊆
          Set.range (fun f : Fin (H + 7) → Fin 2 => ZeckendorfRawWindow.residual c (pack (H + 7) f)) from by
      rintro r ⟨w,hw,rfl⟩
      obtain ⟨v,hv,hl,he⟩ := all_state_cover H c hH hc w hw
      let f : Fin (H + 7) → Fin 2 := fun i => v[i.val]'(by omega)
      refine ⟨f,?_,⟩
      have heq : pack (H + 7) f = v := by
        apply List.ext_getElem
        · simp only [pack,List.length_ofFn]; exact hl.symm
        · intro i hi hj
          simp only [pack,List.getElem_ofFn]
          rfl
      change ZeckendorfRawWindow.residual c (pack (H + 7) f) = _
      rw [heq]
      exact he.symm)
    letI : Fintype (ResidualState c) := hs.fintype
    exact Set.finite_univ
  letI : Finite (ResidualState c) := Set.finite_univ_iff.mp finite_image
  refine ⟨inferInstance, ?_⟩
  let state (w : List (Fin 2)) (hw : NoAdjacentOnes w) : ResidualState c :=
    ⟨ZeckendorfRawWindow.residual c w, w, hw, rfl⟩
  let initial := state [] (by simp [NoAdjacentOnes])
  let rep (s : ResidualState c) := s.property.choose
  have rep_legal (s : ResidualState c) : NoAdjacentOnes (rep s) := s.property.choose_spec.1
  have rep_eq (s : ResidualState c) : ZeckendorfRawWindow.residual c (rep s) = s.val := s.property.choose_spec.2
  have domain (w : List (Fin 2)) (z : List (Fin 2)) :
      (ZeckendorfRawWindow.residual c w z).isSome = decide (NoAdjacentOnes (w ++ z)) := by
    by_cases h : NoAdjacentOnes (w ++ z) <;> simp [ZeckendorfRawWindow.residual,h]
  have same_legal (w v : List (Fin 2)) (he : ZeckendorfRawWindow.residual c w = ZeckendorfRawWindow.residual c v)
      (z : List (Fin 2)) : NoAdjacentOnes (w ++ z) ↔ NoAdjacentOnes (v ++ z) := by
    have := congrArg (fun r => (r z).isSome) he
    simpa only [domain, decide_eq_decide] using this
  have derivative (w : List (Fin 2)) (a : Fin 2) :
      ZeckendorfRawWindow.residual c (w ++ [a]) = fun z => ZeckendorfRawWindow.residual c w (a :: z) := by
    funext z
    simp [ZeckendorfRawWindow.residual,List.append_assoc]
  let stype (s : ResidualState c) : Bool := decide (s.val [1] = none)
  have type_word (w : List (Fin 2)) (hw : NoAdjacentOnes w) :
      stype (state w hw) = decide (w.getLast? = some 1) := by
    change decide (ZeckendorfRawWindow.residual c w [1] = none) = _
    have hchain : w.IsChain (fun a b => a = 0 ∨ b = 0) := hw
    have legal1 : NoAdjacentOnes (w ++ [1]) ↔ w.getLast? ≠ some 1 := by
      cases hh : w.getLast? with
      | none => simp [NoAdjacentOnes,List.isChain_append,hchain,hh]
      | some b => fin_cases b <;> simp [NoAdjacentOnes,List.isChain_append,hchain,hh]
    by_cases h : w.getLast? = some 1 <;> simp [ZeckendorfRawWindow.residual,legal1,h]
  have ext_legal (w : List (Fin 2)) (hw : NoAdjacentOnes w) (a : Fin 2) :
      NoAdjacentOnes (w ++ [a]) ↔ a = 0 ∨ w.getLast? ≠ some 1 := by
    have hchain : w.IsChain (fun a b => a = 0 ∨ b = 0) := hw
    cases hh : w.getLast? with
    | none => simp [NoAdjacentOnes,List.isChain_append,hchain,hh]
    | some b => fin_cases b <;> fin_cases a <;>
        simp [NoAdjacentOnes,List.isChain_append,hchain,hh]
  let step (s : ResidualState c) (a : Fin 2) : Option (ResidualState c) :=
    if h : NoAdjacentOnes (rep s ++ [a]) then some (state (rep s ++ [a]) h) else none
  have step_word (w : List (Fin 2)) (hw : NoAdjacentOnes w) (a : Fin 2) :
      step (state w hw) a =
        if h : NoAdjacentOnes (w ++ [a]) then some (state (w ++ [a]) h) else none := by
    have he := rep_eq (state w hw)
    have hl := same_legal _ _ he [a]
    dsimp only [step]
    split <;> split
    · congr 1
      apply Subtype.ext
      change ZeckendorfRawWindow.residual c (rep (state w hw) ++ [a]) = ZeckendorfRawWindow.residual c (w ++ [a])
      rw [derivative,derivative,he]
    · exact False.elim (‹¬ NoAdjacentOnes (w ++ [a])› (hl.mp ‹_›))
    · exact False.elim (‹¬ NoAdjacentOnes (rep (state w hw) ++ [a])› (hl.mpr ‹_›))
    · rfl
  have represented (s : ResidualState c) : state (rep s) (rep_legal s) = s :=
    Subtype.ext (rep_eq s)
  let M : Machine (Fin 2) Bool Bool (ResidualState c) := {
    base := sourceBase
    start := initial
    step := step
    output := fun s => (s.val []).getD false
    stateType := stype
    start_type := by
      change stype (state [] (by simp [NoAdjacentOnes])) = false
      rw [type_word [] (by simp [NoAdjacentOnes])]
      rfl
    type_preserving := by
      intro s a
      have hp (w : List (Fin 2)) (hw : NoAdjacentOnes w) :
          Option.map stype (step (state w hw) a) = sourceBase.step (stype (state w hw)) a := by
        rw [step_word w hw a,type_word w hw]
        by_cases h : NoAdjacentOnes (w ++ [a])
        · rw [dif_pos h]
          simp only [Option.map_some,type_word (w ++ [a]) h,List.getLast?_concat]
          have hl := (ext_legal w hw a).mp h
          fin_cases a <;> simp_all [sourceBase]
        · rw [dif_neg h]
          have hl : a ≠ 0 ∧ w.getLast? = some 1 := by
            simpa only [ext_legal w hw a,not_or,not_not] using h
          simp [sourceBase,hl.1,hl.2]
      simpa only [represented s] using hp (rep s) (rep_legal s)
    zero := 0
    start_zero_loop := by
      change step (state [] (by simp [NoAdjacentOnes])) 0 = some initial
      rw [step_word [] (by simp [NoAdjacentOnes]) 0]
      simp only [List.nil_append]
      have hz : NoAdjacentOnes [0] := by simp [NoAdjacentOnes]
      rw [dif_pos hz]
      congr 1
      apply Subtype.ext
      funext z
      change ZeckendorfRawWindow.residual c [0] z = ZeckendorfRawWindow.residual c [] z
      simp [ZeckendorfRawWindow.residual,NoAdjacentOnes,List.isChain_cons,
        value,D5.S1.Digit.GoldenBase4IntervalMachine.fibPair]
      by_cases hz' : z.IsChain (fun a b => a = 0 ∨ b = 0) <;> simp [hz']
  }
  have run_word (w : List (Fin 2)) (hw : NoAdjacentOnes w) (z : List (Fin 2)) :
      M.runFrom (state w hw) z =
        if h : NoAdjacentOnes (w ++ z) then some (state (w ++ z) h) else none := by
    induction z generalizing w with
    | nil => simp only [Machine.runFrom,List.append_nil,dif_pos hw]
    | cons a z ih =>
      change (step (state w hw) a).bind _ = _
      rw [step_word w hw a]
      by_cases h : NoAdjacentOnes (w ++ [a])
      · rw [dif_pos h]
        simp only [Option.bind_some]
        rw [ih (w ++ [a]) h]
        simp only [List.append_assoc,List.singleton_append]
      · rw [dif_neg h]
        have hz : ¬ NoAdjacentOnes (w ++ a :: z) := by
          intro hh
          apply h
          have he : w ++ a :: z = (w ++ [a]) ++ z := by simp
          rw [he] at hh
          exact hh.left_of_append
        simp [hz]
  have output_word (w : List (Fin 2)) : M.evalOutput w = ZeckendorfRawWindow.residual c [] w := by
    rw [Machine.evalOutput,Machine.run]
    change Option.map _ (M.runFrom (state [] (by simp [NoAdjacentOnes])) w) = _
    rw [run_word [] (by simp [NoAdjacentOnes]) w]
    by_cases hw : NoAdjacentOnes w
    · simp only [List.nil_append,dif_pos hw]
      change some ((ZeckendorfRawWindow.residual c w []).getD false) = _
      simp [ZeckendorfRawWindow.residual,hw]
    · simp only [List.nil_append,dif_neg hw,Option.map_none,
        ZeckendorfRawWindow.residual,if_neg hw]
  have reachable (s : ResidualState c) : ∃ w, M.run w = some s := by
    refine ⟨rep s,?_⟩
    change M.runFrom (state [] (by simp [NoAdjacentOnes])) (rep s) = some s
    rw [run_word [] (by simp [NoAdjacentOnes]) (rep s)]
    simp only [List.nil_append,dif_pos (rep_legal s)]
    rw [represented]
  letI := Fintype.ofFinite (ResidualState c)
  let e : ResidualState c ≃ Fin (Nat.card (ResidualState c)) :=
    (Fintype.equivFin _).trans (finCongr (Nat.card_eq_fintype_card).symm)
  let N : Machine (Fin 2) Bool Bool (Fin (Nat.card (ResidualState c))) := {
    base := M.base
    start := e M.start
    step := fun s a => (M.step (e.symm s) a).map e
    output := fun s => M.output (e.symm s)
    stateType := fun s => M.stateType (e.symm s)
    start_type := by simp [M.start_type]
    type_preserving := by
      intro s a
      simpa only [Option.map_map,Function.comp_def,Equiv.symm_apply_apply]
        using M.type_preserving (e.symm s) a
    zero := M.zero
    start_zero_loop := by simp [M.start_zero_loop]
  }
  have transport (s : ResidualState c) (w : List (Fin 2)) :
      N.runFrom (e s) w = (M.runFrom s w).map e := by
    induction w generalizing s with
    | nil => rfl
    | cons a w ih =>
      simp only [Machine.runFrom]
      change ((M.step (e.symm (e s)) a).map e).bind (fun next => N.runFrom next w) = _
      rw [Equiv.symm_apply_apply]
      cases ht : M.step s a with
      | none => simp
      | some next => simpa only [Option.map_some,Option.bind_some] using ih next
  let P : BaseAutomaton (Fin 2) (Fin (Nat.card (ResidualState c))) :=
    ⟨N.start,N.step⟩
  have same_run (s : Fin (Nat.card (ResidualState c))) (w : List (Fin 2)) :
      P.runFrom s w = N.runFrom s w := by
    induction w generalizing s with
    | nil => rfl
    | cons a w ih =>
      simp only [BaseAutomaton.runFrom,Machine.runFrom]
      congr 1
      funext t
      exact ih t
  refine ⟨P,N.output,N.start_zero_loop,?_,?_⟩
  · intro w
    change (P.runFrom N.start w).map N.output = _
    rw [same_run]
    simp only [N,transport,Option.map_map]
    simpa only [Function.comp_def,Equiv.symm_apply_apply,Machine.evalOutput,Machine.run]
      using output_word w
  · intro s
    obtain ⟨w,hw⟩ := reachable (e.symm s)
    refine ⟨w,?_⟩
    change P.runFrom (e M.start) w = _
    rw [same_run,transport]
    change Option.map e (M.run w) = _
    simp [hw]

#print axioms finite_residual_realization

end D5.S1.Digit.ZeckendorfResidualMachine

/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BasePathRealization
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BasePathRealization
   mirror-E: none(waiver:complete-arithmetic-path-realization)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: Flushed arithmetic paths lift to the finite certificate graph. -/

/-
proof_shape: content (base_path_realization)
escape_witness: Complete successor reconstruction and unbounded path lifting into the finite graph.
admission_basis: escape-witness
Direct frozen dependencies: none; BaseCertificates is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseCertificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

/-- The literal arithmetic transitions before assigning finite graph indices. -/
def baseRawAutomaton : NFA (ℤ × ℤ × ℤ × ℤ) (List ℤ) where
  start := {s | s ∈ initialStates}
  step s a := {t | (t,a) ∈ baseSuccessors s}
  accept := {t | baseTerminal t = true}

private def realizationRowCheck (i : ℕ) : Bool :=
  let row := baseTable i
  let actual := row.2.1.map fun e => ((baseTable e.1).1, e.2)
  (baseSuccessors row.1).all actual.contains &&
    row.2.1.all (fun e => decide (e.1 < 1492)) &&
    decide (row.1[18]?.getD 0 = 0 ∨ row.1[18]?.getD 0 = 1)

private def realizationBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => realizationRowCheck (start+k)

/-- No arithmetic path from a source to a flushed state is omitted by the finite table. -/
theorem base_path_realization {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ baseRawAutomaton.start) (ht : t ∈ baseRawAutomaton.accept)
    (p : baseRawAutomaton.Path s t xs) :
    ∃ (charge : Bool) (i k : Fin 1492),
      i ∈ (baseAutomaton charge).start ∧ k ∈ (baseAutomaton charge).accept ∧
      (baseTable i.val).1 = s ∧ (baseTable k.val).1 = t ∧
      Nonempty ((baseAutomaton charge).Path i k xs) := by
  have checked (i : ℕ) (hi : i < 1492) : realizationRowCheck i = true := by
    have blocks : ∀ b : Fin 24,
        realizationBlockCheck (64*b.val) (min 64 (1492-64*b.val)) = true := by
      intro b
      fin_cases b <;> decide
    have hb := blocks ⟨i/64, by omega⟩
    dsimp [realizationBlockCheck] at hb
    have hm : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range]
      omega
    have hh := List.all_eq_true.mp hb (i%64) hm
    simpa only [show 64*(i/64)+i%64=i by omega] using hh
  have source : ∃ i : Fin 1492,
      i.val < 7 ∧ (baseTable i.val).1 = s := by
    change s ∈ initialStates at hs
    have hsrc : initialStates =
        ([0,1,2,3,4,5,6] : List ℕ).map (fun i => (baseTable i).1) := by
      decide
    rw [hsrc] at hs
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hs
    have hr : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
      simpa using hi
    refine ⟨⟨i,by omega⟩,?_,he⟩
    change i < 7
    omega
  have lift (charge : Bool) {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : baseRawAutomaton.Path s t xs) (i : Fin 1492)
      (hi : (baseTable i.val).1 = s) :
      ∃ k : Fin 1492, (baseTable k.val).1 = t ∧
        Nonempty ((baseAutomaton charge).Path i k xs) := by
    induction p generalizing i with
    | nil s => exact ⟨i,hi,⟨.nil i⟩⟩
    | cons q s t a xs hstep p ih =>
      have hc := checked i.val i.isLt
      simp only [realizationRowCheck, Bool.and_eq_true] at hc
      have hm : (q,a) ∈ baseSuccessors (baseTable i.val).1 := by
        rw [hi]
        exact hstep
      have ha := List.all_eq_true.mp hc.1.1 (q,a) hm
      have he : (q,a) ∈ (baseTable i.val).2.1.map
          (fun e => ((baseTable e.1).1,e.2)) := by
        simpa only [List.contains_eq_mem,decide_eq_true_eq] using ha
      obtain ⟨e,he,heq⟩ := List.mem_map.mp he
      have hei : e.1 < 1492 := of_decide_eq_true (List.all_eq_true.mp hc.1.2 e he)
      let j : Fin 1492 := ⟨e.1,hei⟩
      have hj : (baseTable j.val).1 = q := congrArg Prod.fst heq
      have hlabel : e.2 = a := congrArg Prod.snd heq
      obtain ⟨k,hk,⟨pk⟩⟩ := ih j hj
      refine ⟨k,hk,⟨.cons j i k a xs ?_ pk⟩⟩
      change (j.val,a) ∈ (baseTable i.val).2.1
      change (e.1,a) ∈ (baseTable i.val).2.1
      rw [← hlabel]
      exact he
  obtain ⟨i,hi,his⟩ := source
  obtain ⟨k,hkt,⟨pk⟩⟩ := lift true p i his
  have hc := checked k.val k.isLt
  simp only [realizationRowCheck,Bool.and_eq_true] at hc
  have hflag := of_decide_eq_true hc.2
  have finish (charge : Bool) (hflag : (baseTable k.val).1[18]?.getD 0 =
      if charge then 0 else 1) : k ∈ (baseAutomaton charge).accept := by
    simp only [baseAutomaton,Set.mem_ofPred_eq,Bool.and_eq_true,beq_iff_eq]
    change baseTerminal t = true at ht
    exact ⟨by simpa only [hkt] using ht,hflag⟩
  have start (charge : Bool) : i ∈ (baseAutomaton charge).start := by
    change ([0,1,2,3,4,5,6] : List ℕ).contains i.val = true
    simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons]
    omega
  rcases hflag with hflag | hflag
  · exact ⟨true,i,k,start true,finish true hflag,his,hkt,⟨pk⟩⟩
  · obtain ⟨k',hkt',pk'⟩ := lift false p i his
    -- The same edge sequence has a path in both modes, but the final index is chosen afresh.
    have hend : (baseTable k'.val).1[18]?.getD 0 = 1 := by
      rw [hkt',← hkt]
      exact hflag
    have ht' : k' ∈ (baseAutomaton false).accept := by
      simp only [baseAutomaton,Set.mem_ofPred_eq,Bool.and_eq_true,beq_iff_eq]
      change baseTerminal t = true at ht
      exact ⟨by simpa only [hkt'] using ht,hend⟩
    exact ⟨false,i,k',start false,ht',his,hkt',pk'⟩

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_realization

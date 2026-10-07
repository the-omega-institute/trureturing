/- GID: D5/S1/Words/AdmissibleWords/KBonacciDirectConcatenation
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciDirectConcatenation
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Direct concatenation of actual scanner words has nested endpoint neighborhoods. -/

import D5.S1.Words.ClosedRunStarts
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.KBonacciDirectConcatenation

open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.ClosedRunStarts

/-- Actual word concatenation, including short and all-true words, is governed by
the sum of the two interface runs. The one-page neighborhoods are nested and the
last is empty; a legal word starting with false imposes no interface restriction. -/
theorem actual_direct_concatenation (k m n : ℕ) (hk : 2 ≤ k) :
  let initialRun : {q : ℕ} → (Fin q → Bool) → ℕ :=
    fun {_} w => (List.ofFn w).findIdx Bool.not
  let terminalRun : {q : ℕ} → (Fin q → Bool) → ℕ :=
    fun {_} w => initialRun (fun i => w i.rev)
  let oneNeighborhood (k n s : ℕ) : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun w => DBonacciAdmissible k n w ∧
      (List.ofFn w).head? = some true ∧ initialRun w < k - s)
  (∀ (x : Fin m → Bool) (y : Fin n → Bool),
    DBonacciAdmissible k m x → DBonacciAdmissible k n y →
    terminalRun x < k ∧ initialRun y < k ∧
      (DBonacciAdmissible k (m + n) (Fin.append x y) ↔
        terminalRun x + initialRun y < k)) ∧
  (∀ s t : ℕ, s ≤ t → oneNeighborhood k n t ⊆ oneNeighborhood k n s) ∧
  oneNeighborhood k n (k - 1) = ∅ ∧
  (∀ (x : Fin m → Bool) (y : Fin n → Bool),
    DBonacciAdmissible k m x → DBonacciAdmissible k n y →
    (List.ofFn y).head? = some false →
    DBonacciAdmissible k (m + n) (Fin.append x y)) := by
  classical
  let initialRun : {q : ℕ} → (Fin q → Bool) → ℕ :=
    fun {_} w => (List.ofFn w).findIdx Bool.not
  let terminalRun : {q : ℕ} → (Fin q → Bool) → ℕ :=
    fun {_} w => initialRun (fun i => w i.rev)
  let oneNeighborhood (k n s : ℕ) : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun w => DBonacciAdmissible k n w ∧
      (List.ofFn w).head? = some true ∧ initialRun w < k - s)
  change
    (∀ (x : Fin m → Bool) (y : Fin n → Bool),
      DBonacciAdmissible k m x → DBonacciAdmissible k n y →
      terminalRun x < k ∧ initialRun y < k ∧
        (DBonacciAdmissible k (m + n) (Fin.append x y) ↔
          terminalRun x + initialRun y < k)) ∧
    (∀ s t : ℕ, s ≤ t → oneNeighborhood k n t ⊆ oneNeighborhood k n s) ∧
    oneNeighborhood k n (k - 1) = ∅ ∧
    (∀ (x : Fin m → Bool) (y : Fin n → Bool),
      DBonacciAdmissible k m x → DBonacciAdmissible k n y →
      (List.ofFn y).head? = some false →
      DBonacciAdmissible k (m + n) (Fin.append x y))
  have avoid : ∀ {q : ℕ} (w : Fin q → Bool),
      DBonacciAdmissible k q w ↔ ∀ s : ℕ, ¬ TrueBlock w s k := by
    intro q w
    by_cases hlong : k ≤ q
    · exact (closed_word_run_start_equivalence q k (by omega) hlong w).1
    · have hshort : q < k := by omega
      have hlegal : DBonacciAdmissible k q w := by
        obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        exact runAdmissible_eq_true_of_length_le a a q w (by omega) le_rfl
      exact ⟨fun _ s hb => by have := hb.1; omega, fun _ => hlegal⟩
  have initial_le : ∀ {q : ℕ} (w : Fin q → Bool), initialRun w ≤ q := by
    intro q w
    simpa [initialRun] using (List.findIdx_le_length (xs := List.ofFn w) (p := Bool.not))
  have hprefix : ∀ {q : ℕ} (w : Fin q → Bool) (t : ℕ), t ≤ q →
      ((∀ i : Fin q, i.val < t → w i = true) ↔ t ≤ initialRun w) := by
    intro q w t ht
    constructor
    · intro hall
      by_contra h
      have hj : initialRun w < t := by omega
      have hlen : initialRun w < (List.ofFn w).length := by simp; omega
      have hfalse := @List.findIdx_getElem Bool Bool.not (List.ofFn w) hlen
      have htrue := hall ⟨initialRun w, by omega⟩ hj
      have hf : Bool.not (w ⟨initialRun w, by omega⟩) = true := by
        calc
          _ = Bool.not ((List.ofFn w)[initialRun w]'hlen) :=
            congrArg Bool.not (List.getElem_ofFn hlen).symm
          _ = true := hfalse
      simp [htrue] at hf
    · intro h i hi
      have hbit := @List.not_of_lt_findIdx Bool Bool.not (List.ofFn w) i.val (by
        change i.val < initialRun w
        omega)
      simpa [List.getElem_ofFn] using hbit
  have hsuffix : ∀ {q : ℕ} (w : Fin q → Bool) (t : ℕ), t ≤ q →
      ((∀ i : Fin q, q - t ≤ i.val → w i = true) ↔ t ≤ terminalRun w) := by
    intro q w t ht
    dsimp only [terminalRun]
    rw [← hprefix (fun i => w i.rev) t ht]
    constructor
    · intro h i hi
      apply h i.rev
      simp only [Fin.val_rev]
      omega
    · intro h i hi
      have hre : i.rev.val < t := by simp only [Fin.val_rev]; omega
      simpa using h i.rev hre
  have terminal_le : ∀ {q : ℕ} (w : Fin q → Bool), terminalRun w ≤ q := by
    intro q w
    exact initial_le (fun i => w i.rev)
  have endpoints : ∀ {q : ℕ} (w : Fin q → Bool), DBonacciAdmissible k q w →
      initialRun w < k ∧ terminalRun w < k := by
    intro q w hw
    have hno := (avoid w).mp hw
    constructor
    · by_contra h
      have hkq : k ≤ q := by have := initial_le w; omega
      have hall := (hprefix w k hkq).mpr (by omega)
      exact hno 0 ⟨by omega, fun i _ hi => hall i (by omega)⟩
    · by_contra h
      have hkq : k ≤ q := by have := terminal_le w; omega
      have hall := (hsuffix w k hkq).mpr (by omega)
      exact hno (q - k) ⟨by omega, fun i hi _ => hall i hi⟩
  have boundary : ∀ (x : Fin m → Bool) (y : Fin n → Bool),
      DBonacciAdmissible k m x → DBonacciAdmissible k n y →
      terminalRun x < k ∧ initialRun y < k ∧
        (DBonacciAdmissible k (m + n) (Fin.append x y) ↔
          terminalRun x + initialRun y < k) := by
    intro x y hx hy
    have hxt := (endpoints x hx).2
    have hyp := (endpoints y hy).1
    have ht := terminal_le x
    have hp := initial_le y
    have xs := (hsuffix x (terminalRun x) ht).mpr le_rfl
    have yp := (hprefix y (initialRun y) hp).mpr le_rfl
    refine ⟨hxt, hyp, ?_⟩
    constructor
    · intro hj
      by_contra hs
      have hs' : k ≤ terminalRun x + initialRun y := by omega
      apply (avoid (Fin.append x y)).mp hj (m - terminalRun x)
      refine ⟨by omega, ?_⟩
      intro i hlo hhi
      by_cases him : i.val < m
      · let j : Fin m := ⟨i.val, him⟩
        have heq : j.castAdd n = i := Fin.ext rfl
        rw [← heq, Fin.append_left]
        exact xs j hlo
      · let j : Fin n := ⟨i.val - m, by omega⟩
        have heq : Fin.natAdd m j = i := by apply Fin.ext; simp [j]; omega
        rw [← heq, Fin.append_right]
        exact yp j (by simp [j]; omega)
    · intro hs
      apply (avoid (Fin.append x y)).mpr
      intro s hb
      by_cases hleft : s + k ≤ m
      · apply (avoid x).mp hx s
        refine ⟨hleft, ?_⟩
        intro i hlo hhi
        have h := hb.2 (i.castAdd n) (by simpa using hlo) (by simpa using hhi)
        simpa using h
      · by_cases hright : m ≤ s
        · apply (avoid y).mp hy (s - m)
          refine ⟨by have := hb.1; omega, ?_⟩
          intro i hlo hhi
          have h := hb.2 (Fin.natAdd m i) (by simp; omega) (by simp; omega)
          simpa using h
        · have hcross : s < m ∧ m < s + k := by omega
          have hxpart : m - s ≤ terminalRun x := by
            apply (hsuffix x (m - s) (by omega)).mp
            intro i hi
            have h := hb.2 (i.castAdd n) (by simp; omega) (by simp; omega)
            simpa using h
          have hypart : s + k - m ≤ initialRun y := by
            apply (hprefix y (s + k - m) (by have := hb.1; omega)).mp
            intro i hi
            have h := hb.2 (Fin.natAdd m i) (by simp; omega) (by simp; omega)
            simpa using h
          omega
  refine ⟨boundary, ?_, ?_, ?_⟩
  · intro s t hst y hy
    simp only [oneNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨hy.1, hy.2.1, by omega⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    simp only [oneNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hone : 1 ≤ initialRun y := by
      cases n with
      | zero => simp at hy
      | succ q =>
        have hh : y 0 = true := by simpa [List.ofFn_succ] using hy.2.1
        simp [initialRun, List.ofFn_succ, hh, List.findIdx_cons]
    omega
  · intro x y hx hy hh
    have hzero : initialRun y = 0 := by
      cases n with
      | zero => simp at hh
      | succ q =>
        have hh' : y 0 = false := by simpa [List.ofFn_succ] using hh
        simp [initialRun, List.ofFn_succ, hh', List.findIdx_cons]
    exact (boundary x y hx hy).2.2.mpr (by rw [hzero]; simpa using (endpoints x hx).2)

#print axioms actual_direct_concatenation

end D5.S1.Words.AdmissibleWords.KBonacciDirectConcatenation

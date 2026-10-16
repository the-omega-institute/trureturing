/- GID: D5/S0/Computability/BinaryMachine/BoundedVerifier
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/BoundedVerifier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.FinCases]
   utility: none
   digest: A concrete polynomial verifier rejects malformed pairs and oversized original target witnesses. -/

import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import D5.S0.Computability.BinaryMachine.WitnessBudget
import D5.S0.Computability.BinaryMachine.DecisionSimulation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.BoundedVerifier
open StackMachine (Registers)
open StackProgram

private def rejectLike {k : Nat} {L : Type} (p : Program k L) : Program k L :=
  ⟨p.start, fun _ => .halt false⟩
private theorem exec_reject {k : Nat} {L : Type} (p : Program k L) (r : Registers k) :
    Exec (rejectLike p) (rejectLike p).start r 1 (false, r) := .halt rfl

def cleanup (M : Machine) := seq (StackWords.clear (k := 6) 2)
  (seq (StackWords.clear (k := 6) 3) (DecisionSimulation.program M))
def cleanupEncoding (M : Machine) := Encoding.bool.sum (Encoding.bool.sum (DecisionSimulation.encoding M))
def resume (M : Machine) := seq (StackControl.moveWord (k := 8) 8 0 7)
  (StackFrame.lift StackFrame.includeRegister (cleanup M))
def continueEncoding (M : Machine) := StackControl.moveEncoding.sum (cleanupEncoding M)
def afterDecode (M : Machine) (c e : Nat) :=
  StackControl.choose (StackFrame.lift StackFrame.includeRegister (WitnessBudget.test c e))
    (resume M) (rejectLike (resume M))
def afterEncoding (M : Machine) (c e : Nat) :=
  StackControl.chooseEncoding (WitnessBudget.encoding c e) (continueEncoding M)
def program (M : Machine) (c e : Nat) := seq (StackWords.copy (k := 8) 0 8 7)
  (StackControl.choose (StackFrame.lift StackFrame.includeRegister StackPair.unpack)
    (afterDecode M c e) (rejectLike (afterDecode M c e)))
def encoding (M : Machine) (c e : Nat) := StackWords.copyMapEncoding.sum
  (StackControl.chooseEncoding StackPair.unpackEncoding (afterEncoding M c e))

/-- Full all-word verifier semantics: both the original pair bytes and the target
witness-length condition must hold before the original decision is consulted. -/
def Good (M : Machine) (c e : Nat) (word : Word) : Prop :=
  ∃ x w, StackPair.decodePair word = some (x, w) ∧
    w.length ≤ powerBound c e x.length ∧ Accepts M word

private theorem exec_continue (M : Machine) (fuel : Nat) (word : Word)
    (decision : Bool) (out : Tape) (h : runInput M fuel word = some (decision, out))
    (r : Registers 6) :
    ∃ t result, t ≤ (r 0).length + (r 2).length + (r 3).length +
        10 * word.length + 6 * fuel + 16 ∧
      Exec (resume M) (resume M).start (StackFrame.extend r [] word) t (decision, result) := by
  let R := StackFrame.extend r [] word
  let s₀ := StackMachine.set r 0 word
  let s₁ := StackMachine.set s₀ 2 []
  let s₂ := StackMachine.set s₁ 3 []
  have hm := StackControl.exec_moveWord (k := 8) 8 0 7 (by decide) (by decide) (by decide) R (by rfl)
  have heq : StackMachine.set (StackMachine.set R 8 []) 0 (R 8) = StackFrame.extend s₀ [] [] := by
    funext a
    fin_cases a <;> rfl
  rw [heq] at hm
  have hc₂ := StackWords.exec_clear (k := 6) 2 s₀
  have hc₃ := StackWords.exec_clear (k := 6) 3 s₁
  obtain ⟨v, result, hv, he⟩ := DecisionSimulation.exec_program M fuel word decision out h s₂
    (by simp [s₂, s₁, s₀]) (by simp [s₂, s₁]) (by simp [s₂])
  have hs := exec_seq _ _ hc₂ (exec_seq _ _ hc₃ he)
  have hs' := StackFrame.exec_extend (cleanup M) hs [] []
  have hh := exec_seq _ _ hm hs'
  refine ⟨_, StackFrame.extend result [] [], ?_, hh⟩
  simp [R, StackFrame.extend, s₀, s₁]
  omega

private def bound (a b c e d l n : Nat) : Nat :=
  100 * (n + 1 + powerBound a b (n + 1) + powerBound c e n + powerBound d l n)

private theorem polynomialBound_bound (a b c e d l : Nat) : PolynomialBound (bound a b c e d l) := by
  exact (PolynomialBound.constant 100).mul
    (((((PolynomialBound.identity.add (PolynomialBound.constant 1)).add
      ((PolynomialBound.power a b).comp (PolynomialBound.identity.add (PolynomialBound.constant 1)))).add
      (PolynomialBound.power c e)).add (PolynomialBound.power d l)))

private theorem run_decision_iff (M : Machine) (word : Word) (t : Nat) (b : Bool) (out : Tape)
    (h : runInput M t word = some (b, out)) : b = true ↔ Accepts M word := by
  constructor
  · intro hb; subst b; exact ⟨t, out, h⟩
  · rintro ⟨s, tape, hs⟩
    have heq := run_deterministic M (initial M word) h hs
    exact congrArg Prod.fst heq

private theorem implementation (M : Machine) (hM : PolynomialTimeMachine M) (c e : Nat) :
    ∃ a b d l, ∀ word, ∃ t decision result,
      t ≤ bound a b c e d l word.length ∧
      Exec (program M c e) (program M c e).start
        (StackFrame.extend (StackPair.initial word) [] []) t (decision, result) ∧
      (decision = true ↔ Good M c e word) := by
  obtain ⟨a, b, htime⟩ := StackPower.polynomialBound_time c e
  obtain ⟨d, l, hM⟩ := hM
  refine ⟨a, b, d, l, ?_⟩
  intro word
  let R := StackFrame.extend (StackPair.initial word) [] []
  have hcopy := StackWords.exec_copy (k := 8) 0 8 7 (by decide) (by decide) (by decide) R (by rfl)
  have hcopyOut : StackMachine.set R 8 (R 0) = StackFrame.extend (StackPair.initial word) [] word := by
    funext j; fin_cases j <;> rfl
  rw [hcopyOut] at hcopy
  have hcopy' : Exec (StackWords.copy (k := 8) 0 8 7) (StackWords.copy (k := 8) 0 8 7).start R
      (5 * word.length + 6) (true, StackFrame.extend (StackPair.initial word) [] word) := by
    simpa [R, StackFrame.extend, StackPair.initial, StackPair.input,
      StackWords.copy, StackWords.copyMap, StackWords.clear, seq] using hcopy
  obtain ⟨u, unpacked, hu, hU, hshape⟩ := StackPair.unpack_runs word
  cases hp : StackPair.decodePair word with
  | none =>
    have hU' : Exec (StackFrame.lift StackFrame.includeRegister StackPair.unpack)
        (StackFrame.lift StackFrame.includeRegister StackPair.unpack).start
        (StackFrame.extend (StackPair.initial word) [] word) u (false, StackFrame.extend unpacked [] word) := by
      simpa [hp, StackFrame.lift] using StackFrame.exec_extend StackPair.unpack hU [] word
    have hno := exec_reject (afterDecode M c e) (StackFrame.extend unpacked [] word)
    have hh := exec_seq _ _ hcopy' (StackControl.exec_choose _ (afterDecode M c e) (rejectLike (afterDecode M c e)) hU' hno)
    refine ⟨_, false, StackFrame.extend unpacked [] word, ?_, hh, ?_⟩
    · unfold bound; omega
    · simp [Good, hp]
  | some pair =>
    obtain ⟨x, w⟩ := pair
    have hword := (StackPair.decodePair_eq_some_iff word x w).mp hp
    have hshape' := hshape x w hp
    subst unpacked
    have hU' : Exec (StackFrame.lift StackFrame.includeRegister StackPair.unpack)
        (StackFrame.lift StackFrame.includeRegister StackPair.unpack).start
        (StackFrame.extend (StackPair.initial word) [] word) u
        (true, StackFrame.extend (StackPair.unpacked x w) [] word) := by
      simpa [hp, StackFrame.lift] using StackFrame.exec_extend StackPair.unpack hU [] word
    have hlen : 2 * x.length + 1 + w.length = word.length := by simp [hword, pairWords]; omega
    have hT := Nat.le_trans (htime (x.length + 1))
      (powerBound_mono a b (by omega : x.length + 1 ≤ word.length + 1))
    have hP := powerBound_mono c e (by omega : x.length ≤ word.length)
    have hGood : Good M c e word ↔ w.length ≤ powerBound c e x.length ∧ Accepts M word := by
      simp [Good, hp]
    obtain ⟨v, q, hv, hV, hq₀, hq₂, hq₄, hq₅, hq₆, hq₃⟩ := WitnessBudget.exec_test c e x w
    by_cases hfits : w.length ≤ powerBound c e x.length
    · have hV' : Exec (StackFrame.lift StackFrame.includeRegister (WitnessBudget.test c e))
          (StackFrame.lift StackFrame.includeRegister (WitnessBudget.test c e)).start
          (StackFrame.extend (StackPair.unpacked x w) [] word) v (true, StackFrame.extend q [] word) := by
        simpa [hfits, StackFrame.lift] using StackFrame.exec_extend (WitnessBudget.test c e) hV [] word
      obtain ⟨s, decision, out, hs, hrun⟩ := hM word
      obtain ⟨z, result, hz, hZ⟩ := exec_continue M s word decision out hrun q
      have hAfter := StackControl.exec_choose _ (resume M) (rejectLike (resume M)) hV' hZ
      have hh := exec_seq _ _ hcopy' (StackControl.exec_choose _ (afterDecode M c e) (rejectLike (afterDecode M c e)) hU' hAfter)
      refine ⟨_, decision, result, ?_, hh, ?_⟩
      · rw [hq₀, hq₂] at hz
        simp only [List.length_replicate] at hz
        unfold bound; omega
      · rw [hGood]
        simpa [hfits] using run_decision_iff M word s decision out hrun
    · have hV' : Exec (StackFrame.lift StackFrame.includeRegister (WitnessBudget.test c e))
          (StackFrame.lift StackFrame.includeRegister (WitnessBudget.test c e)).start
          (StackFrame.extend (StackPair.unpacked x w) [] word) v (false, StackFrame.extend q [] word) := by
        simpa [hfits, StackFrame.lift] using StackFrame.exec_extend (WitnessBudget.test c e) hV [] word
      have hAfter := StackControl.exec_choose _ (resume M) (rejectLike (resume M)) hV' (exec_reject (resume M) (StackFrame.extend q [] word))
      have hh := exec_seq _ _ hcopy' (StackControl.exec_choose _ (afterDecode M c e) (rejectLike (afterDecode M c e)) hU' hAfter)
      refine ⟨_, false, StackFrame.extend q [] word, ?_, hh, ?_⟩
      · unfold bound; omega
      · simp [hGood, hfits]

/-- A total polynomial machine can be normalized to the exact bounded verifier
language without changing any input bytes passed to its original execution. -/
theorem normalize (M : Machine) (hM : PolynomialTimeMachine M) (c e : Nat) :
    ∃ N : Machine, PolynomialTimeMachine N ∧ ∀ word, Accepts N word ↔ Good M c e word := by
  obtain ⟨a,b,d,l,hruns⟩ := implementation M hM c e
  let S := compile (program M c e) (encoding M c e)
  have hinitial (word : Word) :
      (fun j : Fin 9 => if j = 0 then word else []) = StackFrame.extend (StackPair.initial word) [] [] := by
    funext j; fin_cases j <;> rfl
  have hstack : ∀ word, ∃ t decision result, t ≤ bound a b c e d l word.length ∧
      StackMachine.runInput S t word = some (decision,result) ∧
      (decision = true ↔ Good M c e word) := by
    intro word
    obtain ⟨t,decision,result,ht,he,hgood⟩ := hruns word
    refine ⟨t,decision,result,ht,?_,hgood⟩
    have he' : Exec (program M c e) (program M c e).start
        (fun j : Fin 9 => if j = 0 then word else []) t (decision,result) := by
      rw [hinitial word]
      exact he
    exact compile_exec (encoding M c e) he'
  have ht := StackCompile.polynomialTimeMachine_of_stack S (bound a b c e d l)
    (polynomialBound_bound a b c e d l)
    (fun word => by obtain ⟨t,b,r,ht,he,_⟩ := hstack word; exact ⟨t,b,r,ht,he⟩)
  refine ⟨StackCompile.compile S,ht,?_⟩
  intro word
  obtain ⟨t,b,r,ht,he,hgood⟩ := hstack word
  have ha := StackCompile.accepts_iff S word ⟨t,b,r,he⟩
  constructor
  · intro hx
    obtain ⟨s,out,hs⟩ := ha.mp hx
    have heq := StackMachine.run_deterministic S (StackMachine.initial S word) hs he
    exact hgood.mp (congrArg Prod.fst heq).symm
  · intro hx
    have hb := hgood.mpr hx
    subst b
    exact ha.mpr ⟨t,r,he⟩

end Complexity.BoundedVerifier

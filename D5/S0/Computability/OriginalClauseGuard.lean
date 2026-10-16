/- GID: D5/S0/Computability/OriginalClauseGuard
   generality: G
   mirror-B: D5/B/S0/Computability/OriginalClauseGuard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S0/Computability/OriginalClauseClassification.lemma63; instance=D5/S0/Computability/OriginalClauseLanguages.trueWord
   digest: A finite single-tape implementation of the original unrestricted lexical guard. -/

import D5.S0.Computability.OriginalClauseLanguages
import D5.S0.Computability.BinaryMachine.StackControl
import D5.S0.Computability.BinaryMachine.StackCompile
import D5.S0.Computability.BinaryMachine.StackPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.OriginalGuard
open Complexity Complexity.StackProgram
open Complexity.StackMachine (Registers)
open Conventional (ParsePhase)

def phaseEncoding : Encoding ParsePhase where
  states := 10
  encode := fun q => match q with
    | .bodyFirst => 0 | .bodySecond => 1 | .clauseFirst => 2 | .clauseSecond => 3
    | .polarity => 4 | .firstTag => 5 | .firstBit => 6 | .nameTag => 7
    | .nameBit => 8 | .ending => 9 | .dead => 10
  decode := fun q => match q.val with
    | 0 => .bodyFirst | 1 => .bodySecond | 2 => .clauseFirst | 3 => .clauseSecond
    | 4 => .polarity | 5 => .firstTag | 6 => .firstBit | 7 => .nameTag
    | 8 => .nameBit | 9 => .ending | _ => .dead
  decode_encode := by intro q; cases q <;> rfl

def scan : Program 6 (Sum ParsePhase Bool) where
  start := .inl .bodyFirst
  code := fun q => match q with
    | .inl q => .pop 0 (.inr (decide (q = .ending)))
        (.inl (Unrestricted.nextPhase q false)) (.inl (Unrestricted.nextPhase q true))
    | .inr b => .halt b

def scanEncoding := phaseEncoding.sum Encoding.bool

def valid (w : Word) : Bool := decide (Unrestricted.scanPhase .bodyFirst w = .ending)
def repair (fallback w : Word) : Word := if valid w then w else fallback

/-- The scanner consumes exactly one instruction per input bit, then performs
one empty pop and a halt. No width or name-magnitude counter is present. -/
theorem exec_scan (p : ParsePhase) (w : Word) (r : Registers 6) (h : r 0 = w) :
    Exec scan (.inl p) r (w.length+2)
      (decide (Unrestricted.scanPhase p w = .ending), StackMachine.set r 0 []) := by
  induction w generalizing p r with
  | nil =>
    apply Exec.next (q' := .inr (decide (p = .ending)))
      (r' := StackMachine.set r 0 [])
    · simp [StackProgram.step,scan,h,StackMachine.branch]
    · exact
      (.halt (by simp [StackProgram.step,scan,Unrestricted.scanPhase]))
  | cons b w ih =>
    let r' := StackMachine.set r 0 w
    have hr : r' 0 = w := by simp [r']
    have hh := ih (Unrestricted.nextPhase p b) r' hr
    have he : StackMachine.set r' 0 [] = StackMachine.set r 0 [] := by
      funext a; by_cases ha : a = 0 <;> simp [r',StackMachine.set,ha]
    rw [he] at hh
    have hs : StackProgram.step scan (.inl p) r =
        .inr (.inl (Unrestricted.nextPhase p b),r') := by
      cases b <;> simp [StackProgram.step,scan,h,StackMachine.branch,r']
    simpa [Unrestricted.scanPhase,Nat.add_assoc] using Exec.next hs hh

def good := StackControl.moveWord (k := 6) 1 0 2

def program (fallback : Word) := seq (StackWords.copy (k := 6) 0 1 2)
  (StackControl.choose scan
    (StackControl.widenLeft (B := StackControl.WriteLabel fallback) good)
    (StackControl.widenRight (StackControl.write (k := 6) 0 fallback)))

def encoding (fallback : Word) := StackWords.copyMapEncoding.sum
  (StackControl.chooseEncoding scanEncoding
    (StackControl.moveEncoding.sum (StackControl.writeEncoding fallback)))

/-- The finite stack program returns the unchanged word on lexical success and
installs literal fallback bytes on failure; compilation uses the same tape model. -/
theorem polyTime_repair (fallback : Word) : PolyTime (repair fallback) := by
  let bound := fun n => 10*n+2*fallback.length+20
  have hb : PolynomialBound bound :=
    (((PolynomialBound.constant 10).mul PolynomialBound.identity).add
      (PolynomialBound.constant (2*fallback.length))).add (PolynomialBound.constant 20)
  apply StackCompile.polyTime_of_stack (compile (program fallback) (encoding fallback)) bound hb
  intro word
  let r := StackPair.initial word
  let r₁ := StackMachine.set r 1 word
  let r₂ := StackMachine.set r₁ 0 []
  have hcopy := StackWords.exec_copy (k := 6) 0 1 2 (by decide) (by decide) (by decide) r (by rfl)
  have hcopy' : Exec (StackWords.copy (k := 6) 0 1 2) (StackWords.copy (k := 6) 0 1 2).start r
      (5*word.length+6) (true,r₁) := by
    simpa [r,r₁,StackPair.initial,StackPair.input,StackWords.copy,StackWords.copyMap,
      StackWords.clear,seq] using hcopy
  have hscan := exec_scan .bodyFirst word r₁
    (by simp [r₁,r,StackPair.initial,StackPair.input])
  change Exec scan scan.start r₁ (word.length+2) (valid word,r₂) at hscan
  cases hvalid : valid word with
  | false =>
    have hscan' : Exec scan scan.start r₁ (word.length+2)
        (false,r₂) := by simpa only [hvalid] using hscan
    have hw := StackControl.exec_write (k := 6) 0 fallback r₂
    have he := exec_seq _ _ hcopy' (StackControl.exec_choose _
      (StackControl.widenLeft (B := StackControl.WriteLabel fallback) good)
      (StackControl.widenRight (StackControl.write (k := 6) 0 fallback)) hscan'
      (StackControl.exec_widenRight _ hw))
    refine ⟨_,_,?_,compile_exec (encoding fallback) he,?_⟩
    · unfold bound; omega
    · simp [repair,hvalid,r₂,StackMachine.set,StackProgram.compile]
  | true =>
    have hscan' : Exec scan scan.start r₁ (word.length+2)
        (true,r₂) := by simpa only [hvalid] using hscan
    have hg := StackControl.exec_moveWord (k := 6) 1 0 2 (by decide) (by decide) (by decide) r₂
      (by simp [r₂,r₁,r,StackPair.initial,StackPair.input])
    have he := exec_seq _ _ hcopy' (StackControl.exec_choose _
      (StackControl.widenLeft (B := StackControl.WriteLabel fallback) good)
      (StackControl.widenRight (StackControl.write (k := 6) 0 fallback)) hscan'
      (StackControl.exec_widenLeft good hg))
    refine ⟨_,_,?_,compile_exec (encoding fallback) he,?_⟩
    · simp [r₂,r₁,StackMachine.set]; unfold bound; omega
    · simp [repair,hvalid,r₂,r₁,StackMachine.set,StackProgram.compile]

end PredictiveThermodynamic.OriginalGuard

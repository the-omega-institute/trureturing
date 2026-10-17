/- GID: D5/S0/Computability/BinaryMachine/PairProjection
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/PairProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Total polynomial projections use exact unary-prefix pairs and fixed malformed fallbacks. -/

import D5.S0.Computability.BinaryMachine.PairPreimage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.PairProjection
open StackProgram

def project (right : Bool) (fallback word : Word) : Word :=
  match StackPair.decodePair word with
  | none => fallback
  | some (x,y) => if right then y else x

def selected (right : Bool) := if right then
  StackControl.widenLeft (B := Unit) (StackControl.moveWord (k := 6) 1 0 2)
  else StackControl.widenRight (stop 6 true)
def selectedEncoding := StackControl.moveEncoding.sum Encoding.unit

def failure (fallback : Word) := seq (StackWords.clear (k := 6) 0)
  (StackControl.write (k := 6) 0 fallback)

def program (right : Bool) (fallback : Word) := StackControl.choose StackPair.unpack
  (StackControl.widenLeft (B := Sum Bool (StackControl.WriteLabel fallback)) (selected right))
  (StackControl.widenRight (failure fallback))
def encoding (fallback : Word) := StackControl.chooseEncoding StackPair.unpackEncoding
  (selectedEncoding.sum (Encoding.bool.sum (StackControl.writeEncoding fallback)))

/-- Both projections are total on raw words. Malformed lengths, missing unary
terminators and short payloads are detected by the actual supplied decoder. -/
theorem polyTime_project (right : Bool) (fallback : Word) : PolyTime (project right fallback) := by
  let bound := fun n => 20*n+2*fallback.length+40
  have hb : PolynomialBound bound :=
    (((PolynomialBound.constant 20).mul PolynomialBound.identity).add
      (PolynomialBound.constant (2*fallback.length))).add (PolynomialBound.constant 40)
  apply StackCompile.polyTime_of_stack (compile (program right fallback) (encoding fallback)) bound hb
  intro word
  obtain ⟨u,r,hu,hU,hshape⟩ := StackPair.unpack_runs word
  cases hp : StackPair.decodePair word with
  | none =>
    have hU' : Exec StackPair.unpack StackPair.unpack.start (StackPair.initial word) u (false,r) := by
      simpa [hp] using hU
    have hclear := StackWords.exec_clear (k := 6) 0 r
    have hw := StackControl.exec_write (k := 6) 0 fallback (StackMachine.set r 0 [])
    have hf := exec_seq _ _ hclear hw
    have he := StackControl.exec_choose _
      (StackControl.widenLeft (B := Sum Bool (StackControl.WriteLabel fallback)) (selected right))
      (StackControl.widenRight (failure fallback)) hU' (StackControl.exec_widenRight _ hf)
    have hlen := StackMachine.runInput_length_le
      (compile StackPair.unpack StackPair.unpackEncoding) u word (false,r)
      (compile_exec StackPair.unpackEncoding hU') 0
    dsimp only at hlen
    refine ⟨_,_,?_,compile_exec (encoding fallback) he,?_⟩
    · unfold bound; omega
    · simp [project,hp,StackMachine.set]
  | some pair =>
    obtain ⟨x,y⟩ := pair
    have hw := (StackPair.decodePair_eq_some_iff word x y).mp hp
    have hshape' := hshape x y hp
    subst r
    have hU' : Exec StackPair.unpack StackPair.unpack.start (StackPair.initial word) u
        (true,StackPair.unpacked x y) := by simpa [hp] using hU
    have hlen : 2*x.length+1+y.length=word.length := by simp [hw,pairWords]; omega
    cases right with
    | false =>
      have hs : Exec (selected false) (selected false).start (StackPair.unpacked x y) 1
          (true,StackPair.unpacked x y) := StackControl.exec_widenRight _ (exec_stop 6 true _)
      have he := StackControl.exec_choose _
        (StackControl.widenLeft (B := Sum Bool (StackControl.WriteLabel fallback)) (selected false))
        (StackControl.widenRight (failure fallback)) hU' (StackControl.exec_widenLeft _ hs)
      refine ⟨_,_,?_,compile_exec (encoding fallback) he,?_⟩
      · unfold bound; omega
      · simp [project,hp,StackPair.unpacked,StackPair.input]
    | true =>
      have hm := StackControl.exec_moveWord (k := 6) 1 0 2 (by decide) (by decide) (by decide)
        (StackPair.unpacked x y) (by simp [StackPair.unpacked,StackPair.input,StackPair.certificate])
      have hs := StackControl.exec_widenLeft (B := Unit) _ hm
      have he := StackControl.exec_choose _
        (StackControl.widenLeft (B := Sum Bool (StackControl.WriteLabel fallback)) (selected true))
        (StackControl.widenRight (failure fallback)) hU' (StackControl.exec_widenLeft _ hs)
      refine ⟨_,_,?_,compile_exec (encoding fallback) he,?_⟩
      · simp [StackPair.unpacked,StackPair.input,StackPair.certificate]
        unfold bound; omega
      · simp [project,hp,StackMachine.set,StackProgram.compile,
          StackPair.unpacked,StackPair.input,StackPair.certificate]

end Complexity.PairProjection

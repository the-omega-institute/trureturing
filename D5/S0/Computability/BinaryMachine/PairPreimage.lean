/- GID: D5/S0/Computability/BinaryMachine/PairPreimage
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/PairPreimage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial paired preprocessing preserves the witness and rejects malformed outer words. -/

import D5.S0.Computability.BinaryMachine.TransducerPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.PairPreimage
open StackProgram

def map (f : Word → Word) (word : Word) : Word :=
  match StackPair.decodePair word with
  | none => []
  | some (x,w) => pairWords (f x) w

def success (M : Machine) := seq (TransducerPair.normalized M) PairConstructor.build

def program (M : Machine) := StackControl.choose StackPair.unpack
  (StackControl.widenLeft (B := Bool) (success M))
  (StackControl.widenRight (StackWords.clear (k := 6) 0))

def encoding (M : Machine) := StackControl.chooseEncoding StackPair.unpackEncoding
  (((TapeToStacks.normalEncoding M).sum PairConstructor.buildEncoding).sum Encoding.bool)

/-- Every outer word is processed by an actual total polynomial transducer.
The entire certificate is retained when the instance component is transformed. -/
theorem polyTime_map {f : Word → Word} (hf : PolyTime f) : PolyTime (map f) := by
  obtain ⟨M,c,k,hM⟩ := hf
  let bound := fun n => 100 * (n + powerBound c k n + 1)
  have hb : PolynomialBound bound := (PolynomialBound.constant 100).mul
    ((PolynomialBound.identity.add (PolynomialBound.power c k)).add (PolynomialBound.constant 1))
  apply StackCompile.polyTime_of_stack (compile (program M) (encoding M)) bound hb
  intro word
  obtain ⟨u,r,hu,hU,hshape⟩ := StackPair.unpack_runs word
  cases hp : StackPair.decodePair word with
  | none =>
    have hU' : Exec StackPair.unpack StackPair.unpack.start (StackPair.initial word) u (false,r) := by
      simpa [hp] using hU
    have hclear := StackWords.exec_clear (k := 6) 0 r
    have he := StackControl.exec_choose StackPair.unpack
      (StackControl.widenLeft (B := Bool) (success M))
      (StackControl.widenRight (StackWords.clear (k := 6) 0)) hU'
      (StackControl.exec_widenRight (StackWords.clear (k := 6) 0) hclear)
    have hlen := StackMachine.runInput_length_le
      (compile StackPair.unpack StackPair.unpackEncoding) u word (false,r)
      (compile_exec StackPair.unpackEncoding hU') 0
    dsimp only at hlen
    refine ⟨_,StackMachine.set r 0 [],?_,compile_exec (encoding M) he,?_⟩
    · unfold bound; omega
    · simp [map,hp]
  | some pair =>
    obtain ⟨x,w⟩ := pair
    have hw := (StackPair.decodePair_eq_some_iff word x w).mp hp
    have hshape' := hshape x w hp
    subst r
    have hU' : Exec StackPair.unpack StackPair.unpack.start (StackPair.initial word) u
        (true,StackPair.unpacked x w) := by simpa [hp] using hU
    obtain ⟨v,out,hv,hV,hout⟩ := hM x
    obtain ⟨s,hs,hS⟩ := TransducerPair.exec_normalized M v x out hV (StackPair.unpacked x w)
      (by simp [StackPair.unpacked,StackPair.input])
      (by simp [StackPair.unpacked,StackPair.input,StackPair.certificate])
      (by simp [StackPair.unpacked,StackPair.input,StackPair.certificate])
    let q := StackMachine.set (StackPair.unpacked x w) 0 out.output
    have hB := PairConstructor.exec_build q
      (by simp [q,StackPair.unpacked,StackPair.input,StackPair.certificate])
      (by simp [q,StackPair.unpacked,StackPair.input,StackPair.certificate])
    have hyes := exec_seq _ _ hS hB
    have he := StackControl.exec_choose StackPair.unpack
      (StackControl.widenLeft (B := Bool) (success M))
      (StackControl.widenRight (StackWords.clear (k := 6) 0)) hU'
      (StackControl.exec_widenLeft (success M) hyes)
    have hlen := runInput_output_length_le M v x (true,out) hV
    change out.output.length ≤ x.length + 2*v at hlen
    have hpairlen : 2*x.length+1+w.length=word.length := by simp [hw,pairWords]; omega
    have hpoly := powerBound_mono c k (by omega : x.length ≤ word.length)
    refine ⟨_,_,?_,compile_exec (encoding M) he,?_⟩
    · simp [q,StackPair.unpacked,StackPair.input,StackPair.certificate]
      unfold bound; omega
    · simp [q,map,hp,hout,StackPair.unpacked,StackPair.input,StackPair.certificate,
        StackMachine.set,StackProgram.compile]

end Complexity.PairPreimage

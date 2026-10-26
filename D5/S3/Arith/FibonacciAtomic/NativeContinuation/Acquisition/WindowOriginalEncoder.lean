/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalEncoder
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalEncoder
   mirror-E: none(waiver:unbounded-original-encoder-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: The original padded Zeckendorf encoder supplies the physical acquisition input. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.WindowAcquisitionPacked
import D5.S1.Digit.GoldenBase4DenseInput
import D5.S1.Digit.GoldenZeckendorfLanguage

namespace PhysicalWindowContinuation.OriginalEncoder
open D5.S0.Conventions
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit.GoldenBase4DenseInput
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.ZeckendorfFutureKernel (legal)

/-- A bit is selected by the independently defined canonical Fibonacci indices. -/
def bit (N i : ℕ) : Bool := decide (i+2 ∈ wdigits N)

/-- The canonical number of three-bit windows; the independent unit is excluded. -/
def L (N : ℕ) : ℕ := (zeckendorfWordLength N+1)/3

/-- Original high-to-low five-mode windows, independently of machine execution. -/
def W : ℕ → ℕ → List LiteralWindowEnd.Window
  | 0, _ => []
  | h+1, N => LiteralWindowEnd.triple (bit N (3*h+1))
      (bit N (3*h+2)) (bit N (3*h+3)) :: W h N

/-- Only a finite renaming relates the original letters to the local alphabet. -/
def localLetter : LiteralWindowEnd.Window → Window
  | .zero => .zero | .low => .low | .middle => .middle | .ends => .both | .high => .high

def localWord (h N : ℕ) : List Window := (W h N).map localLetter

def display (N k : ℕ) : List Bool := (List.range k).reverse.map (bit N)

theorem display_succ (N k : ℕ) : display N (k+1)=bit N k :: display N k := by
  simp [display,List.range_succ]

theorem original_bits (h N : ℕ) :
    NativeContinuation.NullReplyFiber.highBits (W h N) ++ [bit N 0] = display N (3*h+1) := by
  have triple (a b c : Bool) (hab : ¬(a=true ∧ b=true)) (hbc : ¬(b=true ∧ c=true)) :
      (LiteralWindowEnd.bits (LiteralWindowEnd.triple a b c)).reverse = [c,b,a] := by
    cases a <;> cases b <;> cases c <;> simp_all [LiteralWindowEnd.triple,LiteralWindowEnd.bits]
  have separated (i : ℕ) : ¬ (bit N i=true ∧ bit N (i+1)=true) := by
    simpa [bit,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      D5.S1.Digit.GoldenZeckendorfLanguage.canonical_indices_not_adjacent
        (wdigits N) (wdigits_isCanonical N) (i+2)
  induction h with
  | zero => simp [W,NativeContinuation.NullReplyFiber.highBits,display]
  | succ h ih =>
    rw [W]
    change ((LiteralWindowEnd.bits (LiteralWindowEnd.triple _ _ _)).reverse ++
      NativeContinuation.NullReplyFiber.highBits (W h N)) ++ [bit N 0] = _
    rw [List.append_assoc]
    rw [triple _ _ _ (by simpa [Nat.add_assoc] using separated (3*h+1))
      (by simpa [Nat.add_assoc] using separated (3*h+2)),ih]
    rw [show 3*(h+1)+1=((3*h+1)+1)+1+1 by omega]
    simp only [display_succ,List.cons_append,List.nil_append]

theorem padded_display (N k : ℕ) (hk : zeckendorfWordLength N ≤ k) :
    (display N k).map (fun b : Bool => if b then (1 : Fin 2) else 0) =
      List.replicate (k-zeckendorfWordLength N) 0 ++ zeckendorfMSDWord N := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  have bit_digit (i : ℕ) : (if bit N i then 1 else 0 : Fin 2)=zeckendorfBit N i := by
    simp [bit,zeckendorfBit]
  induction d with
  | zero => simp [display,zeckendorfMSDWord,List.map_map,Function.comp_def,bit_digit]
  | succ d ih =>
    have hz : bit N (zeckendorfWordLength N+d)=false := by
      simp only [bit,decide_eq_false_iff_not]
      intro hm
      have hb := occupied_index_bounds N _ hm
      omega
    rw [Nat.add_succ,display_succ,List.map_cons,hz]
    simpa [Nat.succ_eq_add_one,Nat.add_assoc,List.replicate_succ] using
      congrArg (List.cons (0 : Fin 2)) ih


/-- All extra high windows are literal original nulls, including when L is zero. -/
theorem padded_windows (N h : ℕ) (hh : L N ≤ h) :
    W h N = List.replicate (h-L N) .zero ++ W (L N) N := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hh
  clear hh
  have vanish (j : ℕ) (hj : zeckendorfWordLength N ≤ j) : bit N j=false := by
    simp only [bit,decide_eq_false_iff_not]
    intro hm
    have hb := occupied_index_bounds N _ hm
    omega
  induction d with
  | zero => simp
  | succ d ih =>
    have hk : zeckendorfWordLength N ≤ 3*(L N+d)+1 := by unfold L; omega
    rw [Nat.add_succ,W,vanish _ hk,vanish _ (by omega),vanish _ (by omega)]
    simpa [LiteralWindowEnd.triple,Nat.succ_eq_add_one,Nat.add_assoc,List.replicate_succ] using congrArg (List.cons .zero) ih

theorem local_source (h N : ℕ) (hh : L N ≤ h) :
    (localWord h N).length=h ∧
    legal false (NativeContinuation.NullReplyFiber.highBits
      ((localWord h N).map Original.letter) ++ [bit N 0]) ∧
    Original.numeral (localWord h N) (bit N 0)=N := by
  have hmap : (localWord h N).map Original.letter=W h N := by
    simp only [localWord,List.map_map]
    have he : Original.letter ∘ localLetter=id := by funext b; cases b <;> rfl
    simp [he]
  have hlen : (W h N).length=h := by
    clear hh hmap
    induction h with
    | zero => rfl
    | succ h ih => simpa [W] using ih
  have hk : zeckendorfWordLength N ≤ 3*h+1 := by dsimp [L] at hh; omega
  have hd := padded_display N (3*h+1) hk
  have hchain : NoAdjacentOnes ((display N (3*h+1)).map
      (fun b : Bool => if b then (1 : Fin 2) else 0)) := by
    rw [hd]
    have hz : ∀ k, NoAdjacentOnes (List.replicate k 0 ++ zeckendorfMSDWord N) := by
      intro k
      induction k with
      | zero => simpa using D5.S1.Digit.GoldenZeckendorfLanguage.zeckendorfMSDWord_noAdjacentOnes N
      | succ k ih =>
        apply List.IsChain.cons
        · exact ih
        · intro a ha
          exact Or.inl rfl
    exact hz _
  have bool_chain : ∀ bs : List Bool, NoAdjacentOnes (bs.map
      (fun b : Bool => if b then (1 : Fin 2) else 0)) → legal false bs := by
    intro bs
    have aux : ∀ (bs : List Bool) (s : Bool),
      ((if s then 1 else 0 : Fin 2) :: bs.map (fun b => if b then 1 else 0)).IsChain
        (fun a b => a=0 ∨ b=0) → legal s bs := by
      intro bs
      induction bs with
      | nil => intros; trivial
      | cons b bs ih =>
        intro s hs
        cases s <;> cases b <;> simp_all [legal,List.isChain_cons_cons]
    intro hc
    apply aux bs false
    apply List.IsChain.cons hc
    intro a ha
    exact Or.inl rfl
  have hv : (fibPair ((display N (3*h+1)).map
      (fun b : Bool => if b then (1 : Fin 2) else 0))).1=N := by
    rw [hd]
    have pad (k : ℕ) : (fibPair (List.replicate k 0 ++ zeckendorfMSDWord N)).1=N := by
      induction k with
      | zero => simpa using zeckendorfMSDWord_value N
      | succ k ih => simpa [List.replicate_succ,fibPair] using ih
    exact pad _
  refine ⟨by simpa [localWord] using hlen,?_,?_⟩
  · rw [hmap,original_bits]
    exact bool_chain _ hchain
  · simpa [Original.numeral,NativeContinuation.JointLaw.digits,List.map_append,
      hmap,← original_bits h N] using hv

end PhysicalWindowContinuation.OriginalEncoder

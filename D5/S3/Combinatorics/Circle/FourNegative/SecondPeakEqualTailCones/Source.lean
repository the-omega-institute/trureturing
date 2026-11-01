/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Source
   generality: I
   mirror-B: none(waiver:private-consumed-source)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal equal-tail source rows and their eight recurrences. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

/-! Source preparation only. The physical chains are U,V,W,X, not sorted values. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed sourceMod base newBase charge chainLength chainStart
  nextBase nextNewBase oldValue newValue actual_values chain_values
  new_base_bounds chain_signs source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private def rank (a b s : ℕ) : ℕ := a+b+s+s
private def amplitude (a b s : ℕ) : ℕ := 1+2^a+2^(a+b)+2^(a+b+s)
private def delta (y z : ℤ) : ℤ := y*(z+1)+1
private def heads (x y z : ℤ) : Fin 4 → ℤ :=
  ![x*delta y z+1, x*z*(y+1)+z+1, x*z*z+z*z+z+1, y*z*z+delta y z]
private def newHeads (x y z : ℤ) : Fin 4 → ℤ :=
  ![2*heads x y z 0, 2*heads x y z 1-1,
    2*heads x y z 2-z-1, 2*heads x y z 3-delta y z]
private def sourceN (x y z : ℤ) : ℤ := x*y*z*z-1
private def start (b s : ℕ) : Fin 4 → ℕ := ![0,s,2*s,2*s+b]
private def length (a b s : ℕ) : Fin 4 → ℕ := ![s,s,b,a]
private def f (a b s : ℕ) : ℕ → ℤ := oldValue a b s s
private def g (a b s : ℕ) : ℕ → ℤ := newValue a b s s
private def N (a b s : ℕ) : ℤ := sourceN (2^a) (2^b) (2^s)
private def successor (x y z : ℤ) : Fin 4 → ℤ :=
  ![heads x y z 1,heads x y z 2,heads x y z 3,heads x y z 0]
private def newSuccessor (x y z : ℤ) : Fin 4 → ℤ :=
  ![newHeads x y z 1,newHeads x y z 2,newHeads x y z 3,heads x y z 0]

private theorem row_heads (a b s : ℕ) :
    base a b s s=heads (2^a) (2^b) (2^s) ∧
    newBase a b s s=newHeads (2^a) (2^b) (2^s) ∧
    nextBase a b s s=successor (2^a) (2^b) (2^s) ∧
    nextNewBase a b s s=newSuccessor (2^a) (2^b) (2^s) := by
  repeat' constructor
  all_goals funext r; fin_cases r <;>
    dsimp [base,newBase,charge,nextBase,nextNewBase,heads,newHeads,successor,newSuccessor,delta] <;> ring

private theorem row_layout (a b s : ℕ) :
    chainLength a b s s=length a b s ∧ chainStart b s s=start b s := by
  constructor <;> funext r <;> fin_cases r <;> simp [chainLength,chainStart,length,start] <;> omega

private theorem source_numeric (a b s : ℕ) :
    modulus (rank a b s)=N a b s ∧
    modulus (rank a b s+1)=2*N a b s+1 ∧
    (amplitude a b s:ℤ)=heads (2^a) (2^b) (2^s) 0 := by
  dsimp [rank,N,sourceN,modulus,amplitude,heads,delta]
  push_cast
  simp only [pow_add,pow_succ]
  exact ⟨by ring,by ring,by ring⟩

private theorem eight_recurrences (x y z : ℤ) :
    z*heads x y z 0=sourceN x y z+heads x y z 1 ∧
    z*heads x y z 1=sourceN x y z+heads x y z 2 ∧
    y*heads x y z 2=sourceN x y z+heads x y z 3 ∧
    x*heads x y z 3=sourceN x y z+heads x y z 0 ∧
    z*newHeads x y z 0=2*sourceN x y z+1+newHeads x y z 1 ∧
    z*newHeads x y z 1=2*sourceN x y z+1+newHeads x y z 2 ∧
    y*newHeads x y z 2=2*sourceN x y z+1+newHeads x y z 3 ∧
    x*newHeads x y z 3=2*sourceN x y z+1+heads x y z 0 := by
  dsimp [heads,newHeads,sourceN,delta]
  repeat' constructor <;> ring

private theorem row_bounds (a b s : ℕ) (ha : 2≤a) (hb : 2≤b) (hs : 2≤s) :
    (∀ r, 1≤heads (2^a) (2^b) (2^s) r ∧ heads (2^a) (2^b) (2^s) r<N a b s) ∧
    (∀ r, 1≤newHeads (2^a) (2^b) (2^s) r ∧ newHeads (2^a) (2^b) (2^s) r<2*N a b s+1) := by
  have h := (chain_values a b s s ha hb hs hs).1
  have hn := new_base_bounds a b s s ha hb hs hs
  rw [(row_heads a b s).1] at h
  rw [(row_heads a b s).2.1] at hn
  exact ⟨h,hn⟩

private theorem positive_row (a b s : ℕ) (ha : 2≤a) (hb : 2≤b) (hs : 2≤s)
    (side : Bool) (r : Fin 4) (i : ℕ) (hi : i<length a b s r-1) :
    (if side then g a b s else f a b s) (start b s r+i)=
      (2:ℤ)^i*(if side then newHeads (2^a) (2^b) (2^s) else heads (2^a) (2^b) (2^s)) r := by
  have hl : 2≤length a b s r := by fin_cases r <;> simp [length] <;> omega
  have ht := chain_values a b s s ha hb hs hs
  have he := row_heads a b s
  have el := row_layout a b s
  cases side
  · change f a b s (start b s r+i)=(2:ℤ)^i*heads (2^a) (2^b) (2^s) r
    simpa only [el.1,el.2,he.1,if_pos (by omega : i+1<length a b s r)]
      using ht.2.1 r i (by rw [el.1]; omega)
  · change g a b s (start b s r+i)=(2:ℤ)^i*newHeads (2^a) (2^b) (2^s) r
    simpa only [el.1,el.2,he.2.1,if_pos (by omega : i+1<length a b s r)]
      using ht.2.2.1 r i (by rw [el.1]; omega)

private theorem terminal_row (a b s : ℕ) (ha : 2≤a) (hb : 2≤b) (hs : 2≤s)
    (r : Fin 4) :
    2*f a b s (start b s r+(length a b s r-1))=
      successor (2^a) (2^b) (2^s) r-N a b s ∧
    2*g a b s (start b s r+(length a b s r-1))=
      newSuccessor (2^a) (2^b) (2^s) r-(2*N a b s+1) := by
  have h := native_masses a b s s ha hb hs hs r
  have he := row_heads a b s
  have el := row_layout a b s
  simpa only [el.1,el.2,he.2.2.1,he.2.2.2] using h.2.2

private theorem terminal_nonpos (a b s : ℕ) (ha : 2≤a) (hb : 2≤b) (hs : 2≤s)
    (r : Fin 4) :
    f a b s (start b s r+(length a b s r-1))≤0 ∧
    g a b s (start b s r+(length a b s r-1))≤0 := by
  have el := row_layout a b s
  have hl : 2≤length a b s r := by fin_cases r <;> simp [length] <;> omega
  have h := chain_signs a b s s ha hb hs hs r (length a b s r-1)
    (by rw [el.1]; omega)
  rw [el.1,el.2,if_neg (by omega)] at h
  exact ⟨h.1.le,h.2.le⟩

private theorem totals (a b s : ℕ) (ha : 2≤a) (hb : 2≤b) (hs : 2≤s) :
    ((List.range (rank a b s)).map (f a b s)).sum=0 ∧
    ((List.range (rank a b s)).map (g a b s)).sum= -heads (2^a) (2^b) (2^s) 0 ∧
    g a b s (rank a b s)=heads (2^a) (2^b) (2^s) 0 := by
  simpa only [(row_heads a b s).1] using source_totals a b s s ha hb hs hs

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones

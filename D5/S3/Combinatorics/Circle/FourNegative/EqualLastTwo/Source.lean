/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Source
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Source
   mirror-E: none(waiver:consumed-physical-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical paired chains and literal bank plans for equal last two gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
import Mathlib.Algebra.Order.Interval.Finset.Basic

/-! Exact physical chains and explicit occurrence banks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue chain_values source_totals actual_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private last_double from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

private def rank (a b d : ℕ) := a+b+d+d
private def amplitude (a b d : ℕ) := 1+2^a+2^(a+b)+2^(a+b+d)
private def delta (y t : ℤ) := 1+y+y*t
private def heads (x y t : ℤ) : Fin 4 → ℤ :=
  ![x*delta y t+1, t*(1+x+x*y)+1, t^2*(1+x)+t+1, t*y*t+delta y t]
private def newHeads (x y t : ℤ) : Fin 4 → ℤ :=
  ![2*heads x y t 0, 2*heads x y t 1-1, 2*heads x y t 2-1-t,
    2*heads x y t 3-delta y t]
private def successor (F : Fin 4 → ℤ) : Fin 4 → ℤ := ![F 1,F 2,F 3,F 0]
private def newSuccessor (x y t : ℤ) : Fin 4 → ℤ :=
  ![newHeads x y t 1,newHeads x y t 2,newHeads x y t 3,heads x y t 0]
private def start (b d : ℕ) : Fin 4 → ℕ := ![0,d,2*d,2*d+b]
private def length (a b d : ℕ) : Fin 4 → ℕ := ![d,d,b,a]
private def f (a b d : ℕ) := oldValue a b d d
private def g (a b d : ℕ) := newValue a b d d
private def N (a b d : ℕ) := sourceMod a b d d

private theorem source (a b d : ℕ) (hd : 2 ≤ d) (hb : d < b) (ha : b < a) :
    let x : ℤ := 2^a
    let y : ℤ := 2^b
    let t : ℤ := 2^d
    (∀ r : Fin 4, 0 < heads x y t r) ∧
    (∀ r : Fin 4, 0 < newHeads x y t r) ∧
    (∀ r : Fin 4, ∀ i < length a b d r-1,
      f a b d (start b d r+i) = (2:ℤ)^i*heads x y t r ∧
      g a b d (start b d r+i) = (2:ℤ)^i*newHeads x y t r) ∧
    (∀ r : Fin 4,
      2*f a b d (start b d r+length a b d r-1) = successor (heads x y t) r-N a b d ∧
      2*g a b d (start b d r+length a b d r-1) = newSuccessor x y t r-(2*N a b d+1)) ∧
    g a b d (rank a b d) = heads x y t 0 := by
  dsimp only
  obtain ⟨hbases,hf,hg,he⟩ := chain_values a b d d (by omega) (by omega) hd hd
  have eb (r : Fin 4) : base a b d d r = heads ((2:ℤ)^a) (2^b) (2^d) r := by
    fin_cases r <;> dsimp [base,heads,delta] <;> ring
  have eg (r : Fin 4) : newBase a b d d r = newHeads ((2:ℤ)^a) (2^b) (2^d) r := by
    fin_cases r <;> dsimp [newBase,base,charge,newHeads,heads,delta] <;> ring
  have es (r : Fin 4) : chainStart b d d r = start b d r := by
    fin_cases r <;> simp [chainStart,start] <;> omega
  have el (r : Fin 4) : chainLength a b d d r = length a b d r := by
    fin_cases r <;> rfl
  have en (r : Fin 4) : nextBase a b d d r = successor (heads ((2:ℤ)^a) (2^b) (2^d)) r := by
    fin_cases r <;> simp [nextBase,successor,eb]
  have enn (r : Fin 4) : nextNewBase a b d d r = newSuccessor ((2:ℤ)^a) (2^b) (2^d) r := by
    fin_cases r <;> simp [nextNewBase,newSuccessor,eg,eb]
  have hr (r : Fin 4) : 1 ≤ length a b d r := by
    fin_cases r <;> simp [length] <;> omega
  have rel (r : Fin 4) : (2:ℤ)^(chainLength a b d d r)*base a b d d r =
      sourceMod a b d d+nextBase a b d d r := by
    fin_cases r <;> dsimp [chainLength,base,sourceMod,nextBase] <;> ring
  have reln (r : Fin 4) : (2:ℤ)^(chainLength a b d d r)*newBase a b d d r =
      (2*sourceMod a b d d+1)+nextNewBase a b d d r := by
    fin_cases r <;> dsimp [chainLength,newBase,base,charge,sourceMod,nextNewBase] <;> ring
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r; rw [←eb]; have := (hbases r).1; omega
  · intro r
    have h := new_base_bounds a b d d (by omega) (by omega) hd hd r
    rw [eg] at h
    omega
  · intro r i hi
    have hh := hf r i (by rw [el]; omega)
    have hhn := hg r i (by rw [el]; omega)
    rw [el,ite_eq_left (by omega),eb,es] at hh
    rw [el,ite_eq_left (by omega),eg,es] at hhn
    exact ⟨hh,hhn⟩
  · intro r
    have hr' := hr r
    have hh := hf r (length a b d r-1) (by rw [el]; omega)
    have hhn := hg r (length a b d r-1) (by rw [el]; omega)
    rw [el,ite_eq_right (by omega),es] at hh hhn
    rw [show start b d r+length a b d r-1=start b d r+(length a b d r-1) by omega]
    dsimp [f,g,N]
    rw [hh,hhn]
    constructor
    · rw [←en]; exact last_double _ _ _ _ (by rw [el]; exact hr r) (rel r)
    · rw [←enn]; exact last_double _ _ _ _ (by rw [el]; exact hr r) (reln r)
  · change newValue a b d d (rank a b d) = _
    rw [show rank a b d=size a b d d by rfl,he,eb]

private theorem source_numeric (a b d : ℕ) :
    N a b d=(2:ℤ)^a*2^b*(2^d)^2-1 ∧
    modulus (rank a b d)=N a b d ∧
    modulus (rank a b d+1)=2*N a b d+1 ∧
    (amplitude a b d:ℤ)=heads ((2:ℤ)^a) (2^b) (2^d) 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [N,sourceMod]; ring
  · dsimp [modulus,rank,N,sourceMod]; simp only [pow_add] <;> ring
  · dsimp [modulus,rank,N,sourceMod]; simp only [pow_add,pow_one]; ring
  · simp only [amplitude,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat]
    dsimp [heads,delta]; simp only [pow_add] <;> ring

private def shift (s : ℕ) (P : Finset ℕ) : Finset ℕ := P.image (s+·)

private theorem image_Ico (s l n : ℕ) :
    (Finset.Ico l n).image (s+·) = Finset.Ico (s+l) (s+n) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨j,hj,rfl⟩
    omega
  · intro hi
    refine ⟨i-s,?_,by omega⟩
    omega

private theorem image_range (s n : ℕ) :
    (Finset.range n).image (s+·) = Finset.Ico s (s+n) := by
  simpa only [Finset.range_eq_Ico, Nat.add_zero] using image_Ico s 0 n

private def bankLarge (a d : ℕ) (F : ℕ) : Fin 4 → Finset ℕ :=
  ![{a-d-3} ∪ Finset.Ico (a-d) (a-1),
    {a-d-2},
    {a-d-1} ∪ Finset.Ico F (a-d-3),
    Finset.range F]

private def bankAdjacent (a d : ℕ) : Fin 4 → Finset ℕ :=
  ![{a-d-4} ∪ Finset.Ico (a-d) (a-1),
    {a-d-3},
    {a-d-1},
    {a-d-2} ∪ Finset.range (a-d-4)]

private def largeP (a b d : ℕ) : Finset ℕ :=
  shift (2*d+b) (bankLarge a d (a-b-1) 0)
private def largeQ (a b d : ℕ) : Finset ℕ :=
  Finset.range (d-1) ∪ shift (2*d+b) (bankLarge a d (a-b-1) 1)
private def largeR (a b d : ℕ) : Finset ℕ :=
  shift d (Finset.range (d-1)) ∪ shift (2*d+b) (bankLarge a d (a-b-1) 2)
private def largeG (a b d : ℕ) : Finset ℕ :=
  shift (2*d) (Finset.range (b-1)) ∪ shift (2*d+b) (bankLarge a d (a-b-1) 3)

private def adjacentP (a d : ℕ) : Finset ℕ :=
  shift (3*d+1) (bankAdjacent a d 0)
private def adjacentQ (a d : ℕ) : Finset ℕ :=
  Finset.range (d-1) ∪ shift (3*d+1) (bankAdjacent a d 1)
private def adjacentR (a d : ℕ) : Finset ℕ :=
  shift d (Finset.range (d-1)) ∪ shift (3*d+1) (bankAdjacent a d 2)
private def adjacentG (a d : ℕ) : Finset ℕ :=
  shift (2*d) (Finset.range d) ∪ shift (3*d+1) (bankAdjacent a d 3)

private def corner2P (d : ℕ) : Finset ℕ := Finset.range (d-1) ∪ {3*d+1}
private def corner2Q (d : ℕ) : Finset ℕ := shift d (Finset.range (d-1)) ∪ {3*d+2}
private def corner2R (d : ℕ) : Finset ℕ := Finset.Ico (3*d+3) (4*d+2)
private def corner2G (d : ℕ) : Finset ℕ := shift (2*d) (Finset.range d)

private def corner3P (d : ℕ) : Finset ℕ := {3*d+1} ∪ Finset.Ico (3*d+4) (4*d+3)
private def corner3Q (d : ℕ) : Finset ℕ := shift d (Finset.range (d-1)) ∪ {3*d+3}
private def corner3R (d : ℕ) : Finset ℕ := Finset.range (d-1) ∪ {3*d+2}
private def corner3G (d : ℕ) : Finset ℕ := shift (2*d) (Finset.range d)

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo

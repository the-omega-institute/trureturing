/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/Boundaries
   generality: I
   mirror-B: none(waiver:private-consumed-boundary-certificates)
   mirror-E: none(waiver:private-consumed-boundary-certificates)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual paired allocations at equal and adjacent final gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.Broad
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.PhysicalBanks

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private Values values
  Values.z Values.w Values.r Values.q Values.x Values.y Values.H Values.S
  Values.A Values.B Values.L Values.K Values.SU Values.SV Values.SW
  Values.D Values.Dp Values.E Values.F Values.J broadTerminals
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BroadData
open private size sourceMod base newBase charge oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase weightedMask packet_masses chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private range_mass
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.PhysicalBanks

private def boundaryPieces (a b c d : ℕ) : Fin 9 → List ℕ :=
  let off := d+c+b
  ![List.range' 1 (d-2), [0], List.range' d (c-1),
    List.range' (d+c) (b-a), List.range' (d+c+(b-a)) (a-1),
    List.range' off (a-d-1), [off+(a-d-1)], [off+(a-d)],
    List.range' (off+(a-d)+1) (d-2)]

private def boundaryBanks (a b c d : ℕ) (equal swap : Bool) : Fin 4 → List ℕ :=
  let P := boundaryPieces a b c d
  ![P 4, P 8 ++ (if swap then P 1 ++ P 6 else P 7),
    P 0 ++ (if swap then P 7 else P 1) ++ (if equal && !swap then P 6 else []),
    P 2 ++ P 3 ++ P 5 ++ (if equal then [] else P 6)]

private def boundaryWord (a b c d : ℕ) (equal swap : Bool) : List ℕ :=
  let P := boundaryBanks a b c d equal swap
  let T := broadTerminals a b c d
  P 0 ++ [T 0] ++ P 1 ++ [T 1] ++ P 2 ++ [T 2] ++ P 3 ++ [T 3]

private theorem boundary_inventory (a b c d : ℕ) (hc : 2≤c) (hd : 2≤d)
    (hda : d<a) (hab : a≤b) (equal swap : Bool) (hs : swap=true → equal=true) :
    (boundaryWord a b c d equal swap).Perm (List.range (a+b+c+d)) := by
  let P := boundaryPieces a b c d
  have join (off m n : ℕ) : List.range' off m ++ List.range' (off+m) n =
      List.range' off (m+n) := List.range'_append_1
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1) ++ [off+len-1] = List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega]
      using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have hU : P 1 ++ P 0 = List.range' 0 (d-1) := by
    dsimp [P,boundaryPieces]
    change [0] ++ List.range' (0+1) (d-2) = _
    rw [show [0]=List.range' 0 1 by rfl]
    have hh := join 0 1 (d-2)
    simpa [show 1+(d-2)=d-1 by omega] using hh
  have hW : P 3 ++ P 4 = List.range' (d+c) (b-1) := by
    dsimp [P,boundaryPieces]
    rw [join]
    congr 1
    omega
  have hX : P 5 ++ P 6 ++ P 7 ++ P 8 = List.range' (d+c+b) (a-1) := by
    dsimp [P,boundaryPieces]
    rw [show [d+c+b+(a-d-1)]=List.range' (d+c+b+(a-d-1)) 1 by simp,join]
    rw [show a-d-1+1=a-d by omega]
    rw [show [d+c+b+(a-d)]=List.range' (d+c+b+(a-d)) 1 by simp,join]
    rw [show d+c+b+(a-d)+1=d+c+b+(a-d+1) by omega,join]
    congr 1
    omega
  have hall :
      ((P 1 ++ P 0) ++ [d-1]) ++ (P 2 ++ [d+c-1]) ++
      ((P 3 ++ P 4) ++ [d+c+b-1]) ++
      ((P 5 ++ P 6 ++ P 7 ++ P 8) ++ [a+b+c+d-1]) =
        List.range (a+b+c+d) := by
    rw [hU,hW,hX]
    dsimp [P,boundaryPieces]
    have h0 := merge 0 d (by omega)
    simp only [Nat.zero_add] at h0
    rw [h0,merge d c (by omega),merge (d+c) b (by omega)]
    rw [show a+b+c+d-1=d+c+b+a-1 by omega,merge (d+c+b) a (by omega)]
    rw [show List.range' 0 d ++ List.range' d c=List.range' 0 (d+c) by
      simpa only [Nat.zero_add] using join 0 d c]
    rw [show List.range' 0 (d+c) ++ List.range' (d+c) b=List.range' 0 (d+c+b) by
      simpa only [Nat.zero_add] using join 0 (d+c) b]
    rw [show List.range' 0 (d+c+b) ++ List.range' (d+c+b) a=List.range' 0 (d+c+b+a) by
      simpa only [Nat.zero_add] using join 0 (d+c+b) a]
    simp only [←List.range_eq_range']
    congr 1
    omega
  apply Multiset.coe_eq_coe.mp
  rw [←hall]
  cases equal <;> cases swap
  · dsimp [boundaryWord,boundaryBanks,broadTerminals]
    simp only [←Multiset.coe_add,Multiset.coe_singleton,List.append_nil]
    dsimp only [P]
    ac_rfl
  · simp at hs
  · dsimp [boundaryWord,boundaryBanks,broadTerminals]
    simp only [List.append_nil,←Multiset.coe_add,Multiset.coe_singleton]
    dsimp only [P]
    ac_rfl
  · dsimp [boundaryWord,boundaryBanks,broadTerminals]
    simp only [List.append_nil,←Multiset.coe_add,Multiset.coe_singleton]
    dsimp only [P]
    ac_rfl

private theorem boundary_good (a b c d : ℕ) (hc : 2≤c) (hd : 2≤d)
    (hda : d<a) (hab : a≤b) (equal swap : Bool) (j : Fin 4) (i : ℕ)
    (hi : i∈boundaryBanks a b c d equal swap j) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have range_iff (start len : ℕ) :
      i∈List.range' start len ↔ start ≤ i ∧ i < start+len := by
    simp only [List.mem_range',Nat.one_mul]
    constructor
    · rintro ⟨e,he,rfl⟩; omega
    · intro hh; exact ⟨i-start,by omega,by omega⟩
  cases equal <;> cases swap <;> fin_cases j
  all_goals dsimp [boundaryBanks,boundaryPieces] at hi
  all_goals simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,
    List.mem_singleton,range_iff] at hi
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem boundary_masses (a b c d : ℕ) (hc : 2≤c) (hd : 2≤d)
    (hda : d<a) (hab : a≤b) (equal swap : Bool) (hswap : swap=true → equal=true)
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hs : ∀ j : Fin 4, ∀ i<chainLength a b c d j-1,
      f (chainStart b c d j+i)=2^i*F j) :
    let q : ℤ := 2^(b-a)
    let t : ℤ := 2^(a-d-1)
    let v := if equal then t else 2*t
    let P := boundaryBanks a b c d equal swap
    ((P 0).map f).sum=((2:ℤ)^(b-1)-q)*F 2 ∧
    ((P 1).map f).sum=((2:ℤ)^(a-1)-(if swap then 3*t else 2*t))*F 3+
      (if swap then F 0 else 0) ∧
    ((P 2).map f).sum=((2:ℤ)^(d-1)-1-(if swap then 1 else 0))*F 0+
      (if equal then (if swap then 2*t else t) else 0)*F 3 ∧
    ((P 3).map f).sum=((2:ℤ)^(c-1)-1)*F 1+(q-1)*F 2+(v-1)*F 3 := by
  dsimp only
  have part (j : Fin 4) (lo len : ℕ) (hh : lo+len≤chainLength a b c d j-1) :=
    range_mass f F b c d j lo len (fun i hi => hs j i (by omega))
  have m0 := part 0 1 (d-2) (by simp [chainLength];omega)
  have m1 := hs 0 0 (by simp [chainLength];omega)
  have m2 := part 1 0 (c-1) (by simp [chainLength])
  have m3 := part 2 0 (b-a) (by simp [chainLength];omega)
  have m4 := part 2 (b-a) (a-1) (by simp [chainLength];omega)
  have m5 := part 3 0 (a-d-1) (by simp [chainLength];omega)
  have m6 := hs 3 (a-d-1) (by simp [chainLength];omega)
  have m7 := hs 3 (a-d) (by simp [chainLength];omega)
  have m8 := part 3 (a-d+1) (d-2) (by simp [chainLength];omega)
  simp only [chainStart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Nat.add_zero,pow_zero,zero_add]
    at m0 m1 m2 m3 m4 m5 m6 m7 m8
  rw [show 1+(d-2)=d-1 by omega] at m0
  rw [show b-a+(a-1)=b-1 by omega] at m4
  rw [show a-d+1+(d-2)=a-1 by omega] at m8
  have e1 : (2:ℤ)^(a-d)=2*2^(a-d-1) := by
    conv_lhs => rw [show a-d=(a-d-1)+1 by omega,pow_succ]
    ring
  have e2 : (2:ℤ)^(a-d+1)=4*2^(a-d-1) := by rw [pow_succ,e1];ring
  rw [e1] at m7
  rw [e2] at m8
  cases equal <;> cases swap
  all_goals try { simp at hswap }
  all_goals dsimp [boundaryBanks,boundaryPieces]
  all_goals simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
    List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero]
  all_goals rw [show d+c+b+(a-d)+1=d+c+b+(a-d+1) by omega]
  all_goals rw [m0,m1,m2,m3,m4,m5,m6,m7,m8]
  all_goals refine ⟨by ring,by ring,by ring,by ring⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum

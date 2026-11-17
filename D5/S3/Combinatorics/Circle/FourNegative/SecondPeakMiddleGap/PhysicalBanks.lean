/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/PhysicalBanks
   generality: I
   mirror-B: none(waiver:private-consumed-physical-inventory)
   mirror-E: none(waiver:private-consumed-physical-inventory)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete actual bank inventory and paired dyadic masses for the two allocations. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

/-! Private consumed arithmetic and physical construction for the middle-gap joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size negatives chainStart chainLength)

private def pieces (a b c d : ℕ) : Fin 9 → List ℕ :=
  let off := d+c+b
  ![List.range' 0 (d-1), List.range' d (c-1),
    List.range' (d+c) (b-a), List.range' (d+c+(b-a)) (a-1),
    List.range' off (a-c-1), List.range' (off+(a-c-1)) (c-d-1),
    [off+(a-d-2)], [off+(a-d-1)], List.range' (off+(a-d)) (d-1)]

private def banks (a b c d : ℕ) (first : Bool) : Fin 4 → List ℕ :=
  let P := pieces a b c d
  ![P 3, (if first then P 7 else P 6) ++ P 8,
    P 0 ++ P 5 ++ (if first then P 6 else P 7), P 1 ++ P 2 ++ P 4]

private def terminals (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d+c+b-1,a+b+c+d-1,d-1,d+c-1]

private def word (a b c d : ℕ) (first : Bool) : List ℕ :=
  let P := banks a b c d first
  let T := terminals a b c d
  P 0 ++ [T 0] ++ P 1 ++ [T 1] ++ P 2 ++ [T 2] ++ P 3 ++ [T 3]

private theorem banks_inventory (a b c d : ℕ) (hd : 2≤d) (hdc : d<c)
    (hca : c<a) (hab : a≤b) (first : Bool) :
    (word a b c d first).Perm (List.range (a+b+c+d)) := by
  let P := pieces a b c d
  have join (off m n : ℕ) : List.range' off m ++ List.range' (off+m) n =
      List.range' off (m+n) := List.range'_append_1
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1) ++ [off+len-1] = List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega]
      using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have hW : P 2 ++ P 3 = List.range' (d+c) (b-1) := by
    dsimp [P,pieces]
    rw [join]
    congr 1
    omega
  have hX : P 4 ++ P 5 ++ P 6 ++ P 7 ++ P 8 = List.range' (d+c+b) (a-1) := by
    dsimp [P,pieces]
    rw [join]
    have e0 : a-c-1+(c-d-1)=a-d-2 := by omega
    rw [e0]
    rw [show [d+c+b+(a-d-2)]=List.range' (d+c+b+(a-d-2)) 1 by simp]
    rw [join]
    rw [show a-d-2+1=a-d-1 by omega]
    rw [show [d+c+b+(a-d-1)]=List.range' (d+c+b+(a-d-1)) 1 by simp]
    rw [join]
    rw [show a-d-1+1=a-d by omega,join]
    congr 1
    omega
  have hall :
      (P 0 ++ [d-1]) ++ (P 1 ++ [d+c-1]) ++
      ((P 2 ++ P 3) ++ [d+c+b-1]) ++
      ((P 4 ++ P 5 ++ P 6 ++ P 7 ++ P 8) ++ [a+b+c+d-1]) =
        List.range (a+b+c+d) := by
    rw [hW,hX]
    dsimp [P,pieces]
    have h0 := merge 0 d (by omega)
    simp only [Nat.zero_add] at h0
    rw [h0,merge d c (by omega),merge (d+c) b (by omega)]
    rw [show a+b+c+d-1=d+c+b+a-1 by omega,merge (d+c+b) a (by omega)]
    rw [show List.range' 0 d ++ List.range' d c = List.range' 0 (d+c) by
      simpa only [Nat.zero_add] using join 0 d c]
    rw [show List.range' 0 (d+c) ++ List.range' (d+c) b = List.range' 0 (d+c+b) by
      simpa only [Nat.zero_add] using join 0 (d+c) b]
    rw [show List.range' 0 (d+c+b) ++ List.range' (d+c+b) a =
      List.range' 0 (d+c+b+a) by simpa only [Nat.zero_add] using join 0 (d+c+b) a]
    simp only [←List.range_eq_range']
    congr 1
    omega
  apply Multiset.coe_eq_coe.mp
  rw [←hall]
  cases first <;> dsimp [word,banks,terminals]
  all_goals simp only [←Multiset.coe_add,Multiset.coe_singleton]
  all_goals change _ = _
  all_goals dsimp only [P]
  all_goals ac_rfl

private theorem banks_good (a b c d : ℕ) (hd : 2≤d) (hdc : d<c)
    (hca : c<a) (hab : a≤b) (first : Bool)
    (j : Fin 4) (i : ℕ) (hi : i∈banks a b c d first j) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have range_iff (start len : ℕ) :
      i ∈ List.range' start len ↔ start ≤ i ∧ i < start + len := by
    simp only [List.mem_range',Nat.one_mul]
    constructor
    · rintro ⟨j,hj,rfl⟩
      omega
    · intro hh
      exact ⟨i-start,by omega,by omega⟩
  cases first <;> fin_cases j
  all_goals dsimp [banks,pieces] at hi
  all_goals simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,
    List.mem_singleton,range_iff] at hi
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem range_mass (f : ℕ→ℤ) (F : Fin 4→ℤ) (b c d : ℕ)
    (j : Fin 4) (lo len : ℕ)
    (hs : ∀ i<lo+len, f (chainStart b c d j+i)=2^i*F j) :
    ((List.range' (chainStart b c d j+lo) len).map f).sum=
      ((2:ℤ)^(lo+len)-2^lo)*F j := by
  rw [←chamberLabels_full]
  have hm : 2^len-1<2^len := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hh := chamberLabels_sum len (chainStart b c d j+lo) (2^len-1) hm f
    ((2:ℤ)^lo*F j) (by
      intro i hi
      rw [show chainStart b c d j+lo+i=chainStart b c d j+(lo+i) by omega,
        hs (lo+i) (by omega),pow_add]
      ring)
  rw [hh,Nat.cast_sub (by have := Nat.two_pow_pos len; omega)]
  push_cast
  rw [pow_add]
  ring

private theorem banks_masses (a b c d : ℕ) (hd : 2≤d) (hdc : d<c)
    (hca : c<a) (hab : a≤b) (first : Bool) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hs : ∀ j : Fin 4, ∀ i<chainLength a b c d j-1,
      f (chainStart b c d j+i)=2^i*F j) :
    let q : ℤ := 2^(b-a)
    let s : ℤ := 2^(a-d-2)
    let v : ℤ := 2^(a-c-1)
    let r := if first then 2*s else 3*s
    let C := fun n : ℕ => (2:ℤ)^(n-1)-1
    let P := banks a b c d first
    ((P 0).map f).sum=(C b+1-q)*F 2 ∧
    ((P 1).map f).sum=(C a+1-r)*F 3 ∧
    ((P 2).map f).sum=C d*F 0+(r-v)*F 3 ∧
    ((P 3).map f).sum=C c*F 1+(q-1)*F 2+(v-1)*F 3 := by
  dsimp only
  let P := pieces a b c d
  have part (j : Fin 4) (lo len : ℕ) (hc : lo+len≤chainLength a b c d j-1) :=
    range_mass f F b c d j lo len (fun i hi => hs j i (by omega))
  have m0 := part 0 0 (d-1) (by simp [chainLength])
  have m1 := part 1 0 (c-1) (by simp [chainLength])
  have m2 := part 2 0 (b-a) (by simp [chainLength];omega)
  have m3 := part 2 (b-a) (a-1) (by simp [chainLength];omega)
  have m4 := part 3 0 (a-c-1) (by simp [chainLength];omega)
  have m5 := part 3 (a-c-1) (c-d-1) (by simp [chainLength];omega)
  have m6 := hs 3 (a-d-2) (by simp [chainLength];omega)
  have m7 := hs 3 (a-d-1) (by simp [chainLength];omega)
  have m8 := part 3 (a-d) (d-1) (by simp [chainLength];omega)
  simp only [chainStart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_succ,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Nat.add_zero,pow_zero,zero_add] at m0 m1 m2 m3 m4 m5 m6 m7 m8
  rw [show b-a+(a-1)=b-1 by omega] at m3
  rw [show a-c-1+(c-d-1)=a-d-2 by omega] at m5
  rw [show a-d+(d-1)=a-1 by omega] at m8
  have e1 : (2:ℤ)^(a-d-1)=2*2^(a-d-2) := by
    conv_lhs => rw [show a-d-1=(a-d-2)+1 by omega,pow_succ]
    ring
  have e2 : (2:ℤ)^(a-d)=4*2^(a-d-2) := by
    conv_lhs => rw [show a-d=(a-d-2)+2 by omega,pow_add]
    ring
  rw [e1] at m7
  rw [e2] at m8
  cases first <;> dsimp [banks,pieces]
  all_goals simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
    List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero,
    ite_true,ite_false,Bool.false_eq_true]
  all_goals rw [m0,m1,m2,m3,m4,m5,m6,m7,m8]
  all_goals refine ⟨by ring,by ring,by ring,by ring⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap

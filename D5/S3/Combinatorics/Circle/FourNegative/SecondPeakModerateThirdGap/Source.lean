/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Source
   digest: physical W/X/U/V banks and exact paired actual source masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private size base newBase chainLength chainStart oldValue newValue
  chain_values negatives
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private uFull uRest uRest_eq u_capacity u_native_partition shifted_partition shifted_capacities
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Masks

private def bank (a b c d u H : ℕ) : Fin 4 → List ℕ :=
  let lam := 2^(b-c-1)
  let h := lam*H
  let f := lam*(2^c-1-H)
  let low := lam-1
  ![chamberLabels (d-1) 0 (uRest d u),
    chamberLabels (b-1) (d+c) h,
    chamberLabels (b-1) (d+c) f ++
      chamberLabels (a-1) (d+c+b) (2^(a-1)-1) ++
      chamberLabels (d-1) 0 u,
    chamberLabels (c-1) d (2^(c-1)-1) ++
      chamberLabels (b-1) (d+c) low]

private def terminal (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d+c+b-1,a+b+c+d-1,d-1,d+c-1]

private def word (a b c d u H : ℕ) : List ℕ :=
  let P := bank a b c d u H
  let T := terminal a b c d
  P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3]

private theorem bank_inventory (a b c d u H : ℕ)
    (ha : 2 ≤ a) (had : a < d) (hdc : d < c) (hcb : c < b)
    (hu : u=0 ∨ u=1 ∨ u=2) (hH : H < 2^c) :
    (word a b c d u H).Perm (List.range (a+b+c+d)) := by
  classical
  let U := chamberLabels (d-1) 0 (uRest d u) ++ chamberLabels (d-1) 0 u
  let W := (chamberLabels (b-1) (d+c) (2^(b-c-1)*H) ++
    chamberLabels (b-1) (d+c) (2^(b-c-1)*(2^c-1-H))) ++
    chamberLabels (b-1) (d+c) (2^(b-c-1)-1)
  let V := chamberLabels (c-1) d (2^(c-1)-1)
  let X := chamberLabels (a-1) (d+c+b) (2^(a-1)-1)
  have hU : U.Perm (List.range' 0 (d-1)) := u_native_partition d u (by omega) hu
  have hW : W.Perm (List.range' (d+c) (b-1)) :=
    shifted_partition b c (d+c) H hcb hH
  have hX : X=List.range' (d+c+b) (a-1) := chamberLabels_full _ _
  have hV : V=List.range' d (c-1) := chamberLabels_full _ _
  have merge (o n : ℕ) (hn : 1 ≤ n) :
      List.range' o (n-1) ++ [o+n-1] = List.range' o n := by
    simpa only [show o+(n-1)=o+n-1 by omega,show n-1+1=n by omega] using
      (List.range'_1_concat (s:=o) (n:=n-1)).symm
  have hall :
      (((List.range' 0 (d-1) ++ [d-1]) ++
        (List.range' d (c-1) ++ [d+c-1])) ++
        (List.range' (d+c) (b-1) ++ [d+c+b-1])) ++
        (List.range' (d+c+b) (a-1) ++ [a+b+c+d-1]) =
        List.range (a+b+c+d) := by
    have h0 := merge 0 d (by omega)
    have h1 := merge d c (by omega)
    have h2 := merge (d+c) b (by omega)
    have h3 : List.range' (d+c+b) (a-1) ++ [a+b+c+d-1]=
        List.range' (d+c+b) a := by
      simpa only [show d+c+b+a-1=a+b+c+d-1 by omega] using
        merge (d+c+b) a (by omega)
    simp only [Nat.zero_add] at h0
    rw [h0,h1,h2,h3]
    have hdc' : List.range' 0 d ++ List.range' d c=List.range' 0 (d+c) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d) (n:=c))
    have hdcb : List.range' 0 (d+c) ++ List.range' (d+c) b=List.range' 0 (d+c+b) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d+c) (n:=b))
    have hdcba : List.range' 0 (d+c+b) ++ List.range' (d+c+b) a=List.range' 0 (d+c+b+a) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d+c+b) (n:=a))
    rw [hdc',hdcb,hdcba,List.range_eq_range']
    congr 1 <;> omega
  have rearrange : (word a b c d u H).Perm
      ((((U ++ [d-1]) ++ (V ++ [d+c-1])) ++ (W ++ [d+c+b-1])) ++
        (X ++ [a+b+c+d-1])) := by
    apply Multiset.coe_eq_coe.mp
    dsimp [word,bank,terminal,U,V,W,X]
    simp only [←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,
      Multiset.coe_singleton,Multiset.coe_nil,add_zero,zero_add]
    ac_rfl
  apply rearrange.trans
  rw [hV,hX]
  have hp := (((hU.append_right [d-1]).append (List.Perm.refl
    (List.range' d (c-1) ++ [d+c-1]))).append
      (hW.append_right [d+c+b-1])).append (List.Perm.refl
        (List.range' (d+c+b) (a-1) ++ [a+b+c+d-1]))
  simpa only [hall] using hp

private theorem bank_good (a b c d u H : ℕ)
    (ha : 2 ≤ a) (had : a < d) (hdc : d < c) (hcb : c < b)
    (j : Fin 4) (i : ℕ) (hi : i∈bank a b c d u H j) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have masked (len off mask : ℕ) (hm : i∈chamberLabels len off mask) :
      off ≤ i ∧ i<off+len := by
    obtain ⟨e,he,_,hei⟩ := (chamberLabels_mem _ _ _ _).mp hm
    omega
  fin_cases j
  all_goals dsimp [bank] at hi
  all_goals simp only [List.mem_append] at hi
  all_goals repeat' first
    | (have hbound := masked _ _ _ hi
       constructor
       · dsimp [size]; omega
       · simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false]; omega)
    | (rcases hi with hi|hi)

private theorem bank_masses (a b c d u H : ℕ)
    (ha : 2 ≤ a) (had : a < d) (hdc : d < c) (hcb : c < b)
    (hu : u=0 ∨ u=1 ∨ u=2) (hH : H < 2^c) :
    ∀ side : Bool,
    let F := if side then newBase a b c d else base a b c d
    let f := if side then newValue a b c d else oldValue a b c d
    let P := bank a b c d u H
    let lam := (2^(b-c-1):ℕ)
    ((P 0).map f).sum=((2^(d-1)-1-u:ℕ):ℤ)*F 0 ∧
    ((P 1).map f) .sum=(lam*H:ℤ)*F 2 ∧
    ((P 2).map f).sum=((lam*(2^c-1-H):ℕ):ℤ)*F 2+
      ((2^(a-1)-1:ℕ):ℤ)*F 3+(u:ℤ)*F 0 ∧
    ((P 3).map f).sum=((2^(c-1)-1:ℕ):ℤ)*F 1+((lam-1:ℕ):ℤ)*F 2 := by
  intro side
  dsimp only
  let F := if side then newBase a b c d else base a b c d
  let f := if side then newValue a b c d else oldValue a b c d
  let P := bank a b c d u H
  let lam : ℕ := 2^(b-c-1)
  have tab := chain_values a b c d ha (by omega) (by omega) (by omega)
  have series (q : Fin 4) : ∀ i<chainLength a b c d q-1,
      f (chainStart b c d q+i)=2^i*F q := by
    intro i hi
    cases side
    · exact (tab.2.1 q i (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 q i (by omega)).trans (if_pos (by omega))
  have full (q : Fin 4) :
      ((List.range' (chainStart b c d q) (chainLength a b c d q-1)).map f).sum=
        ((2^(chainLength a b c d q-1)-1:ℕ):ℤ)*F q := by
    rw [←chamberLabels_full]
    apply chamberLabels_sum
    · exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    · exact series q
  have hcU := u_capacity d u (by omega) hu
  have hrest := uRest_eq d u (by omega) hu
  have hcRest : uRest d u<2^(d-1) := by
    rw [hrest]
    have hp := Nat.two_pow_pos (d-1)
    omega
  have hcW := shifted_capacities b c H hcb hH
  have huq := chamberLabels_sum (d-1) 0 (uRest d u)
      hcRest f (F 0)
      (by intro i hi; simpa [chainLength,chainStart] using series 0 i hi)
  have huu := chamberLabels_sum (d-1) 0 u
      hcU f (F 0)
      (by intro i hi; simpa [chainLength,chainStart] using series 0 i hi)
  have hw := chamberLabels_sum (b-1) (d+c) (lam*H)
      hcW.1 f (F 2)
      (by intro i hi; simpa [chainLength,chainStart] using series 2 i hi)
  have hf := chamberLabels_sum (b-1) (d+c) (lam*(2^c-1-H))
      hcW.2.1 f (F 2)
      (by intro i hi; simpa [chainLength,chainStart] using series 2 i hi)
  have hl := chamberLabels_sum (b-1) (d+c) (lam-1)
      hcW.2.2 f (F 2)
      (by intro i hi; simpa [chainLength,chainStart] using series 2 i hi)
  have hv := full 1
  have hx := full 3
  change ((P 0).map f).sum=((2^(d-1)-1-u:ℕ):ℤ)*F 0 ∧
    ((P 1).map f).sum=(lam*H:ℤ)*F 2 ∧
    ((P 2).map f).sum=((lam*(2^c-1-H):ℕ):ℤ)*F 2+
      ((2^(a-1)-1:ℕ):ℤ)*F 3+(u:ℤ)*F 0 ∧
    ((P 3).map f).sum=((2^(c-1)-1:ℕ):ℤ)*F 1+((lam-1:ℕ):ℤ)*F 2
  simp only [chainLength,chainStart] at hx hv
  rw [←chamberLabels_full] at hx hv
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp only [P,bank,List.map_append,List.sum_append,huq,hw,hf,huu,hl,hx,hv,hrest]
  all_goals push_cast
  all_goals ring


private theorem stock_double (n : ℕ) (hn : 1≤n) :
    2*((2^(n-1)-1:ℕ):ℤ)=(2:ℤ)^n-2 := by
  have hpos := Nat.two_pow_pos (n-1)
  rw [Nat.cast_sub (by omega)]
  push_cast
  conv_rhs => rw [show n=(n-1)+1 by omega,pow_succ]
  ring

private theorem bank_double_masses (a b c d u H : ℕ)
    (ha : 2≤a) (had : a<d) (hdc : d<c) (hcb : c<b)
    (hu : u=0 ∨ u=1 ∨ u=2) (hH : H<2^c) (side : Bool) :
    let F := if side then newBase a b c d else base a b c d
    let f := if side then newValue a b c d else oldValue a b c d
    let P := bank a b c d u H
    let la : ℤ := 2^(b-c-1)
    2*((P 0).map f).sum=((2:ℤ)^d-2-2*(u:ℤ))*F 0 ∧
    2*((P 1).map f).sum=2*la*(H:ℤ)*F 2 ∧
    2*((P 2).map f).sum=2*la*((2:ℤ)^c-1-(H:ℤ))*F 2+
      ((2:ℤ)^a-2)*F 3+2*(u:ℤ)*F 0 ∧
    2*((P 3).map f).sum=((2:ℤ)^c-2)*F 1+2*(la-1)*F 2 := by
  dsimp only
  let F := if side then newBase a b c d else base a b c d
  let f := if side then newValue a b c d else oldValue a b c d
  have hm := bank_masses a b c d u H ha had hdc hcb hu hH side
  dsimp only at hm
  have hu_stock : u≤2^(d-1)-1 := by have := u_capacity d u (by omega) hu; omega
  have hHstock : H≤2^c-1 := by omega
  have hla : 1≤(2^(b-c-1):ℕ) := by have := Nat.two_pow_pos (b-c-1); omega
  have hd := stock_double d (by omega)
  have hc := stock_double c (by omega)
  have hx := stock_double a (by omega)
  have hucast : ((2^(d-1)-1-u:ℕ):ℤ)=((2^(d-1)-1:ℕ):ℤ)-(u:ℤ) := by
    exact Nat.cast_sub hu_stock
  have hfcast : ((2^(b-c-1)*(2^c-1-H):ℕ):ℤ)=
      (2:ℤ)^(b-c-1)*((2:ℤ)^c-1-(H:ℤ)) := by
    rw [Nat.cast_mul,Nat.cast_sub hHstock,
      Nat.cast_sub (by have := Nat.two_pow_pos c; omega)]
    simp only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hlcast : ((2^(b-c-1)-1:ℕ):ℤ)=(2:ℤ)^(b-c-1)-1 := by
    rw [Nat.cast_sub hla]
    simp only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hm.1,hucast]
    linear_combination (F 0)*hd
  · rw [hm.2.1]
    push_cast
    ring
  · rw [hm.2.2.1,hfcast]
    linear_combination (F 3)*hx
  · rw [hm.2.2.2,hlcast]
    linear_combination (F 1)*hc

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap

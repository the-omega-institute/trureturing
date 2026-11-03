/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/ModerateNear
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: ThirdPeakEqualOuter ModerateNear for the complete original physical family. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateHigh

/-! ThirdPeakEqualOuter: ModerateNear. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private A B L K SU SV SW Window
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private F G nextF nextG positive_rows native_rows stock_nonnegative Joint
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source
open private FirstTwoWindows moderate_W moderate_near_selector
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateArithmetic
open private moderate_realize
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModeratePhysical
open private moderate_parameters
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateHigh
open private full stock complement terminals stock_split canonical_inventory stock_mass complement_mass
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private chainLength chainStart oldValue newValue
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def upperV (a c p : ℕ) : List ℕ := chamberLabels (c-2) (a+1) p
private def upperComplement (a c p : ℕ) : List ℕ := upperV a c ((2^(c-2)-1) ^^^ p)
private def moderateNearBanks (a b c r p : ℕ) : Fin 4 → List ℕ :=
  ![complement a b c a 0 (r-1)++upperV a c p,
    stock a b c a 0 (r-1)++upperComplement a c p,
    stock a b c a 2 (full a b c a 2)++[a],
    stock a b c a 3 (full a b c a 3)]

private theorem upper_split (a c p : ℕ) :
    (upperComplement a c p++upperV a c p).Perm (upperV a c (2^(c-2)-1)) := by
  apply chamberLabels_split
  intro e he _
  simp [Nat.testBit_two_pow_sub_one,he]

private theorem near_V_inventory (a b c : ℕ) (hc : 2 ≤ c) :
    [a]++upperV a c (2^(c-2)-1)=stock a b c a 1 (full a b c a 1) := by
  simp only [upperV,stock,full,chainLength,chainStart,chamberLabels_full,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  have hh := List.range'_append_1 (s:=a) (m:=1) (n:=c-2)
  simpa only [List.range'_one,show 1+(c-2)=c-1 by omega] using hh

private theorem moderate_near_inventory (a b c r p : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    let P := moderateNearBanks a b c r p
    (P 0++[a-1]++P 1++[a+c-1]++P 2++[a+c+b-1]++P 3++[a+b+c+a-1]).Perm
      (List.range (a+b+c+a)) := by
  have hu := Multiset.coe_eq_coe.mpr (stock_split a b c a 0 (r-1))
  have hv := Multiset.coe_eq_coe.mpr (upper_split a c p)
  have hall := congrArg (fun l : List ℕ => (l:Multiset ℕ)) (near_V_inventory a b c hc)
  simp only [←Multiset.coe_add] at hu hv hall
  dsimp only
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b c a ha hb hc ha]
  dsimp [moderateNearBanks]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←hu,←hall,←hv]
  simp only [Multiset.coe_singleton]
  ac_rfl

private theorem moderate_near_positive (a b c r p : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (j : Fin 4) (i : ℕ) (hi : i ∈ moderateNearBanks a b c r p j) :
    0 ≤ oldValue a b c a i ∧ 0 ≤ newValue a b c a i := by
  have upper_good (mask i : ℕ) (hi : i ∈ upperV a c mask) :
      i ∈ stock a b c a 1 (full a b c a 1) := by
    obtain ⟨e,he,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp hi
    rw [stock,full,chamberLabels_full]
    simp only [chainLength,chainStart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    apply List.mem_range'_1.mpr
    omega
  have zero_good : a ∈ stock a b c a 1 (full a b c a 1) := by
    rw [stock,full,chamberLabels_full]
    simp only [chainLength,chainStart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    apply List.mem_range'_1.mpr
    omega
  fin_cases j <;> dsimp [moderateNearBanks,upperComplement] at hi
  all_goals try (rcases List.mem_append.mp hi with hi|hi)
  all_goals first
    | exact stock_nonnegative a b c ha hb hc _ _ i hi
    | exact stock_nonnegative a b c ha hb hc 1 _ i (upper_good _ i hi)
    | rw [List.mem_singleton.mp hi]; exact stock_nonnegative a b c ha hb hc 1 _ a zero_good

private theorem moderate_near_masses (a b c r p : ℕ) (hc : 2 ≤ c)
    (hr : 1 ≤ r) (hrcap : r ≤ 2^(a-1)) (hp : p < 2^(c-2))
    (f : ℕ → ℤ) (H : Fin 4 → ℤ)
    (hf : ∀ j : Fin 4, ∀ e < chainLength a b c a j-1,
      f (chainStart b c a j+e)=2^e*H j) :
    let C := fun j : Fin 4 => (full a b c a j : ℤ)
    let P := moderateNearBanks a b c r p
    ((P 0).map f).sum=(C 0-(r-1:ℤ))*H 0+2*(p:ℤ)*H 1 ∧
    ((P 1).map f).sum=(r-1:ℤ)*H 0+(C 1-1-2*(p:ℤ))*H 1 ∧
    ((P 2).map f).sum=C 2*H 2+H 1 ∧
    ((P 3).map f).sum=C 3*H 3 := by
  have hfull (j : Fin 4) : full a b c a j < 2^(chainLength a b c a j-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c a j-1); omega
  have hru : r-1 < 2^(chainLength a b c a 0-1) := by simp [chainLength]; omega
  have ur := stock_mass a b c a 0 (r-1) hru f H hf
  have uc := complement_mass a b c a 0 (r-1) hru f H hf
  have wf := stock_mass a b c a 2 _ (hfull 2) f H hf
  have xf := stock_mass a b c a 3 _ (hfull 3) f H hf
  have v0 : f a=H 1 := by
    simpa only [chainStart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Nat.add_zero,pow_zero,one_mul] using hf 1 0 (by simp [chainLength]; omega)
  have upper_mass (q : ℕ) (hq : q < 2^(c-2)) :
      ((upperV a c q).map f).sum=2*(q:ℤ)*H 1 := by
    have hm := chamberLabels_sum (c-2) (a+1) q hq f (2*H 1) (by
      intro e he
      have hrow := hf 1 (e+1) (by simp [chainLength]; omega)
      simpa only [chainStart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,show a+(e+1)=a+1+e by omega,pow_succ,mul_assoc] using hrow)
    simpa only [upperV,mul_assoc,mul_comm,mul_left_comm] using hm
  have up := upper_mass p hp
  have ufull := upper_mass (2^(c-2)-1) (by have := Nat.two_pow_pos (c-2); omega)
  have usplit := ((upper_split a c p).map f).sum_eq
  simp only [List.map_append,List.sum_append,up,ufull] at usplit
  have hC : 2*((2^(c-2)-1:ℕ):ℤ)=(full a b c a 1:ℤ)-1 := by
    have hpw : (2:ℤ)^(c-1)=2*(2:ℤ)^(c-2) := by
      conv_lhs => rw [show c-1=(c-2)+1 by omega,pow_succ]
      ring
    simp only [full,chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Nat.cast_sub (show 1 ≤ 2^(c-2) by have := Nat.two_pow_pos (c-2); omega),
      Nat.cast_sub (show 1 ≤ 2^(c-1) by have := Nat.two_pow_pos (c-1); omega),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    omega
  have ucV : ((upperComplement a c p).map f).sum=((full a b c a 1:ℤ)-1-2*(p:ℤ))*H 1 := by
    have hmul := congrArg (fun t : ℤ => t*H 1) hC
    nlinarith only [usplit,hmul]
  dsimp only [moderateNearBanks]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
    ur,uc,wf,xf,up,ucV,v0,Nat.cast_sub hr,Nat.cast_one]
  trivial

set_option maxHeartbeats 1800000 in
private theorem moderate_near_joint (a b c : ℕ) (hb : 2 ≤ b) (hba : a=b+1)
    (hac : a < c) (hmod : c ≤ a+b-2) : Joint a b c := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let m : ℤ := 2^(c-a)
  obtain ⟨hy,hx2,hm,hmy,hmcase,hz⟩ := moderate_parameters a b c hb (by omega) hac hmod
  change z=m*x at hz
  have hx : x=2*y := by dsimp [x,y]; rw [hba,pow_succ]; ring
  obtain ⟨r,hr,hry,hw⟩ := moderate_near_selector y m hy hm hmy
  let rn := r.toNat
  have er : (rn:ℤ)=r := Int.toNat_of_nonneg (by omega)
  let p : ℤ := (r*m-2)/2
  have hmhalf : m=2*(2:ℤ)^(c-a-1) := by
    dsimp [m]
    conv_lhs => rw [show c-a=(c-a-1)+1 by omega,pow_succ]
    ring
  have hpar : r*m=2*(r*(2:ℤ)^(c-a-1)) := by rw [hmhalf]; ring
  have hpval : 2*p=r*m-2 := by dsimp [p]; omega
  have hp0 : 0 ≤ p := by have := mul_le_mul hr hm (by omega) (by omega); nlinarith only [this,hpval]
  let pn := p.toNat
  have ep : (pn:ℤ)=p := Int.toNat_of_nonneg hp0
  have hrcap : rn ≤ 2^(a-1) := by
    have he : a-1=b := by omega
    rw [he]
    have : (rn:ℤ) ≤ (2:ℤ)^b := by rw [er]; exact le_of_lt hry
    exact_mod_cast this
  have hpcap : pn < 2^(c-2) := by
    have hrr := mul_lt_mul_of_pos_right hry (show 0 < m by omega)
    have hz4 : z=4*(2:ℤ)^(c-2) := by
      dsimp [z]
      conv_lhs => rw [show c=(c-2)+2 by omega,pow_add]
      norm_num
      ring
    have hzy : z=2*m*y := by rw [hz,hx]; ring
    have : (pn:ℤ) < (2:ℤ)^(c-2) := by rw [ep]; nlinarith only [hrr,hpval,hz4,hzy]
    exact_mod_cast this
  let early := decide (m=2)
  let P := moderateNearBanks a b c rn pn
  let C := fun j : Fin 4 => (full a b c a j : ℤ)
  let E := r*(m*B x y-A x y z)-B x y
  let Ep := 2*E-r*m+1
  let R := L x z-A x y z-B x y
  let Rp := 2*R-z
  have wfirst : FirstTwoWindows x y z E Ep R Rp := by simpa only [E,Ep,R,Rp,hz,hx] using hw
  obtain ⟨wW,wWn⟩ := moderate_W x y m hy hx2 hmcase
  have wW' : Window (K x y z-A x y z) (K x y z) := by simpa only [hz] using wW
  have wWn' : Window (SW x y z-2*A x y z+(if early then A x y z else 0)) (SW x y z) := by
    simpa [early,hz] using wWn
  have mo := moderate_near_masses a b c rn pn (by omega)
    (by exact_mod_cast (show (1:ℤ) ≤ rn by omega)) hrcap hpcap (oldValue a b c a) (F x y z)
    (positive_rows a b c (by omega) hb (by omega)).1
  have mn := moderate_near_masses a b c rn pn (by omega)
    (by exact_mod_cast (show (1:ℤ) ≤ rn by omega)) hrcap hpcap (newValue a b c a) (G x y z)
    (positive_rows a b c (by omega) hb (by omega)).2
  rw [er,ep] at mo mn
  have nu := native_rows a b c (by omega) hb (by omega) 0
  have nv := native_rows a b c (by omega) hb (by omega) 1
  have nw := native_rows a b c (by omega) hb (by omega) 2
  dsimp only [F,G,nextF,nextG,terminals] at mo mn nu nv nw
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at mo mn nu nv nw
  change ((P 0).map (oldValue a b c a)).sum=(C 0-(r-1))*A x y z+2*p*B x y ∧
    ((P 1).map (oldValue a b c a)).sum=(r-1)*A x y z+(C 1-1-2*p)*B x y ∧
    ((P 2).map (oldValue a b c a)).sum=C 2*L x z+B x y ∧
    ((P 3).map (oldValue a b c a)).sum=C 3*K x y z at mo
  change ((P 0).map (newValue a b c a)).sum=(C 0-(r-1))*(2*A x y z)+2*p*SU x y ∧
    ((P 1).map (newValue a b c a)).sum=(r-1)*(2*A x y z)+(C 1-1-2*p)*SU x y ∧
    ((P 2).map (newValue a b c a)).sum=C 2*SV x z+SU x y ∧
    ((P 3).map (newValue a b c a)).sum=C 3*SW x y z at mn
  apply moderate_realize a b c (by omega) hb (by omega) P early E Ep R Rp
    (moderate_near_inventory a b c rn pn (by omega) hb (by omega))
    (moderate_near_positive a b c rn pn (by omega) hb (by omega))
  · dsimp [E]
    have hpB := congrArg (fun t : ℤ => t*B x y) hpval
    nlinarith only [mo.1,nu.1,hpB]
  · dsimp [Ep,E,SU] at *
    have hpU := congrArg (fun t : ℤ => t*SU x y) hpval
    dsimp [SU] at hpU
    nlinarith only [mn.1,nu.2.1,hpU]
  · dsimp [E,R]
    have hpB := congrArg (fun t : ℤ => t*B x y) hpval
    nlinarith only [mo.2.1,nu.1,nv.1,hpB]
  · dsimp [Ep,E,Rp,R,SU,SV] at *
    have hpU := congrArg (fun t : ℤ => t*SU x y) hpval
    dsimp [SU] at hpU
    nlinarith only [mn.2.1,nu.2.1,nv.2.1,hpU]
  · dsimp [R]; nlinarith only [mo.2.2.1,nw.1]
  · dsimp [Rp,R,SU,SV] at *; nlinarith only [mn.2.2.1,nw.2.1]
  · exact wfirst
  · exact wW'
  · exact wWn'

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter

/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Schedule
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: The ceiling selector gives both complete physical source orders at literal cut zero. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Selection
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Source
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical

/-! The ceiling selector gives both complete physical source orders at literal cut zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open private DD AA BB LL MM NN BBn LLn MMn EE dyadicT dyadicZ dyadicY
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Algebra
open private SeamBounds chooseH roundDelta secondNew selection_bounds
  SeamBounds.H_nonneg SeamBounds.H_upper
  SeamBounds.first_old_nonneg SeamBounds.first_old_cap
  SeamBounds.delta_nonneg SeamBounds.second_old_cap
  SeamBounds.third_old_nonneg SeamBounds.third_old_cap
  SeamBounds.fresh_cap SeamBounds.first_new_nonneg
  SeamBounds.first_new_cap SeamBounds.second_new_nonneg
  SeamBounds.second_new_cap SeamBounds.third_new_nonneg
  SeamBounds.third_new_cap
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Selection
open private MaskPartition native_partition
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks
open private bank terminal word bank_inventory bank_good bank_masses
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Source
open private size seed sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue source_signs negatives chain_values new_base_bounds source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private inserted_perm from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option maxHeartbeats 3000000 in
private theorem joint_construction (a b c d : ℕ)
    (ha : 2 ≤ a) (had : a+1 ≤ d) (hdc : a+d+1 ≤ c) (hcb : c+1 ≤ b) :
    ∃ sigma : List (Fin (a+b+c+d)),
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma 0) := by
  classical
  have hb : 2 ≤ b := by omega
  have hc : 2 ≤ c := by omega
  have hd : 2 ≤ d := by omega
  let k := a+b+c+d
  let seedN := 1+2^a+2^(a+b)+2^(a+b+c)
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let t : ℤ := 2^d
  let R : ℤ := 2^(d-a-1)
  let Z : ℤ := 2^(c-a-d-1)
  let lam : ℤ := 2^(b-c-1)
  let A := AA x y z
  let B := BB x y t
  let L := LL x z t
  let M := MM y z t
  let D := DD y z
  let Bn := BBn x y t
  let Ln := LLn x z t
  let Mn := MMn y z t
  let N := NN x y z t
  let f := oldValue a b c d
  let g := newValue a b c d
  have hx : 4 ≤ x := by
    dsimp [x]
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) ha
  have hR : 1 ≤ R := by dsimp [R]; exact one_le_pow₀ (by norm_num)
  have hZ : 1 ≤ Z := by dsimp [Z]; exact one_le_pow₀ (by norm_num)
  have hlam : 1 ≤ lam := by dsimp [lam]; exact one_le_pow₀ (by norm_num)
  have ht : t=dyadicT x R := by
    calc
      t=(2:ℤ)^(a+1)*2^(d-a-1) := by
        dsimp [t]
        rw [←pow_add]
        congr 1
        omega
      _=dyadicT x R := by dsimp [dyadicT,x,R]; rw [pow_succ]; ring
  have hz : z=dyadicZ x R Z := by
    change z=2*x*dyadicT x R*Z
    rw [←ht]
    calc
      z=(2:ℤ)^(a+d+1)*2^(c-a-d-1) := by
        dsimp [z]
        rw [←pow_add]
        congr 1
        omega
      _=2*x*t*Z := by dsimp [x,t,Z]; rw [pow_succ,pow_add]; ring
  have hy : y=dyadicY x R Z lam := by
    change y=2*dyadicZ x R Z*lam
    rw [←hz]
    calc
      y=(2:ℤ)^(c+1)*2^(b-c-1) := by
        dsimp [y]
        rw [←pow_add]
        congr 1
        omega
      _=2*z*lam := by dsimp [z,lam]; rw [pow_succ]; ring
  have bounds : SeamBounds x y z t lam := by
    rw [hy,hz,ht]
    exact selection_bounds x R Z lam hx hR hZ hlam

  -- The signed bounds above are established before the first Int.toNat.
  let HZ := chooseH x y z t lam
  have H0 : 0 ≤ HZ := (SeamBounds.H_nonneg bounds)
  have Hupper : HZ ≤ z-1 := (SeamBounds.H_upper bounds)
  let H := HZ.toNat
  have eH : (H:ℤ)=HZ := Int.toNat_of_nonneg H0
  have Hcap : H ≤ 2^c-1 := by
    have hlt : (H:ℤ)<(2:ℤ)^c := by rw [eH]; change HZ<z; omega
    have hltN : H<2^c := by exact_mod_cast hlt
    omega
  let s := b-c-1
  let lamN := 2^s
  let h := lamN*H
  let m := (2^c-1)*lamN
  let low := lamN-1
  have masks := native_partition c s H Hcap
  change (m ^^^ h)+h=m ∧ MaskPartition (c+s) h (m ^^^ h) low at masks
  have part : MaskPartition (b-1) h (m ^^^ h) low := by
    simpa only [show c+s=b-1 by dsimp [s]; omega] using masks.2
  have elam : (lamN:ℤ)=lam := by dsimp [lamN,s,lam]
  have eh : (h:ℤ)=lam*HZ := by simp only [h,Nat.cast_mul,elam,eH]
  have em : (m:ℤ)=(z-1)*lam := by
    simp only [m,Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ (2:ℕ)^c by have := Nat.two_pow_pos c; omega),
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,elam,z]
  have elow : (low:ℤ)=lam-1 := by
    dsimp [low]
    rw [Nat.cast_sub (by dsimp [lamN]; have := Nat.two_pow_pos s; omega),elam]
    norm_num
  have eqmask : ((m ^^^ h:ℕ):ℤ)=(z-1)*lam-lam*HZ := by
    have hs := congrArg (fun n : ℕ => (n:ℤ)) masks.1
    push_cast at hs
    rw [eh,em] at hs
    linarith
  let delta := roundDelta x y z t lam
  have deltaeq : delta=2*lam*L*HZ-EE x y z t := rfl
  have Eeq : EE x y z t=2*N-M-(t-1)*A := rfl
  have relU : t*A=N+B := by dsimp [t,A,N,B,AA,BB,NN,DD]; ring

  have hbase : base a b c d=![A,B,L,M] := by
    funext i
    fin_cases i <;> dsimp [base,A,B,L,M,AA,BB,LL,MM,DD,x,y,z,t] <;> ring
  have hnewbase : newBase a b c d=![2*A,Bn,Ln,Mn] := by
    funext i
    fin_cases i <;> dsimp [newBase,charge,Bn,Ln,Mn,BBn,LLn,MMn,D,DD,y,z]
    all_goals rw [hbase] <;> dsimp <;> ring
  have hseed : (seedN:ℤ)=A := by
    dsimp [seedN,A,AA,DD,x,y,z]
    push_cast
    simp only [pow_add]
    ring
  have hsourceMod : sourceMod a b c d=N := by dsimp [sourceMod,N,NN,x,y,z,t]
  have hmod : modulus k=N := by dsimp [modulus,k,N,NN,x,y,z,t]; ring
  have hmodn : modulus (k+1)=2*N+1 := by dsimp [modulus,k,N,NN,x,y,z,t]; ring
  let P := bank a b c d h m low
  let T := terminal a b c d
  let l := word a b c d h m low
  have hp : l.Perm (List.range k) := bank_inventory a b c d h m low ha hb hc hd part
  have pos (j : Fin 4) (i : ℕ) (hi : i∈P j) : 0 ≤ f i ∧ 0 ≤ g i := by
    have good := bank_good a b c d h m low ha hb hc hd j i hi
    have signs := source_signs a b c d ha hb hc hd i good.1
    rw [if_neg good.2] at signs
    exact ⟨signs.1.le,signs.2.le⟩
  have masses := bank_masses a b c d h m low ha hb hc hd part
  have mo := masses false
  have mg := masses true
  dsimp only [Bool.false_eq_true,ite_false,ite_true] at mo mg
  rw [hbase] at mo
  rw [hnewbase] at mg
  simp only [chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,eh,elow,eqmask] at mo mg
  let C := fun n : ℕ => (((2^(n-1)-1:ℕ):ℤ))
  change ((P 0).map f).sum=C d*A ∧
    ((P 1).map f).sum=(lam*HZ)*L ∧
    ((P 2).map f).sum=((z-1)*lam-lam*HZ)*L+C a*M ∧
    ((P 3).map f).sum=C c*B+(lam-1)*L at mo
  change ((P 0).map g).sum=C d*(2*A) ∧
    ((P 1).map g).sum=(lam*HZ)*Ln ∧
    ((P 2).map g).sum=((z-1)*lam-lam*HZ)*Ln+C a*Mn ∧
    ((P 3).map g).sum=C c*Bn+(lam-1)*Ln at mg
  have nat0 := native_masses a b c d ha hb hc hd 0
  have nat1 := native_masses a b c d ha hb hc hd 1
  have nat2 := native_masses a b c d ha hb hc hd 2
  have nat3 := native_masses a b c d ha hb hc hd 3
  have eu : 0+(d-1)=T 2 := by dsimp [T,terminal]; omega
  have ev : d+(c-1)=T 3 := by dsimp [T,terminal]; omega
  have ew : d+c+(b-1)=T 0 := by dsimp [T,terminal]; omega
  have ex : d+c+b+(a-1)=T 1 := by dsimp [T,terminal]; omega
  simp only [chainLength,chainStart,nextBase,nextNewBase,hbase,hnewbase,hsourceMod,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply,eu,ev,ew,ex] at nat0 nat1 nat2 nat3
  change C d*A+f (T 2)=B-A ∧ C d*(2*A)+g (T 2)=Bn-2*A ∧
    2*f (T 2)=B-N ∧ 2*g (T 2)=Bn-(2*N+1) at nat0
  change C c*B+f (T 3)=L-B ∧ C c*Bn+g (T 3)=Ln-Bn ∧
    2*f (T 3)=L-N ∧ 2*g (T 3)=Ln-(2*N+1) at nat1
  change C b*L+f (T 0)=M-L ∧ C b*Ln+g (T 0)=Mn-Ln ∧
    2*f (T 0)=M-N ∧ 2*g (T 0)=Mn-(2*N+1) at nat2
  change C a*M+f (T 1)=A-M ∧ C a*Mn+g (T 1)=A-Mn ∧
    2*f (T 1)=A-N ∧ 2*g (T 1)=A-(2*N+1) at nat3

  -- These equations refer to the actual source sums on P, not abstract packets.
  have os0 : 2*(((P 0).map f).sum+f (T 0))=B+M-2*A := by
    nlinarith only [mo.1,nat0.1,nat0.2.2.1,nat2.2.2.1]
  have os1 : 2*(((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1))=delta := by
    nlinarith only [os0,mo.2.1,nat3.2.2.1,relU,deltaeq,Eeq]
  have ns0 : 2*(A+((P 0).map g).sum+g (T 0))=2*B-2*A+Mn-1 := by
    have bn : Bn=2*B-1 := rfl
    nlinarith only [mg.1,nat0.2.1,nat0.2.2.2,nat2.2.2.2,bn]
  have ns1 : 2*(A+((P 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1))=
      secondNew x y z t lam := by
    have ln : Ln=2*L-z-1 := rfl
    have mn : Mn=2*M-D := rfl
    have mass1 := mg.2.1
    rw [ln] at mass1
    change 2*(A+((P 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1))=
      2*delta+A-D-2*(lam*HZ)*(z+1)-2
    nlinarith only [ns0,mass1,nat3.2.2.2,mn,relU,deltaeq,Eeq]
  have totals := source_totals a b c d ha hb hc hd
  have hfzero : (l.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hear : g k=A := by simpa [size,hbase] using totals.2.2
  have hgzero : A+(l.map g).sum=0 := by
    have hh := (hp.map g).sum_eq.trans totals.2.1
    rw [hbase] at hh
    change (l.map g).sum=-A at hh
    omega
  have totalold : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2)+((P 3).map f).sum+f (T 3)=0 := by
    simpa only [l,word,P,T,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      List.map_nil,List.sum_nil,add_zero,add_assoc] using hfzero
  have totalnew : A+((P 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1)+
      ((P 2).map g).sum+g (T 2)+((P 3).map g).sum+g (T 3)=0 := by
    simpa only [l,word,P,T,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      List.map_nil,List.sum_nil,add_zero,add_assoc] using hgzero
  have os2 : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2)=B-lam*L := by
    nlinarith only [totalold,mo.2.2.2,nat1.1]
  have ns2 : A+((P 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1)+
      ((P 2).map g).sum+g (T 2)=Bn-lam*Ln := by
    nlinarith only [totalnew,mg.2.2.2,nat1.2.1]
  have half (n : ℕ) (hn : 1 ≤ n) : (2:ℤ)^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
    ring
  have hNodd : N%2=1 := by
    have ht2 := half d (by omega)
    have eqn : N=2*((2:ℤ)^a*2^b*2^c*2^(d-1)-1)+1 := by
      dsimp [N,NN,x,y,z,t]
      rw [ht2]
      ring
    omega
  have basebounds := (chain_values a b c d ha hb hc hd).1
  have newbounds := new_base_bounds a b c d ha hb hc hd
  have hA : 1 ≤ A ∧ A<N := by simpa [hbase,hsourceMod] using basebounds 0
  have hN0 : 0 ≤ N := by omega
  have lastold : 0 ≤ -f (T 3) ∧ -f (T 3) ≤ N/2 := by
    have hL : 1 ≤ L ∧ L<N := by simpa [hbase,hsourceMod] using basebounds 2
    omega
  have lastnew : 0 ≤ -g (T 3) ∧ -g (T 3) ≤ N := by
    have hLn : 1 ≤ Ln ∧ Ln<2*N+1 := by simpa [hnewbase,hsourceMod] using newbounds 2
    omega
  have oldstrip : InStrip f (N/2) 0 l := by
    change InStrip f (N/2) 0 (P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3])
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) le_rfl
    · constructor <;> nlinarith only [os0,nat2.2.2.1,(SeamBounds.first_old_nonneg bounds),
        (SeamBounds.first_old_cap bounds),hNodd,Int.emod_add_mul_ediv N 2]
    · constructor <;> nlinarith only [os1,nat3.2.2.1,(SeamBounds.delta_nonneg bounds),
        (SeamBounds.second_old_cap bounds),hNodd,Int.emod_add_mul_ediv N 2]
    · constructor <;> nlinarith only [os2,nat0.2.2.1,(SeamBounds.third_old_nonneg bounds),
        (SeamBounds.third_old_cap bounds),hNodd,Int.emod_add_mul_ediv N 2]
    · exact lastold
    · simpa [l,word,P,T] using hfzero
  have initial : 0 ≤ A ∧ A ≤ N := ⟨by omega,(SeamBounds.fresh_cap bounds)⟩
  have newtail : InStrip g N A l := by
    change InStrip g N A (P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3])
    apply four_strip g (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) N A
      (fun i hi => (pos 0 i hi).2) (fun i hi => (pos 1 i hi).2)
      (fun i hi => (pos 2 i hi).2) (fun i hi => (pos 3 i hi).2) initial.1
    · constructor <;> nlinarith only [ns0,nat2.2.2.2,(SeamBounds.first_new_nonneg bounds),(SeamBounds.first_new_cap bounds)]
    · constructor <;> nlinarith only [ns1,nat3.2.2.2,(SeamBounds.second_new_nonneg bounds),(SeamBounds.second_new_cap bounds)]
    · constructor <;> nlinarith only [ns2,nat0.2.2.2,(SeamBounds.third_new_nonneg bounds),(SeamBounds.third_new_cap bounds)]
    · exact lastnew
    · simpa [l,word,P,T] using hgzero
  -- Install the independently proved fresh-prefix gate as the tail's first bound.
  have checkedTail : InStrip g N A l := by
    cases hl : l with
    | nil => exact initial
    | cons i xs =>
      rw [hl] at newtail
      exact ⟨initial.1,initial.2,newtail.2.2⟩
  have newstrip : InStrip g N 0 (k::l) := by
    refine ⟨le_rfl,hN0,?_⟩
    simpa only [hear,zero_add] using checkedTail
  have hpnew : (k::l).Perm (List.range (k+1)) := by
    simpa only [List.nil_append] using inserted_perm k [] l (by simpa only [List.nil_append] using hp)
  have fform : f=fun i => centered N ((2:ℤ)^i*A) := by
    funext i
    dsimp [f,oldValue]
    rw [hsourceMod,hbase]
    rfl
  have gform : g=fun i => centered (2*N+1) ((2:ℤ)^i*(2*A)) := by
    funext i
    dsimp [g,newValue]
    rw [hsourceMod,hbase]
    rfl
  refine ⟨l.map (label k (by dsimp [k]; omega)),?_,?_⟩
  · apply lift_order k seedN (by dsimp [k]; omega) l hp
    · simpa only [fform,hmod,hseed] using oldstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k seedN (by dsimp [k]; omega)
  · have hm := marked_word k 0 (by dsimp [k]; omega) [] l rfl (by simpa using hp)
    simp only [List.nil_append] at hm
    rw [hm]
    apply lift_order (k+1) (2*seedN) (by omega) (k::l) hpnew
    · have hs : ((2*seedN:ℕ):ℤ)=2*A := by push_cast; rw [hseed]
      simpa only [gform,hmodn,hs,show (2*N+1)/2=N by omega] using newstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seedN) (by dsimp [k]; omega)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap

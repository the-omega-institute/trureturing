/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-original-exponent-masses)
   mirror-E: none(waiver:private-consumed-original-exponent-masses)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Original powers identify every native submask and both physical mass rows. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Masks

/-! Rational coefficients avoid truncating divisions;
all actual label values and all physical prefix sums remain integers. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
open private branch route route_valid bitRange bitRange_mem bitRange_zero vbits wbits shift shift_range
  banks terminals word maskOf maskOf_append native_inventories
  NativePartition NativePartition.physical NativePartition.fits NativePartition.supports
  NativePartition.disjoint NativePartition.fullSupport NativePartition.counts
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Masks
open private A B L K SU SV SW rowBase rowHeads rowSeams reserve bankMasses window
  windows_I_one windows_I_many windows_II windows_III
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Arithmetic
open private chainStart chainLength
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def xval (a : ℕ) : ℚ := 2^a
private def rval (a d : ℕ) : ℚ := 2^(d-a)
private def sval (b d : ℕ) : ℚ := 2^(b-d)
private def qval (b c : ℕ) : ℚ := 2^(c-b)

private theorem power_coordinates (a b c d : ℕ) (had : a≤d) (hdb : d<b) (hbc : b<c) :
    (2:ℚ)^d=rval a d*xval a ∧
    (2:ℚ)^b=sval b d*rval a d*xval a ∧
    (2:ℚ)^c=qval b c*sval b d*rval a d*xval a := by
  have ht : (2:ℚ)^d=rval a d*xval a := by
    dsimp [rval,xval]
    rw [←pow_add]
    congr 1
    omega
  have hy : (2:ℚ)^b=sval b d*(2:ℚ)^d := by
    dsimp [sval]
    rw [←pow_add]
    congr 1
    omega
  have hz : (2:ℚ)^c=qval b c*(2:ℚ)^b := by
    dsimp [qval]
    rw [←pow_add]
    congr 1
    omega
  exact ⟨ht,by rw [hy,ht]; ring,by rw [hz,hy,ht]; ring⟩
private theorem half_power (n : ℕ) (hn : 1≤n) : (2:ℚ)^(n-1)=2^n/2 := by
  have he : (2:ℚ)^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
    ring
  linarith only [he]
private theorem quarter_power (n : ℕ) (hn : 2≤n) : (2:ℚ)^(n-2)=2^n/4 := by
  have he : (2:ℚ)^n=4*2^(n-2) := by
    conv_lhs => rw [show n=(n-2)+2 by omega,pow_add]
    norm_num
    ring
  linarith only [he]

private theorem range_weight_raw (lo n : ℕ) :
    (maskOf (List.range' lo n):ℚ)=(2:ℚ)^(lo+n)-2^lo := by
  induction n with
  | zero => simp [maskOf]
  | succ n ih =>
    rw [List.range'_1_concat,maskOf_append]
    rw [show maskOf [lo+n]=2^(lo+n) by simp [maskOf]]
    push_cast
    change (maskOf (List.range' lo n):ℚ)+(2:ℚ)^(lo+n)=2^(lo+(n+1))-2^lo
    rw [ih,show lo+(n+1)=(lo+n)+1 by omega,pow_succ]
    ring
private theorem range_weight (lo hi : ℕ) (h : lo≤hi) :
    (maskOf (bitRange lo hi):ℚ)=(2:ℚ)^hi-2^lo := by
  simpa only [bitRange,show lo+(hi-lo)=hi by omega] using range_weight_raw lo (hi-lo)
private theorem mask_nil : maskOf []=0 := rfl
private theorem mask_one (e : ℕ) : maskOf [e]=2^e := by simp [maskOf]
private theorem mask_cons (e : ℕ) (l : List ℕ) :
    maskOf (e::l)=2^e+maskOf l := by simp [maskOf]

set_option maxHeartbeats 2400000 in
/-- Exact masks in original V/W coordinates, not capacities. In particular W3
is h=3s/4-1 in I, W2 is p-h, q/2 is a single V bit, and r-2 has no low bit. -/
private theorem native_mask_values (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    let x:=xval a
    let r:=rval a d
    let s:=sval b d
    let q:=qval b c
    (∀ i : Fin 4, (maskOf (vbits mode b c i):ℚ)=
      (![q*s*r*x/2-q,0,if mode=0 ∨ mode=1 then 0 else q/2,
        if mode=0 ∨ mode=1 then q-1 else q/2-1] : Fin 4→ℚ) i) ∧
    (∀ i : Fin 4, (maskOf (wbits mode a b d i):ℚ)=
      (![0,s*r*x/2-(reserve mode r s+1),
        if mode=0 ∨ mode=1 then reserve mode r s-(3*s/4-1)
        else if mode=2 then r-2 else 0,
        if mode=0 ∨ mode=1 then 3*s/4-1 else 1] : Fin 4→ℚ) i) := by
  dsimp only
  have hp:=power_coordinates a b c d had hdb hbc
  fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Fin.mk.injEq,Fin.reduceEq] at hm
  all_goals constructor <;> intro i <;> fin_cases i
  all_goals norm_num [vbits,wbits,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Fin.mk.injEq,Fin.reduceEq,ite_true,ite_false,
    mask_nil,mask_one,mask_cons,maskOf_append,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
  all_goals simp (disch := omega) only [range_weight,half_power,quarter_power,
    pow_add,hp.1,hp.2.1,hp.2.2,reserve,Fin.reduceEq,ite_true,ite_false]
  all_goals dsimp only [xval,rval,sval,qval]
  all_goals first
    | (have er : d-a=0 := by omega
       have es : b-d=1 := by omega
       simp only [er,es,pow_zero,pow_one]
       ring)
    | (have er : d-a=0 := by omega
       simp only [er,pow_zero]
       ring)
    | (have es : b-d=1 := by omega
       simp only [es,pow_one]
       ring)
    | ring

private theorem original_windows (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    ∀ (side : Bool) (i : Fin 4),
      window (rowSeams mode (xval a) (rval a d) (sval b d) (qval b c) side i)
        (rowHeads (xval a) (rval a d) (sval b d) (qval b c) side i) := by
  have hx : (4:ℚ)≤xval a := by
    convert pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) ha using 1 <;> norm_num [xval]
  have hq : (2:ℚ)≤qval b c := by
    simpa [qval] using pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show 1≤c-b by omega)
  fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Fin.mk.injEq,Fin.reduceEq] at hm
  · have er : rval a d=1 := by simp [rval,show d-a=0 by omega]
    have hs : (4:ℚ)≤sval b d := by
      convert pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show 2≤b-d by omega) using 1 <;> norm_num [sval]
    rw [er]
    exact windows_I_one _ _ _ hx hs hq
  · have hr : (2:ℚ)≤rval a d := by
      simpa [rval] using pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show 1≤d-a by omega)
    have hs : (4:ℚ)≤sval b d := by
      convert pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show 2≤b-d by omega) using 1 <;> norm_num [sval]
    exact windows_I_many _ _ _ _ hx hr hs hq
  · have hr : (2:ℚ)≤rval a d := by
      simpa [rval] using pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show 1≤d-a by omega)
    have es : sval b d=2 := by simp [sval,show b-d=1 by omega]
    rw [es]
    exact windows_II _ _ _ hx hr hq
  · have er : rval a d=1 := by simp [rval,show d-a=0 by omega]
    have es : sval b d=2 := by simp [sval,show b-d=1 by omega]
    rw [er,es]
    exact windows_III _ _ hx hq

private theorem shift_mass (off : ℕ) (l : List ℕ) (f : ℕ→ℤ) (F : ℤ)
    (hf : ∀ e∈l, f (off+e)=(2:ℤ)^e*F) :
    ((shift off l).map f).sum=(maskOf l:ℤ)*F := by
  induction l with
  | nil => simp [shift,maskOf]
  | cons e l ih =>
    have he:=hf e (by simp)
    have ht:=ih (fun i hi => hf i (by simp [hi]))
    simp only [shift,List.map_cons,List.sum_cons] at ht ⊢
    rw [he,ht]
    change (2:ℤ)^e*F+(maskOf l:ℤ)*F=((2^e+maskOf l:ℕ):ℤ)*F
    push_cast
    ring

private theorem banks_masses (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode)
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ j : Fin 4, ∀ e<chainLength a b c d j-1,
      f (chainStart b c d j+e)=2^e*F j) :
    ∀ i : Fin 4, (((banks mode a b c d i).map f).sum:ℚ)=
      bankMasses mode (xval a) (rval a d) (sval b d) (qval b c) (fun j => (F j:ℚ)) i := by
  let V:=vbits mode b c
  let W:=wbits mode a b d
  have native:=native_inventories mode a b c d ha had hdb hbc hm
  have vfit (j : Fin 4) (e : ℕ) (he : e∈V j) : e<c-1 := by
    apply List.mem_range.mp
    apply (NativePartition.physical native.1).mem_iff.mp
    fin_cases j
    · simp only [List.mem_append]; exact Or.inl (Or.inl (by simpa [V,W] using he))
    · simpa [V,vbits] using he
    · simp only [List.mem_append]; exact Or.inl (Or.inr (by simpa [V,W] using he))
    · simp only [List.mem_append]; exact Or.inr (by simpa [V,W] using he)
  have wfit (j : Fin 4) (e : ℕ) (he : e∈W j) : e<b-1 := by
    apply List.mem_range.mp
    apply (NativePartition.physical native.2).mem_iff.mp
    fin_cases j
    · fin_cases mode <;> simpa [W,wbits] using he
    · simp only [List.mem_append]; exact Or.inl (Or.inl (by simpa [V,W] using he))
    · simp only [List.mem_append]; exact Or.inl (Or.inr (by simpa [V,W] using he))
    · simp only [List.mem_append]; exact Or.inr (by simpa [V,W] using he)
  have mv (i : Fin 4) : ((shift d (V i)).map f).sum=(maskOf (V i):ℤ)*F 1 := by
    apply shift_mass
    intro e he
    simpa [chainStart,chainLength] using hf 1 e (by simp [chainLength]; exact vfit i e he)
  have mw (i : Fin 4) : ((shift (d+c) (W i)).map f).sum=(maskOf (W i):ℤ)*F 2 := by
    apply shift_mass
    intro e he
    simpa [chainStart,chainLength] using hf 2 e (by simp [chainLength]; exact wfit i e he)
  have mu : ((List.range (d-1)).map f).sum=(maskOf (List.range (d-1)):ℤ)*F 0 := by
    simpa [shift] using shift_mass 0 (List.range (d-1)) f (F 0)
      (fun e he => by simpa [chainStart] using hf 0 e (by simpa [chainLength] using List.mem_range.mp he))
  have mx : ((List.range' (d+c+b) (a-1)).map f).sum=(maskOf (List.range (a-1)):ℤ)*F 3 := by
    rw [←shift_range (d+c+b) (a-1)]
    apply shift_mass
    intro e he
    simpa [chainStart] using hf 3 e (by simpa [chainLength] using List.mem_range.mp he)
  have masks:=native_mask_values mode a b c d ha had hdb hbc hm
  have hp:=power_coordinates a b c d had hdb hbc
  have uval : (maskOf (List.range (d-1)):ℚ)=rval a d*xval a/2-1 := by
    rw [←bitRange_zero,range_weight 0 (d-1) (by omega),half_power d (by omega),hp.1]
    norm_num
  have xval' : (maskOf (List.range (a-1)):ℚ)=xval a/2-1 := by
    rw [←bitRange_zero,range_weight 0 (a-1) (by omega),half_power a (by omega)]
    simp [xval]
  intro i
  fin_cases i <;> simp only [banks,bankMasses,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  all_goals simp only [List.map_append,List.sum_append,mv,mw,mu,mx,Int.cast_add,
    Int.cast_mul,Int.cast_natCast,masks.1,masks.2,uval,xval',V,W,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  all_goals split_ifs <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail

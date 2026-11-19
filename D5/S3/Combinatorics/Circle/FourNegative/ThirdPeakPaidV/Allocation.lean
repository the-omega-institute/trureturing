/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Allocation
   generality: I
   mirror-B: none(waiver:private-consumed-unbounded-allocation)
   mirror-E: none(waiver:private-consumed-unbounded-allocation)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exhaustive original-exponent substitution for the entire paid-low-V subregion. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.SourceCertificate
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

/-! Physical paid-V construction. No bound on exponents or finite control is used.
The scope includes b=d; in the full third-peak partition its new contribution
is the strict b<d moderate piece. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
open D5.S3.Combinatorics.Circle.SourceWidth
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private A B L K H SU SV SW window quotient quotient_bounds E Ep R Rp G Gp
  first_windows v_windows w_windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Arithmetic
open private word from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private rowBase rowHeads rowSeams freshCut source_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.SourceCertificate
open private charge sourceMod chain_values from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base newBase oldValue newValue)
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (insertAt)
open private gap_power half_power
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

private def paidQuotient (a b c d : ℕ) : ℤ :=
  quotient (2^a) (2^b) (2^c) (2^d) (2^(c-d))
private def paidH (a b c d : ℕ) : ℕ := (paidQuotient a b c d).toNat
private def paidEarly (a b c d : ℕ) : Bool :=
  decide (Rp (2^a) (2^b) (2^c) (2^d) (2^(c-d))<0)

/-- The dyadic quotient and the upper bound y/4 are exact on original gaps. -/
private theorem dyadic_m (b c d : ℕ) (hdc : d<c) (hupper : c≤b+d-2) :
    (2:ℕ)^c/2^d=2^(c-d) ∧ 2≤(2:ℤ)^(c-d) ∧
      (2:ℤ)^(c-d)≤(2:ℤ)^b/4 := by
  have he : c=c-d+d := by omega
  have hquot : (2:ℕ)^c/2^d=2^(c-d) := by
    conv_lhs => arg 1;rw [he,pow_add]
    simp
  have hm : 2≤(2:ℤ)^(c-d) := by
    have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤c-d by omega)
    norm_num at hh
    exact hh
  have he' : c-d+2≤b := by omega
  have hp:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) he'
  have hid : (2:ℤ)^(c-d+2)=4*2^(c-d) := by rw [pow_add];norm_num;ring
  rw [hid] at hp
  exact ⟨hquot,hm,by omega⟩

set_option maxHeartbeats 2400000 in
private theorem paid_source (a b c d : ℕ)
    (ha : 2≤a) (hab : a<b) (hbd : b≤d) (hdc : d<c)
    (had : a+2≤d) (hupper : c≤b+d-2) :
    Nonempty (Certificate a b c d) ∧
    (word a b c d (paidH a b c d)).Perm (List.range (size a b c d)) ∧
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word a b c d (paidH a b c d)) ∧
    freshCut a b c d (paidH a b c d) (paidEarly a b c d)<size a b c d ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (word a b c d (paidH a b c d))
        (freshCut a b c d (paidH a b c d) (paidEarly a b c d))) := by
  let x : ℤ:=2^a
  let y : ℤ:=2^b
  let z : ℤ:=2^c
  let t : ℤ:=2^d
  let m : ℤ:=2^(c-d)
  let w : ℤ:=2^(b-a-1)
  let T : ℤ:=2^(d-1)
  have hx : 4≤x := by
    have hp:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha
    norm_num at hp
    exact hp
  have hy : 2*x≤y := by
    have he : y=2*x*w := by simpa [x,y,w] using gap_power b a 1 (by omega)
    have hw : 1≤w := one_le_pow₀ (by norm_num)
    have hp:=mul_le_mul_of_nonneg_left hw (show 0≤2*x by omega)
    nlinarith only [he,hp]
  have ht : y≤t := pow_le_pow_right₀ (by norm_num) hbd
  have ht4 : 4*x≤t := by
    have he : t=4*x*(2:ℤ)^(d-a-2) := by
      simpa [x,t,show (2:ℤ)^2=4 by norm_num] using gap_power d a 2 had
    have hp : 1≤(2:ℤ)^(d-a-2) := one_le_pow₀ (by norm_num)
    have hm:=mul_le_mul_of_nonneg_left hp (show 0≤4*x by omega)
    nlinarith only [he,hm]
  have hz2 : 2*t≤z := by
    have he : z=2*t*(2:ℤ)^(c-d-1) := by
      simpa [z,t] using gap_power c d 1 (by omega)
    have hp : 1≤(2:ℤ)^(c-d-1) := one_le_pow₀ (by norm_num)
    have hm:=mul_le_mul_of_nonneg_left hp (show 0≤2*t by omega)
    nlinarith only [he,hm]
  have dm:=dyadic_m b c d hdc hupper
  have hm : 2≤m := dm.2.1
  have hmY : 4*m≤y := by dsimp [m,y];have hh:=dm.2.2;omega
  have hzt : z=m*t := by
    dsimp [z,m,t]
    rw [←pow_add]
    congr 1
    omega
  have hw : 2*x*w=y := by simpa [x,y,w] using (gap_power b a 1 (by omega)).symm
  have hT : 2*T=t := by simpa [T,t] using (half_power d (by omega)).symm
  have dyadic : t=y ∨ 2*y≤t := by
    by_cases he : b=d
    · left;simpa [y,t,he]
    · right
      have he' : t=2*y*(2:ℤ)^(d-b-1) := by
        simpa [t,y] using gap_power d b 1 (by omega)
      have hp : 1≤(2:ℤ)^(d-b-1) := one_le_pow₀ (by norm_num)
      have hm:=mul_le_mul_of_nonneg_left hp (show 0≤2*y by omega)
      nlinarith only [he',hm]
  have qb:=quotient_bounds x y z t m T hx hy ht ht4 hz2 hm hzt hT
  have fw:=first_windows x y z t m hx hy ht hz2 hm hmY hzt
  have vw:=v_windows x y z t m T hx hy ht ht4 hz2 hm hmY hzt hT dyadic
  have ww:=w_windows x y z t w hx hy ht4 hz2 hw
  have hcast : (paidH a b c d:ℤ)=quotient x y z t m :=
    Int.toNat_of_nonneg qb.1
  have hFloor : (paidH a b c d:ℤ)=(L x z t-A x y z)/(m*B x y t) := hcast
  have hHalf : (paidH a b c d:ℤ)<t/2 := by
    have he : t/2=T := by omega
    rw [hcast,he]
    exact qb.2.1
  have hbound : paidH a b c d<2^(d-1) := by
    have he : ((2^(d-1):ℕ):ℤ)=T := by simp [T]
    exact_mod_cast (show (paidH a b c d:ℤ)<((2^(d-1):ℕ):ℤ) by rw [hcast,he];exact qb.2.1)
  have hbase : base a b c d=![A x y z,B x y t,L x z t,K y z t] := by
    funext r
    fin_cases r <;> dsimp [base,A,B,L,K,x,y,z,t] <;> ring
  have hnew : newBase a b c d=![2*A x y z,SU x y t,SV x z t,SW y z t] := by
    funext r
    fin_cases r <;> dsimp [newBase,charge]
    all_goals rw [hbase]
    all_goals dsimp [SU,SV,SW,H,y,z] <;> ring
  have vNew : window
      (if paidEarly a b c d then Rp x y z t m+A x y z else Rp x y z t m) (SV x z t) := by
    simpa [paidEarly,x,y,z,t,m] using vw.2
  have wNew : window
      (if paidEarly a b c d then Gp x y z t w+A x y z else Gp x y z t w) (SW y z t) := by
    cases paidEarly a b c d
    · exact ww.2.1
    · exact ww.2.2
  apply source_certificate a b c d (paidH a b c d) ha hab hbd hdc hbound (paidEarly a b c d)
  intro side r
  have last (s : Bool) : window (0:ℤ) (rowHeads a b c d s 3) := by
    have hA:=((chain_values a b c d ha (by omega) (by omega) (by omega)).1 0).1
    simpa [window,rowHeads] using And.intro (show (0:ℤ)≤0 by omega) (show 0≤base a b c d 0-1 by omega)
  cases side <;> fin_cases r
  · convert fw.1 using 1 <;> simp [rowSeams,rowHeads,rowBase,hbase,hnew,x,y,z,t,m,w] <;> dsimp [E] <;> ring
  · convert vw.1 using 1 <;> simp [rowSeams,rowHeads,rowBase,hbase,hnew,hcast,x,y,z,t,m,w] <;> dsimp [R] <;> ring
  · convert ww.1 using 1 <;> simp [rowSeams,rowHeads,rowBase,hbase,hnew,hcast,x,y,z,t,m,w] <;> dsimp [G] <;> ring
  · simpa [rowSeams] using last false
  · convert fw.2 using 1 <;> simp [rowSeams,rowHeads,rowBase,hbase,hnew,hcast,x,y,z,t,m,w] <;> dsimp [Ep,E,SU] <;> ring
  · convert vNew using 1 <;> simp [rowSeams,rowHeads,rowBase,hbase,hnew,hcast,x,y,z,t,m,w]
    all_goals split_ifs <;> dsimp [Rp,R,SV,SU] <;> ring
  · convert wNew using 1 <;> simp [rowSeams,rowHeads,rowBase,hbase,hnew,hcast,x,y,z,t,m,w]
    all_goals split_ifs <;> dsimp [Gp,G,SW,SV] <;> ring
  · simpa [rowSeams] using last true

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV

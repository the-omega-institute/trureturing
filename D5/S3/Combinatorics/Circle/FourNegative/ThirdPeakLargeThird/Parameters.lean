/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Parameters
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact original dyadic parameters and the ceiling in the full physical V stock. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Physical
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.DiagonalArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

/-! ThirdPeakLargeThird: Parameters. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
open private A B L K H SU SV SW window quotient remainder ceilDiv ceil_bounds ceil_le
  large_head quotient_remainder from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Arithmetic
open private base newBase sourceMod chain_values charge nextBase chainStart oldValue from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private full from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private chainLength from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private half_power from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

private def selectedV (a b c d : ℕ) : ℕ := (quotient (2^a) (2^b) (2^c) (2^d)).toNat

private theorem dictionary (a b c d : ℕ) :
    base a b c d=![A (2^a) (2^b) (2^c),B (2^a) (2^b) (2^d),
      L (2^a) (2^c) (2^d),K (2^b) (2^c) (2^d)] ∧
    newBase a b c d=![2*A (2^a) (2^b) (2^c),SU (2^a) (2^b) (2^d),
      SV (2^a) (2^c) (2^d),SW (2^b) (2^c) (2^d)] := by
  constructor
  · funext r;fin_cases r <;> dsimp [base,A,B,L,K] <;> ring
  · funext r;fin_cases r <;> dsimp [newBase,base,charge,A,B,L,K,SU,SV,SW,H] <;> ring

private theorem dyadic_parameters (a b c d : ℕ)
    (hb : 2≤b) (hba : b≤a) (had : a<d) (hdc : d+3≤c) :
    (4:ℤ)≤2^b ∧ (2:ℤ)^b≤2^a ∧ (2:ℤ)^a≤2^d ∧
    8*(2:ℤ)^d≤2^c := by
  have hy:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hb
  have hxy:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hba
  have hxt:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) had.le
  have hzt:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hdc
  have he : (2:ℤ)^(d+3)=8*2^d := by rw [pow_add];norm_num;ring
  rw [he] at hzt
  exact ⟨by simpa using hy,hxy,hxt,hzt⟩

private theorem strict_dyadic (u v : ℕ) (h : u<v) : 2*(2:ℤ)^u≤2^v := by
  have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show u+1≤v by omega)
  simpa [pow_succ,mul_comm] using hh

private theorem double_gap_dyadic (u v : ℕ) (h : u+2≤v) : 4*(2:ℤ)^u≤2^v := by
  have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) h
  have he : (2:ℤ)^(u+2)=4*2^u := by rw [pow_add];norm_num;ring
  rwa [he] at hh

private theorem selected_properties (a b c d : ℕ)
    (hb : 2≤b) (hba : b≤a) (had : a<d) (hdc : d+3≤c) :
    1≤selectedV a b c d ∧ selectedV a b c d<2^(c-1) ∧
    (selectedV a b c d:ℤ)=quotient (2^a) (2^b) (2^c) (2^d) ∧
    2*(selectedV a b c d:ℤ)≤(2:ℤ)^c-2 := by
  let x : ℤ:=2^a
  let y : ℤ:=2^b
  let z : ℤ:=2^c
  let t : ℤ:=2^d
  let v:=quotient x y z t
  have dp:=dyadic_parameters a b c d hb hba had hdc
  have big:=large_head x y z t dp.1 dp.2.1 dp.2.2.1 dp.2.2.2
  have dic:=dictionary a b c d
  have tab:=chain_values a b c d (by omega) hb (by omega) (by omega)
  have bbpos : 0<B x y t := by
    have hh:=(tab.1 1).1
    rw [dic.1] at hh
    change 1≤B x y t at hh
    omega
  have cb:=ceil_bounds (L x z t-B x y t) (2*B x y t) (by omega)
  have vpos : 1≤v := by
    by_contra hn
    have hm:=mul_nonpos_of_nonpos_of_nonneg (show v≤0 by omega) (show 0≤2*B x y t by omega)
    dsimp [v,quotient] at hm
    nlinarith only [cb.2,big.2,hm]
  have nn:=native_masses a b c d (by omega) hb (by omega) (by omega) 1
  dsimp only at nn
  have headbound : B x y t<sourceMod a b c d := by
    have hh:=(tab.1 1).2
    rw [dic.1] at hh
    simpa [x,y,t] using hh
  have inventory_bound : L x z t-B x y t≤(full a b c d 1:ℤ)*(2*B x y t) := by
    have oldmass:=nn.1
    have terminal:=nn.2.2.1
    simp only [nextBase,dic.1,Matrix.cons_val_one,Matrix.cons_val_two] at oldmass terminal
    change (full a b c d 1:ℤ)*B x y t+
      oldValue a b c d (chainStart b c d 1+(chainLength a b c d 1-1))=
      L x z t-B x y t at oldmass
    change 2*oldValue a b c d (chainStart b c d 1+(chainLength a b c d 1-1))=
      L x z t-sourceMod a b c d at terminal
    nlinarith only [oldmass,terminal,headbound]
  have cap:=ceil_le (L x z t-B x y t) (2*B x y t) (full a b c d 1:ℤ)
    (by omega) inventory_bound
  change v≤(full a b c d 1:ℤ) at cap
  have cast : (selectedV a b c d:ℤ)=v := Int.toNat_of_nonneg (by omega)
  have fullcast : (full a b c d 1:ℤ)=(2:ℤ)^(c-1)-1 := by
    simp [full,chainLength,Nat.cast_sub (show 1≤2^(c-1) by have := Nat.two_pow_pos (c-1);omega)]
  have half:=half_power c (by omega)
  have vlt : selectedV a b c d<2^(c-1) := by
    have hh : (selectedV a b c d:ℤ)<(2:ℤ)^(c-1) := by omega
    exact_mod_cast hh
  refine ⟨by exact_mod_cast (show (1:ℤ)≤(selectedV a b c d:ℤ) by omega),vlt,cast,?_⟩
  change 2*(selectedV a b c d:ℤ)≤z-2
  dsimp [z]
  omega

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird

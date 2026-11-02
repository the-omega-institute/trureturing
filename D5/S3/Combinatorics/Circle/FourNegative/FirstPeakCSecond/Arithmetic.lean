/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exhaustive dyadic chart substitution and tight integer allocation gates for the strict branch. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Polynomials
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.PolynomialsSeparated
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.PolynomialsCorner
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
open private UniformBounds chart_adjacent_t8 chart_adjacent_y4
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Polynomials
open private chart_separated
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.PolynomialsSeparated
open private chart_small_corner
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.PolynomialsCorner
open private floor_bounds from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

private def corner (b c d : ℕ) : Prop := d=2 ∧ b=3 ∧ c=4
private instance (b c d : ℕ) : Decidable (corner b c d) := by unfold corner; infer_instance
private def grainExponent (a b c d : ℕ) : ℕ := if corner b c d then a-5 else a-d-2
private def grain (a b c d : ℕ) : ℤ := 2^(grainExponent a b c d)
private def reserve (a b c d : ℕ) : ℤ :=
  grain a b c d * (if corner b c d then 11 else 2*(2:ℤ)^d-3)

private theorem power_split (n j : ℕ) (hj : j≤n) :
    (2:ℤ)^n = 2^j*2^(n-j) := by rw [←pow_add,Nat.add_sub_of_le hj]

private theorem half_power (n : ℕ) (hn : 1≤n) : (2:ℤ)^n=2*2^(n-1) := by
  rw [power_split n 1 hn]
  norm_num

private theorem gap_power (u v h : ℕ) (huv : v+h≤u) :
    (2:ℤ)^u = 2^h*2^v*2^(u-v-h) := by
  calc
    (2:ℤ)^u=2^(v+h)*2^(u-(v+h)) := power_split u (v+h) huv
    _ = _ := by rw [pow_add,show u-(v+h)=u-v-h by omega]; ring

-- Dyadic exhaustion is on exponent gaps; no bounded enumeration of a is involved.
set_option maxHeartbeats 1800000 in
private theorem uniform_bounds (a b c d : ℕ)
    (hd : 2≤d) (hdb : d<b) (hbc : b<c) (hca : c<a) :
    UniformBounds ((2:ℤ)^a) (2^b) (2^c) (2^d) (2^(a-c-1))
      (grain a b c d) (reserve a b c d) := by
  let H : ℤ := 2^(a-c-1)
  have hH : 1≤H := by dsimp [H]; exact one_le_pow₀ (by norm_num)
  have hx : (2:ℤ)^a=2*2^c*H := by
    simpa [H] using gap_power a c 1 (by omega)
  by_cases hsep : b+2≤c
  · have hn : ¬corner b c d := by simp only [corner]; omega
    let T : ℤ := 2^d-4
    let Y : ℤ := 2^(b-d-1)-1
    let E : ℤ := 2^(c-b-2)-1
    have hT : 0≤T := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd
      norm_num at hh
      dsimp [T]; omega
    have hY : 0≤Y := by dsimp [Y]; have := one_le_pow₀ (n := b-d-1) (by norm_num : (1:ℤ)≤2); omega
    have hE : 0≤E := by dsimp [E]; have := one_le_pow₀ (n := c-b-2) (by norm_num : (1:ℤ)≤2); omega
    have hy : (2:ℤ)^b=2*2^d*(1+Y) := by
      dsimp [Y]; rw [gap_power b d 1 (by omega)]; norm_num
    have hz : (2:ℤ)^c=4*2^b*(1+E) := by
      dsimp [E]; rw [gap_power c b 2 hsep]; norm_num
    have hg : grain a b c d=4*(1+E)*(1+Y)*H := by
      dsimp [grain,grainExponent]; rw [if_neg hn]
      calc
        (2:ℤ)^(a-d-2)=4*2^(c-b-2)*2^(b-d-1)*2^(a-c-1) := by
          calc
            (2:ℤ)^(a-d-2)=2^(2+(c-b-2)+(b-d-1)+(a-c-1)) := by congr 1; omega
            _ = _ := by simp only [pow_add]; norm_num
        _ = _ := by dsimp [E,Y,H]; ring
    have hh := chart_separated Y T (H-1) E hY hT (by omega) hE
    have et : 4+T=(2:ℤ)^d := by dsimp [T]; ring
    dsimp only at hh
    rw [et,show (1:ℤ)+(H-1)=H by ring,←hy,←hz,←hx,←hg] at hh
    simpa only [reserve,if_neg hn] using hh
  · have hcb : c=b+1 := by omega
    by_cases ht8 : 3≤d
    · have hn : ¬corner b c d := by simp only [corner]; omega
      let T : ℤ := 2^d-8
      let Y : ℤ := 2^(b-d-1)-1
      have hT : 0≤T := by
        have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ht8
        norm_num at hh; dsimp [T]; omega
      have hY : 0≤Y := by dsimp [Y]; have := one_le_pow₀ (n := b-d-1) (by norm_num : (1:ℤ)≤2); omega
      have hy : (2:ℤ)^b=2*2^d*(1+Y) := by
        dsimp [Y]; rw [gap_power b d 1 (by omega)]; norm_num
      have hz : (2:ℤ)^c=2*2^b := by rw [hcb,pow_succ]; ring
      have hg : grain a b c d=2*(1+Y)*H := by
        dsimp [grain,grainExponent]; rw [if_neg hn]
        calc
          (2:ℤ)^(a-d-2)=2*2^(b-d-1)*2^(a-c-1) := by
            calc
              (2:ℤ)^(a-d-2)=2^(1+(b-d-1)+(a-c-1)) := by congr 1; omega
              _ = _ := by simp only [pow_add]; norm_num
          _ = _ := by dsimp [Y,H]; ring
      have hh := chart_adjacent_t8 Y T (H-1) 0 hY hT (by omega) (by omega)
      have et : 8+T=(2:ℤ)^d := by dsimp [T]; ring
      dsimp only at hh
      rw [et,show (1:ℤ)+(H-1)=H by ring,←hy,←hz,←hx,←hg] at hh
      simpa only [reserve,if_neg hn] using hh
    · have hd2 : d=2 := by omega
      by_cases hy4 : d+2≤b
      · have hn : ¬corner b c d := by simp only [corner]; omega
        let T : ℤ := 2^d-4
        let Y : ℤ := 2^(b-d-2)-1
        have hT : 0≤T := by dsimp [T]; rw [hd2]; norm_num
        have hY : 0≤Y := by dsimp [Y]; have := one_le_pow₀ (n := b-d-2) (by norm_num : (1:ℤ)≤2); omega
        have hy : (2:ℤ)^b=4*2^d*(1+Y) := by
          dsimp [Y]; rw [gap_power b d 2 hy4]; norm_num
        have hz : (2:ℤ)^c=2*2^b := by rw [hcb,pow_succ]; ring
        have hg : grain a b c d=4*(1+Y)*H := by
          dsimp [grain,grainExponent]; rw [if_neg hn]
          calc
            (2:ℤ)^(a-d-2)=4*2^(b-d-2)*2^(a-c-1) := by
              calc
                (2:ℤ)^(a-d-2)=2^(2+(b-d-2)+(a-c-1)) := by congr 1; omega
                _ = _ := by simp only [pow_add]; norm_num
            _ = _ := by dsimp [Y,H]; ring
        have hh := chart_adjacent_y4 Y T (H-1) 0 hY hT (by omega) (by omega)
        have et : 4+T=(2:ℤ)^d := by dsimp [T]; ring
        dsimp only at hh
        rw [et,show (1:ℤ)+(H-1)=H by ring,←hy,←hz,←hx,←hg] at hh
        simpa only [reserve,if_neg hn] using hh
      · have hb3 : b=3 := by omega
        have hc4 : c=4 := by omega
        subst d; subst b; subst c
        have hh := chart_small_corner 0 0 (H-1) 0 (by omega) (by omega) (by omega) (by omega)
        have ha : a - 5 = a - 4 - 1 := by omega
        have hg : grain a 3 4 2=H := by simp [grain,grainExponent,corner,H,ha]
        have hs : reserve a 3 4 2=11*H := by simp [reserve,corner,hg]; ring
        convert hh using 1 <;>
          simp [show (1:ℤ)+(H-1)=H by ring,hg,hs] <;>
          first | simpa using hx | ring | exact ha | omega

private theorem reserve_capacity (a b c d : ℕ)
    (hd : 2≤d) (hdb : d<b) (hbc : b<c) (hca : c<a) :
    1≤grain a b c d ∧ 1≤reserve a b c d ∧
    2*reserve a b c d≤(2:ℤ)^a ∧ grain a b c d ∣ reserve a b c d := by
  have hg : 1≤grain a b c d := by dsimp [grain]; exact one_le_pow₀ (by norm_num)
  have ht : 4≤(2:ℤ)^d := by
    have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd
    norm_num at this; exact this
  by_cases hc : corner b c d
  · obtain ⟨rfl,rfl,rfl⟩ := hc
    have hx : (2:ℤ)^a=32*grain a 3 4 2 := by
      simp only [grain,grainExponent,corner,if_pos (by decide : 2=2 ∧ 3=3 ∧ 4=4)]
      rw [power_split a 5 (by omega)]; norm_num
    have hs : reserve a 3 4 2 = 11 * grain a 3 4 2 := by simp [reserve, corner, mul_comm]
    rw [hs]
    refine ⟨hg,by nlinarith,by nlinarith [hx],by simpa [mul_comm] using dvd_mul_right (grain a 3 4 2) 11⟩
  · have hx : (2:ℤ)^a=4*2^d*grain a b c d := by
      dsimp [grain,grainExponent]; rw [if_neg hc]
      simpa using gap_power a d 2 (by omega)
    have hprod := mul_nonneg (show 0≤grain a b c d by omega) (show 0≤(2:ℤ)^d-4 by omega)
    simp only [reserve,if_neg hc]
    refine ⟨hg,by nlinarith,by nlinarith [hx],dvd_mul_right _ _⟩

-- ceil(B/Mn) written using Euclidean division, valid also when Mn divides B.
private theorem tight_ceiling (B M D H : ℤ)
    (hB : 1≤B) (hM : 0<M) (hMn : 0<2*M-D) (hH : 1≤H)
    (hcap : B≤H*(2*M-D)) (hbank : H*M≤B-1) :
    let r := (B-1)/(2*M-D)+1
    1≤r ∧ r≤H ∧ B≤r*(2*M-D) ∧ r*(2*M-D)<B+(2*M-D) ∧
      r*M≤B-1 := by
  let Mn := 2*M-D
  have hf := floor_bounds (B-1) Mn hMn
  have hr0 := Int.ediv_nonneg (show 0≤B-1 by omega) hMn.le
  dsimp only
  have hrH : (B-1)/Mn+1≤H := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (show H≤(B-1)/Mn by omega) hMn.le
    nlinarith only [hf.1,hcap,hm]
  have hmul := mul_le_mul_of_nonneg_right hrH hM.le
  exact ⟨by omega,hrH,by nlinarith only [hf.2],
    by nlinarith only [hf.1],by nlinarith only [hmul,hbank]⟩

-- All second/third seam gates. The first four gates are exactly the polynomial margins.
set_option maxHeartbeats 1000000 in
private theorem later_gates (B L M D z H r : ℤ)
    (hB : 1≤B) (hM : 0<M) (hD : z+1≤D) (hz : 4≤z) (hH : 1≤H)
    (hr : 1≤r ∧ r≤H ∧ B≤r*(2*M-D) ∧ r*(2*M-D)<B+(2*M-D) ∧ r*M≤B-1)
    (adj : Bool)
    (hthird : if adj then (0≤L-B-H*M ∧ 0≤2*B-L-1) else
      (0≤L-2*B-H*D ∧ 0≤z*B-2*L-1))
    (hzEven : z%2=0) :
    let w := if adj then 1 else (L-r*M)/B
    0≤w ∧ w<z/2 ∧
    (0≤2*(B-r*M) ∧ 2*(B-r*M)≤B-1) ∧
    (0≤2*((2*B-1)-r*(2*M-D)) ∧ 2*((2*B-1)-r*(2*M-D))≤(2*B-1)-1) ∧
    (0≤2*(L-r*M-w*B) ∧ 2*(L-r*M-w*B)≤L-1) ∧
    (0≤2*((2*L-z-1)-r*(2*M-D)-w*(2*B-1)) ∧
      2*((2*L-z-1)-r*(2*M-D)-w*(2*B-1))≤(2*L-z-1)-1) := by
  have hzdiv : z=2*(z/2) := by omega
  have hrD : 1≤r*D := by nlinarith only [hr.1,hD,hz,mul_nonneg (show 0≤r-1 by omega) (show 0≤D-1 by omega)]
  have hrM := mul_le_mul_of_nonneg_right hr.2.1 hM.le
  have hrM0 : 0≤r*M := mul_nonneg (by omega) hM.le
  have g1 : 0≤2*(B-r*M) ∧ 2*(B-r*M)≤B-1 := by
    constructor <;> nlinarith only [hr.2.2.2.2,hr.2.2.1,hrD]
  have k1 : 0≤2*((2*B-1)-r*(2*M-D)) ∧
      2*((2*B-1)-r*(2*M-D))≤(2*B-1)-1 := by
    constructor <;> nlinarith only [hr.2.2.2.2,hr.2.2.1,hrD]
  cases adj with
  | true =>
    change 0≤L-B-H*M ∧ 0≤2*B-L-1 at hthird
    dsimp only
    simp only [ite_true]
    have hzhalf : (1 : ℤ) < z / 2 := by nlinarith [hz, hzdiv]
    have hrDz : z≤r*D := by
      nlinarith only [hr.1,hD,hz,mul_nonneg (show 0≤r-1 by omega) (show 0≤D by omega)]
    refine ⟨by omega,hzhalf,g1,k1,?_,?_⟩
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  | false =>
    change 0≤L-2*B-H*D ∧ 0≤z*B-2*L-1 at hthird
    have hsep := hthird
    let w := (L-r*M)/B
    have hnum : 0≤L-r*M := by nlinarith only [hsep.1,hr.2.2.2.2,hB,hD,hH,hz,mul_nonneg (show 0≤H by omega) (show 0≤D by omega)]
    have hw : 0≤w := Int.ediv_nonneg hnum (by omega)
    have hf := floor_bounds (L-r*M) B (by omega)
    have hwcap : w<z/2 := by
      by_contra hn
      have hmul := mul_le_mul_of_nonneg_right (show z≤2*w by omega) (show 0≤B by omega)
      dsimp [w] at *
      nlinarith only [hf.1,hsep.2,hrM0,hmul]
    have hS : 0≤L-r*M-w*B ∧ L-r*M-w*B≤B-1 := by
      dsimp [w]; constructor <;> nlinarith only [hf.1,hf.2]
    have hrDcap := mul_le_mul_of_nonneg_right hr.2.1 (show 0≤D by omega)
    have hrDz : z+1≤r*D := by
      nlinarith only [hr.1,hD,hz,mul_nonneg (show 0≤r-1 by omega) (show 0≤D by omega)]
    dsimp only
    change
      0≤(L-r*M)/B ∧ (L-r*M)/B<z/2 ∧
      (0≤2*(B-r*M) ∧ 2*(B-r*M)≤B-1) ∧
      (0≤2*((2*B-1)-r*(2*M-D)) ∧
        2*((2*B-1)-r*(2*M-D))≤(2*B-1)-1) ∧
      (0≤2*(L-r*M-((L-r*M)/B)*B) ∧
        2*(L-r*M-((L-r*M)/B)*B)≤L-1) ∧
      (0≤2*((2*L-z-1)-r*(2*M-D)-((L-r*M)/B)*(2*B-1)) ∧
        2*((2*L-z-1)-r*(2*M-D)-((L-r*M)/B)*(2*B-1))≤(2*L-z-1)-1)
    refine ⟨hw,hwcap,g1,k1,?_,?_⟩
    · constructor <;> nlinarith
    · constructor <;> nlinarith

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond

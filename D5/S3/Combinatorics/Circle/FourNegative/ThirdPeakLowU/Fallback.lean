/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Fallback
   generality: I
   mirror-B: none(waiver:consumed-low-u-support)
   mirror-E: none(waiver:physical-low-u-construction)
   anchors: []
   utility: none
   digest: Unbounded remainder selection and all six fallback physical windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Arithmetic

/-! Unbounded remainder selection and all six fallback physical windows. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
open private A B L K C SU SV SW window
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Arithmetic

private theorem fallback_selector (s : ℤ) (hs : 2≤s) :
    let A := 1024*s+37
    let M := 592*s+1
    let D₀ := (2*s*A)%M
    let r := if 4*s≤D₀ ∧ D₀≤(A-1)/2 then s else s-1
    let D := (2*r*A)%M
    s-1≤r ∧ r≤s ∧ 4*s≤D ∧ 2*D≤A-1 ∧ 1≤(2*r*A)/M ∧ (2*r*A)/M<4*s := by
  dsimp only
  let AA := 1024*s+37
  let M := 592*s+1
  let delta := 272*s+71
  let D₀ := (2*s*AA)%M
  have hM : 0<M := by dsimp [M]; omega
  have hd : 0<delta ∧ delta<M := by dsimp [delta,M]; constructor <;> omega
  have hD₀ : 0≤D₀ ∧ D₀<M := ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hM⟩
  have half : (AA-1)/2=512*s+18 := by dsimp [AA]; omega
  have hdelta : 2*AA=3*M+delta := by dsimp [AA,M,delta]; ring
  have div := Int.mul_ediv_add_emod (2*s*AA) M
  have quot (r : ℤ) (hr : s-1≤r ∧ r≤s) : 1≤(2*r*AA)/M ∧ (2*r*AA)/M<4*s := by
    have hp : 0<AA := by dsimp [AA]; omega
    have l := mul_nonneg (show 0≤r-(s-1) by omega) hp.le
    have u := mul_nonneg (show 0≤s-r by omega) hp.le
    constructor
    · apply (Int.le_ediv_iff_mul_le hM).mpr
      dsimp [AA,M] at *
      nlinarith [sq_nonneg (s-2)]
    · apply (Int.ediv_lt_iff_lt_mul hM).mpr
      dsimp [AA,M] at *
      nlinarith [sq_nonneg (s-2)]
  let r := if 4*s≤D₀ ∧ D₀≤(AA-1)/2 then s else s-1
  change s-1≤r ∧ r≤s ∧ 4*s≤(2*r*AA)%M ∧ 2*((2*r*AA)%M)≤AA-1 ∧
    1≤(2*r*AA)/M ∧ (2*r*AA)/M<4*s
  dsimp only [r]
  by_cases good : 4*s≤D₀ ∧ D₀≤(AA-1)/2
  · simp only [if_pos good]
    exact ⟨by omega,le_rfl,good.1,by omega,quot s ⟨by omega,le_rfl⟩⟩
  · have hc : D₀<4*s ∨ (AA-1)/2<D₀ := by omega
    have hD : 4*s≤(2*(s-1)*AA)%M ∧ 2*((2*(s-1)*AA)%M)≤AA-1 := by
      rcases hc with hc|hc
      · let R := D₀+M-delta
        have bounds : 4*s≤R ∧ R≤(AA-1)/2 ∧ R<M := by
          dsimp [R,M,delta] at *
          omega
        have eq : 2*(s-1)*AA=M*((2*s*AA)/M-4)+R := by
          dsimp [R,D₀] at *
          nlinarith only [div,hdelta]
        have rem : (2*(s-1)*AA)%M=R := by
          rw [eq,Int.add_emod]
          simp only [Int.mul_emod_right,zero_add,Int.emod_emod]
          exact Int.emod_eq_of_lt (by omega) bounds.2.2
        rw [rem]
        omega
      · let R := D₀-delta
        have bounds : 4*s≤R ∧ R≤(AA-1)/2 ∧ R<M := by
          dsimp [R,M,delta] at *
          omega
        have eq : 2*(s-1)*AA=M*((2*s*AA)/M-3)+R := by
          dsimp [R,D₀] at *
          nlinarith only [div,hdelta]
        have rem : (2*(s-1)*AA)%M=R := by
          rw [eq,Int.add_emod]
          simp only [Int.mul_emod_right,zero_add,Int.emod_emod]
          exact Int.emod_eq_of_lt (by omega) bounds.2.2
        rw [rem]
        omega
    simp only [if_neg good]
    exact ⟨le_rfl,by omega,hD.1,hD.2,quot (s-1) ⟨le_rfl,by omega⟩⟩

private theorem fallback_select (s : ℤ) (hs : 2≤s) (hgap : s=2 ∨ 4≤s) :
    ∃ u v w : ℕ, 2*(u : ℤ)<8*s ∧ 1≤v ∧ (v : ℤ)<4*s ∧ w=1 ∧
      window (L 4 8 s (32*s)-v*B 4 8 s) (L 4 8 s (32*s)) ∧
      window (K 8 s (32*s)-w*L 4 8 s (32*s)+u*A 4 8 (32*s)-v*B 4 8 s) (K 8 s (32*s)) ∧
      window ((u+1 : ℤ)*A 4 8 (32*s)-v*B 4 8 s) (A 4 8 (32*s)) ∧
      window (SV 4 8 s (32*s)-v*SU 4 8 s) (SV 4 8 s (32*s)) ∧
      window (SW 8 s (32*s)-w*SV 4 8 s (32*s)+(2*u+1 : ℤ)*A 4 8 (32*s)-v*SU 4 8 s) (SW 8 s (32*s)) ∧
      window ((2*u+2 : ℤ)*A 4 8 (32*s)-v*SU 4 8 s) (A 4 8 (32*s)) := by
  rcases hgap with rfl|hs4
  · refine ⟨1,7,1,?_,?_,?_,rfl,?_,?_,?_,?_,?_,?_⟩ <;>
      norm_num [window,A,B,L,K,SU,SV,SW,C]
  let AA := 1024*s+37
  let M := 592*s+1
  let D₀ := (2*s*AA)%M
  let r := if 4*s≤D₀ ∧ D₀≤(AA-1)/2 then s else s-1
  let V := (2*r*AA)/M
  let D := (2*r*AA)%M
  obtain ⟨hr0,hr1,hD0,hD1,hV0,hV1⟩ := fallback_selector s hs
  change s-1≤r at hr0
  change r≤s at hr1
  change 4*s≤D at hD0
  change 2*D≤AA-1 at hD1
  change 1≤V at hV0
  change V<4*s at hV1
  have div : M*V+D=2*r*AA := Int.mul_ediv_add_emod _ _
  have castV : (V.toNat : ℤ)=V := Int.toNat_of_nonneg (by omega)
  have castU : ((r-1).toNat : ℤ)=r-1 := Int.toNat_of_nonneg (by omega)
  have hp : 0<AA := by dsimp [AA]; omega
  have lower := mul_nonneg (show 0≤r-(s-1) by omega) hp.le
  have upper := mul_nonneg (show 0≤s-r by omega) hp.le
  refine ⟨(r-1).toNat,V.toNat,1,?_,?_,?_,rfl,?_,?_,?_,?_,?_,?_⟩
  · rw [castU]; omega
  · omega
  · simpa only [castV] using hV1
  all_goals simp only [window,Nat.cast_one,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,castV,castU]
  all_goals dsimp [A,B,L,K,SU,SV,SW,C]
  all_goals dsimp [AA,M] at div lower upper hD1
  all_goals constructor
  all_goals nlinarith [sq_nonneg (s-2)]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU

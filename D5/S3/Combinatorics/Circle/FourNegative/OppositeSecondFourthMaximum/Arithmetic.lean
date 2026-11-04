/- GID: D5/S3/Combinatorics/Circle/FourNegative/OppositeSecondFourthMaximum/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-quotient-construction)
   mirror-E: none(waiver:private-consumed-quotient-construction)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded quotient masks and paired terminal windows in both strict sectors. -/
import Mathlib.Data.Int.DivMod
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Arithmetic

/-! The two orders below are constructed directly in the original chain coordinates.
The Boolean selects their displayed order, not an action on the source. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum

private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y z : ℤ) : ℤ := 1+y+x*y+x*y*y
private def L (x y z : ℤ) : ℤ := 1+z+z*y+x*z*y
private def K (x y z : ℤ) : ℤ := 1+y+y*z+y*y*z
private def SU (x y z : ℤ) : ℤ := 2*B x y z-1
private def SV (x y z : ℤ) : ℤ := 2*L x y z-z-1
private def SW (x y z : ℤ) : ℤ := 2*K x y z-1-y*(z+1)
private def window (r C : ℤ) : Prop := 0≤2*r ∧ 2*r≤C-1
private def oldSeams (x y z m n : ℤ) (rev : Bool) : Fin 3 → ℤ :=
  if rev then ![K x y z-(n+1)*L x y z,A x y z-L x y z,
    B x y z-L x y z-m*A x y z]
  else ![B x y z-(m+1)*A x y z,L x y z-A x y z,
    K x y z-A x y z-n*L x y z]
private def newSeams (x y z m n : ℤ) (rev : Bool) : Fin 3 → ℤ :=
  if rev then ![SW x y z-(n+1)*SV x y z,2*A x y z-SV x y z,
    SU x y z-SV x y z-2*m*A x y z]
  else ![SU x y z-2*(m+1)*A x y z,SV x y z-2*A x y z,
    SW x y z-2*A x y z-n*SV x y z]
private def oldHeads (x y z : ℤ) (rev : Bool) : Fin 4 → ℤ :=
  if rev then ![K x y z,A x y z,B x y z,L x y z]
  else ![B x y z,L x y z,K x y z,A x y z]
private def newHeads (x y z : ℤ) (rev : Bool) : Fin 4 → ℤ :=
  if rev then ![SW x y z,A x y z,SU x y z,SV x y z]
  else ![SU x y z,SV x y z,SW x y z,A x y z]
private def Windows (x y z m n : ℤ) (rev : Bool) : Prop :=
  ∀ i : Fin 3, window (oldSeams x y z m n rev i) (oldHeads x y z rev i.castSucc) ∧
    window (newSeams x y z m n rev i) (newHeads x y z rev i.castSucc)

private theorem quotient_spec (u v T : ℤ) (hu : 0≤u) (hv : 0<v)
    (hcap : u<T*v) :
    0≤u/v ∧ u/v<T ∧ 0≤u-(u/v)*v ∧ u-(u/v)*v<v := by
  have hq := Int.ediv_nonneg hu hv.le
  have he := Int.emod_add_mul_ediv u v
  have hr := Int.emod_nonneg u (ne_of_gt hv)
  have hr' := Int.emod_lt_of_pos u hv
  have heq : u-(u/v)*v=u%v := by nlinarith only [he]
  have hqc : u/v<T := by
    by_contra h
    have hp := mul_le_mul_of_nonneg_right (show T≤u/v by omega) hv.le
    nlinarith only [he,hr,hcap,hp]
  exact ⟨hq,hqc,by rw [heq];exact hr,by rw [heq];exact hr'⟩

private theorem common_polys (x y z : ℤ) (hx : 4≤x) (hy : 4≤y) (hz : 4≤z) :
    0<A x y z ∧ 0<B x y z ∧ 0<L x y z ∧ 0<SV x y z ∧
    2*B x y z<y*A x y z ∧ 2*SW x y z<y*SV x y z ∧
    L x y z≤2*A x y z-1 ∧ A x y z≤2*L x y z-1 ∧
    2*(2*A x y z-SV x y z)≤A x y z-1 := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ x=u+4 := ⟨x-4,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ y=v+4 := ⟨y-4,by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ z=w+4 := ⟨z-4,by omega,by omega⟩
  dsimp [A,B,L,SV,SW,K]
  repeat' constructor
  all_goals first | apply sub_pos.mp | apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

private theorem ascending_polys (x y z : ℤ) (hx : 4≤x)
    (hz : 2*x≤z) (hy : 2*z≤y) :
    1≤B x y z-A x y z ∧ 0≤SW x y z-2*A x y z ∧
    1≤L x y z-A x y z ∧ 0≤SV x y z-2*A x y z ∧
    2*L x y z+(y-1)*(z+1)≤K x y z-1 ∧
    2*SV x y z-2≤SW x y z-1 := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ x=u+4 := ⟨x-4,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ z=2*(u+4)+v := ⟨z-2*(u+4),by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ y=2*(2*(u+4)+v)+w :=
    ⟨y-2*(2*(u+4)+v),by omega,by omega⟩
  dsimp [A,B,L,K,SV,SW]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

private theorem descending_polys (x y z : ℤ) (hz : 4≤z)
    (hx : 2*z≤x) (hy : 2*x≤y) :
    1≤SW x y z-SV x y z ∧ 0≤B x y z-L x y z ∧
    1≤A x y z-L x y z ∧ 0≤2*A x y z-SV x y z ∧
    2*A x y z+z-1≤B x y z := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ z=u+4 := ⟨z-4,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ x=2*(u+4)+v := ⟨x-2*(u+4),by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ y=2*(2*(u+4)+v)+w :=
    ⟨y-2*(2*(u+4)+v),by omega,by omega⟩
  dsimp [A,B,L,K,SV,SW]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

private theorem separated_slack (x y z : ℤ) (hx : 4≤x) (hz : 4≤z) (hy : 4*x≤y) :
    2*L x y z+(y-2)*(z+1)≤K x y z-1 := by
  have hid : K x y z-1-(2*L x y z+(y-2)*(z+1))=y*z*(y-2*x-2) := by
    dsimp [K,L];ring
  apply sub_nonneg.mp
  rw [hid]
  exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)

private theorem adjacent_slack (x z : ℤ) (hx : 4≤x) (hz : 4≤z) :
    K x (2*x) z≤2*L x (2*x) z-1 := by
  have hid : 2*L x (2*x) z-1-K x (2*x) z=2*x*(z-1)+2*z := by
    dsimp [K,L];ring
  apply sub_nonneg.mp
  rw [hid]
  have hz0 : 0≤z-1 := by omega
  positivity

private theorem ascending_masks (x y z T : ℤ) (hx : 4≤x) (hz : 2*x≤z)
    (hy : 2*z≤y) (hT : 2*T=y) :
    ∃ m n : ℤ, (0≤m ∧ m<T) ∧ (0≤n ∧ n<T) ∧ Windows x y z m n false := by
  have hz4 : 4≤z := by omega
  have hy4 : 4≤y := by omega
  obtain ⟨hA,hB,hL,hSV,hBA,hSW,hLA,hAL,hfresh⟩ := common_polys x y z hx hy4 hz4
  obtain ⟨hgap,hnon,hpos,hepos,hhead,hnewhead⟩ := ascending_polys x y z hx hz hy
  have hTA : y*A x y z=2*(T*A x y z) := by rw [←hT];ring
  have hTV : y*SV x y z=2*(T*SV x y z) := by rw [←hT];ring
  let h := (B x y z-1)/A x y z
  let n := (SW x y z-2*A x y z)/SV x y z
  have qh := quotient_spec (B x y z-1) (A x y z) T (by omega) hA
    (by nlinarith only [hBA,hTA])
  have qn := quotient_spec (SW x y z-2*A x y z) (SV x y z) T hnon hSV
    (by nlinarith only [hSW,hTV,hA])
  change 0≤h ∧ h<T ∧ 0≤B x y z-1-h*A x y z ∧ B x y z-1-h*A x y z<A x y z at qh
  change 0≤n ∧ n<T ∧ 0≤SW x y z-2*A x y z-n*SV x y z ∧
    SW x y z-2*A x y z-n*SV x y z<SV x y z at qn
  have hh : 1≤h := by
    by_contra hn
    have he : h=0 := by omega
    rw [he] at qh
    nlinarith only [qh.2.2.2,hgap]
  let r := B x y z-h*A x y z
  let e := SW x y z-2*A x y z-n*SV x y z
  have hr : 1≤r ∧ r≤A x y z := by dsimp [r];omega
  have hmul := mul_le_mul_of_nonneg_right hh hA.le
  have hodd : B x y z%2=1 := by
    have hid : B x y z=2*(T*(1+x+x*y))+1 := by dsimp [B];rw [←hT];ring
    omega
  have hrB : 2*r≤B x y z-1 := by
    have hle : 2*r≤B x y z := by dsimp [r] at hr ⊢;nlinarith only [hmul,hr.2]
    omega
  have hnY : n≤y-1 := by omega
  have hnq := mul_le_mul_of_nonneg_right (show 0≤n by omega) (show 0≤z+1 by omega)
  have hvid : SV x y z=2*L x y z-z-1 := rfl
  have hid : 2*(K x y z-A x y z-n*L x y z)=e+1+(y-n)*(z+1) := by
    dsimp [e,K,A,L,SW,SV];ring
  have er : 0≤e ∧ e≤SV x y z-1 := by dsimp [e];omega
  have hprod : 0≤(y-n)*(z+1) := mul_nonneg (by omega) (by omega)
  refine ⟨h-1,n,⟨by omega,by omega⟩,⟨qn.1,qn.2.1⟩,?_⟩
  intro i
  fin_cases i <;> dsimp [Windows,oldSeams,newSeams,oldHeads,newHeads,window,SU]
  · constructor <;> constructor
    all_goals dsimp [r] at hr hrB
    all_goals nlinarith only [hr.1,hrB]
  · constructor <;> constructor
    all_goals dsimp [SV] at hepos ⊢
    all_goals nlinarith only [hpos,hepos,hLA,hz4]
  · constructor <;> constructor
    · nlinarith only [hid,er.1,hprod]
    · nlinarith only [hid,er.2,hhead,hnq,hvid]
    · nlinarith only [er.1]
    · nlinarith only [er.2,hnewhead]

private theorem descending_masks (x y z T : ℤ) (hz : 4≤z) (hx : 2*z≤x)
    (hy : 2*x≤y) (hT : 2*T=y) (dyadic : y=2*x ∨ 4*x≤y) :
    ∃ m n : ℤ, (0≤m ∧ m<T) ∧ (0≤n ∧ n<T) ∧ Windows x y z m n true := by
  have hx4 : 4≤x := by omega
  have hy4 : 4≤y := by omega
  obtain ⟨hA,hB,hL,hSV,hBA,hSW,hLA,hAL,hfresh⟩ := common_polys x y z hx4 hy4 hz
  obtain ⟨hgap,hBL,hpos,hepos,hbig⟩ := descending_polys x y z hz hx hy
  have hTA : y*A x y z=2*(T*A x y z) := by rw [←hT];ring
  have hTV : y*SV x y z=2*(T*SV x y z) := by rw [←hT];ring
  let p := SW x y z/SV x y z
  let m := (B x y z-L x y z)/A x y z
  have qp := quotient_spec (SW x y z) (SV x y z) T (by omega) hSV
    (by nlinarith only [hSW,hTV])
  have qm := quotient_spec (B x y z-L x y z) (A x y z) T hBL hA
    (by nlinarith only [hBA,hTA,hL])
  change 0≤p ∧ p<T ∧ 0≤SW x y z-p*SV x y z ∧ SW x y z-p*SV x y z<SV x y z at qp
  change 0≤m ∧ m<T ∧ 0≤B x y z-L x y z-m*A x y z ∧
    B x y z-L x y z-m*A x y z<A x y z at qm
  have hp : 1≤p := by
    by_contra hn
    have he : p=0 := by omega
    rw [he] at qp
    nlinarith only [qp.2.2.2,hgap]
  let e := SW x y z-p*SV x y z
  let r := K x y z-p*L x y z
  have er : 0≤e ∧ e≤SV x y z-1 := by dsimp [e];omega
  have hid : 2*r=e+1+(y-p)*(z+1) := by dsimp [r,e,K,L,SW,SV];ring
  have hprod : 0≤(y-p)*(z+1) := mul_nonneg (by omega) (by omega)
  have hr0 : 0≤2*r := by nlinarith only [hid,er.1,hprod]
  have hr1 : 2*r≤K x y z-1 := by
    rcases dyadic with he|hsep
    · have hs := adjacent_slack x z hx4 hz
      rw [←he] at hs
      have hm := mul_le_mul_of_nonneg_right hp hL.le
      dsimp [r]
      nlinarith only [hs,hm]
    · have hs := separated_slack x y z hx4 hz hsep
      have hm := mul_le_mul_of_nonneg_right (show 1≤p by omega) (show 0≤z+1 by omega)
      dsimp [SV] at er
      nlinarith only [hid,er.2,hs,hm]
  have he1 : 2*e≤SW x y z-1 := by
    have hm := mul_le_mul_of_nonneg_right hp hSV.le
    dsimp [e] at er ⊢
    nlinarith only [hm,er.2]
  have hid3 : SU x y z-SV x y z-2*m*A x y z=
      2*(B x y z-L x y z-m*A x y z)+z := by dsimp [SU,SV];ring
  refine ⟨m,p-1,⟨qm.1,qm.2.1⟩,⟨by omega,by omega⟩,?_⟩
  intro i
  fin_cases i <;> dsimp [Windows,oldSeams,newSeams,oldHeads,newHeads,window]
  · constructor <;> constructor
    · simpa [r] using hr0
    · simpa [r] using hr1
    · simpa [e] using (show 0≤2*e by omega)
    · simpa [e] using he1
  · constructor <;> constructor <;> nlinarith only [hpos,hAL,hepos,hfresh]
  · rw [hid3]
    constructor <;> constructor
    all_goals try dsimp [SU]
    all_goals nlinarith only [qm.2.2.1,qm.2.2.2,hbig,hz]

private theorem power_four (a : ℕ) (ha : 2≤a) : (4:ℤ)≤2^a := by
  calc
    (4:ℤ)=2^2 := by norm_num
    _ ≤ 2^a := by gcongr <;> omega

private theorem power_gap (a b : ℕ) (hab : a<b) : 2*(2:ℤ)^a≤2^b := by
  calc
    2*(2:ℤ)^a=2^(a+1) := by rw [pow_succ];ring
    _ ≤ 2^b := by gcongr <;> omega

private theorem selection (a s c : ℕ) (ha : 2≤a) (hc : 2≤c)
    (hab : a<s) (hcb : c<s) (hne : a≠c) :
    ∃ m n : ℕ, m<2^(s-1) ∧ n<2^(s-1) ∧
      Windows (2^a) (2^s) (2^c) m n (decide (c<a)) := by
  have hhalf : 2*(2:ℤ)^(s-1)=2^s := by
    calc
      2*(2:ℤ)^(s-1)=2^((s-1)+1) := by rw [pow_succ];ring
      _ = 2^s := by congr 1;omega
  have hmasks (rev : Bool)
      (h : ∃ m n : ℤ, (0≤m ∧ m<(2:ℤ)^(s-1)) ∧
        (0≤n ∧ n<(2:ℤ)^(s-1)) ∧ Windows (2^a) (2^s) (2^c) m n rev) :
      ∃ m n : ℕ, m<2^(s-1) ∧ n<2^(s-1) ∧
        Windows (2^a) (2^s) (2^c) m n rev := by
    obtain ⟨m,n,hm,hn,hw⟩ := h
    refine ⟨m.toNat,n.toNat,?_,?_,?_⟩
    · exact_mod_cast (show (m.toNat:ℤ)<(2:ℤ)^(s-1) by
        simpa only [Int.toNat_of_nonneg hm.1] using hm.2)
    · exact_mod_cast (show (n.toNat:ℤ)<(2:ℤ)^(s-1) by
        simpa only [Int.toNat_of_nonneg hn.1] using hn.2)
    · simpa only [Int.toNat_of_nonneg hm.1,Int.toNat_of_nonneg hn.1] using hw
  rcases lt_or_gt_of_ne hne with hac|hca
  · simpa only [show decide (c<a)=false by simp [Nat.not_lt.mpr hac.le]] using
      hmasks false (ascending_masks _ _ _ _ (power_four a ha)
        (power_gap a c hac) (power_gap c s hcb) hhalf)
  · have hd : (2:ℤ)^s=2*2^a ∨ 4*2^a≤(2:ℤ)^s := by
      by_cases he : s=a+1
      · left;rw [he,pow_succ];ring
      · right
        calc
          4*(2:ℤ)^a=2^(a+2) := by rw [pow_add];norm_num;ring
          _ ≤ 2^s := by gcongr <;> omega
    simpa only [show decide (c<a)=true by simp [hca]] using
      hmasks true (descending_masks _ _ _ _ (power_four c hc)
        (power_gap c a hca) (power_gap a s hab) hhalf hd)

end D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum

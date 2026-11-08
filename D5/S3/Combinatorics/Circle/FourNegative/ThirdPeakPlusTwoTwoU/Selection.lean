/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPlusTwoTwoU/Selection
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded integer window selection for the original two-U plus-two domain. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Arithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
open private A B L K SU SV SW D window firstTwo general_firstTwo general_aux boundary_firstTwo
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Arithmetic

/- The lower new window is proved only after the chosen D is nonnegative.
Unused later candidates are allowed to have negative D and T. -/
private theorem general_select (x y t : ℤ) (hy : 4≤y) (hx : 2*y≤x) (ht : 8*x≤t) :
    ∃ u v : ℕ, u≤2 ∧ 1≤v ∧ 4*(v:ℤ)≤4*t ∧
      firstTwo x y t u ∧ window (D x y t u v) (A x y t) ∧
      window (2*D x y t u v+4*t-2*v) (A x y t) := by
  obtain ⟨hEz,hEB,hstop,hratio,hLB⟩ := general_aux x y t hy hx ht
  have hx0 : 0≤x := by omega
  have hy0 : 0≤y := by omega
  have ht0 : 0≤t := by omega
  have hB : 0<B x y t := by dsimp [B]; positivity
  have hL : 0<L x y t := by dsimp [L]; positivity
  let E := 4*B x y t-A x y t
  let z := 4*t
  have heq : E=4*B x y t-A x y t := rfl
  have hz : 256≤z := by dsimp [z]; omega
  have hE : z<E := hEz
  have hstopZ : 28*B x y t+z<9*A x y t := hstop
  have hEA : 3*B x y t<A x y t := by omega
  -- Positive-integer ceiling: ceil((L-B)/(2B)) = (L-B-1)/(2B)+1.
  let c := (L x y t-B x y t-1)/(2*B x y t)+1
  have hc : 1≤c := by
    have hq := Int.ediv_nonneg (show 0≤L x y t-B x y t-1 by omega)
      (show 0≤2*B x y t by omega)
    dsimp [c]; omega
  let d0 := (2*c+1)*B x y t-L x y t
  have hd0 : 0≤d0 ∧ d0<2*B x y t := by
    have hrem := Int.emod_nonneg (L x y t-B x y t-1)
      (show 2*B x y t≠0 by omega)
    have hrem' := Int.emod_lt_of_pos (L x y t-B x y t-1)
      (show 0<2*B x y t by omega)
    have hdiv := Int.mul_ediv_add_emod (L x y t-B x y t-1) (2*B x y t)
    dsimp [d0,c]
    constructor <;> nlinarith only [hrem,hrem',hdiv]
  have hratio4 : 4*L x y t<z*B x y t := by
    have hmul : 0≤(y-4)*L x y t := mul_nonneg (by omega) hL.le
    dsimp [z]
    nlinarith only [hratio,hmul]
  have hcstock : 8*c<z+4 := by
    by_contra hh
    have hs : (z+4)*B x y t≤8*c*B x y t :=
      mul_le_mul_of_nonneg_right (by omega) hB.le
    dsimp [d0] at hd0
    nlinarith only [hd0.2,hratio4,hs]
  let d1 := d0+2*E-2*B x y t
  let d2 := d0+4*E-4*B x y t
  let v0 := c
  let v1 := c+3
  let v2 := c+6
  let T0 := 2*d0+z-2*v0
  let T1 := 2*d1+z-2*v1
  let T2 := 2*d2+z-2*v2
  have hstock (i : ℤ) (hi : 0≤ i ∧ i≤2) : 1≤c+3*i ∧ 4*(c+3*i)≤z := by
    constructor <;> omega
  have hD1 : D x y t 1 v1=d1 := by dsimp [D,d1,d0,v1,E]; ring
  have hD2 : D x y t 2 v2=d2 := by dsimp [D,d2,d0,v2,E]; ring
  have hD0 : D x y t 0 v0=d0 := by dsimp [D,d0,v0]; ring
  have hd1upper : d1<2*B x y t := by dsimp [d1]; omega
  have hd2upper : d2<2*B x y t := by dsimp [d2]; omega
  have hnext1 (hf : A x y t≤T0) : 0<d1 := by
    dsimp [T0,v0,d1] at hf ⊢
    omega
  have hnext2 (hf : A x y t≤T1) : 0<d2 := by
    dsimp [T1,v1,d1,d2] at hf ⊢
    omega
  have hT2 : T2≤A x y t-1 := by
    dsimp [T2,d2,v2]
    omega
  have finish (u : ℕ) (hu : u≤2) (v : ℤ) (hv : 1≤v ∧ 4*v≤z)
      (hd : window (D x y t u v) (A x y t))
      (hT : 2*D x y t u v+z-2*v≤A x y t-1) :
      ∃ u v : ℕ, u≤2 ∧ 1≤v ∧ 4*(v:ℤ)≤4*t ∧
        firstTwo x y t u ∧ window (D x y t u v) (A x y t) ∧
        window (2*D x y t u v+4*t-2*v) (A x y t) := by
    have hvcast : (v.toNat:ℤ)=v := Int.toNat_of_nonneg (by omega)
    have hTlow : 0≤2*D x y t u v+z-2*v := by
      have hnon := hd.1
      omega
    refine ⟨u,v.toNat,hu,?_,?_,general_firstTwo x y t hy hx ht u ⟨by positivity,by exact_mod_cast hu⟩,?_,?_⟩
    · exact_mod_cast (show (1:ℤ)≤(v.toNat:ℤ) by rw [hvcast]; exact hv.1)
    · simpa only [hvcast] using hv.2
    · simpa only [hvcast] using hd
    · simpa only [window,hvcast] using And.intro hTlow hT
  by_cases h0 : T0≤A x y t-1
  · apply finish 0 (by omega) v0 (by simpa [v0] using hstock 0 ⟨by omega,by omega⟩)
    · simp only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat, hD0]; exact ⟨hd0.1,by omega⟩
    · simpa only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,hD0,T0] using h0
  · have hd1pos := hnext1 (by omega)
    by_cases h1 : T1≤A x y t-1
    · apply finish 1 (by omega) v1 (by simpa [v1] using hstock 1 ⟨by omega,by omega⟩)
      · simp only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat, hD1]; exact ⟨hd1pos.le,by omega⟩
      · simpa only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,hD1,T1] using h1
    · have hd2pos := hnext2 (by omega)
      apply finish 2 (by omega) v2 (by simpa [v2] using hstock 2 ⟨by omega,by omega⟩)
      · simp only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat, hD2]; exact ⟨hd2pos.le,by omega⟩
      · simpa only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,hD2,T2] using hT2

private theorem boundary_mod0 (x v : ℤ) (hx : 8≤x) (hv : 5*v=8*x+7) :
    window (D x 4 (4*x) 0 v) (A x 4 (4*x)) ∧
    window (2*D x 4 (4*x) 0 v+16*x-2*v) (A x 4 (4*x)) ∧
    1≤v ∧ v≤8*x-1 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have c0 : 0<5*(D x 4 (4*x) 0 v) := by
    have he : 5*(D x 4 (4*x) 0 v) = 124 * p^2 + 1996 * p + 8046 := by
      have hm := congrArg (fun w : ℤ => (2*(1+4*x+20*x^2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c1 : 0<5*(A x 4 (4*x)-1-D x 4 (4*x) 0 v) := by
    have he : 5*(A x 4 (4*x)-1-D x 4 (4*x) 0 v) = 196 * p^2 + 3149 * p + 12634 := by
      have hm := congrArg (fun w : ℤ => (-(2*(1+4*x+20*x^2))) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c2 : 0<5*(2*D x 4 (4*x) 0 v+16*x-2*v) := by
    have he : 5*(2*D x 4 (4*x) 0 v+16*x-2*v) = 248 * p^2 + 4056 * p + 16590 := by
      have hm := congrArg (fun w : ℤ => (4*(1+4*x+20*x^2)-2) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c3 : 0<5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 0 v+16*x-2*v)) := by
    have he : 5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 0 v+16*x-2*v)) = 72 * p^2 + 1089 * p + 4090 := by
      have hm := congrArg (fun w : ℤ => (-(4*(1+4*x+20*x^2)-2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c4 : 0<5*(v) := by
    have he : 5*(v) = 8 * p + 71 := by
      have hm := congrArg (fun w : ℤ => (1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c5 : 0<5*(8*x-1-v) := by
    have he : 5*(8*x-1-v) = 32 * p + 244 := by
      have hm := congrArg (fun w : ℤ => (-1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by omega⟩

private theorem boundary_mod1 (x v : ℤ) (hx : 8≤x) (hv : 5*v=8*x+4) :
    window (D x 4 (4*x) 0 v) (A x 4 (4*x)) ∧
    window (2*D x 4 (4*x) 0 v+16*x-2*v) (A x 4 (4*x)) ∧
    1≤v ∧ v≤8*x-1 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have c0 : 0<5*(D x 4 (4*x) 0 v) := by
    have he : 5*(D x 4 (4*x) 0 v) = 4 * p^2 + 52 * p + 168 := by
      have hm := congrArg (fun w : ℤ => (2*(1+4*x+20*x^2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c1 : 0<5*(A x 4 (4*x)-1-D x 4 (4*x) 0 v) := by
    have he : 5*(A x 4 (4*x)-1-D x 4 (4*x) 0 v) = 316 * p^2 + 5093 * p + 20512 := by
      have hm := congrArg (fun w : ℤ => (-(2*(1+4*x+20*x^2))) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c2 : 0<5*(2*D x 4 (4*x) 0 v+16*x-2*v) := by
    have he : 5*(2*D x 4 (4*x) 0 v+16*x-2*v) = 8 * p^2 + 168 * p + 840 := by
      have hm := congrArg (fun w : ℤ => (4*(1+4*x+20*x^2)-2) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c3 : 0<5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 0 v+16*x-2*v)) := by
    have he : 5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 0 v+16*x-2*v)) = 312 * p^2 + 4977 * p + 19840 := by
      have hm := congrArg (fun w : ℤ => (-(4*(1+4*x+20*x^2)-2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c4 : 0<5*(v) := by
    have he : 5*(v) = 8 * p + 68 := by
      have hm := congrArg (fun w : ℤ => (1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c5 : 0<5*(8*x-1-v) := by
    have he : 5*(8*x-1-v) = 32 * p + 247 := by
      have hm := congrArg (fun w : ℤ => (-1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by omega⟩

private theorem boundary_mod2 (x v : ℤ) (hx : 8≤x) (hv : 5*v=8*x+23) :
    window (D x 4 (4*x) 1 v) (A x 4 (4*x)) ∧
    window (2*D x 4 (4*x) 1 v+16*x-2*v) (A x 4 (4*x)) ∧
    1≤v ∧ v≤8*x-1 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have c0 : 0<5*(D x 4 (4*x) 1 v) := by
    have he : 5*(D x 4 (4*x) 1 v) = 124 * p^2 + 2074 * p + 8692 := by
      have hm := congrArg (fun w : ℤ => (2*(1+4*x+20*x^2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c1 : 0<5*(A x 4 (4*x)-1-D x 4 (4*x) 1 v) := by
    have he : 5*(A x 4 (4*x)-1-D x 4 (4*x) 1 v) = 196 * p^2 + 3071 * p + 11988 := by
      have hm := congrArg (fun w : ℤ => (-(2*(1+4*x+20*x^2))) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c2 : 0<5*(2*D x 4 (4*x) 1 v+16*x-2*v) := by
    have he : 5*(2*D x 4 (4*x) 1 v+16*x-2*v) = 248 * p^2 + 4212 * p + 17850 := by
      have hm := congrArg (fun w : ℤ => (4*(1+4*x+20*x^2)-2) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c3 : 0<5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 1 v+16*x-2*v)) := by
    have he : 5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 1 v+16*x-2*v)) = 72 * p^2 + 933 * p + 2830 := by
      have hm := congrArg (fun w : ℤ => (-(4*(1+4*x+20*x^2)-2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c4 : 0<5*(v) := by
    have he : 5*(v) = 8 * p + 87 := by
      have hm := congrArg (fun w : ℤ => (1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c5 : 0<5*(8*x-1-v) := by
    have he : 5*(8*x-1-v) = 32 * p + 228 := by
      have hm := congrArg (fun w : ℤ => (-1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by omega⟩

private theorem boundary_mod3 (x v : ℤ) (hx : 8≤x) (hv : 5*v=8*x+6) :
    window (D x 4 (4*x) 0 v) (A x 4 (4*x)) ∧
    window (2*D x 4 (4*x) 0 v+16*x-2*v) (A x 4 (4*x)) ∧
    1≤v ∧ v≤8*x-1 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have c0 : 0<5*(D x 4 (4*x) 0 v) := by
    have he : 5*(D x 4 (4*x) 0 v) = 84 * p^2 + 1348 * p + 5420 := by
      have hm := congrArg (fun w : ℤ => (2*(1+4*x+20*x^2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c1 : 0<5*(A x 4 (4*x)-1-D x 4 (4*x) 0 v) := by
    have he : 5*(A x 4 (4*x)-1-D x 4 (4*x) 0 v) = 236 * p^2 + 3797 * p + 15260 := by
      have hm := congrArg (fun w : ℤ => (-(2*(1+4*x+20*x^2))) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c2 : 0<5*(2*D x 4 (4*x) 0 v+16*x-2*v) := by
    have he : 5*(2*D x 4 (4*x) 0 v+16*x-2*v) = 168 * p^2 + 2760 * p + 11340 := by
      have hm := congrArg (fun w : ℤ => (4*(1+4*x+20*x^2)-2) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c3 : 0<5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 0 v+16*x-2*v)) := by
    have he : 5*(A x 4 (4*x)-1-(2*D x 4 (4*x) 0 v+16*x-2*v)) = 152 * p^2 + 2385 * p + 9340 := by
      have hm := congrArg (fun w : ℤ => (-(4*(1+4*x+20*x^2)-2)) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c4 : 0<5*(v) := by
    have he : 5*(v) = 8 * p + 70 := by
      have hm := congrArg (fun w : ℤ => (1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  have c5 : 0<5*(8*x-1-v) := by
    have he : 5*(8*x-1-v) = 32 * p + 245 := by
      have hm := congrArg (fun w : ℤ => (-1) * w) hv
      dsimp [D,A,B,L,p]
      nlinarith only [hm]
    rw [he]
    positivity
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by omega⟩

private theorem power_mod_five (a : ℕ) :
    (a%4=0 ∧ 2^a%5=1) ∨ (a%4=1 ∧ 2^a%5=2) ∨
    (a%4=2 ∧ 2^a%5=4) ∨ (a%4=3 ∧ 2^a%5=3) := by
  have hpow : (2:ℕ)^a=2^(a%4)*(2^4)^(a/4) := by
    conv_lhs => rw [←Nat.mod_add_div a 4]
    rw [pow_add,pow_mul]
  have hm : (2:ℕ)^a%5=2^(a%4)%5 := by
    have hf : ((2^4:ℕ)^(a/4))%5=1 := by rw [Nat.pow_mod]; norm_num
    rw [hpow,Nat.mul_mod,hf]
    simp
  have hr := Nat.mod_lt a (by decide : 0<4)
  have hc : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
  rcases hc with hc|hc|hc|hc
  · left; exact ⟨hc,by norm_num [hc] at hm; exact hm⟩
  · right; left; exact ⟨hc,by norm_num [hc] at hm; exact hm⟩
  · right; right; left; exact ⟨hc,by norm_num [hc] at hm; exact hm⟩
  · right; right; right; exact ⟨hc,by norm_num [hc] at hm; exact hm⟩

private theorem boundary_select (a : ℕ) (ha : 3≤a) :
    let x : ℤ := 2^a
    ∃ u v : ℕ, u≤1 ∧ 1≤v ∧ (v:ℤ)≤8*x-1 ∧
      firstTwo x 4 (4*x) u ∧ window (D x 4 (4*x) u v) (A x 4 (4*x)) ∧
      window (2*D x 4 (4*x) u v+16*x-2*v) (A x 4 (4*x)) := by
  dsimp only
  let x : ℤ := 2^a
  have hx : 8≤x := by
    simpa [x] using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha
  have divcast (n : ℕ) (hn : (8*2^a+n)%5=0) :
      5*(((8*2^a+n)/5:ℕ):ℤ)=8*x+n := by
    have hh := Nat.mod_add_div (8*2^a+n) 5
    rw [hn,zero_add] at hh
    dsimp [x]
    exact_mod_cast hh
  rcases power_mod_five a with h|h|h|h
  · let v := (8*2^a+7)/5
    have hv : 5*(v:ℤ)=8*x+7 := divcast 7 (by norm_num [Nat.add_mod,Nat.mul_mod,h.2])
    obtain ⟨ho,hn,hv0,hv1⟩ := boundary_mod0 x v hx hv
    exact ⟨0,v,by omega,by exact_mod_cast hv0,hv1,
      boundary_firstTwo x hx 0 ⟨by omega,by omega⟩,ho,hn⟩
  · let v := (8*2^a+4)/5
    have hv : 5*(v:ℤ)=8*x+4 := divcast 4 (by norm_num [Nat.add_mod,Nat.mul_mod,h.2])
    obtain ⟨ho,hn,hv0,hv1⟩ := boundary_mod1 x v hx hv
    exact ⟨0,v,by omega,by exact_mod_cast hv0,hv1,
      boundary_firstTwo x hx 0 ⟨by omega,by omega⟩,ho,hn⟩
  · let v := (8*2^a+23)/5
    have hv : 5*(v:ℤ)=8*x+23 := divcast 23 (by norm_num [Nat.add_mod,Nat.mul_mod,h.2])
    obtain ⟨ho,hn,hv0,hv1⟩ := boundary_mod2 x v hx hv
    exact ⟨1,v,by omega,by exact_mod_cast hv0,hv1,
      boundary_firstTwo x hx 1 ⟨by omega,by omega⟩,ho,hn⟩
  · let v := (8*2^a+6)/5
    have hv : 5*(v:ℤ)=8*x+6 := divcast 6 (by norm_num [Nat.add_mod,Nat.mul_mod,h.2])
    obtain ⟨ho,hn,hv0,hv1⟩ := boundary_mod3 x v hx hv
    exact ⟨0,v,by omega,by exact_mod_cast hv0,hv1,
      boundary_firstTwo x hx 0 ⟨by omega,by omega⟩,ho,hn⟩

private theorem original_select (a b d : ℕ) (hb : 2≤b) (hba : b<a)
    (hdom : a+3≤d ∨ b=2 ∧ d=a+2) :
    ∃ u v : ℕ, u<2^(d-1) ∧ v<2^((d+2)-1) ∧
      firstTwo (2^a) (2^b) (2^d) u ∧
      window (D (2^a) (2^b) (2^d) u v) (A (2^a) (2^b) (2^d)) ∧
      window (2*D (2^a) (2^b) (2^d) u v+4*2^d-2*v) (A (2^a) (2^b) (2^d)) := by
  have hd : 2≤d := by rcases hdom with h|⟨_,h⟩ <;> omega
  have hU : (2:ℤ)*((2^(d-1):ℕ):ℤ)=(2:ℤ)^d := by
    push_cast
    calc
      (2:ℤ)*2^(d-1)=2^((d-1)+1) := by rw [pow_succ]; ring
      _=2^d := by congr 1; omega
  have hV : ((2^((d+2)-1):ℕ):ℤ)=2*(2:ℤ)^d := by
    push_cast
    simp only [show d+2-1=d+1 by omega,pow_succ]
    ring
  have hy : (4:ℤ)≤2^b := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hb
  rcases hdom with hdom|⟨rfl,rfl⟩
  · have hx : (2:ℤ)*2^b≤2^a := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show b+1≤a by omega)
      simpa [pow_succ,mul_comm] using hh
    have ht : (8:ℤ)*2^a≤2^d := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hdom
      simpa [pow_add,mul_comm] using hh
    obtain ⟨u,v,hu,hv0,hv,hf,ho,hn⟩ := general_select (2^a) (2^b) (2^d) hy hx ht
    have ht0 : (64:ℤ)≤2^d := by omega
    refine ⟨u,v,?_,?_,hf,ho,hn⟩
    · have hu' : (u:ℤ)≤2 := by exact_mod_cast hu
      have : (u:ℤ)<((2^(d-1):ℕ):ℤ) := by omega
      exact_mod_cast this
    · have : (v:ℤ)<((2^((d+2)-1):ℕ):ℤ) := by rw [hV]; omega
      exact_mod_cast this
  · obtain ⟨u,v,hu,hv0,hv,hf,ho,hn⟩ := boundary_select a (by omega)
    have ht : (2:ℤ)^(a+2)=4*(2:ℤ)^a := by rw [pow_add]; norm_num; ring
    have hx : (8:ℤ)≤2^a := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 3≤a by omega)
    refine ⟨u,v,?_,?_,?_,?_,?_⟩
    · have hu' : (u:ℤ)≤1 := by exact_mod_cast hu
      have : (u:ℤ)<((2^(a+2-1):ℕ):ℤ) := by rw [ht] at hU; omega
      exact_mod_cast this
    · have : (v:ℤ)<((2^((a+2+2)-1):ℕ):ℤ) := by rw [hV,ht]; omega
      exact_mod_cast this
    · simpa only [ht,show (2:ℤ)^2=4 by norm_num] using hf
    · simpa only [ht,show (2:ℤ)^2=4 by norm_num] using ho
    · have h16 : 4*(4*(2:ℤ)^a)=16*(2:ℤ)^a := by ring
      simpa only [ht,show (2:ℤ)^2=4 by norm_num,h16] using hn

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU

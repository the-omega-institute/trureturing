/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: ThirdPeakEqualOuter Arithmetic for the complete original physical family. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

/-! ThirdPeakEqualOuter: Arithmetic. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter

private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y : ℤ) : ℤ := 1+x+x*x+x*x*y
private def L (x z : ℤ) : ℤ := 1+z+z*x+x*x*z
private def K (x y z : ℤ) : ℤ := 1+y+y*z+x*y*z
private def SU (x y : ℤ) : ℤ := 2*B x y-1
private def SV (x z : ℤ) : ℤ := 2*L x z-1-z
private def SW (x y z : ℤ) : ℤ := 2*K x y z-(1+y+y*z)
private def Window (e head : ℤ) : Prop := 0 ≤ 2*e ∧ 2*e ≤ head-1

private def AfterWWindows (x y z r v : ℤ) : Prop :=
  let δ := r*A x y z-v*B x y
  let ε := 2*r*A x y z-v*SU x y
  Window (L x z-v*B x y) (L x z) ∧
  Window (K x y z-A x y z+δ) (K x y z) ∧
  Window δ (A x y z) ∧ Window 0 (B x y) ∧
  Window (SV x z-v*SU x y) (SV x z) ∧
  Window (SW x y z-2*A x y z+ε) (SW x y z) ∧
  Window ε (A x y z) ∧ Window 0 (SU x y)

private theorem window_zero (h : ℤ) (hh : 1 ≤ h) : Window 0 h := by
  dsimp [Window]; omega

private theorem geometric_slacks (s y z : ℤ) (hs : 2 ≤ s) (hy : 4 ≤ y)
    (hz : 2*(s*y) ≤ z) :
    0 < L (s*y) z-s*A (s*y) y z ∧
    0 < SV (s*y) z-2*s*A (s*y) y z ∧
    0 < K (s*y) y z-A (s*y) y z ∧
    0 < 3*A (s*y) y z-2*K (s*y) y z ∧
    0 < 3*A (s*y) y z-SW (s*y) y z := by
  obtain ⟨S,hS,rfl⟩ : ∃ S : ℤ, 0 ≤ S ∧ s=2+S := ⟨s-2,by omega,by ring⟩
  obtain ⟨Y,hY,rfl⟩ : ∃ Y : ℤ, 0 ≤ Y ∧ y=4+Y := ⟨y-4,by omega,by ring⟩
  obtain ⟨Z,hZ,rfl⟩ : ∃ Z : ℤ, 0 ≤ Z ∧ z=2*((2+S)*(4+Y))+Z :=
    ⟨z-2*((2+S)*(4+Y)),by omega,by ring⟩
  dsimp [A,B,L,K,SU,SV,SW]
  repeat' constructor
  all_goals ring_nf
  all_goals positivity

/-- Only the reached selector is constrained. In particular, this lemma makes
no assertion about a selector that another residue branch did not choose. -/
private theorem afterW_windows (s y z r v : ℤ) (hs : 2 ≤ s) (hy : 4 ≤ y)
    (hz : 2*(s*y) ≤ z) (hr : r ≤ s) (hv : 0 < v)
    (hd : 0 < r*A (s*y) y z-v*B (s*y) y)
    (he : 2*(2*r*A (s*y) y z-v*SU (s*y) y) ≤ A (s*y) y z-1)
    (hfirst : 2*v*SU (s*y) y > 2*L (s*y) z+2)
    (hsecond : 0 ≤ SW (s*y) y z-2*A (s*y) y z+
      (2*r*A (s*y) y z-v*SU (s*y) y)) :
    AfterWWindows (s*y) y z r v := by
  let x := s*y
  let δ := r*A x y z-v*B x y
  let ε := 2*r*A x y z-v*SU x y
  have hrel : ε=2*δ+v := by dsimp [ε,δ,SU]; ring
  have hδ : 0 < δ := hd
  have hε : 0 < ε := by omega
  have hx : 0 < x := by dsimp [x]; exact mul_pos (by omega) (by omega)
  have hz0 : 0 ≤ z := by change 2*x ≤ z at hz; omega
  have ha : 0 < A x y z := by
    dsimp [A]; positivity
  have hb : 1 ≤ B x y := by
    have hh : 0 ≤ x+x*x+x*x*y := by positivity
    dsimp [B]; nlinarith only [hh]
  obtain ⟨hl,hn,hk,hka,hsa⟩ := geometric_slacks s y z hs hy hz
  change 0 < L x z-s*A x y z at hl
  change 0 < SV x z-2*s*A x y z at hn
  change 0 < K x y z-A x y z at hk
  change 0 < 3*A x y z-2*K x y z at hka
  change 0 < 3*A x y z-SW x y z at hsa
  have hra : r*A x y z ≤ s*A x y z := mul_le_mul_of_nonneg_right hr ha.le
  have hεbound : 2*ε ≤ A x y z-1 := he
  have hfirst' : 2*v*SU x y > 2*L x z+2 := hfirst
  have hsecond' : 0 ≤ SW x y z-2*A x y z+ε := hsecond
  have hsu : SU x y=2*B x y-1 := rfl
  have hsv : SV x z=2*L x z-1-z := rfl
  have hvrel : 2*v*B x y=v*SU x y+v := by dsimp [SU]; ring
  dsimp only [AfterWWindows]
  change Window (L x z-v*B x y) (L x z) ∧
    Window (K x y z-A x y z+δ) (K x y z) ∧
    Window δ (A x y z) ∧ Window 0 (B x y) ∧
    Window (SV x z-v*SU x y) (SV x z) ∧
    Window (SW x y z-2*A x y z+ε) (SW x y z) ∧
    Window ε (A x y z) ∧ Window 0 (SU x y)
  refine ⟨?_,?_,?_,window_zero _ hb,?_,?_,?_,window_zero _ (by omega)⟩
  · dsimp [Window]
    constructor
    · dsimp [δ] at hδ
      nlinarith only [hl,hra,hδ]
    · nlinarith only [hfirst',hvrel,hv]
  · dsimp [Window]; constructor <;> omega
  · dsimp [Window]; constructor <;> omega
  · dsimp [Window]
    constructor
    · dsimp [ε] at hε
      nlinarith only [hn,hra,hε]
    · nlinarith only [hfirst',hsv,hz0]
  · dsimp [Window]; constructor <;> omega
  · dsimp [Window]; constructor <;> omega

private theorem pow_split (u v : ℕ) (h : v ≤ u) :
    (2:ℤ)^u=2^(u-v)*2^v := by
  rw [←pow_add]
  congr 1
  omega

private theorem pow_lower (n lo : ℕ) (h : lo ≤ n) :
    (2:ℤ)^lo ≤ 2^n := pow_le_pow_right₀ (by norm_num) h

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter

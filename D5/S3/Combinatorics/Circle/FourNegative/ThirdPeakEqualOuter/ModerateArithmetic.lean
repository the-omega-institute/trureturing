/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/ModerateArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: ThirdPeakEqualOuter ModerateArithmetic for the complete original physical family. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.LargeThird

/-! ThirdPeakEqualOuter: ModerateArithmetic. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open private A B L K SU SV SW Window
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private floor_bounds
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

private def FirstTwoWindows (x y z E Ep R Rp : ℤ) : Prop :=
  Window E (B x y) ∧ Window Ep (SU x y) ∧
  Window R (L x z) ∧ Window Rp (SV x z)

private theorem moderate_W (x y m : ℤ) (hy : 8 ≤ y) (hx : 2*y ≤ x)
    (hm : m=2 ∨ 4 ≤ m) :
    Window (K x y (m*x)-A x y (m*x)) (K x y (m*x)) ∧
    Window (SW x y (m*x)-2*A x y (m*x)+(if m=2 then A x y (m*x) else 0))
      (SW x y (m*x)) := by
  obtain ⟨Y,hY,rfl⟩ : ∃ Y : ℤ, 0 ≤ Y ∧ y=8+Y := ⟨y-8,by omega,by ring⟩
  obtain ⟨X,hX,rfl⟩ : ∃ X : ℤ, 0 ≤ X ∧ x=2*(8+Y)+X := ⟨x-2*(8+Y),by omega,by ring⟩
  rcases hm with rfl|hm
  · simp only [ite_true]
    dsimp [Window]
    repeat' constructor
    all_goals first | apply sub_nonneg.mp | skip
    all_goals dsimp [A,B,L,K,SU,SV,SW]
    all_goals ring_nf
    all_goals positivity
  · obtain ⟨M,hM,rfl⟩ : ∃ M : ℤ, 0 ≤ M ∧ m=4+M := ⟨m-4,by omega,by ring⟩
    rw [if_neg (by omega)]
    dsimp [Window]
    repeat' constructor
    all_goals first | apply sub_nonneg.mp | skip
    all_goals dsimp [A,B,L,K,SU,SV,SW]
    all_goals ring_nf
    all_goals positivity

private theorem moderate_high_slacks (x y m : ℤ)
    (hy : 8 ≤ y) (hx : 4*y ≤ x) (hm : 2 ≤ m) (hmy : 4*m ≤ y) :
    0 < m*B x y-A x y (m*x) ∧
    0 < 2*(m*B x y-A x y (m*x))-m ∧
    0 < B x y-1-2*(m*B x y-A x y (m*x)) ∧
    0 < L x (m*x)-2*m*B x y := by
  obtain ⟨M,hM,rfl⟩ : ∃ M : ℤ, 0 ≤ M ∧ m=2+M := ⟨m-2,by omega,by ring⟩
  obtain ⟨β,hβ,rfl⟩ : ∃ β : ℤ, 0 ≤ β ∧ y=4*(2+M)+β := ⟨y-4*(2+M),by omega,by ring⟩
  obtain ⟨X,hX,rfl⟩ : ∃ X : ℤ, 0 ≤ X ∧ x=4*(4*(2+M)+β)+X :=
    ⟨x-4*(4*(2+M)+β),by omega,by ring⟩
  dsimp [A,B,L]
  repeat' constructor
  all_goals ring_nf
  all_goals positivity

set_option maxHeartbeats 1800000 in
private theorem moderate_high_selector (x y m : ℤ)
    (hy : 8 ≤ y) (hx : 4*y ≤ x) (hm : 2 ≤ m) (hmy : 4*m ≤ y) :
    ∃ h : ℤ, 0 ≤ h ∧ 2*h < x ∧
      FirstTwoWindows x y (m*x)
        (m*B x y-A x y (m*x)) (2*(m*B x y-A x y (m*x))-m)
        (L x (m*x)-A x y (m*x)-h*m*B x y)
        (2*(L x (m*x)-A x y (m*x)-h*m*B x y)-m*x-1+m*h) := by
  let h := (x-y)/(y+1)
  let ρ := (x-y)%(y+1)
  let J := m*B x y
  let R := L x (m*x)-A x y (m*x)-h*J
  have hden : 0 < y+1 := by omega
  have hf := floor_bounds (x-y) (y+1) hden
  have hh : 0 ≤ h := Int.ediv_nonneg (by omega) (by omega)
  have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ (ne_of_gt hden)
  have hρhi : ρ ≤ y := by have := Int.emod_lt_of_pos (x-y) hden; dsimp [ρ]; omega
  have heq : x-y=(y+1)*h+ρ := (Int.mul_ediv_add_emod (x-y) (y+1)).symm
  have hhy : h*y < x := by change (y+1)*h ≤ x-y ∧ _ at hf; nlinarith only [hf.1,hh,hy]
  have hhcap : 2*h < x := by
    have hh' := mul_nonneg hh (show 0 ≤ y-2 by omega)
    nlinarith only [hhy,hh']
  have hhm : 4*h*m < x := by
    have hh' := mul_le_mul_of_nonneg_left hmy hh
    nlinarith only [hh',hhy]
  have hx0 : 0 < x := by omega
  have hxy : 4*x*y ≤ x*x := by
    have := mul_nonneg hx0.le (show 0 ≤ x-4*y by omega)
    nlinarith only [this]
  have hhm' := mul_lt_mul_of_pos_right hhm (show 0 < x+1 by omega)
  have hRidentity : R=m*x*x*(ρ+1)+m*x-x*y-x-h*m*(x+1) := by
    have he := congrArg (fun t : ℤ => m*x*x*t) heq
    dsimp [R,J,A,B,L]
    nlinarith only [he]
  have hρterm : 0 ≤ m*x*x*ρ := by positivity
  have hmterm : 2*x*x ≤ m*x*x := by nlinarith [mul_nonneg (show 0 ≤ m-2 by omega) (sq_nonneg x)]
  have hRlo : m*x < R := by
    have hpoly : 0 < 6*x*x-5*x := by nlinarith [sq_nonneg (x-1)]
    nlinarith only [hRidentity,hρterm,hmterm,hxy,hhm',hpoly]
  have hRminus : R-J=m*x*x*(ρ-y)+m*x-x*y-x-(h+1)*m*(x+1) := by
    rw [hRidentity]; dsimp [J,B]; ring
  have hRhi : R < J := by
    have hneg := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ m*x*x by positivity)
      (show ρ-y ≤ 0 by omega)
    have hextra := mul_nonneg hh (show 0 ≤ m*(x+1) by positivity)
    have hxy0 : 0 < x*y := by positivity
    nlinarith only [hRminus,hneg,hextra,hxy0,hm,hx0]
  obtain ⟨hE,hEp,hEup,hLJ⟩ := moderate_high_slacks x y m hy hx hm hmy
  have hLJ' : 2*J < L x (m*x) := by
    dsimp [J]
    nlinarith only [hLJ]
  have hmhcap : 2*m*h < m*x := by
    have := mul_lt_mul_of_pos_left hhcap (show 0 < m by omega)
    nlinarith only [this]
  have hRp : 0 < 2*R-m*x-1+m*h := by
    have hmh : 0 ≤ m*h := by positivity
    nlinarith only [hRlo,hmh,hm,hx0]
  refine ⟨h,hh,hhcap,?_⟩
  have hRdef : L x (m*x)-A x y (m*x)-h*m*B x y=R := by dsimp [R,J]; ring
  rw [hRdef]
  change FirstTwoWindows x y (m*x) _ _ R (2*R-m*x-1+m*h)
  dsimp [FirstTwoWindows,Window,SU,SV]
  refine ⟨⟨by omega,by omega⟩,⟨by omega,?_⟩,⟨by nlinarith [hRlo],by omega⟩,
    ⟨by omega,?_⟩⟩
  · nlinarith only [hEup,hm]
  · nlinarith only [hRhi,hLJ',hmhcap]

private theorem moderate_near_slacks (y m : ℤ) (hy : 8 ≤ y) (hm : 2 ≤ m) (hmy : 4*m ≤ y) :
    let x := 2*y
    let z := m*x
    let E := m*B x y-A x y z
    let R := L x z-A x y z-B x y
    0 < E ∧ m*y < E ∧ 0 < (y-2)*E-B x y ∧
    0 < B x y-4*E ∧ z < R ∧ 0 < L x z-1-2*R := by
  dsimp only
  have hfloor : 0 < 2*y^3-14*y^2-5*y-3 := by
    obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ y=8+u := ⟨y-8,by omega,by ring⟩
    ring_nf; positivity
  have hfirst : 2*y^3-14*y^2-5*y-3 ≤
      (y-2)*(m*B (2*y) y-A (2*y) y (m*(2*y)))-B (2*y) y := by
    obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ y=8+u := ⟨y-8,by omega,by ring⟩
    obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0 ≤ v ∧ m=2+v := ⟨m-2,by omega,by ring⟩
    apply sub_nonneg.mp
    dsimp [A,B]; ring_nf; positivity
  have hrest :
      0 < m*B (2*y) y-A (2*y) y (m*(2*y)) ∧
      m*y < m*B (2*y) y-A (2*y) y (m*(2*y)) ∧
      0 < B (2*y) y-4*(m*B (2*y) y-A (2*y) y (m*(2*y))) ∧
      m*(2*y) < L (2*y) (m*(2*y))-A (2*y) y (m*(2*y))-B (2*y) y ∧
      0 < L (2*y) (m*(2*y))-1-2*(L (2*y) (m*(2*y))-A (2*y) y (m*(2*y))-B (2*y) y) := by
    obtain ⟨M,hM,rfl⟩ : ∃ M : ℤ, 0 ≤ M ∧ m=2+M := ⟨m-2,by omega,by ring⟩
    obtain ⟨β,hβ,rfl⟩ : ∃ β : ℤ, 0 ≤ β ∧ y=4*(2+M)+β := ⟨y-4*(2+M),by omega,by ring⟩
    repeat' constructor
    all_goals first | apply sub_pos.mp | skip
    all_goals dsimp [A,B,L]
    all_goals ring_nf
    all_goals positivity
  exact ⟨hrest.1,hrest.2.1,by omega,hrest.2.2.1,hrest.2.2.2.1,hrest.2.2.2.2⟩

private theorem moderate_near_selector (y m : ℤ) (hy : 8 ≤ y) (hm : 2 ≤ m) (hmy : 4*m ≤ y) :
    ∃ r : ℤ, 1 ≤ r ∧ r < y ∧
      FirstTwoWindows (2*y) y (m*(2*y))
        (r*(m*B (2*y) y-A (2*y) y (m*(2*y)))-B (2*y) y)
        (2*(r*(m*B (2*y) y-A (2*y) y (m*(2*y)))-B (2*y) y)-r*m+1)
        (L (2*y) (m*(2*y))-A (2*y) y (m*(2*y))-B (2*y) y)
        (2*(L (2*y) (m*(2*y))-A (2*y) y (m*(2*y))-B (2*y) y)-m*(2*y)) := by
  let x := 2*y
  let z := m*x
  let BB := B x y
  let E := m*BB-A x y z
  let R := L x z-A x y z-BB
  let r := (BB-1)/E+2
  let e := r*E-BB
  obtain ⟨hE,hEmy,hrcap,hB4E,hRlo,hRup⟩ := moderate_near_slacks y m hy hm hmy
  change 0 < E at hE
  change m*y < E at hEmy
  change 0 < (y-2)*E-BB at hrcap
  change 0 < BB-4*E at hB4E
  have hB : 1 ≤ BB := by omega
  have hf0 := floor_bounds (BB-1) E hE
  have hrq : r-2=(BB-1)/E := by dsimp [r]; omega
  have hrq1 : r-1=(BB-1)/E+1 := by dsimp [r]; omega
  have hf : E*(r-2) ≤ BB-1 ∧ BB-1 < E*(r-1) := by rw [hrq,hrq1]; exact hf0
  have hr : 1 ≤ r := by
    have := Int.ediv_nonneg (show 0 ≤ BB-1 by omega) hE.le
    dsimp [r]; omega
  have he : E ≤ e ∧ e < 2*E := by
    dsimp [e]
    constructor <;> nlinarith only [hf.1,hf.2]
  have hry : r < y := by
    apply (mul_lt_mul_iff_of_pos_right hE).mp
    nlinarith only [hf.1,hrcap,hE]
  have hrm : r*m < E := by
    have hh := mul_lt_mul_of_pos_right hry (show 0 < m by omega)
    nlinarith only [hh,hEmy]
  have hEp : 0 < 2*e-r*m+1 := by omega
  have hEup : 2*e ≤ BB-1 := by omega
  have hz0 : 0 < z := by dsimp [z,x]; positivity
  have hRlo' : z < R := hRlo
  have hRup' : 0 < L x z-1-2*R := hRup
  refine ⟨r,hr,hry,?_⟩
  change FirstTwoWindows x y z e (2*e-r*m+1) R (2*R-z)
  dsimp [FirstTwoWindows,Window,SU,SV]
  refine ⟨⟨by omega,hEup⟩,⟨by omega,?_⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  have hrm1 : 1 ≤ r*m := by nlinarith
  omega

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter

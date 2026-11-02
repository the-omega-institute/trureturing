/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/BoundaryArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-boundary-windows)
   mirror-E: none(waiver:private-consumed-boundary-windows)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact old and new terminal windows on both boundary cones. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.Broad

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
open private Values values
  Values.z Values.w Values.r Values.q Values.x Values.y Values.H Values.S
  Values.A Values.B Values.L Values.K Values.SU Values.SV Values.SW Values.D Values.Dp
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BroadData

private def window (e S : ℤ) : Prop := 0≤e ∧ 2*e≤S-1

set_option maxHeartbeats 2400000 in
private theorem adjacent_windows (z t q : ℤ) (hz : 4≤z) (ht : 1≤t) (hq : 1≤q) :
    let V := values z (2*z) (2*t) q
    window (Values.D V) (Values.K V) ∧ window (Values.Dp V) (Values.SW V) ∧
    window ((Values.D V)+(Values.A V)-2*t*(Values.K V)) (Values.A V) ∧
    window ((Values.Dp V)+2*(Values.A V)-2*t*(Values.SW V)) (Values.A V) ∧
    window ((Values.D V)+(Values.B V)-2*t*(Values.K V)) (Values.B V) ∧
    window ((Values.Dp V)+(Values.SU V)-2*t*(Values.SW V)) (Values.SU V) := by
  dsimp only
  let z0 := z-4
  let t0 := t-1
  let q0 := q-1
  have hz0 : 0≤z0 := by dsimp [z0];omega
  have ht0 : 0≤t0 := by dsimp [t0];omega
  have hq0 : 0≤q0 := by dsimp [q0];omega
  have ez : z=z0+4 := by dsimp [z0];omega
  have et : t=t0+1 := by dsimp [t0];omega
  have eq : q=q0+1 := by dsimp [q0];omega
  dsimp [window,values]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals first
    | (rw [ez,et,eq]; ring_nf; positivity)
    | (apply le_of_sub_nonneg; rw [ez,et,eq]; ring_nf; positivity)

set_option maxHeartbeats 2400000 in
private theorem diagonal_windows (w t q : ℤ) (hw : 4≤w) (ht : 1≤t) (hq : 1≤q) :
    let V := values w w (2*t) q
    let alpha := 2*t*(Values.H V)-(Values.S V)
    let swap := decide ((Values.D V)<alpha)
    window (Values.D V) (Values.K V) ∧ window (Values.Dp V) (Values.SW V) ∧
    window ((Values.D V)+(Values.A V)-(if swap then 3*t else 2*t)*(Values.K V)+(if swap then (Values.A V) else 0)) (Values.A V) ∧
    window ((Values.Dp V)+(Values.A V)-(if swap then 3*t else 2*t)*(Values.SW V)+(if swap then 2*(Values.A V) else (Values.A V))) (Values.A V) ∧
    window ((Values.D V)+(Values.B V)-t*(Values.K V)) (Values.B V) ∧
    window ((Values.Dp V)+(Values.SU V)-t*(Values.SW V)) (Values.SU V) := by
  dsimp only
  let V := values w w (2*t) q
  let alpha := 2*t*(Values.H V)-(Values.S V)
  let h := t*(Values.H V)
  let g := (Values.S V)-t*(Values.H V)
  let w0 := w-4
  let t0 := t-1
  let q0 := q-1
  have hw0 : 0≤w0 := by dsimp [w0];omega
  have ht0 : 0≤t0 := by dsimp [t0];omega
  have hq0 : 0≤q0 := by dsimp [q0];omega
  have ew : w=w0+4 := by dsimp [w0];omega
  have et : t=t0+1 := by dsimp [t0];omega
  have eq : q=q0+1 := by dsimp [q0];omega
  have hD : 0≤(Values.D V) := by dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
  have hDp : 0≤(Values.Dp V) := by dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
  have hK : 2*(Values.D V)≤(Values.K V)-1 := by
    apply le_of_sub_nonneg
    dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
  have hSW : 2*(Values.Dp V)≤(Values.SW V)-1 := by
    apply le_of_sub_nonneg
    dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
  have hA : 2*(Values.D V)≤(Values.A V)-1 := by
    apply le_of_sub_nonneg
    dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
  have ha : 0<alpha := by dsimp [alpha,V,values];rw [ew,et,eq];ring_nf;positivity
  have ha4 : 4*alpha<(Values.A V) := by
    apply lt_of_sub_pos
    dsimp [alpha,V,values];rw [ew,et,eq];ring_nf;positivity
  have hh : 0<h := by dsimp [h,V,values];rw [ew,et,eq];ring_nf;positivity
  have hg : 0≤g := by dsimp [g,V,values];rw [ew,et,eq];ring_nf;positivity
  have hDh : (Values.Dp V)≤h := by
    apply le_of_sub_nonneg
    dsimp [h,V,values];rw [ew,et,eq];ring_nf;positivity
  have hid : (Values.A V)-1=2*w*h := by dsimp [h,V,values];ring
  have hag : g=h-alpha := by dsimp [g,h,alpha];ring
  have htK : 2*t*(Values.K V)=(Values.A V)+alpha := by dsimp [alpha,V,values];ring
  have htSW : t*(Values.SW V)=(Values.A V)-g := by dsimp [g,V,values];ring
  have hn (ell : ℤ) (hel : 0≤ell) (helw : ell+1≤w) : window ((Values.Dp V)+ell*g) (Values.A V) := by
    have hprod := mul_le_mul_of_nonneg_right helw hh.le
    have hprod' := mul_nonneg hel ha.le
    dsimp [window]
    constructor
    · exact add_nonneg hDp (mul_nonneg hel hg)
    · rw [hid]
      nlinarith only [hprod,hprod',hDh,hag]
  have hU : window ((Values.D V)+(Values.B V)-t*(Values.K V)) (Values.B V) := by
    dsimp [window]
    constructor
    · dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
    · apply le_of_sub_nonneg
      dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
  have hUn : window ((Values.Dp V)+(Values.SU V)-t*(Values.SW V)) (Values.SU V) := by
    dsimp [window]
    constructor
    · dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
    · apply le_of_sub_nonneg
      dsimp [V,values];rw [ew,et,eq];ring_nf;positivity
  change window (Values.D V) (Values.K V) ∧ window (Values.Dp V) (Values.SW V) ∧
    window ((Values.D V)+(Values.A V)-(if decide ((Values.D V)<alpha) then 3*t else 2*t)*(Values.K V)+
      (if decide ((Values.D V)<alpha) then (Values.A V) else 0)) (Values.A V) ∧
    window ((Values.Dp V)+(Values.A V)-(if decide ((Values.D V)<alpha) then 3*t else 2*t)*(Values.SW V)+
      (if decide ((Values.D V)<alpha) then 2*(Values.A V) else (Values.A V))) (Values.A V) ∧
    window ((Values.D V)+(Values.B V)-t*(Values.K V)) (Values.B V) ∧
    window ((Values.Dp V)+(Values.SU V)-t*(Values.SW V)) (Values.SU V)
  refine ⟨⟨hD,hK⟩,⟨hDp,hSW⟩,?_,?_,hU,hUn⟩
  · by_cases hs : (Values.D V)<alpha
    · simp only [decide_eq_true hs,ite_true]
      dsimp [window]
      constructor <;> nlinarith only [htK,ha4,hD,ha,hs]
    · simp only [decide_eq_false (by exact hs),Bool.false_eq_true,ite_false]
      dsimp [window]
      constructor <;> nlinarith only [htK,hs,hA,ha]
  · by_cases hs : (Values.D V)<alpha
    · simp only [decide_eq_true hs,ite_true]
      have he : (Values.Dp V)+(Values.A V)-3*t*(Values.SW V)+2*(Values.A V)=
          (Values.Dp V)+3*g := by nlinarith only [htSW]
      rw [he]
      exact hn 3 (by norm_num) (by omega)
    · simp only [decide_eq_false hs,Bool.false_eq_true,ite_false]
      have he : (Values.Dp V)+(Values.A V)-2*t*(Values.SW V)+(Values.A V)=
          (Values.Dp V)+2*g := by nlinarith only [htSW]
      rw [he]
      exact hn 2 (by norm_num) (by omega)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum

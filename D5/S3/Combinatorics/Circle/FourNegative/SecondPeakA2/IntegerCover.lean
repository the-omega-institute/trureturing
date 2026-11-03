/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/IntegerCover
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/IntegerCover
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Original a2 near-b construction: IntegerCover and its physical source consumer. -/
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2

private def Hit (A D e X : ℤ) : Prop :=
  ∃ j v : ℤ, 0 ≤ j ∧ j ≤ 15 ∧
    ((e ≤ X+j*(5*A-D)+8*v*A ∧ X+j*(5*A-D)+8*v*A ≤ A-e) ∨
     (3*A+e ≤ X+j*(5*A-D)+8*v*A ∧ X+j*(5*A-D)+8*v*A ≤ 4*A-e))

private theorem interval_i (A D e X j n : ℤ)
    (hov : D+2*e ≤ A) (hj : 1 ≤ j) (hj' : j ≤ 15)
    (hl : -5*j*A+j*D+8*n*A-D+e ≤ X)
    (hu : X ≤ -5*j*A+j*D+8*n*A+A-e) : Hit A D e X := by
  by_cases h : -5*j*A+j*D+8*n*A+e ≤ X
  · refine ⟨j,-n,by omega,hj',Or.inl ⟨?_,?_⟩⟩ <;> nlinarith
  · refine ⟨j-1,1-n,by omega,by omega,Or.inr ⟨?_,?_⟩⟩ <;> nlinarith

private theorem interval_j (A D e X j n : ℤ)
    (hov : D+2*e ≤ A) (hov' : 7*D+2*e ≤ A)
    (hj : 1 ≤ j) (hj' : j ≤ 7)
    (hl : -5*j*A+j*D+8*n*A-D+e ≤ X)
    (hu : X ≤ -5*j*A+j*D+8*n*A+A+8*D-e) : Hit A D e X := by
  by_cases h : X ≤ -5*j*A+j*D+8*n*A+A-e
  · exact interval_i A D e X j n hov hj (by omega) hl h
  · apply interval_i A D e X (j+8) (n+5) hov (by omega) (by omega) <;>
      nlinarith

private theorem interval_zero (A D e X : ℤ)
    (hov : D+2*e ≤ A) (hov' : 7*D+2*e ≤ A)
    (hl : e ≤ X) (hu : X ≤ A+8*D-e) : Hit A D e X := by
  by_cases h : X ≤ A-e
  · exact ⟨0,0,by omega,by omega,Or.inl ⟨by simpa using hl,by simpa using h⟩⟩
  · apply interval_i A D e X 8 5 hov (by norm_num) (by norm_num) <;> nlinarith

private theorem eight_interval_chain (A D e X : ℤ)
    (hD : 0 < D) (he : 0 ≤ e) (heD : 16*e ≤ D) (hDA : 13*D ≤ A)
    (hl : e ≤ X) (hu : X ≤ 8*A+e) : Hit A D e X := by
  have hov : D+2*e ≤ A := by omega
  have hov' : 7*D+2*e ≤ A := by omega
  by_cases h0 : X ≤ A+8*D-e
  · exact interval_zero A D e X hov hov' hl h0
  by_cases h3 : X ≤ 2*A+11*D-e
  · apply interval_j A D e X 3 2 hov hov' (by norm_num) (by norm_num) <;> omega
  by_cases h6 : X ≤ 3*A+14*D-e
  · apply interval_j A D e X 6 4 hov hov' (by norm_num) (by norm_num) <;> omega
  by_cases h1 : X ≤ 4*A+9*D-e
  · apply interval_j A D e X 1 1 hov hov' (by norm_num) (by norm_num) <;> omega
  by_cases h4 : X ≤ 5*A+12*D-e
  · apply interval_j A D e X 4 3 hov hov' (by norm_num) (by norm_num) <;> omega
  by_cases h7 : X ≤ 6*A+15*D-e
  · apply interval_j A D e X 7 5 hov hov' (by norm_num) (by norm_num) <;> omega
  by_cases h2 : X ≤ 7*A+10*D-e
  · apply interval_j A D e X 2 2 hov hov' (by norm_num) (by norm_num) <;> omega
  · apply interval_j A D e X 5 4 hov hov' (by norm_num) (by norm_num) <;> omega

/-- One Euclidean division lifts the explicit eight-interval chain to every integer. -/
theorem sixteen_step_cover (A D e X : ℤ)
    (hD : 0 < D) (he : 0 ≤ e) (heD : 16*e ≤ D) (hDA : 13*D ≤ A) :
    ∃ j v : ℤ, 0 ≤ j ∧ j ≤ 15 ∧
      ((e ≤ X+j*(5*A-D)+8*v*A ∧ X+j*(5*A-D)+8*v*A ≤ A-e) ∨
       (3*A+e ≤ X+j*(5*A-D)+8*v*A ∧ X+j*(5*A-D)+8*v*A ≤ 4*A-e)) := by
  have hA : 0 < 8*A := by omega
  let r := X % (8*A)
  let q := X / (8*A)
  have hr : 0 ≤ r := Int.emod_nonneg X (by omega)
  have hr' : r < 8*A := Int.emod_lt_of_pos X hA
  have hx : r+8*A*q=X := by
    dsimp [r,q]
    exact Int.emod_add_mul_ediv X (8*A)
  by_cases h : e ≤ r
  · obtain ⟨j,v,hj,hj',hv⟩ := eight_interval_chain A D e r hD he heD hDA h (by omega)
    refine ⟨j,v-q,hj,hj',?_⟩
    rcases hv with hv|hv
    · left; constructor <;> nlinarith [hv.1,hv.2]
    · right; constructor <;> nlinarith [hv.1,hv.2]
  · obtain ⟨j,v,hj,hj',hv⟩ := eight_interval_chain A D e (r+8*A) hD he heD hDA
      (by omega) (by omega)
    refine ⟨j,v+1-q,hj,hj',?_⟩
    rcases hv with hv|hv
    · left; constructor <;> nlinarith [hv.1,hv.2]
    · right; constructor <;> nlinarith [hv.1,hv.2]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2

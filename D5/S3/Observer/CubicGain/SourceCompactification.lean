/- GID: D5/S3/Observer/CubicGain/SourceCompactification
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/SourceCompactification
   mirror-E: none(waiver:compact-source-polynomial-relations)
   anchors: []
   utility: none
   digest: Derived bounded coordinates retain all source boundaries and a nonvanishing normalized drift vector. -/

import D5.S3.Observer.CubicGain.ParentCoordinates
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.RealVectorSpace

/-! Auxiliary bounded coordinates are derived from the original positive offdiagonals.
They impose no bound on those offdiagonals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

abbrev CompactCoordinates := Fin 5 → ℝ

def compactSource (r b : ℝ) : CompactCoordinates :=
  ![r,b/(1+b),sourceJ r b/(1+sourceJ r b),
    sourceJ r b/(sourceJ r b+sourceN r b),b/sourceJ r b]

def ClosedSource (z : CompactCoordinates) : Prop :=
  (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
  z 0*(1-z 0)*(1-z 1)^2*(1-z 2) = z 1*(z 2-z 1) ∧
  z 1*(1-z 2) = z 4*z 2*(1-z 1) ∧
  z 0*(1-z 2)*z 3 = z 2*(1-2*z 3) ∧
  (1-2*z 3)*(1-z 0)*(1-z 1) = z 3*z 1*(1-z 4) ∧
  z 0*(1-z 0)*(1-z 1)^2*z 4 = (z 1)^2*(1-z 4)

def vNorm (z : CompactCoordinates) : ℝ :=
  (1+z 0)*(1-z 2)+2*z 4*z 2+z 2

def uNorm (z : CompactCoordinates) : ℝ := 1-z 2+2*z 4*z 2

def ell (z : CompactCoordinates) : ℝ :=
  (8-6*(z 1)^2)*z 2*(1-z 3)-4*(1-z 2)*(1+z 1)

def alpha (z : CompactCoordinates) : ℝ :=
  (1-z 2)*z 2*(1-z 3)+vNorm z*
    ((24-20*z 1)*z 2*(1-z 3)-(15-5*z 3)*(1-z 2))

set_option maxHeartbeats 2000000 in
-- Exact polynomial expansion and denominator clearing use the larger finite allowance.
theorem closedSource_isCompact : IsCompact {z | ClosedSource z} := by
  have hc : IsClosed {z | ClosedSource z} := by
    unfold ClosedSource
    apply IsClosed.inter
    · change IsClosed {z : CompactCoordinates | ∀ i, 0 ≤ z i ∧ z i ≤ 1}
      have he : {z : CompactCoordinates | ∀ i, 0 ≤ z i ∧ z i ≤ 1} =
          Set.Icc (0 : CompactCoordinates) 1 := by
        ext z
        simp [Set.mem_Icc,Pi.le_def,forall_and]
      rw [he]
      exact isClosed_Icc
    · repeat' apply IsClosed.inter
      all_goals apply isClosed_eq <;> fun_prop
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : CompactCoordinates) 1)).of_isClosed_subset hc
  intro z hz
  exact ⟨fun i => (hz.1 i).1,fun i => (hz.1 i).2⟩

set_option maxHeartbeats 2000000 in
-- Exact polynomial expansion and denominator clearing use the larger finite allowance.
theorem compactSource_mem (r b : ℝ) (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b) :
    ClosedSource (compactSource r b) := by
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
  have hsum : 0 < sourceJ r b+sourceN r b := by positivity
  have hbJ : b ≤ sourceJ r b := by
    unfold sourceJ
    have : 0 ≤ r*(1-r)/b := by positivity
    linarith
  have hJ1 : 0 < 1+sourceJ r b := by positivity
  unfold ClosedSource compactSource
  dsimp
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> dsimp
    · exact ⟨hr.le,hr1.le⟩
    · exact ⟨by positivity,(div_le_one ht).mpr (by linarith)⟩
    · exact ⟨by positivity,(div_le_one hJ1).mpr (by linarith)⟩
    · exact ⟨by positivity,(div_le_one hsum).mpr (by linarith)⟩
    · exact ⟨by positivity,(div_le_one hj).mpr hbJ⟩
  all_goals
    simp only [sourceN,sourceJ]
    field_simp
    <;> ring

set_option maxHeartbeats 2000000 in
-- Exact polynomial expansion and denominator clearing use the larger finite allowance.
private theorem compactSource_nonzero_interior
    (r x k u t : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 0 < x) (hx1 : x < 1) (hk : 0 < k) (hk1 : k < 1)
    (c1 : r*(1-r)*(1-x)^2*(1-k)=x*(k-x))
    (c2 : x*(1-k)=t*k*(1-x))
    (c3 : r*(1-k)*u=k*(1-2*u)) :
    ell ![r,x,k,u,t] ≠ 0 ∨ alpha ![r,x,k,u,t] ≠ 0 := by
  have hx0 := ne_of_gt hx
  have hx10 : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hk0 := ne_of_gt hk
  have hk10 : 1-k ≠ 0 := ne_of_gt (sub_pos.mpr hk1)
  have hd : 0 < 2*k+r*(1-k) := by positivity
  have hnd : 0 < k+r*(1-k) := by positivity
  have hu : u=k/(2*k+r*(1-k)) := by
    apply (eq_div_iff (ne_of_gt hd)).mpr
    nlinarith [c3]
  have ht : t=x*(1-k)/(k*(1-x)) := by
    apply (eq_div_iff (mul_ne_zero hk0 hx10)).mpr
    nlinarith [c2]
  have hb : 0 < x/(1-x) := div_pos hx (sub_pos.mpr hx1)
  have hj : sourceJ r (x/(1-x)) = k/(1-k) := by
    unfold sourceJ
    field_simp [hx0,hx10,hk10]
    nlinarith [c1]
  have hn : sourceN r (x/(1-x)) = k/(1-k)+r := by rw [sourceN,hj]
  have hjn : 0 < k/(1-k)+r := by positivity
  have ht' : 0 < 1+x/(1-x) := by positivity
  have hu' : 0 < 1+2*(x/(1-x)) := by positivity
  have hl : ell ![r,x,k,u,t] =
      (1+x)*k*(1-u)*parentLambda r (x/(1-x)) := by
    simp only [ell,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      parentLambda,hj,hn]
    rw [hu]
    field_simp [hx10,hk10,ne_of_gt hd,ne_of_gt hnd,ne_of_gt hjn,
      ne_of_gt ht',ne_of_gt hu',hk0]
    <;> ring
  have ha : alpha ![r,x,k,u,t] =
      (1-k)*k*(1-u)*fifthDrift r (x/(1-x)) := by
    simp only [alpha,vNorm,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      fifthDrift,hj,hn]
    rw [hu,ht]
    field_simp [hx10,hk10,hk0,ne_of_gt hd,ne_of_gt hnd,ne_of_gt hjn,ne_of_gt ht']
    <;> ring
  have hu1 : 0 < 1-u := by rw [hu]; apply sub_pos.mpr; exact (div_lt_one hd).mpr (by nlinarith)
  have hls : (1+x)*k*(1-u) ≠ 0 := ne_of_gt (by positivity)
  have has : (1-k)*k*(1-u) ≠ 0 := ne_of_gt (by positivity)
  obtain h | h := drift_vector_nonzero r (x/(1-x)) hr hr1 hb
  · left; rw [hl]; exact mul_ne_zero hls h
  · right; rw [ha]; exact mul_ne_zero has h

set_option maxHeartbeats 2000000 in
-- Exact polynomial expansion and denominator clearing use the larger finite allowance.
/-- The drift vector stays nonzero on the full derived compactification,
including vanishing traces, unbounded traces, and unbounded b. -/
theorem compact_drift_vector_nonzero (z : CompactCoordinates) (hz : ClosedSource z) :
    ell z ≠ 0 ∨ alpha z ≠ 0 := by
  obtain ⟨bounds,c1,c2,c3,c4,c5⟩ := hz
  have hr := bounds 0
  have hx := bounds 1
  have hk := bounds 2
  have hu := bounds 3
  have ht := bounds 4
  by_cases hk0 : z 2=0
  · left
    simp [ell,hk0]
    linarith
  by_cases hk1 : z 2=1
  · left
    have hu' : z 3=1/2 := by rw [hk1] at c3; nlinarith [c3]
    have hx2 : (z 1)^2 ≤ 1 := by nlinarith [hx.1,hx.2]
    intro hzero
    have he : (8-6*(z 1)^2)*(1-(1/2 : ℝ))=0 := by simpa [ell,hk1,hu'] using hzero
    nlinarith only [he,hx2]
  have hk' : 0 < z 2 := lt_of_le_of_ne hk.1 (Ne.symm hk0)
  have hk1' : z 2 < 1 := lt_of_le_of_ne hk.2 hk1
  by_cases hx0 : z 1=0
  · have ht0 : z 4=0 := by rw [hx0] at c2; nlinarith [c2,ht.1]
    have hr01 : z 0=0 ∨ z 0=1 := by
      rw [hx0] at c1
      have hprod : z 0*(1-z 0)*(1-z 2)=0 := by simpa using c1
      have : z 0*(1-z 0)=0 := (mul_eq_zero.mp hprod).resolve_right (by linarith only [hk1'])
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rcases hr01 with hr0 | hr1
    · have hu' : z 3=1/2 := by rw [hx0,hr0] at c4; nlinarith [c4]
      by_cases hl : ell z=0
      · right
        have hk' : z 2=1/2 := by simp [ell,hx0,hu'] at hl; linarith
        norm_num [alpha,vNorm,hx0,hr0,ht0,hu',hk']
      · exact Or.inl hl
    · by_contra h
      push Not at h
      obtain ⟨hl,ha⟩ := h
      have hd : 0 < 1+z 2 := by positivity
      have hu' : z 3=z 2/(1+z 2) := by
        apply (eq_div_iff (ne_of_gt hd)).mpr
        rw [hr1] at c3
        nlinarith [c3]
      have l : 4*((z 2)^2+2*z 2-1)=0 := by
        simp [ell,hx0,hu'] at hl
        field_simp [ne_of_gt hd] at hl
        nlinarith only [hl]
      have a : -2*(5*(z 2)^3+5*(z 2)^2-37*z 2+15)=0 := by
        simp [alpha,vNorm,hx0,hr1,ht0,hu'] at ha
        field_simp [ne_of_gt hd] at ha
        nlinarith only [ha]
      have hbad : (1 : ℝ)=0 := by
        linear_combination (-55*(z 2)^2/112-5*(z 2)/7+377/112)*l +
          (-11*(z 2)/56-27/56)*a
      norm_num at hbad
  · have hx' : 0 < z 1 := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hx1' : z 1 < 1 := by
      by_contra h
      have he : z 1=1 := by linarith
      rw [he] at c1
      have : z 2=1 := by nlinarith [c1]
      exact hk1 this
    have heq : z = ![z 0,z 1,z 2,z 3,z 4] := by ext i; fin_cases i <;> rfl
    rw [heq]
    exact compactSource_nonzero_interior _ _ _ _ _ hr.1 hr.2 hx' hx1' hk' hk1' c1 c2 c3

#print axioms compact_drift_vector_nonzero

end D5.S3.Observer.CubicGain

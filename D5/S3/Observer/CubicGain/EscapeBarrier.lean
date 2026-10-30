/- GID: D5/S3/Observer/CubicGain/EscapeBarrier
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/EscapeBarrier
   mirror-E: none(waiver:universal-boundary-response-identities)
   anchors: []
   utility: none
   digest: The displayed polynomial barrier annihilates the exhaustive finite responses at all source boundaries. -/

import D5.S3.Observer.CubicGain.BoundedWholeGain

/-! The barrier is used only in the vanishing direction. Its zero set is not
claimed to consist of realizable escape responses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

def barrier0 (p v : ℝ) : ℝ :=
  51072900*p^3-38068700*p^2*v-1933224270*p^2+8423500*p*v^2+
  601454235*p*v+10167680250*p-581725*v^3-45839880*v^2-
  1393526691*v+136430551152

def barrier1 (p v : ℝ) : ℝ :=
  1055100*p^4-1141850*p^3*v-116130990*p^3+416900*p^2*v^2+
  79145580*p^2*v+273455568*p^2-63500*p*v^3-17883810*p*v^2-
  175084740*p*v-9069191838*p+3475*v^4+1327830*v^3+
  23513292*v^2+2292881202*v-50360535

def barrier2 (p v : ℝ) : ℝ :=
  9000*p^2-1300*p*v-175350*p-1600*v^2+225120*v-6050961

def barrier3 (p v : ℝ) : ℝ :=
  5356125*p^3-471600*p^2*v-197333550*p^2-592800*p*v^2+
  93450960*p*v-635417028*p+89600*v^3-8052480*v^2-
  277806240*v+17962000344

def escapeBarrier (q : ℝ × ℝ) : ℝ :=
  barrier0 q.1 q.2*barrier1 q.1 q.2*barrier2 q.1 q.2*barrier3 q.1 q.2*
    ((5*q.1+216)^2+(q.2+225)^2)

def responseOpen : Set (ℝ × ℝ) := {q | q.1 ≠ 24 ∧ escapeBarrier q ≠ 0}

def escapeR0 (z : ℝ) : ℝ × ℝ :=
  (-3*(72*z^3+746*z^2+465*z+130)/(5*(z^3-8*z-4)),
   -3*(375*z^3+4431*z^2+2486*z+344)/(5*(z^3-8*z-4)))
def escapeR1 (z : ℝ) : ℝ × ℝ :=
  (-6*(36*z^4+61*z^3+221*z^2+181*z+30)/(5*(z+1)*(z^3-4*z-2)),
   -3*(375*z^4+881*z^3+2486*z^2+1706*z+266)/(5*(z+1)*(z^3-4*z-2)))
def escapeB0 (z : ℝ) : ℝ × ℝ :=
  (-3*(16*z^2-80*z+65)/(10*(z-1)),
   3*(45*z^2+125*z-172)/(10*(z-1)))
def escapeB1 (z : ℝ) : ℝ × ℝ :=
  (-6*(8*z^3-24*z^2-2*z+15)/(5*(2*z^2-1)),
   3*(45*z^3+215*z^2-33*z-133)/(5*(2*z^2-1)))

private theorem barrier0_curve (z : ℝ) (hz : z^3-8*z-4 ≠ 0) :
    barrier0 (escapeR0 z).1 (escapeR0 z).2=0 := by
  unfold barrier0 escapeR0
  dsimp
  generalize hD : z^3-8*z-4=d at hz ⊢
  field_simp [hz]
  simp only [← hD]
  ring
private theorem barrier1_curve (z : ℝ) (hz : z^3-4*z-2 ≠ 0) (hz1 : z+1 ≠ 0) :
    barrier1 (escapeR1 z).1 (escapeR1 z).2=0 := by
  unfold barrier1 escapeR1
  dsimp
  generalize hD : z^3-4*z-2=d at hz ⊢
  field_simp [hz,hz1]
  simp only [← hD]
  ring
private theorem barrier2_curve (z : ℝ) (hz : z-1 ≠ 0) :
    barrier2 (escapeB0 z).1 (escapeB0 z).2=0 := by
  unfold barrier2 escapeB0
  dsimp
  field_simp [hz]
  ring
private theorem barrier3_curve (z : ℝ) (hz : 2*z^2-1 ≠ 0) :
    barrier3 (escapeB1 z).1 (escapeB1 z).2=0 := by
  unfold barrier3 escapeB1
  dsimp
  generalize hD : 2*z^2-1=d at hz ⊢
  field_simp [hz]
  simp only [← hD]
  ring

def ClosureWorld (z : CompactCoordinates) (e : ℝ) (a h : Gain) (p v : ℝ) : Prop :=
  ClosedSource z ∧
  a 0=-24-e ∧ a 2=(1-z 1)*(27/5-e) ∧
  (1+z 1)*gain a 4=(1-z 1)*(-6-e) ∧
  z 2*a 1=-(1-z 2)*e ∧
  (z 2+z 0*(1-z 2))*a 3=-(1-z 2)*e ∧
  z 3*a 1=(1-z 3)*a 3 ∧
  (∀ i, (1-z 1)*h i=(1+z 1)*a i) ∧
  z 2*h 1=-e*uNorm z ∧
  (z 2+z 0*(1-z 2))*h 3=-e*uNorm z ∧
  h 2=(1+z 1)*(27/5-e) ∧ gain h 4=-6-e ∧
  (p-24-e)*uNorm z=vNorm z*gain h 5 ∧
  (v-24-e)*uNorm z=(2*uNorm z+z 2+z 0*(1-z 2))*gain h 6 ∧
  (p-24-e)*(1-z 2)=vNorm z*gain a 5 ∧
  (v-24-e)*(1-z 2)=(2*uNorm z+z 2+z 0*(1-z 2))*gain a 6 ∧
  e*ell z=(6/5)*(1-9*z 1)*(2+3*z 1)*z 2*(1-z 3)

private theorem closure_infinite_b (z : CompactCoordinates) (e : ℝ) (a h : Gain)
    (p v : ℝ) (hw : ClosureWorld z e a h p v) (hx : z 1=1) :
    (p,v)=(-216/5,-225) := by
  obtain ⟨hz,a0,a2,a4,a1,a3,odd,sc,h1,h3,h2,h4,p5,p6,g5,g6,ep⟩ := hw
  obtain ⟨bounds,c1,c2,c3,c4,c5⟩ := hz
  have hk : z 2=1 := by rw [hx] at c1; nlinarith only [c1]
  have ht : z 4=1 := by rw [hx] at c5; nlinarith only [c5]
  have ha (i : Fin 4) : a i=0 := by have hi := sc i; rw [hx] at hi; nlinarith only [hi]
  have he : e=-24 := by have := ha 0; linarith only [this,a0]
  have hh1 : h 1=48 := by norm_num [hk,ht,he,uNorm] at h1; exact h1
  have hh3 : h 3=48 := by norm_num [hk,ht,he,uNorm] at h3; exact h3
  have hh2 : h 2=294/5 := by norm_num [hx,he] at h2; exact h2
  have hh0 : h 0=66/5 := by
    norm_num [gain,he,hh1,hh2,hh3] at h4
    linarith only [h4]
  have hh5 : gain h 5=-144/5 := by norm_num [gain,hh0,hh1,hh2,hh3]
  have hh6 : gain h 6=-90 := by norm_num [gain,hh0,hh1,hh2,hh3]
  apply Prod.ext
  · simp [uNorm,vNorm,hk,ht,he,hh5] at p5
    linarith only [p5]
  · simp [uNorm,vNorm,hk,ht,he,hh6] at p6
    linarith only [p6]

private theorem closure_large_j_small_b (z : CompactCoordinates) (e : ℝ) (a h : Gain)
    (p v : ℝ) (hw : ClosureWorld z e a h p v) (hx : z 1=0) (hk : z 2=1) : False := by
  obtain ⟨hz,a0,a2,a4,a1,a3,odd,sc,h1,h3,h2,h4,p5,p6,g5,g6,ep⟩ := hw
  have c2 := hz.2.2.1
  have c3 := hz.2.2.2.1
  have ht : z 4=0 := by rw [hx,hk] at c2; nlinarith only [c2]
  have hu : z 3=1/2 := by rw [hk] at c3; nlinarith only [c3]
  have he : e=3/10 := by norm_num [ell,hx,hk,hu] at ep; linarith only [ep]
  have aa1 : a 1=0 := by simpa [hk] using a1
  have aa3 : a 3=0 := by simpa [hk] using a3
  have aa0 : a 0=-243/10 := by linarith only [a0,he]
  have aa2 : a 2=51/10 := by rw [hx,he] at a2; norm_num at a2; exact a2
  have aa5 : gain a 5=-24/5 := by norm_num [gain,aa0,aa1,aa2,aa3]
  norm_num [vNorm,hk,ht,aa5] at g5

private theorem closure_zero_j (z : CompactCoordinates) (e : ℝ) (a h : Gain)
    (p v : ℝ) (hw : ClosureWorld z e a h p v) (hx : z 1=0) (hk : z 2=0) :
    (p,v)=escapeB0 0 ∨ (p,v)=escapeB1 0 := by
  obtain ⟨hz,a0,a2,a4,a1,a3,odd,sc,h1,h3,h2,h4,p5,p6,g5,g6,ep⟩ := hw
  have c1 := hz.2.1
  have c3 := hz.2.2.2.1
  have c4 := hz.2.2.2.2.1
  have he : e=0 := by norm_num [ell,hx,hk] at ep; linarith only [ep]
  have aa0 : a 0=-24 := by linarith only [a0,he]
  have aa2 : a 2=27/5 := by simpa [hx,he] using a2
  have aa4 : gain a 4=-6 := by simpa [hx,he] using a4
  have hr : z 0=0 ∨ z 0=1 := by
    rw [hx,hk] at c1
    have hh : z 0*(1-z 0)=0 := by simpa using c1
    rcases mul_eq_zero.mp hh with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith only [h])
  rcases hr with hr0 | hr1
  · have hu : z 3=1/2 := by rw [hx,hr0] at c4; nlinarith only [c4]
    have aa1 : a 1=3/10 := by
      rw [hu] at odd
      norm_num [gain,aa0,aa2] at aa4
      linarith only [odd,aa4]
    have aa3 : a 3=3/10 := by rw [hu,aa1] at odd; linarith only [odd]
    left
    apply Prod.ext
    · norm_num [escapeB0]
      norm_num [gain,vNorm,hk,hr0,he,aa0,aa1,aa2,aa3] at g5
      linarith only [g5]
    · norm_num [escapeB0]
      norm_num [gain,uNorm,vNorm,hk,hr0,he,aa0,aa1,aa2,aa3] at g6
      linarith only [g6]
  · have hu : z 3=0 := by rw [hr1,hk] at c3; nlinarith only [c3]
    have aa3 : a 3=0 := by simpa [hu] using odd.symm
    have aa1 : a 1=3/5 := by
      norm_num [gain,aa0,aa2,aa3] at aa4
      linarith only [aa4]
    right
    apply Prod.ext
    · norm_num [escapeB1]
      norm_num [gain,vNorm,hk,hr1,he,aa0,aa1,aa2,aa3] at g5
      linarith only [g5]
    · norm_num [escapeB1]
      norm_num [gain,uNorm,vNorm,hk,hr1,he,aa0,aa1,aa2,aa3] at g6
      linarith only [g6]

/-- On a finite positive source, the polynomial closure equations recover the
actual parent coordinates and the actual chronological M pair. -/
theorem finite_closure_lift (z : CompactCoordinates) (e : ℝ) (a h : Gain)
    (p v : ℝ) (hw : ClosureWorld z e a h p v)
    (hx : 0 < z 1) (hx1 : z 1 < 1) (hk : 0 < z 2) (hk1 : z 2 < 1) :
    parentEq (z 0,z 1/(1-z 1),e)=0 ∧
    a=parentGain (z 0,z 1/(1-z 1),e) ∧
    response (z 0,z 1/(1-z 1),e)=(p,v) := by
  obtain ⟨hz,a0,a2,a4,a1,a3,odd,sc,h1,h3,h2,h4,p5,p6,g5,g6,ep⟩ := hw
  obtain ⟨bounds,c1,c2,c3,c4,c5⟩ := hz
  have hr := bounds 0
  have hb : 0 < z 1/(1-z 1) := div_pos hx (sub_pos.mpr hx1)
  have hx0 := ne_of_gt hx
  have hx10 := ne_of_gt (sub_pos.mpr hx1)
  have hk0 := ne_of_gt hk
  have hk10 := ne_of_gt (sub_pos.mpr hk1)
  have hj : sourceJ (z 0) (z 1/(1-z 1))=z 2/(1-z 2) := by
    unfold sourceJ
    field_simp [hx0,hx10,hk10]
    nlinarith only [c1]
  have hn : sourceN (z 0) (z 1/(1-z 1))=z 2/(1-z 2)+z 0 := by rw [sourceN,hj]
  obtain ⟨hjpos,hnpos,htpos,hupos⟩ := source_positivity (z 0) (z 1/(1-z 1)) hr.1 hr.2 hb
  have hnd : 0 < z 2+z 0*(1-z 2) := by have hh : 0 ≤ z 0 := hr.1; positivity
  have ht : z 4=z 1*(1-z 2)/(z 2*(1-z 1)) := by
    apply (eq_div_iff (mul_ne_zero hk0 hx10)).mpr
    nlinarith only [c2]
  have ha : a=parentGain (z 0,z 1/(1-z 1),e) := by
    ext i
    fin_cases i <;> dsimp [parentGain]
    · exact a0
    · rw [hj]
      field_simp [hk0,hk10]
      nlinarith only [a1]
    · field_simp [hx10]
      nlinarith only [a2]
    · rw [hn]
      have hnd' : z 2+(1-z 2)*z 0 ≠ 0 := by nlinarith only [hnd]
      field_simp [hk10,hnd']
      nlinarith only [a3]
  have he4 : (24+e)+gain a 4*(1+2*(z 1/(1-z 1)))-18=0 := by
    field_simp [hx10]
    nlinarith only [a4]
  have hp : parentEq (z 0,z 1/(1-z 1),e)=0 := by
    have heq := fourth_residual (z 0) (z 1/(1-z 1)) (24+e)
      (ne_of_gt hjpos) (ne_of_gt hnpos) (ne_of_gt htpos) (ne_of_gt hupos)
    have haa : parentGain (z 0,z 1/(1-z 1),24+e-24)=a := by
      convert ha.symm using 1 <;> simp
    rw [haa,he4] at heq
    have hzero : (1+2*(z 1/(1-z 1)))*parentEq (z 0,z 1/(1-z 1),e)=0 := by
      convert heq.symm using 1 <;> simp
    exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hupos)
  refine ⟨hp,ha,?_⟩
  have hv : vNorm z=(1-z 2)*(1+2*(z 1/(1-z 1))+sourceN (z 0) (z 1/(1-z 1))) := by
    unfold vNorm
    rw [ht,hn]
    field_simp [hx10,hk0,hk10]
    <;> ring
  have hu : uNorm z=(1-z 2)*(1+2*(z 1/(1-z 1))) := by
    unfold uNorm
    rw [ht]
    field_simp [hx10,hk0]
    <;> ring
  obtain ⟨hm5,hm6⟩ := actual_m_responses (z 0,z 1/(1-z 1),e)
  have hh5 := congrFun (literal_traces (z 0) (z 1/(1-z 1))) (5 : Fin 7)
  have hh6 := congrFun (literal_traces (z 0) (z 1/(1-z 1))) (6 : Fin 7)
  norm_num at hh5 hh6
  apply Prod.ext
  · dsimp [response]
    rw [← hm5]
    change 24+e+gain (parentGain (z 0,z 1/(1-z 1),e)) 5*traceAt (z 0) (z 1/(1-z 1)) 5=p
    rw [hh5,← ha]
    rw [hv] at g5
    apply mul_left_cancel₀ hk10
    linear_combination -g5
  · dsimp [response]
    rw [← hm6]
    change 24+e+gain (parentGain (z 0,z 1/(1-z 1),e)) 6*traceAt (z 0) (z 1/(1-z 1)) 6=v
    rw [hh6,← ha]
    rw [hu] at g6
    have hN : (1-z 2)*sourceN (z 0) (z 1/(1-z 1))=z 2+z 0*(1-z 2) := by
      rw [hn]
      field_simp [hk10]
    apply mul_left_cancel₀ hk10
    linear_combination -g6 + gain a 6*hN
private theorem endpoint_parent_barrier (r b e : ℝ) (hr : r=0 ∨ r=1) (hb : 0 < b)
    (hp : parentEq (r,b,e)=0) : escapeBarrier (response (r,b,e))=0 := by
  have ht : 0 < 1+b := by positivity
  have hu : 0 < 1+2*b := by positivity
  have hB : 0 < parentB b := by
    have heq : parentB b=2*(2+5*b)/((1+b)*(1+2*b)) := by
      unfold parentB
      field_simp
      <;> ring
    rw [heq]
    positivity
  have hl : parentLambda r b ≠ 0 := by
    intro hl
    have hzero : b=1/8 := by
      unfold parentEq at hp
      dsimp at hp
      rw [hl,mul_zero,zero_add] at hp
      have hh := (mul_eq_zero.mp hp).resolve_right (ne_of_gt hB)
      nlinarith only [hh]
    subst b
    rcases hr with h | h <;> subst r <;>
      norm_num [parentLambda,sourceJ,sourceN] at hl
  have he : e=(-(24/5)*(b-1/8)*parentB b)/parentLambda r b := by
    apply (eq_div_iff hl).mpr
    unfold parentEq at hp
    dsimp at hp
    linarith only [hp]
  rcases hr with hr0 | hr1
  · subst r
    have hlform : parentLambda 0 b=2*(b^3-8*b-4)/(b*(b+1)*(2*b+1)) := by
      unfold parentLambda sourceN sourceJ
      field_simp
      <;> ring
    have hd : b^3-8*b-4 ≠ 0 := by intro hh; rw [hlform,hh] at hl; norm_num at hl
    have hresp : response (0,b,e)=escapeR0 b := by
      rw [he,hlform]
      apply Prod.ext <;>
        dsimp [response,fifthResponse,sixthResponse,fifthDrift,sixthDrift,
          parentB,sourceN,sourceJ,escapeR0]
      all_goals
        generalize hD : b^3-8*b-4=d at hd ⊢
        field_simp [ne_of_gt hb,ne_of_gt ht,ne_of_gt hu,hd]
        simp only [← hD]
        ring
    rw [hresp]
    unfold escapeBarrier
    rw [barrier0_curve b hd]
    ring
  · subst r
    have hlform : parentLambda 1 b=2*(b^3-4*b-2)/(b*(b+1)*(2*b+1)) := by
      unfold parentLambda sourceN sourceJ
      field_simp
      <;> ring
    have hd : b^3-4*b-2 ≠ 0 := by intro hh; rw [hlform,hh] at hl; norm_num at hl
    have hresp : response (1,b,e)=escapeR1 b := by
      rw [he,hlform]
      apply Prod.ext <;>
        dsimp [response,fifthResponse,sixthResponse,fifthDrift,sixthDrift,
          parentB,sourceN,sourceJ,escapeR1]
      all_goals
        generalize hD : b^3-4*b-2=d at hd ⊢
        field_simp [ne_of_gt hb,ne_of_gt ht,ne_of_gt hu,hd]
        simp only [← hD]
        ring
    rw [hresp]
    unfold escapeBarrier
    rw [barrier1_curve b hd (by positivity)]
    ring

private theorem closure_small_b_finite_j (z : CompactCoordinates) (e : ℝ) (a h : Gain)
    (p v : ℝ) (hw : ClosureWorld z e a h p v) (hx : z 1=0)
    (hk : 0 < z 2) (hk1 : z 2 < 1) : escapeBarrier (p,v)=0 := by
  obtain ⟨hz,a0,a2,a4,a1,a3,odd,sc,h1,h3,h2,h4,p5,p6,g5,g6,ep⟩ := hw
  obtain ⟨bounds,c1,c2,c3,c4,c5⟩ := hz
  have hk0 := ne_of_gt hk
  have hk10 := ne_of_gt (sub_pos.mpr hk1)
  have ht : z 4=0 := by rw [hx] at c2; nlinarith only [c2,hk]
  have hr : z 0=0 ∨ z 0=1 := by
    have hh : z 0*(1-z 0)*(1-z 2)=0 := by simpa [hx] using c1
    have hprod : z 0*(1-z 0)=0 := (mul_eq_zero.mp hh).resolve_right hk10
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith only [h])
  let j : ℝ := z 2/(1-z 2)
  have hj : 0 < j := div_pos hk (sub_pos.mpr hk1)
  have aa1 : a 1=-e/j := by
    dsimp [j]
    field_simp [hk0,hk10]
    nlinarith only [a1]
  have aa2 : a 2=27/5-e := by simpa [hx] using a2
  have aa3 : a 3=-e/(j+z 0) := by
    have hnd : 0 < z 2+z 0*(1-z 2) := by have := (bounds 0).1; positivity
    dsimp [j]
    have hnd' : z 2+(1-z 2)*z 0 ≠ 0 := by nlinarith only [hnd]
    field_simp [hk10,hnd']
    nlinarith only [a3]
  have hjrel : (1-z 2)*j=z 2 := by
    dsimp [j]
    field_simp [hk10]
  have gp : p=24+e+(1+z 0+j)*gain a 5 := by
    apply mul_left_cancel₀ hk10
    norm_num [vNorm,ht] at g5
    linear_combination g5 - gain a 5*hjrel
  have gv : v=24+e+(2+z 0+j)*gain a 6 := by
    apply mul_left_cancel₀ hk10
    norm_num [uNorm,ht] at g6
    linear_combination g6 - gain a 6*hjrel
  rcases hr with hr0 | hr1
  · have hu : z 3=1/2 := by rw [hr0] at c3; nlinarith only [c3,hk]
    have ep' : e*(8*(j-1)/j)=12/5 := by
      dsimp [j]
      norm_num [ell,hx,hu] at ep
      field_simp [hk0,hk10]
      nlinarith only [ep]
    have hd : j-1 ≠ 0 := by
      intro hh
      have jj : j=1 := by linarith only [hh]
      rw [jj] at ep'
      norm_num at ep'
    have he : e=3*j/(10*(j-1)) := by
      apply (eq_div_iff (by exact mul_ne_zero (by norm_num) hd)).mpr
      field_simp [ne_of_gt hj] at ep'
      nlinarith only [ep']
    have hlabel : (p,v)=escapeB0 j := by
      rw [gp,gv]
      apply Prod.ext <;>
        norm_num [escapeB0,gain,aa1,aa2,aa3,a0,hr0,he]
      all_goals
        field_simp [ne_of_gt hj,hd]
        ring
    rw [hlabel]
    unfold escapeBarrier
    rw [barrier2_curve j hd]
    ring
  · have hu : z 3=z 2/(1+z 2) := by
      apply (eq_div_iff (by positivity : 1+z 2 ≠ 0)).mpr
      rw [hr1] at c3
      nlinarith only [c3]
    have ep' : e*(4*(2*j^2-1)/(j*(j+1)))=12/5 := by
      dsimp [j]
      norm_num [ell,hx,hu] at ep
      field_simp [hk0,hk10,show 1+z 2 ≠ 0 by positivity] at ep ⊢
      nlinarith only [ep]
    have hd : 2*j^2-1 ≠ 0 := by intro hh; rw [hh] at ep'; norm_num at ep'
    have he : e=3*j*(j+1)/(5*(2*j^2-1)) := by
      apply (eq_div_iff (by exact mul_ne_zero (by norm_num) hd)).mpr
      field_simp [ne_of_gt hj,show j+1 ≠ 0 by positivity] at ep'
      nlinarith only [ep']
    have hlabel : (p,v)=escapeB1 j := by
      rw [gp,gv]
      apply Prod.ext <;>
        norm_num [escapeB1,gain,aa1,aa2,aa3,a0,hr1,he]
      all_goals
        generalize hD : 2*j^2-1=d at hd ⊢
        field_simp [ne_of_gt hj,show j+1 ≠ 0 by positivity,hd]
        simp only [← hD]
        ring
    rw [hlabel]
    unfold escapeBarrier
    rw [barrier3_curve j hd]
    ring

/-- Every boundary of the full source compactification has its finite actual
response on the displayed barrier. No classification or bound is assumed. -/
theorem closure_boundary_barrier (z : CompactCoordinates) (e : ℝ) (a h : Gain)
    (p v : ℝ) (hw : ClosureWorld z e a h p v)
    (hbd : z 0=0 ∨ z 0=1 ∨ z 1=0 ∨ z 1=1) : escapeBarrier (p,v)=0 := by
  have hz := hw.1
  have bounds := hz.1
  by_cases hx1 : z 1=1
  · rw [closure_infinite_b z e a h p v hw hx1]
    norm_num [escapeBarrier]
  by_cases hx0 : z 1=0
  · by_cases hk0 : z 2=0
    · rcases closure_zero_j z e a h p v hw hx0 hk0 with h | h
      · rw [h]; unfold escapeBarrier; rw [barrier2_curve 0 (by norm_num)]; ring
      · rw [h]; unfold escapeBarrier; rw [barrier3_curve 0 (by norm_num)]; ring
    by_cases hk1 : z 2=1
    · exact (closure_large_j_small_b z e a h p v hw hx0 hk1).elim
    exact closure_small_b_finite_j z e a h p v hw hx0
      (lt_of_le_of_ne (bounds 2).1 (Ne.symm hk0))
      (lt_of_le_of_ne (bounds 2).2 hk1)
  have hx : 0 < z 1 := lt_of_le_of_ne (bounds 1).1 (Ne.symm hx0)
  have hx1' : z 1 < 1 := lt_of_le_of_ne (bounds 1).2 hx1
  have hr : z 0=0 ∨ z 0=1 := by tauto
  have hk : z 2=z 1 := by
    have c1 := hz.2.1
    rcases hr with h | h <;> rw [h] at c1 <;> nlinarith only [c1,hx]
  obtain ⟨hp,ha,hrsp⟩ := finite_closure_lift z e a h p v hw hx hx1'
    (by rw [hk]; exact hx) (by rw [hk]; exact hx1')
  rw [← hrsp]
  exact endpoint_parent_barrier _ _ _ hr (div_pos hx (sub_pos.mpr hx1')) hp

#print axioms closure_boundary_barrier

end D5.S3.Observer.CubicGain

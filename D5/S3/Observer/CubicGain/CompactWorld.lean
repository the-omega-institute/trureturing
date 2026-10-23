/- GID: D5/S3/Observer/CubicGain/CompactWorld
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/CompactWorld
   mirror-E: none(waiver:uniform-scaled-whole-gain-estimate)
   anchors: []
   utility: none
   digest: The actual whole-gain parent embeds in the polynomial closure with uniformly bounded scaled gains. -/

import D5.S3.Observer.CubicGain.EscapeBarrier

/-! Scaling multiplies the whole gain by one common source-dependent number.
The responses always use the original gain and fixed drift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

def scaledGain (C : Coordinates) : Gain := fun i => (1+2*C.2.1)*parentGain C i

theorem gain_scale (a : Gain) (t s : ℝ) :
    gain (fun i => t*a i) s=t*gain a s := by
  unfold gain
  ring

/-- The closure equations are consequences of actual parent worlds. -/
theorem closureWorld_actual (C : Coordinates) (hC : StrictParent C) :
    ClosureWorld (compactSource C.1 C.2.1) C.2.2 (parentGain C) (scaledGain C)
      (fifthResponse C) (sixthResponse C) := by
  obtain ⟨r,b,e⟩ := C
  obtain ⟨hr,hr1,hb,hp⟩ := hC
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
  have hs : 0 < sourceJ r b+sourceN r b := by positivity
  have hj1 : 0 < 1+sourceJ r b := by positivity
  have he4 := fourth_residual r b (24+e) (ne_of_gt hj) (ne_of_gt hn) (ne_of_gt ht) (ne_of_gt hu)
  have headd : 24+e-24=e := by ring
  rw [headd,hp,mul_zero] at he4
  have ga4 : (1+2*b)*gain (parentGain (r,b,e)) 4=-6-e := by
    linarith only [he4]
  have ga4scaled : gain (scaledGain (r,b,e)) 4=-6-e := by
    change gain (fun i => (1+2*b)*parentGain (r,b,e) i) 4 = _
    rw [gain_scale,ga4]
  unfold ClosureWorld
  refine ⟨compactSource_mem r b hr hr1 hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · dsimp [parentGain,compactSource]
    field_simp [ne_of_gt ht]
    ring
  · dsimp [compactSource]
    field_simp [ne_of_gt ht]
    nlinarith only [ga4]
  · dsimp [compactSource,parentGain]
    field_simp [ne_of_gt hj,ne_of_gt hj1]
    ring
  · dsimp [compactSource,parentGain]
    simp only [sourceN]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt hj1]
    <;> ring
  · dsimp [compactSource,parentGain]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt hs]
    ring
  · intro i
    dsimp [compactSource,scaledGain]
    field_simp [ne_of_gt ht]
    ring
  · dsimp [compactSource,scaledGain,parentGain,uNorm]
    field_simp [ne_of_gt hj,ne_of_gt hj1]
    ring
  · dsimp [compactSource,scaledGain,parentGain,uNorm]
    simp only [sourceN]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt hj1]
    <;> ring
  · dsimp [compactSource,scaledGain,parentGain]
    field_simp [ne_of_gt ht]
    ring
  · exact ga4scaled
  · dsimp [compactSource,scaledGain,uNorm,vNorm,fifthResponse,fifthDrift]
    norm_num [gain,scaledGain,parentGain]
    simp only [sourceN]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hj1]
    <;> ring
  · dsimp [compactSource,scaledGain,uNorm,vNorm,sixthResponse,sixthDrift]
    norm_num [gain,scaledGain,parentGain]
    simp only [sourceN]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hj1]
    <;> ring
  · dsimp [compactSource,vNorm,fifthResponse,fifthDrift]
    norm_num [gain,scaledGain,parentGain]
    simp only [sourceN]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hj1]
    <;> ring
  · dsimp [compactSource,uNorm,vNorm,sixthResponse,sixthDrift]
    norm_num [gain,scaledGain,parentGain]
    simp only [sourceN]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hj1]
    <;> ring
  · have hh := (normalized_parent_equations (r,b,e) ⟨hr,hr1,hb,hp⟩).1
    convert hh using 1 <;> dsimp [driftRight,qNorm] <;> ring

/-- Bounded responses control both the entire unscaled gain and U times
that same entire gain, including the unbounded-b regime. -/
theorem bounded_fifth_bounds_scaled_gain (M : ℝ) :
    ∃ D G H : ℝ, ∀ C : Coordinates, StrictParent C → |fifthResponse C| ≤ M →
      |C.2.2| ≤ D ∧ (∀ i, |parentGain C i| ≤ G) ∧ ∀ i, |scaledGain C i| ≤ H := by
  obtain ⟨D,G,hbounds⟩ := bounded_fifth_bounds_whole_gain M
  let D' := max D 0
  let G' := max G 0
  refine ⟨D',G',100+100*(D'+G'),?_⟩
  intro C hC hp
  obtain ⟨hd,hg⟩ := hbounds C hC hp
  have hd' : |C.2.2| ≤ D' := hd.trans (le_max_left _ _)
  have hg' (i : Fin 4) : |parentGain C i| ≤ G' := (hg i).trans (le_max_left _ _)
  have hD : 0 ≤ D' := le_max_right _ _
  have hG : 0 ≤ G' := le_max_right _ _
  refine ⟨hd',hg',?_⟩
  obtain ⟨r,b,e⟩ := C
  obtain ⟨hr,hr1,hb,hpeq⟩ := hC
  dsimp at hd' hg' ⊢
  have hU : 0 < 1+2*b := by positivity
  by_cases hb1 : b ≤ 1
  · intro i
    dsimp [scaledGain]
    rw [abs_mul,abs_of_pos hU]
    have hh : (1+2*b)*|parentGain (r,b,e) i| ≤ 3*G' := by
      have := hg' i
      nlinarith [abs_nonneg (parentGain (r,b,e) i)]
    linarith
  · have hb1 : 1 ≤ b := by linarith
    obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
    have hjb : b ≤ sourceJ r b := by
      unfold sourceJ
      have : 0 ≤ r*(1-r)/b := by positivity
      linarith
    have hnb : b ≤ sourceN r b := by unfold sourceN; linarith
    have hratJ : (1+2*b)/sourceJ r b ≤ 3 := by
      apply (div_le_iff₀ hj).mpr
      linarith
    have hratN : (1+2*b)/sourceN r b ≤ 3 := by
      apply (div_le_iff₀ hn).mpr
      linarith
    have hratT : (1+2*b)/(1+b) ≤ 2 := by
      apply (div_le_iff₀ ht).mpr
      linarith
    have hs1 : |scaledGain (r,b,e) 1| ≤ 3*D' := by
      dsimp [scaledGain,parentGain]
      rw [abs_mul,abs_div,abs_neg,abs_of_pos hu,abs_of_pos hj]
      have heabs : |e| ≤ D' := hd'
      calc
        (1+2*b)*(|e|/sourceJ r b) = ((1+2*b)/sourceJ r b)*|e| := by ring
        _ ≤ 3*|e| := mul_le_mul_of_nonneg_right hratJ (abs_nonneg e)
        _ ≤ 3*D' := by linarith
    have hs3 : |scaledGain (r,b,e) 3| ≤ 3*D' := by
      dsimp [scaledGain,parentGain]
      rw [abs_mul,abs_div,abs_neg,abs_of_pos hu,abs_of_pos hn]
      have heabs : |e| ≤ D' := hd'
      calc
        (1+2*b)*(|e|/sourceN r b) = ((1+2*b)/sourceN r b)*|e| := by ring
        _ ≤ 3*|e| := mul_le_mul_of_nonneg_right hratN (abs_nonneg e)
        _ ≤ 3*D' := by linarith
    have hs2 : |scaledGain (r,b,e) 2| ≤ 2*(27/5+D') := by
      dsimp [scaledGain,parentGain]
      rw [abs_mul,abs_div,abs_of_pos hu,abs_of_pos ht]
      have heabs : |27/5-e| ≤ 27/5+D' := by
        calc |27/5-e| ≤ |(27/5 : ℝ)|+|e| := abs_sub _ _
             _ ≤ 27/5+D' := by norm_num; exact hd'
      calc
        (1+2*b)*(|27/5-e|/(1+b)) = ((1+2*b)/(1+b))*|27/5-e| := by ring
        _ ≤ 2*|27/5-e| := mul_le_mul_of_nonneg_right hratT (abs_nonneg _)
        _ ≤ 2*(27/5+D') := by linarith
    have hfour := (closureWorld_actual (r,b,e) ⟨hr,hr1,hb,hpeq⟩).2.2.2.2.2.2.2.2.2.2.2.1
    change gain (scaledGain (r,b,e)) 4=-6-e at hfour
    have hzero : scaledGain (r,b,e) 0 =
        4*scaledGain (r,b,e) 1-6*scaledGain (r,b,e) 2+
        4*scaledGain (r,b,e) 3+6+e := by
      norm_num [gain] at hfour
      linarith only [hfour]
    have hs0 : |scaledGain (r,b,e) 0| ≤ 100+100*(D'+G') := by
      rw [hzero]
      apply abs_le.mpr
      have h1 := abs_le.mp hs1
      have h2 := abs_le.mp hs2
      have h3 := abs_le.mp hs3
      have he := abs_le.mp hd'
      constructor <;> linarith
    intro i
    fin_cases i
    · exact hs0
    · exact hs1.trans (by linarith)
    · exact hs2.trans (by linarith)
    · exact hs3.trans (by linarith)

#print axioms closureWorld_actual
#print axioms bounded_fifth_bounds_scaled_gain

end D5.S3.Observer.CubicGain

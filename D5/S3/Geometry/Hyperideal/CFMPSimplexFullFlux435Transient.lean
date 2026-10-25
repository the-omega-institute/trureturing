import D5.S3.Geometry.Hyperideal.CFMPSimplexDirection435Transient
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact reference-simplex integral and coordinate-flux applications. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped MeasureTheory Interval
namespace CFMPSimplexDirection435Transient
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def tetrahedron (a : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧ z.1 + z.2.1 + z.2.2 ≤ a}

theorem tetrahedron_compact (a : ℝ) : IsCompact (tetrahedron a) := by
  have heq : tetrahedron a = (Icc 0 a ×ˢ (Icc 0 a ×ˢ Icc 0 a)) ∩
      {z : ℝ × (ℝ × ℝ) | z.1 + z.2.1 + z.2.2 ≤ a} := by
    ext z
    simp only [tetrahedron, mem_setOf_eq, mem_inter_iff, mem_prod, mem_Icc]
    constructor
    · rintro ⟨hx,hy,hz,hxyz⟩
      exact ⟨⟨⟨hx,by linarith⟩,⟨⟨hy,by linarith⟩,⟨hz,by linarith⟩⟩⟩,hxyz⟩
    · rintro ⟨⟨⟨hx,_⟩,⟨⟨hy,_⟩,⟨hz,_⟩⟩⟩,hxyz⟩
      exact ⟨hx,hy,hz,hxyz⟩
  rw [heq]
  exact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
    (isClosed_le ((continuous_fst.add (continuous_fst.comp continuous_snd)).add
      (continuous_snd.comp continuous_snd)) continuous_const)

theorem tetrahedron_section (a : ℝ) (yz : ℝ × ℝ) :
    {x : ℝ | (x,yz) ∈ tetrahedron a} =
      if yz ∈ triangle a then Icc 0 (a-yz.1-yz.2) else ∅ := by
  classical
  ext x
  split_ifs with hy
  · simp only [tetrahedron, mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨hx,_,_,hxyz⟩;exact ⟨hx,by linarith⟩
    · rintro ⟨hx,hxyz⟩;exact ⟨hx,hy.1,hy.2.1,by linarith⟩
  · simp only [tetrahedron, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx hy0 hz0 hxyz
    exact hy ⟨hy0,hz0,by linarith⟩

theorem tetrahedron_iterated (a : ℝ) (D : ℝ × (ℝ × ℝ) → E)
    (hD : ContinuousOn D (tetrahedron a)) :
    (∫ z in tetrahedron a, D z) =
      ∫ yz in triangle a, ∫ x in (0 : ℝ)..(a-yz.1-yz.2), D (x,yz) := by
  classical
  have hK := tetrahedron_compact a
  have hInt : IntegrableOn D (tetrahedron a) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact hK hD
  have hs (yz : ℝ × ℝ) :
      (∫ x in {x : ℝ | (x,yz) ∈ tetrahedron a}, D (x,yz)) =
      (triangle a).indicator (fun yz => ∫ x in Icc 0 (a-yz.1-yz.2), D (x,yz)) yz := by
    rw [tetrahedron_section]
    by_cases hy : yz ∈ triangle a <;> simp [hy]
  calc
    (∫ z in tetrahedron a, D z) =
        ∫ yz, ∫ x in {x : ℝ | (x,yz) ∈ tetrahedron a}, D (x,yz) :=
      sections_snd hK.measurableSet hInt
    _ = ∫ yz, (triangle a).indicator
        (fun yz => ∫ x in Icc 0 (a-yz.1-yz.2), D (x,yz)) yz := by
      apply integral_congr_ae
      filter_upwards with yz
      exact hs yz
    _ = ∫ yz in triangle a, ∫ x in Icc 0 (a-yz.1-yz.2), D (x,yz) :=
      integral_indicator (triangle_compact a).measurableSet
    _ = ∫ yz in triangle a, ∫ x in (0 : ℝ)..(a-yz.1-yz.2), D (x,yz) := by
      apply setIntegral_congr_fun (triangle_compact a).measurableSet
      intro yz hy
      have hab : 0 ≤ a-yz.1-yz.2 := by linarith [hy.2.2]
      change (∫ x in Icc (0 : ℝ) (a-yz.1-yz.2), D (x,yz)) =
        ∫ x in (0 : ℝ)..(a-yz.1-yz.2), D (x,yz)
      rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]

theorem tetrahedron_directional (a : ℝ) (P D : ℝ × (ℝ × ℝ) → E)
    (hP : ContinuousOn P (tetrahedron a)) (hD : ContinuousOn D (tetrahedron a))
    (hd : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P (t,yz)) (D (x,yz)) x) :
    (∫ z in tetrahedron a, D z) =
      ∫ yz in triangle a, P (a-yz.1-yz.2,yz)-P (0,yz) := by
  rw [tetrahedron_iterated a D hD]
  apply setIntegral_congr_fun (triangle_compact a).measurableSet
  intro yz hy
  have hab : 0 ≤ a-yz.1-yz.2 := by linarith [hy.2.2]
  have hmap : MapsTo (fun x : ℝ => (x,yz)) (Icc 0 (a-yz.1-yz.2)) (tetrahedron a) := by
    intro x hx
    exact ⟨hx.1,hy.1,hy.2.1,by linarith [hx.2]⟩
  have hpair : Continuous (fun x : ℝ => (x,yz)) :=
    continuous_id.prodMk continuous_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hP.comp' hpair.continuousOn hmap) (hd yz hy)
    (ContinuousOn.intervalIntegrable_of_Icc hab (hD.comp' hpair.continuousOn hmap))

theorem triangle_boundary_integrable (a : ℝ) (ha : 0 ≤ a)
    (P : ℝ × ℝ → E) (hP : ContinuousOn P (triangle a)) :
    IntervalIntegrable (fun y => P (a-y,y)-P (0,y)) volume 0 a := by
  have ht : ContinuousOn (fun y : ℝ => P (a-y,y)) (Icc 0 a) := by
    apply hP.comp' (show Continuous (fun y : ℝ => (a-y,y)) by fun_prop).continuousOn
    intro y hy
    exact ⟨sub_nonneg.mpr hy.2,hy.1,by linarith⟩
  have hb : ContinuousOn (fun y : ℝ => P (0,y)) (Icc 0 a) := by
    apply hP.comp' (show Continuous (fun y : ℝ => ((0:ℝ),y)) by fun_prop).continuousOn
    intro y hy
    exact ⟨le_rfl,hy.1,by linarith [hy.2]⟩
  exact ContinuousOn.intervalIntegrable_of_Icc ha (ht.sub hb)

theorem tetrahedron_boundary_integrable (a : ℝ)
    (P : ℝ × (ℝ × ℝ) → E) (hP : ContinuousOn P (tetrahedron a)) :
    IntegrableOn (fun yz => P (a-yz.1-yz.2,yz)-P (0,yz)) (triangle a) := by
  have ht : ContinuousOn (fun yz : ℝ × ℝ => P (a-yz.1-yz.2,yz)) (triangle a) := by
    apply hP.comp' (show Continuous (fun yz : ℝ × ℝ => (a-yz.1-yz.2,yz)) by fun_prop).continuousOn
    intro yz hy
    exact ⟨by linarith [hy.2.2],hy.1,hy.2.1,by linarith⟩
  have hb : ContinuousOn (fun yz : ℝ × ℝ => P (0,yz)) (triangle a) := by
    apply hP.comp' (show Continuous (fun yz : ℝ × ℝ => ((0:ℝ),yz)) by fun_prop).continuousOn
    intro yz hy
    exact ⟨le_rfl,hy.1,hy.2.1,by simpa using hy.2.2⟩
  exact ContinuousOn.integrableOn_compact (triangle_compact a) (ht.sub hb)

example (D : ℝ × ℝ → ℝ) (hD : ContinuousOn D (triangle 0)) :
    (∫ z in triangle 0, D z) = 0 := by
  simpa using triangle_iterated 0 (le_refl 0) D hD

example : (∫ z in triangle 2, (2*z.1*z.2 : ℝ)) =
    ∫ y in (0:ℝ)..2, (2-y)^2*y := by
  have h := triangle_directional 2 (by norm_num)
    (fun z : ℝ × ℝ => z.1^2*z.2) (fun z : ℝ × ℝ => 2*z.1*z.2)
    (by fun_prop) (by fun_prop) (by
      intro y hy x hx
      convert (((hasDerivAt_id x).pow 2).mul_const y) using 1 <;> simp <;> ring)
  simpa using h

theorem triangle_swap_integral (a : ℝ) (f : ℝ × ℝ → E) :
    (∫ z in triangle a, f z.swap) = ∫ z in triangle a, f z := by
  classical
  have hs (z : ℝ × ℝ) : z.swap ∈ triangle a ↔ z ∈ triangle a := by
    simp only [triangle, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap]
    constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h2,h1,by linarith⟩
  calc
    (∫ z in triangle a, f z.swap) =
        ∫ z, (triangle a).indicator (fun z : ℝ × ℝ => f z.swap) z :=
      (integral_indicator (triangle_compact a).measurableSet).symm
    _ = ∫ z : ℝ × ℝ, (triangle a).indicator f z.swap := by
      congr 1
      funext z
      by_cases hz : z ∈ triangle a <;> simp [hz, hs z]
    _ = ∫ z, (triangle a).indicator f z := integral_prod_swap _
    _ = ∫ z in triangle a, f z :=
      integral_indicator (triangle_compact a).measurableSet

def triangle_reflection (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (a-z.1-z.2,z.2)

theorem triangle_reflection_maps (a : ℝ) :
    MapsTo (triangle_reflection a) (triangle a) (triangle a) := by
  intro z hz
  exact ⟨by dsimp [triangle_reflection];linarith [hz.2.2],hz.2.1,
    by dsimp [triangle_reflection];linarith [hz.1]⟩

theorem triangle_reflection_integral (a : ℝ) (ha : 0 ≤ a)
    (f : ℝ × ℝ → E) (hf : ContinuousOn f (triangle a)) :
    (∫ z in triangle a, f (triangle_reflection a z)) = ∫ z in triangle a, f z := by
  have hc : Continuous (triangle_reflection a) := by unfold triangle_reflection;fun_prop
  rw [triangle_iterated a ha _ (hf.comp' hc.continuousOn (triangle_reflection_maps a)),
    triangle_iterated a ha _ hf]
  apply intervalIntegral.integral_congr_Ioo_of_le ha
  intro y hy
  have heq (x : ℝ) : a-x-y = (a-y)-x := by ring
  simp_rw [triangle_reflection, heq]
  simpa only [sub_self, sub_zero] using
    (intervalIntegral.integral_comp_sub_left (fun x : ℝ => f (x,y))
      (a:=0) (b:=a-y) (a-y))

theorem triangle_cyclic_integral (a : ℝ) (ha : 0 ≤ a)
    (f : ℝ × ℝ → E) (hf : ContinuousOn f (triangle a)) :
    (∫ z in triangle a, f (a-z.1-z.2,z.1)) = ∫ z in triangle a, f z := by
  calc
    (∫ z in triangle a, f (a-z.1-z.2,z.1)) =
        ∫ z in triangle a, f (triangle_reflection a z.swap) := by
      congr 1;funext z;congr 1;dsimp [triangle_reflection];congr 1;ring
    _ = ∫ z in triangle a, f (triangle_reflection a z) := triangle_swap_integral a (fun z => f (triangle_reflection a z))
    _ = ∫ z in triangle a, f z := triangle_reflection_integral a ha f hf

def swapXY : (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.prodAssoc (α:=ℝ) (β:=ℝ) (γ:=ℝ)).symm.trans
    ((MeasurableEquiv.prodComm (α:=ℝ) (β:=ℝ)).prodCongr
      (MeasurableEquiv.refl ℝ)) |>.trans MeasurableEquiv.prodAssoc

def cycleXYZ : (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
  MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc

theorem swapXY_preserving : MeasurePreserving swapXY := by
  have ha := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)
  have hs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).prod (MeasurePreserving.id (volume : Measure ℝ))
  exact ha.comp (hs.comp (MeasurePreserving.symm _ ha))

theorem cycleXYZ_preserving : MeasurePreserving cycleXYZ := by
  exact (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)).comp Measure.measurePreserving_swap

theorem tetrahedron_swapXY_preimage (a : ℝ) :
    swapXY ⁻¹' tetrahedron a = tetrahedron a := by
  ext z
  change (0 ≤ z.2.1 ∧ 0 ≤ z.1 ∧ 0 ≤ z.2.2 ∧ z.2.1+z.1+z.2.2 ≤ a) ↔ _
  simp only [tetrahedron, mem_setOf_eq]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨h2,h1,h3,by linarith⟩

theorem tetrahedron_cycleXYZ_preimage (a : ℝ) :
    cycleXYZ ⁻¹' tetrahedron a = tetrahedron a := by
  ext z
  change (0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧ 0 ≤ z.1 ∧ z.2.1+z.2.2+z.1 ≤ a) ↔ _
  simp only [tetrahedron, mem_setOf_eq]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩;exact ⟨h3,h1,h2,by linarith⟩
  · rintro ⟨h1,h2,h3,h4⟩;exact ⟨h2,h3,h1,by linarith⟩

theorem tetrahedron_swapXY_integral (a : ℝ) (f : ℝ × (ℝ × ℝ) → E) :
    (∫ z in tetrahedron a, f (swapXY z)) = ∫ z in tetrahedron a, f z := by
  have hp := (swapXY_preserving.restrict_preimage (tetrahedron_compact a).measurableSet).integral_comp swapXY.measurableEmbedding f
  simpa only [tetrahedron_swapXY_preimage] using hp

theorem tetrahedron_cycleXYZ_integral (a : ℝ) (f : ℝ × (ℝ × ℝ) → E) :
    (∫ z in tetrahedron a, f (cycleXYZ z)) = ∫ z in tetrahedron a, f z := by
  have hp := (cycleXYZ_preserving.restrict_preimage (tetrahedron_compact a).measurableSet).integral_comp cycleXYZ.measurableEmbedding f
  simpa only [tetrahedron_cycleXYZ_preimage] using hp

theorem tetrahedron_directional_y (a : ℝ) (P D : ℝ × (ℝ × ℝ) → E)
    (hP : ContinuousOn P (tetrahedron a)) (hD : ContinuousOn D (tetrahedron a))
    (hd : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P (yz.1,(t,yz.2))) (D (yz.1,(x,yz.2))) x) :
    (∫ z in tetrahedron a, D z) =
      ∫ yz in triangle a, P (yz.1,(a-yz.1-yz.2,yz.2))-P (yz.1,(0,yz.2)) := by
  have hc : Continuous swapXY := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1,(z.1,z.2.2)))
    fun_prop
  have hm : MapsTo swapXY (tetrahedron a) (tetrahedron a) := by
    intro z hz
    change z ∈ swapXY ⁻¹' tetrahedron a
    rwa [tetrahedron_swapXY_preimage]
  rw [← tetrahedron_swapXY_integral a D]
  exact tetrahedron_directional a (fun z => P (swapXY z)) (fun z => D (swapXY z))
    (hP.comp' hc.continuousOn hm) (hD.comp' hc.continuousOn hm) hd

theorem tetrahedron_directional_z (a : ℝ) (P D : ℝ × (ℝ × ℝ) → E)
    (hP : ContinuousOn P (tetrahedron a)) (hD : ContinuousOn D (tetrahedron a))
    (hd : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P (yz.1,(yz.2,t))) (D (yz.1,(yz.2,x))) x) :
    (∫ z in tetrahedron a, D z) =
      ∫ yz in triangle a, P (yz.1,(yz.2,a-yz.1-yz.2))-P (yz.1,(yz.2,0)) := by
  have hc : Continuous cycleXYZ := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1,(z.2.2,z.1)))
    fun_prop
  have hm : MapsTo cycleXYZ (tetrahedron a) (tetrahedron a) := by
    intro z hz
    change z ∈ cycleXYZ ⁻¹' tetrahedron a
    rwa [tetrahedron_cycleXYZ_preimage]
  rw [← tetrahedron_cycleXYZ_integral a D]
  exact tetrahedron_directional a (fun z => P (cycleXYZ z)) (fun z => D (cycleXYZ z))
    (hP.comp' hc.continuousOn hm) (hD.comp' hc.continuousOn hm) hd

theorem tetrahedron_directional_sum (a : ℝ)
    (P₁ P₂ P₃ D₁ D₂ D₃ : ℝ × (ℝ × ℝ) → E)
    (hP₁ : ContinuousOn P₁ (tetrahedron a)) (hP₂ : ContinuousOn P₂ (tetrahedron a))
    (hP₃ : ContinuousOn P₃ (tetrahedron a)) (hD₁ : ContinuousOn D₁ (tetrahedron a))
    (hD₂ : ContinuousOn D₂ (tetrahedron a)) (hD₃ : ContinuousOn D₃ (tetrahedron a))
    (hd₁ : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P₁ (t,yz)) (D₁ (x,yz)) x)
    (hd₂ : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P₂ (yz.1,(t,yz.2))) (D₂ (yz.1,(x,yz.2))) x)
    (hd₃ : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P₃ (yz.1,(yz.2,t))) (D₃ (yz.1,(yz.2,x))) x) :
    (∫ z in tetrahedron a, D₁ z + D₂ z + D₃ z) =
      (∫ yz in triangle a, P₁ (a-yz.1-yz.2,yz)-P₁ (0,yz)) +
      (∫ yz in triangle a, P₂ (yz.1,(a-yz.1-yz.2,yz.2))-P₂ (yz.1,(0,yz.2))) +
      (∫ yz in triangle a, P₃ (yz.1,(yz.2,a-yz.1-yz.2))-P₃ (yz.1,(yz.2,0))) := by
  have hi₁ : IntegrableOn D₁ (tetrahedron a) := ContinuousOn.integrableOn_compact (tetrahedron_compact a) hD₁
  have hi₂ : IntegrableOn D₂ (tetrahedron a) := ContinuousOn.integrableOn_compact (tetrahedron_compact a) hD₂
  have hi₃ : IntegrableOn D₃ (tetrahedron a) := ContinuousOn.integrableOn_compact (tetrahedron_compact a) hD₃
  change (∫ z in tetrahedron a, ((D₁ + D₂) + D₃) z) = _
  rw [integral_add' (hi₁.add hi₂) hi₃, integral_add' hi₁ hi₂,
    tetrahedron_directional a P₁ D₁ hP₁ hD₁ hd₁,
    tetrahedron_directional_y a P₂ D₂ hP₂ hD₂ hd₂,
    tetrahedron_directional_z a P₃ D₃ hP₃ hD₃ hd₃]

theorem tetrahedron_top_y_integral (a : ℝ) (ha : 0 ≤ a)
    (P : ℝ × (ℝ × ℝ) → E) (hP : ContinuousOn P (tetrahedron a)) :
    (∫ yz in triangle a, P (yz.1,(a-yz.1-yz.2,yz.2))) =
      ∫ yz in triangle a, P (a-yz.1-yz.2,yz) := by
  have hc : ContinuousOn (fun yz : ℝ × ℝ => P (yz.1,(a-yz.1-yz.2,yz.2)))
      (triangle a) := by
    apply hP.comp' (show Continuous (fun yz : ℝ × ℝ =>
      (yz.1,(a-yz.1-yz.2,yz.2))) by fun_prop).continuousOn
    intro yz hy
    exact ⟨hy.1,by linarith [hy.2.2],hy.2.1,by dsimp;linarith⟩
  have h := triangle_reflection_integral a ha _ hc
  calc
    (∫ yz in triangle a, P (yz.1,(a-yz.1-yz.2,yz.2))) =
        ∫ yz in triangle a, P ((triangle_reflection a yz).1,
          (a-(triangle_reflection a yz).1-(triangle_reflection a yz).2,
            (triangle_reflection a yz).2)) := h.symm
    _ = ∫ yz in triangle a, P (a-yz.1-yz.2,yz) := by
      congr 1;funext yz;congr 1
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · dsimp [triangle_reflection];ring
        · rfl

theorem tetrahedron_top_z_integral (a : ℝ) (ha : 0 ≤ a)
    (P : ℝ × (ℝ × ℝ) → E) (hP : ContinuousOn P (tetrahedron a)) :
    (∫ yz in triangle a, P (yz.1,(yz.2,a-yz.1-yz.2))) =
      ∫ yz in triangle a, P (a-yz.1-yz.2,yz) := by
  have hc : ContinuousOn (fun yz : ℝ × ℝ => P (yz.1,(yz.2,a-yz.1-yz.2)))
      (triangle a) := by
    apply hP.comp' (show Continuous (fun yz : ℝ × ℝ =>
      (yz.1,(yz.2,a-yz.1-yz.2))) by fun_prop).continuousOn
    intro yz hy
    exact ⟨hy.1,hy.2.1,by linarith [hy.2.2],by dsimp;linarith⟩
  have h := triangle_cyclic_integral a ha _ hc
  calc
    (∫ yz in triangle a, P (yz.1,(yz.2,a-yz.1-yz.2))) =
        ∫ yz in triangle a, P (a-yz.1-yz.2,(yz.1,a-(a-yz.1-yz.2)-yz.1)) := h.symm
    _ = ∫ yz in triangle a, P (a-yz.1-yz.2,yz) := by
      congr 1;funext yz;congr 1
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · ring

theorem tetrahedron_full_flux (a : ℝ) (ha : 0 ≤ a)
    (P₁ P₂ P₃ D₁ D₂ D₃ : ℝ × (ℝ × ℝ) → E)
    (hP₁ : ContinuousOn P₁ (tetrahedron a)) (hP₂ : ContinuousOn P₂ (tetrahedron a))
    (hP₃ : ContinuousOn P₃ (tetrahedron a)) (hD₁ : ContinuousOn D₁ (tetrahedron a))
    (hD₂ : ContinuousOn D₂ (tetrahedron a)) (hD₃ : ContinuousOn D₃ (tetrahedron a))
    (hd₁ : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P₁ (t,yz)) (D₁ (x,yz)) x)
    (hd₂ : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P₂ (yz.1,(t,yz.2))) (D₂ (yz.1,(x,yz.2))) x)
    (hd₃ : ∀ yz ∈ triangle a, ∀ x ∈ Ioo (0 : ℝ) (a-yz.1-yz.2),
      HasDerivAt (fun t : ℝ => P₃ (yz.1,(yz.2,t))) (D₃ (yz.1,(yz.2,x))) x) :
    (∫ z in tetrahedron a, D₁ z + D₂ z + D₃ z) =
      ∫ yz in triangle a,
        P₁ (a-yz.1-yz.2,yz) + P₂ (a-yz.1-yz.2,yz) + P₃ (a-yz.1-yz.2,yz)
        - P₁ (0,yz) - P₂ (yz.1,(0,yz.2)) - P₃ (yz.1,(yz.2,0)) := by
  let t : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun yz => (a-yz.1-yz.2,yz)
  let b₁ : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun yz => (0,yz)
  let b₂ : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun yz => (yz.1,(0,yz.2))
  let b₃ : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun yz => (yz.1,(yz.2,0))
  let r₂ : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun yz => (yz.1,(a-yz.1-yz.2,yz.2))
  let r₃ : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun yz => (yz.1,(yz.2,a-yz.1-yz.2))
  have trace (P : ℝ × (ℝ × ℝ) → E) (hP : ContinuousOn P (tetrahedron a))
      (f : ℝ × ℝ → ℝ × (ℝ × ℝ)) (hc : Continuous f)
      (hm : MapsTo f (triangle a) (tetrahedron a)) :
      IntegrableOn (fun yz => P (f yz)) (triangle a) :=
    ContinuousOn.integrableOn_compact (triangle_compact a) (hP.comp' hc.continuousOn hm)
  have ht : MapsTo t (triangle a) (tetrahedron a) := by
    intro yz hy; exact ⟨by dsimp [t];linarith [hy.2.2],hy.1,hy.2.1,
      by dsimp [t];linarith⟩
  have hb₁ : MapsTo b₁ (triangle a) (tetrahedron a) := by
    intro yz hy;exact ⟨le_rfl,hy.1,hy.2.1,by simpa [b₁] using hy.2.2⟩
  have hb₂ : MapsTo b₂ (triangle a) (tetrahedron a) := by
    intro yz hy;exact ⟨hy.1,le_rfl,hy.2.1,by simpa [b₂] using hy.2.2⟩
  have hb₃ : MapsTo b₃ (triangle a) (tetrahedron a) := by
    intro yz hy;exact ⟨hy.1,hy.2.1,le_rfl,by simpa [b₃] using hy.2.2⟩
  have hr₂ : MapsTo r₂ (triangle a) (tetrahedron a) := by
    intro yz hy;exact ⟨hy.1,by dsimp [r₂];linarith [hy.2.2],hy.2.1,
      by dsimp [r₂];linarith⟩
  have hr₃ : MapsTo r₃ (triangle a) (tetrahedron a) := by
    intro yz hy;exact ⟨hy.1,hy.2.1,by dsimp [r₃];linarith [hy.2.2],
      by dsimp [r₃];linarith⟩
  have it₁ := trace P₁ hP₁ t (by dsimp [t];fun_prop) ht
  have it₂ := trace P₂ hP₂ t (by dsimp [t];fun_prop) ht
  have it₃ := trace P₃ hP₃ t (by dsimp [t];fun_prop) ht
  have ib₁ := trace P₁ hP₁ b₁ (by dsimp [b₁];fun_prop) hb₁
  have ib₂ := trace P₂ hP₂ b₂ (by dsimp [b₂];fun_prop) hb₂
  have ib₃ := trace P₃ hP₃ b₃ (by dsimp [b₃];fun_prop) hb₃
  have ir₂ := trace P₂ hP₂ r₂ (by dsimp [r₂];fun_prop) hr₂
  have ir₃ := trace P₃ hP₃ r₃ (by dsimp [r₃];fun_prop) hr₃
  have hc₂ : (∫ yz in triangle a, P₂ (r₂ yz)) = ∫ yz in triangle a, P₂ (t yz) :=
    tetrahedron_top_y_integral a ha P₂ hP₂
  have hc₃ : (∫ yz in triangle a, P₃ (r₃ yz)) = ∫ yz in triangle a, P₃ (t yz) :=
    tetrahedron_top_z_integral a ha P₃ hP₃
  have hsum := tetrahedron_directional_sum a P₁ P₂ P₃ D₁ D₂ D₃
    hP₁ hP₂ hP₃ hD₁ hD₂ hD₃ hd₁ hd₂ hd₃
  change (∫ z in tetrahedron a, D₁ z + D₂ z + D₃ z) =
    ∫ yz in triangle a, P₁ (t yz)+P₂ (t yz)+P₃ (t yz)
      -P₁ (b₁ yz)-P₂ (b₂ yz)-P₃ (b₃ yz)
  have hexpand :
      (∫ yz in triangle a, P₁ (t yz)+P₂ (t yz)+P₃ (t yz)
        -P₁ (b₁ yz)-P₂ (b₂ yz)-P₃ (b₃ yz)) =
      (∫ yz in triangle a, P₁ (t yz))+(∫ yz in triangle a, P₂ (t yz))+
        (∫ yz in triangle a, P₃ (t yz))-(∫ yz in triangle a, P₁ (b₁ yz))-
        (∫ yz in triangle a, P₂ (b₂ yz))-(∫ yz in triangle a, P₃ (b₃ yz)) := by
    change (∫ yz in triangle a,
      (((((fun yz => P₁ (t yz)) + (fun yz => P₂ (t yz))) +
        (fun yz => P₃ (t yz))) - (fun yz => P₁ (b₁ yz))) -
        (fun yz => P₂ (b₂ yz)) - (fun yz => P₃ (b₃ yz))) yz) = _
    rw [integral_sub' ((((it₁.add it₂).add it₃).sub ib₁).sub ib₂) ib₃,
      integral_sub' (((it₁.add it₂).add it₃).sub ib₁) ib₂,
      integral_sub' ((it₁.add it₂).add it₃) ib₁,
      integral_add' (it₁.add it₂) it₃, integral_add' it₁ it₂]
  rw [hexpand]
  change (∫ z in tetrahedron a, D₁ z + D₂ z + D₃ z) =
    (∫ yz in triangle a, P₁ (t yz)-P₁ (b₁ yz))+
    (∫ yz in triangle a, P₂ (r₂ yz)-P₂ (b₂ yz))+
    (∫ yz in triangle a, P₃ (r₃ yz)-P₃ (b₃ yz)) at hsum
  rw [integral_sub it₁ ib₁, integral_sub ir₂ ib₂, integral_sub ir₃ ib₃,hc₂,hc₃] at hsum
  rw [hsum]
  abel

def nativeProduct : EuclideanSpace ℝ (Fin 3) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))))

theorem nativeProduct_apply (u : EuclideanSpace ℝ (Fin 3)) :
    nativeProduct u = (u 0,(u 1,u 2)) := rfl

theorem nativeProduct_preserving : MeasurePreserving nativeProduct := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)))

def nativeSimplex (a : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ 0 ≤ u 2 ∧ u 0 + u 1 + u 2 ≤ a}

theorem nativeSimplex_integral (a : ℝ) (f : ℝ × (ℝ × ℝ) → E) :
    (∫ u in nativeSimplex a, f (u 0,(u 1,u 2))) =
      ∫ z in tetrahedron a, f z := by
  have hp := (nativeProduct_preserving.restrict_preimage
    (tetrahedron_compact a).measurableSet).integral_comp nativeProduct.measurableEmbedding f
  exact hp

end CFMPSimplexDirection435Transient

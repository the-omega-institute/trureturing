/- GID: D5/S3/Observer/CubicGain/ResponseProper
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/ResponseProper
   mirror-E: none(waiver:properness-relative-to-open-response-set)
   anchors: [mathlib/module/Mathlib.Topology.Maps.Proper.CompactlyGenerated]
   utility: none
   digest: The actual full-parent M response map is proper precisely relative to the displayed open response set. -/

import D5.S3.Observer.CubicGain.CompactWorld
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Properness is relative to the explicit complement of the escape barrier.
The full strict source domain and the singular Lambda stratum are retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

abbrev ClosureCoordinates := CompactCoordinates × ℝ × Gain × Gain × (ℝ × ℝ)

def ValidClosure (w : ClosureCoordinates) : Prop :=
  ClosureWorld w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2

def compactWorld (C : Coordinates) : ClosureCoordinates :=
  (compactSource C.1 C.2.1,C.2.2,parentGain C,scaledGain C,response C)

def recoverCoordinates (w : ClosureCoordinates) : Coordinates :=
  (w.1 0,w.1 1/(1-w.1 1),w.2.1)

private theorem validClosure_closed : IsClosed {w | ValidClosure w} := by
  have hsc : IsClosed {w : ClosureCoordinates | ∀ i : Fin 4,
      (1-w.1 1)*w.2.2.2.1 i=(1+w.1 1)*w.2.2.1 i} := by
    have he : {w : ClosureCoordinates | ∀ i : Fin 4,
        (1-w.1 1)*w.2.2.2.1 i=(1+w.1 1)*w.2.2.1 i} =
        ⋂ i : Fin 4, {w : ClosureCoordinates |
          (1-w.1 1)*w.2.2.2.1 i=(1+w.1 1)*w.2.2.1 i} := by ext w; simp
    rw [he]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) (by fun_prop)
  unfold ValidClosure ClosureWorld
  apply IsClosed.inter
  · exact closedSource_isCompact.isClosed.preimage continuous_fst
  · repeat' apply IsClosed.inter
    all_goals first
    | exact hsc
    | (apply isClosed_eq <;> (try dsimp [gain,uNorm,vNorm,ell]) <;> fun_prop)

private theorem closure_is_strict (w : ClosureCoordinates) (hw : ValidClosure w)
    (hEsc : escapeBarrier w.2.2.2.2 ≠ 0) :
    0 < w.1 0 ∧ w.1 0 < 1 ∧ 0 < w.1 1 ∧ w.1 1 < 1 ∧
      0 < w.1 2 ∧ w.1 2 < 1 := by
  have bounds := hw.1.1
  have hn (hb : w.1 0=0 ∨ w.1 0=1 ∨ w.1 1=0 ∨ w.1 1=1) : False :=
    hEsc (closure_boundary_barrier _ _ _ _ _ _ hw hb)
  have hr0 : w.1 0 ≠ 0 := fun h => hn (Or.inl h)
  have hr1 : w.1 0 ≠ 1 := fun h => hn (Or.inr (Or.inl h))
  have hx0 : w.1 1 ≠ 0 := fun h => hn (Or.inr (Or.inr (Or.inl h)))
  have hx1 : w.1 1 ≠ 1 := fun h => hn (Or.inr (Or.inr (Or.inr h)))
  have hr : 0 < w.1 0 := lt_of_le_of_ne (bounds 0).1 (Ne.symm hr0)
  have hr' : w.1 0 < 1 := lt_of_le_of_ne (bounds 0).2 hr1
  have hx : 0 < w.1 1 := lt_of_le_of_ne (bounds 1).1 (Ne.symm hx0)
  have hx' : w.1 1 < 1 := lt_of_le_of_ne (bounds 1).2 hx1
  have hk0 : w.1 2 ≠ 0 := by
    intro h
    have c1 := hw.1.2.1
    rw [h] at c1
    have hnon : 0 ≤ w.1 0*(1-w.1 0)*(1-w.1 1)^2 := by positivity
    nlinarith only [c1,hnon,sq_pos_of_pos hx]
  have hk1 : w.1 2 ≠ 1 := by
    intro h
    have c1 := hw.1.2.1
    rw [h] at c1
    have hp : 0 < w.1 1*(1-w.1 1) := mul_pos hx (sub_pos.mpr hx')
    nlinarith only [c1,hp]
  exact ⟨hr,hr',hx,hx',lt_of_le_of_ne (bounds 2).1 (Ne.symm hk0),
    lt_of_le_of_ne (bounds 2).2 hk1⟩


abbrev ParentOverOpen := {C : Coordinates // StrictParent C ∧ response C ∈ responseOpen}

def responseOverOpen (C : ParentOverOpen) : responseOpen := ⟨response C.1,C.2.2⟩

private theorem response_continuousAt (C : Coordinates) (hC : StrictParent C) :
    ContinuousAt response C := by
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity C.1 C.2.1 hC.1.le hC.2.1.le hC.2.2.1
  have hb := hC.2.2.1
  unfold response fifthResponse sixthResponse fifthDrift sixthDrift sourceN sourceJ
  fun_prop (disch := first | exact ne_of_gt hj | exact ne_of_gt hn | exact ne_of_gt ht | exact ne_of_gt hu | exact ne_of_gt hb)

/-- The complete original-coordinate parent map is proper relative to O.
No escape premise, normalization, nonzero sample, or bound is a hypothesis. -/
theorem full_parent_response_proper : IsProperMap responseOverOpen := by
  have hpreimage (K : Set (ℝ × ℝ)) (hK : IsCompact K)
      (hKO : K ⊆ responseOpen) :
      IsCompact {C : Coordinates | StrictParent C ∧ response C ∈ K} := by
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_fst.continuousOn
    obtain ⟨D,G,H,hbounds⟩ := bounded_fifth_bounds_scaled_gain M
    let B : Set ClosureCoordinates :=
      Set.Icc (0 : CompactCoordinates) 1 ×ˢ Set.Icc (-D) D ×ˢ
        Set.Icc (fun _ : Fin 4 => -G) (fun _ => G) ×ˢ
        Set.Icc (fun _ : Fin 4 => -H) (fun _ => H) ×ˢ K
    let J : Set ClosureCoordinates := B ∩ {w | ValidClosure w}
    have hB : IsCompact B :=
      isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod hK)))
    have hJ : IsCompact J := hB.inter_right validClosure_closed
    have hstrict (w : ClosureCoordinates) (hw : w ∈ J) :=
      closure_is_strict w hw.2 ((hKO hw.1.2.2.2.2).2)
    have hrec : ContinuousOn recoverCoordinates J := by
      unfold recoverCoordinates
      fun_prop (disch := intro w hw; have hh := (hstrict w hw).2.2.2.1; exact ne_of_gt (sub_pos.mpr hh))
    have himage : recoverCoordinates '' J = {C : Coordinates | StrictParent C ∧ response C ∈ K} := by
      ext C
      constructor
      · rintro ⟨w,hw,rfl⟩
        obtain ⟨hr,hr1,hx,hx1,hk,hk1⟩ := hstrict w hw
        obtain ⟨hp,ha,hrsp⟩ := finite_closure_lift _ _ _ _ _ _ hw.2 hx hx1 hk hk1
        refine ⟨⟨hr,hr1,div_pos hx (sub_pos.mpr hx1),hp⟩,?_⟩
        change response (w.1 0,w.1 1/(1-w.1 1),w.2.1) ∈ K
        rw [hrsp]
        exact hw.1.2.2.2.2
      · rintro ⟨hC,hCK⟩
        have hbound : |fifthResponse C| ≤ M := by
          simpa [response] using hM (response C) hCK
        obtain ⟨hd,hg,hh⟩ := hbounds C hC hbound
        have hz := compactSource_mem C.1 C.2.1 hC.1 hC.2.1 hC.2.2.1
        have hbox : compactSource C.1 C.2.1 ∈ Set.Icc (0 : CompactCoordinates) 1 :=
          ⟨fun i => (hz.1 i).1,fun i => (hz.1 i).2⟩
        have ha : parentGain C ∈ Set.Icc (fun _ : Fin 4 => -G) (fun _ => G) :=
          ⟨fun i => (abs_le.mp (hg i)).1,fun i => (abs_le.mp (hg i)).2⟩
        have hh' : scaledGain C ∈ Set.Icc (fun _ : Fin 4 => -H) (fun _ => H) :=
          ⟨fun i => (abs_le.mp (hh i)).1,fun i => (abs_le.mp (hh i)).2⟩
        refine ⟨compactWorld C,⟨⟨hbox,abs_le.mp hd,ha,hh',hCK⟩,closureWorld_actual C hC⟩,?_⟩
        dsimp [recoverCoordinates,compactWorld,compactSource]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · have hb : 0 < 1+C.2.1 := by have := hC.2.2.1; positivity
            field_simp [ne_of_gt hb]
            ring
          · rfl
    rw [← himage]
    exact hJ.image_of_continuousOn hrec
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨?_,?_⟩
  · apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro C
    exact (response_continuousAt C.1 C.2.1).comp continuous_subtype_val.continuousAt
  · intro K hK
    let L : Set (ℝ × ℝ) := Subtype.val '' K
    have hL : IsCompact L := hK.image continuous_subtype_val
    have hLO : L ⊆ responseOpen := by
      rintro _ ⟨q,hq,rfl⟩
      exact q.2
    have hcomp := hpreimage L hL hLO
    apply Subtype.isCompact_iff.mpr
    convert hcomp using 1
    ext C
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact ⟨c.2.1,⟨responseOverOpen c,hc,rfl⟩⟩
    · rintro ⟨hC,q,hq,heq⟩
      have hCO : response C ∈ responseOpen := heq ▸ q.2
      refine ⟨⟨C,hC,hCO⟩,?_,rfl⟩
      change responseOverOpen ⟨C,hC,hCO⟩ ∈ K
      have hsame : responseOverOpen ⟨C,hC,hCO⟩=q := Subtype.ext heq.symm
      rwa [hsame]

#print axioms full_parent_response_proper

end D5.S3.Observer.CubicGain

/- GID: D5/S3/Quantum/Fibers/OriginalRepeatedPrefix
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalRepeatedPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal repeated original controls and native exponential survival. -/

import D5.S3.Quantum.Fibers.OriginalMarkedConcatenation

/-! Native all-n original early/late height construction. -/

noncomputable section
namespace D5.S3.Quantum.Fibers.OriginalRepeatedPrefix
open Set MeasureTheory
open OriginalControlComposition OriginalControlMarkedJump OriginalMarkedConcatenation
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The actual fixed support band of the early/late construction. -/
structure Band where
  a : ℝ
  b : ℝ
  c : ℝ
  a_pos : 0 < a
  ab : a < b
  bc : b < c
  c_lt : c < 1/2

namespace Band

def q (B : Band) : ℝ := (B.a/B.b)*((B.c-B.b)/(B.c-B.a))

def up (B : Band) (d : ℝ) (hd : 0 < d) : Leg :=
  ⟨B.c,B.a,B.b,d,B.c_lt,B.a_pos,B.ab.trans B.bc,
    B.a_pos.trans B.ab,B.bc,hd⟩
def down (B : Band) (d : ℝ) (hd : 0 < d) : Leg :=
  ⟨B.c,B.b,B.a,d,B.c_lt,B.a_pos.trans B.ab,B.bc,
    B.a_pos,B.ab.trans B.bc,hd⟩
def wait (B : Band) : Leg :=
  ⟨B.c,B.a,B.a,1/2,B.c_lt,B.a_pos,B.ab.trans B.bc,
    B.a_pos,B.ab.trans B.bc,by norm_num⟩

def loop (B : Band) (d : ℝ) (hd : 0 < d) : ℝ → ℝ :=
  concatenate (B.up d hd).height (B.down d hd).height d

def repeated (B : Band) (d : ℝ) (hd : 0 < d) : ℕ → ℝ → ℝ
  | 0 => fun _ => B.a
  | j+1 => concatenate (repeated B d hd j) (B.loop d hd) (2*(j:ℝ)*d)

def earlySuffix (B : Band) : ℝ → ℝ :=
  concatenate (B.loop (1/4) (by norm_num)) B.wait.height (1/2)
def lateSuffix (B : Band) : ℝ → ℝ :=
  concatenate B.wait.height (B.loop (1/4) (by norm_num)) (1/2)

def halfStep (n : ℕ) : ℝ := 1/(2*(n:ℝ))
theorem halfStep_pos (n : ℕ) (hn : 1 ≤ n) : 0 < halfStep n := by
  unfold halfStep
  positivity

def early (B : Band) (n : ℕ) (hn : 1 ≤ n) : ℝ → ℝ :=
  concatenate (B.repeated (halfStep n) (halfStep_pos n hn) n) B.earlySuffix 1
def late (B : Band) (n : ℕ) (hn : 1 ≤ n) : ℝ → ℝ :=
  concatenate (B.repeated (halfStep n) (halfStep_pos n hn) n) B.lateSuffix 1

private theorem phase_join (T chi : ℝ) :
    concatenate (fun _ => chi) (fun _ => chi) T = (fun _ => chi) := by
  funext t
  simp [concatenate]

private theorem append_control (B : Band) (T U chi : ℝ) (f g : ℝ → ℝ)
    (hf : OriginalControl (B.c,B.c,1-2*B.c) T f (fun _ => chi))
    (hg : OriginalControl (B.c,B.c,1-2*B.c) U g (fun _ => chi))
    (hj : f T = g 0) :
    OriginalControl (B.c,B.c,1-2*B.c) (T+U) (concatenate f g T) (fun _ => chi) := by
  simpa only [phase_join] using
    (concatenate_original _ _ _ _ _ _ _ hf hg hj).1

private theorem leg_end (L : Leg) : L.height L.duration = L.y := by
  dsimp [Leg.height,Leg.speed]
  field_simp [L.duration_pos.ne']
  <;> ring

private theorem leg_terminal (L : Leg) :
    survival L.c L.height L.duration =
      if L.x ≤ L.y then L.x/L.y else (L.c-L.x)/(L.c-L.y) := by
  rw [leg_survival]
  simpa only [leg_end] using
    (L.affine_marked_probability 0 0 0 (fun _ => 0)).2.2.2.2.2.2.1
      L.duration ⟨L.duration_pos.le,le_rfl⟩

theorem loop_zero (B : Band) (d : ℝ) (hd : 0 < d) : B.loop d hd 0=B.a := by
  simp [loop,concatenate,hd.le,up,Leg.height]
theorem loop_end (B : Band) (d : ℝ) (hd : 0 < d) : B.loop d hd (2*d)=B.a := by
  have ht : ¬ 2*d ≤ d := by linarith
  simp only [loop,concatenate,if_neg ht]
  rw [show 2*d-d=d by ring]
  change (B.up d hd).height (B.up d hd).duration +
    (B.down d hd).height (B.down d hd).duration - (B.down d hd).height 0 = B.a
  rw [leg_end,leg_end]
  simp [up,down,Leg.height]

theorem loop_control (B : Band) (d chi : ℝ) (hd : 0 < d) :
    OriginalControl (B.c,B.c,1-2*B.c) (2*d) (B.loop d hd) (fun _ => chi) := by
  have h0 := ((B.up d hd).affine_marked_probability chi 0 0 (fun _ => 0)).1
  have h1 := ((B.down d hd).affine_marked_probability chi 0 0 (fun _ => 0)).1
  have hj : (B.up d hd).height d=(B.down d hd).height 0 := by
    change (B.up d hd).height (B.up d hd).duration = _
    rw [leg_end]
    simp [up,down,Leg.height]
  simpa only [two_mul,loop] using append_control B d d chi _ _ h0 h1 hj

theorem loop_survival (B : Band) (d : ℝ) (hd : 0 < d) :
    survival B.c (B.loop d hd) (2*d)=B.q := by
  have hj : (B.up d hd).height d=(B.down d hd).height 0 := by
    change (B.up d hd).height (B.up d hd).duration = _
    rw [leg_end]
    simp [up,down,Leg.height]
  have hs := (native_concatenation B.c d d B.a 0
    (B.up d hd).height (B.down d hd).height B.c_lt hd.le hd.le hj
    ⟨B.a_pos,B.ab.trans B.bc⟩
    (by change (B.up d hd).height (B.up d hd).duration ∈ Ioo 0 B.c
        rw [leg_end]; exact ⟨B.a_pos.trans B.ab,B.bc⟩)
    (by change (B.down d hd).height (B.down d hd).duration ∈ Ioo 0 B.c
        rw [leg_end]; exact ⟨B.a_pos,B.ab.trans B.bc⟩)
    ((B.up d hd).affine_marked_probability 0 0 0 (fun _ => 0)).1
    ((B.down d hd).affine_marked_probability 0 0 0 (fun _ => 0)).1).2.1
  change survival B.c (B.loop d hd) (d+d)=_ at hs
  rw [show d+d=2*d by ring] at hs
  rw [hs]
  have hu := leg_terminal (B.up d hd)
  have hv := leg_terminal (B.down d hd)
  simpa [up,down,B.ab.le,not_le.mpr B.ab,q] using congrArg₂ (·*·) hu hv

theorem prefix_facts (B : Band) (d chi : ℝ) (hd : 0 < d) (j : ℕ) :
    OriginalControl (B.c,B.c,1-2*B.c) (2*(j:ℝ)*d) (B.repeated d hd j) (fun _ => chi) ∧
    B.repeated d hd j 0=B.a ∧ B.repeated d hd j (2*(j:ℝ)*d)=B.a ∧
    survival B.c (B.repeated d hd j) (2*(j:ℝ)*d)=B.q^j := by
  induction j with
  | zero =>
    have ha := (LipschitzWith.const B.a).lipschitzOnWith.absolutelyContinuousOnInterval
      (a:=0) (b:=0)
    have hc := (LipschitzWith.const chi).lipschitzOnWith.absolutelyContinuousOnInterval
      (a:=0) (b:=0)
    refine ⟨?_,by simp [repeated],by simp [repeated],by simp [survival]⟩
    simp only [Nat.cast_zero,mul_zero,zero_mul,repeated]
    change OriginalControl (B.c,B.c,1-2*B.c) 0 (fun _ => B.a) (fun _ => chi)
    refine ⟨by simp,continuousOn_const,continuousOn_const,?_,hc.boundedVariationOn,
      Or.inl ⟨ha,hc⟩⟩
    intro t ht
    have hl : FiniteRectangleTransport.lower (B.c,B.c,1-2*B.c)=0 := by
      dsimp [FiniteRectangleTransport.lower]
      ring_nf
      simp
    simpa [repeated,hl,FiniteRectangleTransport.upper] using ⟨B.a_pos,B.ab.trans B.bc⟩
  | succ j ih =>
    have hT : 0 ≤ 2*(j:ℝ)*d := by positivity
    have hj : B.repeated d hd j (2*(j:ℝ)*d)=B.loop d hd 0 := by rw [ih.2.2.1,loop_zero]
    have he : 2*((j+1:ℕ):ℝ)*d=2*(j:ℝ)*d+2*d := by push_cast; ring
    have ho := append_control B _ (2*d) chi _ _ ih.1 (loop_control B d chi hd) hj
    have hs := (native_concatenation B.c _ (2*d) B.a chi
      (B.repeated d hd j) (B.loop d hd) B.c_lt hT (by positivity) hj
      ⟨B.a_pos,B.ab.trans B.bc⟩ (by rw [ih.2.2.1]; exact ⟨B.a_pos,B.ab.trans B.bc⟩)
      (by rw [loop_end]; exact ⟨B.a_pos,B.ab.trans B.bc⟩)
      ih.1 (loop_control B d chi hd)).2.1
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [repeated,he] using ho
    · simp only [repeated,concatenate,if_pos hT,ih.2.1]
    · rw [he]
      simp only [repeated,concatenate,if_neg (by linarith : ¬ 2*(j:ℝ)*d+2*d ≤ 2*(j:ℝ)*d),
        add_sub_cancel_left,ih.2.2.1,loop_end,loop_zero,add_sub_cancel_right]
    · rw [he]
      change survival B.c (concatenate (B.repeated d hd j) (B.loop d hd) (2*(j:ℝ)*d))
        (2*(j:ℝ)*d+2*d)=_
      rw [hs,ih.2.2.2,loop_survival,pow_succ]

theorem wait_facts (B : Band) (chi : ℝ) :
    OriginalControl (B.c,B.c,1-2*B.c) (1/2) B.wait.height (fun _ => chi) ∧
    B.wait.height 0=B.a ∧ B.wait.height (1/2)=B.a ∧
    survival B.c B.wait.height (1/2)=1 := by
  refine ⟨(B.wait.affine_marked_probability chi 0 0 (fun _ => 0)).1,?_,?_,?_⟩
  · simp [wait,Leg.height]
  · exact leg_end B.wait
  · simpa [wait,B.a_pos.ne'] using leg_terminal B.wait

theorem suffix_facts (B : Band) (chi : ℝ) (e : Bool) :
    let k := if e then B.earlySuffix else B.lateSuffix
    OriginalControl (B.c,B.c,1-2*B.c) 1 k (fun _ => chi) ∧
    k 0=B.a ∧ k 1=B.a ∧ survival B.c k 1=B.q := by
  have hlo := loop_control B (1/4) chi (by norm_num)
  have hl0 := loop_zero B (1/4) (by norm_num)
  have hl1 := loop_end B (1/4) (by norm_num)
  have hls := loop_survival B (1/4) (by norm_num)
  rw [show (2:ℝ)*(1/4)=1/2 by norm_num] at hlo hl1 hls
  obtain ⟨hwo,hw0,hw1,hws⟩ := wait_facts B chi
  cases e <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · have hj : B.wait.height (1/2)=B.loop (1/4) (by norm_num) 0 := hw1.trans hl0.symm
    have ho := append_control B (1/2) (1/2) chi _ _ hwo hlo hj
    have hs := (native_concatenation B.c (1/2) (1/2) B.a chi _ _ B.c_lt
      (by norm_num) (by norm_num) hj ⟨B.a_pos,B.ab.trans B.bc⟩
      (by rw [hw1]; exact ⟨B.a_pos,B.ab.trans B.bc⟩)
      (by rw [hl1]; exact ⟨B.a_pos,B.ab.trans B.bc⟩) hwo hlo).2.1
    rw [show (1/2:ℝ)+1/2=1 by norm_num] at ho hs
    refine ⟨ho,?_,?_,?_⟩
    · simpa [lateSuffix,concatenate] using hw0
    · norm_num [lateSuffix,concatenate,hw1,hl1,hl0]
    · simpa only [lateSuffix,hws,hls,one_mul] using hs
  · have hj : B.loop (1/4) (by norm_num) (1/2)=B.wait.height 0 := hl1.trans hw0.symm
    have ho := append_control B (1/2) (1/2) chi _ _ hlo hwo hj
    have hs := (native_concatenation B.c (1/2) (1/2) B.a chi _ _ B.c_lt
      (by norm_num) (by norm_num) hj ⟨B.a_pos,B.ab.trans B.bc⟩
      (by rw [hl1]; exact ⟨B.a_pos,B.ab.trans B.bc⟩)
      (by rw [hw1]; exact ⟨B.a_pos,B.ab.trans B.bc⟩) hlo hwo).2.1
    rw [show (1/2:ℝ)+1/2=1 by norm_num] at ho hs
    refine ⟨ho,?_,?_,?_⟩
    · simpa [earlySuffix,concatenate] using hl0
    · norm_num [earlySuffix,concatenate,hw1,hl1,hw0]
    · simpa only [earlySuffix,hws,hls,mul_one] using hs

end Band
open Band

/-- Every n uses a literal repeated height, native exponential survival and
the original constant-phase control class. The displayed nonzero gap is
attained by those same height functions at the original clock 5/4. -/
theorem early_late_native_survival (B : Band) (n : ℕ) (hn : 1 ≤ n) (chi : ℝ) :
    0 < B.q ∧ B.q < 1 ∧
    OriginalControl (B.c,B.c,1-2*B.c) 2 (B.early n hn) (fun _ => chi) ∧
    OriginalControl (B.c,B.c,1-2*B.c) 2 (B.late n hn) (fun _ => chi) ∧
    AbsolutelyContinuousOnInterval (B.early n hn) 0 2 ∧
    AbsolutelyContinuousOnInterval (B.late n hn) 0 2 ∧
    (∀ t ∈ Icc (0:ℝ) 1, B.early n hn t=B.repeated (halfStep n) (halfStep_pos n hn) n t ∧
      B.late n hn t=B.repeated (halfStep n) (halfStep_pos n hn) n t) ∧
    B.early n hn 2=B.a ∧ B.late n hn 2=B.a ∧
    survival B.c (B.early n hn) 2=B.q^(n+1) ∧
    survival B.c (B.late n hn) 2=B.q^(n+1) ∧
    B.early n hn (5/4)=B.b ∧ B.late n hn (5/4)=B.a := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n≠0)
  have htime : 2*(n:ℝ)*halfStep n=1 := by dsimp [halfStep]; field_simp
  obtain ⟨hpo,hp0,hp1,hps⟩ := prefix_facts B (halfStep n) chi (halfStep_pos n hn) n
  rw [htime] at hpo hp1 hps
  have branch (e : Bool) :
      let k := if e then B.earlySuffix else B.lateSuffix
      OriginalControl (B.c,B.c,1-2*B.c) 2
        (concatenate (B.repeated (halfStep n) (halfStep_pos n hn) n) k 1) (fun _ => chi) ∧
      concatenate (B.repeated (halfStep n) (halfStep_pos n hn) n) k 1 2=B.a ∧
      survival B.c (concatenate (B.repeated (halfStep n) (halfStep_pos n hn) n) k 1) 2=B.q^(n+1) := by
    obtain ⟨hso,hs0,hs1,hss⟩ := suffix_facts B chi e
    dsimp only at hso hs0 hs1 hss ⊢
    have hj := hp1.trans hs0.symm
    have ho := append_control B 1 1 chi _ _ hpo hso hj
    have hs := (native_concatenation B.c 1 1 B.a chi _ _ B.c_lt zero_le_one zero_le_one hj
      ⟨B.a_pos,B.ab.trans B.bc⟩ (by rw [hp1]; exact ⟨B.a_pos,B.ab.trans B.bc⟩)
      (by rw [hs1]; exact ⟨B.a_pos,B.ab.trans B.bc⟩) hpo hso).2.1
    norm_num only at ho hs
    refine ⟨ho,?_,?_⟩
    · norm_num [concatenate,hp1,hs1,hs0]
    · rw [hs,hps,hss,pow_succ]
  have he := branch true
  have hl := branch false
  dsimp only at he hl
  have hq0 : 0 < B.q := mul_pos (div_pos B.a_pos (B.a_pos.trans B.ab))
    (div_pos (sub_pos.mpr B.bc) (sub_pos.mpr (B.ab.trans B.bc)))
  have hq1 : B.q < 1 := by
    have hu : B.a/B.b < 1 := (div_lt_one (B.a_pos.trans B.ab)).mpr B.ab
    have hv : (B.c-B.b)/(B.c-B.a) < 1 :=
      (div_lt_one (sub_pos.mpr (B.ab.trans B.bc))).mpr (by linarith [B.ab])
    exact (mul_lt_mul_of_pos_right hu
      (div_pos (sub_pos.mpr B.bc) (sub_pos.mpr (B.ab.trans B.bc)))).trans (by simpa using hv)
  refine ⟨hq0,hq1,he.1,hl.1,(original_ac _ _ _ _ he.1).1,
    (original_ac _ _ _ _ hl.1).1,?_,he.2.1,hl.2.1,he.2.2,hl.2.2,?_,?_⟩
  · intro t ht
    simp [early,late,concatenate,ht.2]
  · norm_num [early,concatenate,hp1,earlySuffix,loop,up,down,wait,Leg.height,Leg.speed]
    <;> ring
  · norm_num [late,concatenate,hp1,lateSuffix,loop,up,down,wait,Leg.height,Leg.speed]
    <;> ring

end D5.S3.Quantum.Fibers.OriginalRepeatedPrefix

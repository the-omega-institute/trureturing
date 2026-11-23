/- GID: D5/S3/Quantum/Entanglement/SectorChannels/CoherentBinaryOptimalFilter
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/CoherentBinaryOptimalFilter
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact maximizing filters and the largest coherence-retaining filter at the weighted diagonal optimum. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter

section Scalar
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def score (q w t : K) : K :=
  min w (q*t^2)+min (1-w) (1-2*q*t+q*t^2)

private theorem p_inc (q u v : K) (hq : 0<q) (hu : 0≤u) (huv : u<v) :
    q*u^2 < q*v^2 := by
  have h : 0 < q*(v-u)*(v+u) :=
    mul_pos (mul_pos hq (sub_pos.mpr huv)) (by linarith)
  nlinarith only [h]

private theorem r_dec (q u v : K) (hq : 0<q) (huv : u<v) (hv : v≤1) :
    1-2*q*v+q*v^2 < 1-2*q*u+q*u^2 := by
  have h : 0 < q*(v-u)*(2-u-v) :=
    mul_pos (mul_pos hq (sub_pos.mpr huv)) (by linarith)
  nlinarith only [h]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem r_one (q w t : K) (h : w=q*(2*t-t^2)) :
    (1-w)=(1-2*q*t+q*t^2) := by rw [h]; ring

private theorem score_lower_half (q w t1 t2 t : K)
    (hq : 0<q) (h1 : 0<t1) (h12 : t1<t2) (h2 : t2<1) (ht : 0≤t)
    (hwt1 : w=q*(2*t1-t1^2)) (hwt2 : w=q*t2^2) (hh : t<t1) :
    score q w t < score q w t1 := by
  have hp1 : q*t1^2<w := hwt2.symm ▸ p_inc q t1 t2 hq h1.le h12
  have hp : q*t^2<w := (p_inc q t t1 hq ht hh).trans hp1
  have hr : 1-w < 1-2*q*t+q*t^2 := (r_one q w t1 hwt1) ▸ r_dec q t t1 hq hh (h12.trans h2).le
  rw [score,score,min_eq_right hp.le,min_eq_left hr.le,min_eq_right hp1.le,
    ←r_one q w t1 hwt1,min_self]
  exact add_lt_add_left (p_inc q t t1 hq ht hh) _

private theorem score_upper_half (q w t1 t2 t : K)
    (hq : 0<q) (h1 : 0<t1) (h12 : t1<t2) (h2 : t2<1) (ht : t≤1)
    (hwt1 : w=q*(2*t1-t1^2)) (hwt2 : w=q*t2^2) (hh : t2<t) :
    score q w t < score q w t2 := by
  have hp : w<q*t^2 := hwt2.symm ▸ p_inc q t2 t hq (h1.trans h12).le hh
  have hr2 : 1-2*q*t2+q*t2^2 < 1-w :=
    (r_one q w t1 hwt1).symm ▸ r_dec q t1 t2 hq h12 h2.le
  have hr : 1-2*q*t+q*t^2 < 1-w := (r_dec q t2 t hq hh ht).trans hr2
  rw [score,score,min_eq_left hp.le,min_eq_right hr.le,min_eq_left hwt2.le,min_eq_right hr2.le]
  exact add_lt_add_right (r_dec q t2 t hq hh ht) _

private theorem score_middle (q w t1 t2 t : K)
    (hq : 0<q) (h1 : 0<t1) (h2 : t2<1)
    (hwt1 : w=q*(2*t1-t1^2)) (hwt2 : w=q*t2^2)
    (h1t : t1≤t) (ht2 : t≤t2) :
    score q w t = 1-2*q*t+2*q*t^2 := by
  have hp : q*t^2≤w := by
    rcases lt_or_eq_of_le ht2 with h|h
    · exact (hwt2.symm ▸ p_inc q t t2 hq (h1.le.trans h1t) h).le
    · rw [h,←hwt2]
  have hr : 1-2*q*t+q*t^2 ≤ 1-w := by
    rcases lt_or_eq_of_le h1t with h|h
    · exact ((r_one q w t1 hwt1).symm ▸ r_dec q t1 t hq h (ht2.trans h2.le)).le
    · rw [←h,←r_one q w t1 hwt1]
  rw [score,min_eq_right hp,min_eq_right hr]
  ring

/-- Exact characterization of equality in the small-marginal clipped score.
The admissible thresholds are expressed by their defining algebraic equations,
avoiding any appeal to a square-root operation in the ordered carrier. -/
private theorem score_maximizer_iff (q w t1 t2 t : K)
    (hq : 0<q) (h1 : 0<t1) (h12 : t1<t2) (h2 : t2<1) (ht0 : 0≤t) (ht1 : t≤1)
    (hwt1 : w=q*(2*t1-t1^2)) (hwt2 : w=q*t2^2) :
    score q w t ≤ max (score q w t1) (score q w t2) ∧
    (score q w t = max (score q w t1) (score q w t2) ↔
      (t=t1 ∧ 2*w≤q) ∨ (t=t2 ∧ q≤2*w)) := by
  have htS1 := score_middle q w t1 t2 t1 hq h1 h2 hwt1 hwt2 le_rfl h12.le
  have htS2 := score_middle q w t1 t2 t2 hq h1 h2 hwt1 hwt2 h12.le le_rfl
  have hdiff : score q w t2 - score q w t1 = 2*q*(t2-t1)*(t1+t2-1) := by rw [htS1,htS2]; ring
  have hsw : 2*w-q = q*(t1+t2-1)*(t2+1-t1) := by nlinarith only [hwt1,hwt2]
  have hcoeff : 0<2*q*(t2-t1) := mul_pos (by linarith) (sub_pos.mpr h12)
  have hwcoeff : 0<q*(t2+1-t1) := mul_pos hq (by linarith)
  have Hsw : 2*w-q = q*(t2+1-t1)*(t1+t2-1) := by rw [hsw]; ring
  have hs12 : score q w t1≤score q w t2 ↔ q≤2*w := calc
    _ ↔ 0≤score q w t2-score q w t1 := sub_nonneg.symm
    _ ↔ 0≤t1+t2-1 := by rw [hdiff,mul_nonneg_iff_of_pos_left hcoeff]
    _ ↔ 0≤2*w-q := by rw [Hsw,mul_nonneg_iff_of_pos_left hwcoeff]
    _ ↔ _ := sub_nonneg
  have hd' : score q w t1-score q w t2 = 2*q*(t2-t1)*(1-t1-t2) := by
    rw [←neg_sub,hdiff]
    ring
  have hw' : q-2*w = q*(t2+1-t1)*(1-t1-t2) := by rw [←neg_sub,Hsw]; ring
  have hs21 : score q w t2≤score q w t1 ↔ 2*w≤q := calc
    _ ↔ 0≤score q w t1-score q w t2 := sub_nonneg.symm
    _ ↔ 0≤1-t1-t2 := by rw [hd',mul_nonneg_iff_of_pos_left hcoeff]
    _ ↔ 0≤q-2*w := by rw [hw',mul_nonneg_iff_of_pos_left hwcoeff]
    _ ↔ _ := sub_nonneg
  have strictInterior (h1t : t1<t) (ht2 : t<t2) :
      score q w t < max (score q w t1) (score q w t2) := by
    have htp := score_middle q w t1 t2 t hq h1 h2 hwt1 hwt2 h1t.le ht2.le
    have hsum1 : 0<t-t1 := sub_pos.mpr h1t
    have hsum2 : 0<t2-t := sub_pos.mpr ht2
    have hd : 0<2*q*(t-t1)*(t2-t)*(t2-t1) :=
      mul_pos (mul_pos (mul_pos (by linarith) hsum1) hsum2) (sub_pos.mpr h12)
    have hid :
        (t2-t)*(score q w t1-score q w t)+(t-t1)*(score q w t2-score q w t) =
          2*q*(t-t1)*(t2-t)*(t2-t1) := by rw [htp,htS1,htS2]; ring
    by_contra hn
    have hmn := le_of_not_gt hn
    have hz : (t2-t)*(score q w t1-score q w t)+(t-t1)*(score q w t2-score q w t)≤0 :=
      add_nonpos (mul_nonpos_of_nonneg_of_nonpos hsum2.le (sub_nonpos.mpr ((le_max_left _ _).trans hmn)))
        (mul_nonpos_of_nonneg_of_nonpos hsum1.le (sub_nonpos.mpr ((le_max_right _ _).trans hmn)))
    exact (not_le_of_gt hd) (hid ▸ hz)
  have strictOff (hne1 : t≠t1) (hne2 : t≠t2) : score q w t < max (score q w t1) (score q w t2) := by
    rcases lt_or_gt_of_ne hne1 with hl|hg
    · exact (score_lower_half q w t1 t2 t hq h1 h12 h2 ht0 hwt1 hwt2 hl).trans_le (le_max_left _ _)
    · rcases lt_or_gt_of_ne hne2 with hl|hg'
      · exact strictInterior hg hl
      · exact (score_upper_half q w t1 t2 t hq h1 h12 h2 ht1 hwt1 hwt2 hg').trans_le (le_max_right _ _)
  by_cases hT1 : t=t1
  · subst t
    simp only [true_and, (ne_of_lt h12),false_and,or_false]
    refine ⟨le_max_left _ _,?_⟩
    constructor
    · intro he
      exact hs21.mp (he ▸ le_max_right _ _)
    · intro he
      exact (max_eq_left (hs21.mpr he)).symm
  · by_cases hT2 : t=t2
    · subst t
      simp only [hT1,false_and,true_and,false_or]
      refine ⟨le_max_right _ _,?_⟩
      constructor
      · intro he
        exact hs12.mp (he ▸ le_max_left _ _)
      · intro he
        exact (max_eq_right (hs12.mpr he)).symm
    · have hlt := strictOff hT1 hT2
      simp only [hT1,hT2,false_and,or_self,iff_false]
      exact ⟨hlt.le,hlt.ne⟩


end Scalar

/-- The two strictly interior clipping thresholds of the smaller-Schmidt
filter curve for a physical target with strictly smaller matched weight. -/
structure FilterCurve where
  q : ℝ
  w : ℝ
  t₁ : ℝ
  t₂ : ℝ
  q_pos : 0 < q
  q_le_half : 2*q ≤ 1
  t₁_pos : 0 < t₁
  t_lt : t₁ < t₂
  t₂_lt_one : t₂ < 1
  cap₁ : w = q*(2*t₁-t₁^2)
  cap₂ : w = q*t₂^2

noncomputable def largestFilter (β : FilterCurve) : ℝ :=
  if 2*β.w < β.q then β.t₁ else β.t₂

/-- The literal clipped score has exactly the specified optimal filter(s),
and the selected filter is the largest among them. At the transition both
values attain the same score, but only the larger is the readout. -/
theorem largest_optimal_filter (β : FilterCurve) :
    let chosen := largestFilter β
    0<chosen ∧ chosen<1 ∧
    ∀ t : ℝ, 0≤t → t≤1 →
      score β.q β.w t ≤ score β.q β.w chosen ∧
      (score β.q β.w t = score β.q β.w chosen ↔
        (t=β.t₁ ∧ 2*β.w≤β.q) ∨ (t=β.t₂ ∧ β.q≤2*β.w)) ∧
      (score β.q β.w t = score β.q β.w chosen → t≤chosen) := by
  let c := largestFilter β
  change 0<c ∧ c<1 ∧ _
  have hpos : 0<c := by
    unfold c largestFilter
    split
    · exact β.t₁_pos
    · exact β.t₁_pos.trans β.t_lt
  have hlt : c<1 := by
    unfold c largestFilter
    split
    · exact β.t_lt.trans β.t₂_lt_one
    · exact β.t₂_lt_one
  have hmax : score β.q β.w c = max (score β.q β.w β.t₁) (score β.q β.w β.t₂) := by
    apply (score_maximizer_iff β.q β.w β.t₁ β.t₂ c β.q_pos β.t₁_pos β.t_lt
      β.t₂_lt_one hpos.le hlt.le β.cap₁ β.cap₂).2.mpr
    by_cases h : 2*β.w<β.q
    · exact Or.inl ⟨ite_eq_left h,h.le⟩
    · exact Or.inr ⟨ite_eq_right h,le_of_not_gt h⟩
  refine ⟨hpos,hlt,?_⟩
  intro t ht₀ ht₁
  have h := score_maximizer_iff β.q β.w β.t₁ β.t₂ t β.q_pos β.t₁_pos β.t_lt
      β.t₂_lt_one ht₀ ht₁ β.cap₁ β.cap₂
  rw [←hmax] at h
  refine ⟨h.1,h.2,?_⟩
  intro hs
  rcases h.2.mp hs with ⟨rfl,_⟩ | ⟨rfl,hc⟩
  · unfold largestFilter
    split
    · exact le_rfl
    · exact β.t_lt.le
  · unfold largestFilter
    rw [ite_eq_right (not_lt_of_ge hc)]

#print axioms largest_optimal_filter
end D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter

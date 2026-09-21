/- GID: D5/S3/Geometry/Hyperideal/FourCycleCurvature
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FourCycleCurvature
   mirror-E: none(waiver:unbounded-finite-incidence-real-estimate)
   anchors: []
   utility: none
   digest: Uniform inward curvature margins on an explicit four-cycle incidence box. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
One variable per global edge; every local occurrence is counted separately.
The only hypotheses are finite incidence, the four-cycle colouring, and the
actual fibre cardinalities. All angles use the exact six-variable formula.
No curvature sign, small-enough parameter, solution or geometric realization
is assumed. The floor is explicitly constructed from the occurrence count.

The result is an analytic statement about the tetrahedral incidence system.
It does not certify vertex links, identify the formula with a geometric
angle, or supply a formal Brouwer/co-volume existence theorem. The imported
analytic source has the same geometric boundary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.FourCycleCurvature
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-- Each local coordinate reads one shared global edge label. -/
structure Incidence (T E : Type*) where
  edge : T → Fin 6 → E
  low : E → Bool

/-- Local order (12,13,14,34,24,23); high slots are the opposite pair 0,3. -/
def lowSlot (i : Fin 6) : Bool := decide (i ≠ 0 ∧ i ≠ 3)

/-- Genuine vertex relabelings, chosen so a low target has low slots 0,1,3,4. -/
def frame (i : Fin 6) : Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5], ![1,2,0,4,5,3], ![2,1,0,5,4,3],
    ![3,1,5,0,4,2], ![4,5,0,1,2,3], ![5,4,0,2,1,3]] i

variable {T E : Type*} [Fintype T] [DecidableEq E]

def source (s : Incidence T E) (o : T × Fin 6) : E := s.edge o.1 o.2

def coordinate (s : Incidence T E) (o : T × Fin 6) (j : Fin 6) : E :=
  s.edge o.1 (frame o.2 j)

def star (s : Incidence T E) (e : E) : Finset (T × Fin 6) :=
  Finset.univ.filter (fun o => source s o = e)

def degree (s : Incidence T E) (e : E) : ℕ := (star s e).card

/-- Cardinalities are calculated from s.edge, not separately supplied numbers. -/
def FourCycle (s : Incidence T E) : Prop :=
  (∀ t i, s.low (s.edge t i) = lowSlot i) ∧
  (∀ e, s.low e = true → degree s e = 8) ∧
  (∀ e, s.low e = false → 12 ≤ degree s e)

def localCosine (s : Incidence T E) (x : E → ℝ) (o : T × Fin 6) : ℝ :=
  cosine (x (coordinate s o 0)) (x (coordinate s o 1))
    (x (coordinate s o 2)) (x (coordinate s o 3))
    (x (coordinate s o 4)) (x (coordinate s o 5))

def angle (s : Incidence T E) (x : E → ℝ) (o : T × Fin 6) : ℝ :=
  Real.arccos (localCosine s x o)

def curvature (s : Incidence T E) (x : E → ℝ) (e : E) : ℝ :=
  2*Real.pi - ∑ o ∈ star s e, angle s x o

/-- This angle uses the total number of occurrences, even when there are none. -/
def smallAngle (T : Type*) [Fintype T] : ℝ :=
  Real.pi / ((Fintype.card (T × Fin 6) : ℝ) + 2)

def floorIncrement (T : Type*) [Fintype T] : ℝ :=
  min (1/8) ((1-Real.cos (smallAngle T))/(2+Real.cos (smallAngle T)))

def lower (s : Incidence T E) (e : E) : ℝ :=
  if s.low e = true then 5/4 else 1 + floorIncrement T

def upper (s : Incidence T E) (e : E) : ℝ :=
  if s.low e = true then 2 else 8/5

def Box (s : Incidence T E) (x : E → ℝ) : Prop :=
  ∀ e, x e ∈ Set.Icc (lower s e) (upper s e)

/-- Independent of the size of the incidence system. -/
def margin : ℝ :=
  min Real.pi (min (2*Real.pi-8*Real.arccos (293/400))
    (min (8*Real.arccos (1577/2236)-2*Real.pi)
      (12*Real.arccos (37/43)-2*Real.pi)))

/-- A nonempty explicitly constructed box, genuine cosine values and
universal signed curvature margins on all of its coordinate faces. -/
theorem fourcycle_curvature_box (s : Incidence T E) (hs : FourCycle s) :
    0 < floorIncrement T ∧ floorIncrement T ≤ 1/8 ∧ 0 < margin ∧
    Box s (lower s) ∧
    (∀ x : E → ℝ, Box s x →
      (∀ o : T × Fin 6, -1 < localCosine s x o ∧ localCosine s x o < 1) ∧
      (∀ e : E,
        (x e = lower s e → margin ≤ curvature s x e) ∧
        (x e = upper s e → curvature s x e ≤ -margin))) := by
  classical
  rcases hs with ⟨hcolour, hlowDegree, hhighDegree⟩
  have hrad : ∀ x y z : ℝ, 1 ≤ x → 1 ≤ y → 1 ≤ z → 0 < rad x y z := by
    intro x y z hx hy hz
    have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
    have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y-1)]
    have hz2 : 1 ≤ z^2 := by nlinarith [sq_nonneg (z-1)]
    have hp : 0 ≤ 2*x*y*z := by positivity
    unfold rad
    linarith
  have cmp := cosine_mixed_comparison
  have hI1 : (1:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hI2 : (2:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hI54 : (5/4:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hI85 : (8/5:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hbase : ∀ x y z o v w : ℝ,
      x ∈ Set.Icc 1 2 → y ∈ Set.Icc 1 2 → z ∈ Set.Icc 1 2 →
      o ∈ Set.Icc 1 2 → v ∈ Set.Icc 1 2 → w ∈ Set.Icc 1 2 →
      2*(2-x)/(x+1) ≤ cosine x y z o v w ∧
      cosine x y z o v w ≤ (9-x)/(7+x) := by
    intro x y z o v w hx hy hz ho hv hw
    have hlo : cosine x 1 1 2 1 1 = 2*(2-x)/(x+1) := by
      have hs := Real.sq_sqrt (hrad x 1 1 hx.1 (by norm_num) (by norm_num)).le
      unfold cosine
      rw [div_div, ← pow_two, hs]
      have hrw : rad x 1 1 = (x+1)^2 := by unfold rad; ring
      rw [hrw]
      unfold numerator
      field_simp [show x+1 ≠ 0 by linarith [hx.1]]
      ring
    have hhi : cosine x 2 2 1 2 2 = (9-x)/(7+x) := by
      have hs := Real.sq_sqrt (hrad x 2 2 hx.1 (by norm_num) (by norm_num)).le
      unfold cosine
      rw [div_div, ← pow_two, hs]
      have hrw : rad x 2 2 = (x+1)*(x+7) := by unfold rad; ring
      rw [hrw]
      unfold numerator
      field_simp [show x+1 ≠ 0 by linarith [hx.1], show x+7 ≠ 0 by linarith [hx.1],
        show 7+x ≠ 0 by linarith [hx.1]]
      ring
    constructor
    · rw [← hlo]
      exact cmp x 1 1 2 1 1 y z o v w hx hI1 hI1 hI2 hI1 hI1 hy hz ho hv hw
        hy.1 hz.1 ho.2 hv.1 hw.1
    · rw [← hhi]
      exact cmp x y z o v w 2 2 1 2 2 hx hy hz ho hv hw hI2 hI2 hI1 hI2 hI2
        hy.2 hz.2 ho.1 hv.2 hw.2
  have hlowFace : ∀ y z o v w : ℝ,
      y ∈ Set.Icc (5/4) 2 → z ∈ Set.Icc 1 (8/5) →
      o ∈ Set.Icc (5/4) 2 → v ∈ Set.Icc (5/4) 2 →
      w ∈ Set.Icc 1 (8/5) →
      (293:ℝ)/400 ≤ cosine (5/4) y z o v w := by
    intro y z o v w hy hz ho hv hw
    have hy' : y ∈ Set.Icc (1:ℝ) 2 := ⟨by linarith [hy.1], hy.2⟩
    have hz' : z ∈ Set.Icc (1:ℝ) 2 := ⟨hz.1, by linarith [hz.2]⟩
    have ho' : o ∈ Set.Icc (1:ℝ) 2 := ⟨by linarith [ho.1], ho.2⟩
    have hv' : v ∈ Set.Icc (1:ℝ) 2 := ⟨by linarith [hv.1], hv.2⟩
    have hw' : w ∈ Set.Icc (1:ℝ) 2 := ⟨hw.1, by linarith [hw.2]⟩
    have h := cmp (5/4) (5/4) 1 2 (5/4) 1 y z o v w
      hI54 hI54 hI1 hI2 hI54 hI1 hy' hz' ho' hv' hw' hy.1 hz.1 ho.2 hv.1 hw.1
    have he : cosine (5/4) (5/4) 1 2 (5/4) 1 = (293:ℝ)/400 := by
      have hA : rad (5/4) (5/4) 1 = (25:ℝ)/4 := by norm_num [rad]
      have hB : rad (5/4) 1 (5/4) = (25:ℝ)/4 := by norm_num [rad]
      have hP : numerator (5/4) (5/4) 1 2 (5/4) 1 = (293:ℝ)/64 := by
        norm_num [numerator]
      rw [cosine, hA, hB, hP, div_div, ← pow_two,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 25/4)]
      norm_num
    simpa only [he] using h
  have huppFace : ∀ y z o v w : ℝ,
      y ∈ Set.Icc (5/4) 2 → z ∈ Set.Icc 1 (8/5) →
      o ∈ Set.Icc (5/4) 2 → v ∈ Set.Icc (5/4) 2 →
      w ∈ Set.Icc 1 (8/5) →
      cosine 2 y z o v w ≤ (1577:ℝ)/2236 := by
    intro y z o v w hy hz ho hv hw
    have hy' : y ∈ Set.Icc (1:ℝ) 2 := ⟨by linarith [hy.1], hy.2⟩
    have hz' : z ∈ Set.Icc (1:ℝ) 2 := ⟨hz.1, by linarith [hz.2]⟩
    have ho' : o ∈ Set.Icc (1:ℝ) 2 := ⟨by linarith [ho.1], ho.2⟩
    have hv' : v ∈ Set.Icc (1:ℝ) 2 := ⟨by linarith [hv.1], hv.2⟩
    have hw' : w ∈ Set.Icc (1:ℝ) 2 := ⟨hw.1, by linarith [hw.2]⟩
    have h := cmp 2 y z o v w 2 (8/5) (5/4) 2 (8/5)
      hI2 hy' hz' ho' hv' hw' hI2 hI85 hI54 hI2 hI85 hy.2 hz.2 ho.1 hv.2 hw.2
    have he : cosine 2 2 (8/5) (5/4) 2 (8/5) = (1577:ℝ)/2236 := by
      have hA : rad 2 2 (8/5) = (559:ℝ)/25 := by norm_num [rad]
      have hB : rad 2 (8/5) 2 = (559:ℝ)/25 := by norm_num [rad]
      have hP : numerator 2 2 (8/5) (5/4) 2 (8/5) = (1577:ℝ)/100 := by
        norm_num [numerator]
      rw [cosine, hA, hB, hP, div_div, ← pow_two,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 559/25)]
      norm_num
    simpa only [he] using h
  have hhighFace : ∀ y z o v w : ℝ,
      y ∈ Set.Icc 1 2 → z ∈ Set.Icc 1 2 → o ∈ Set.Icc 1 2 →
      v ∈ Set.Icc 1 2 → w ∈ Set.Icc 1 2 →
      cosine (8/5) y z o v w ≤ (37:ℝ)/43 := by
    intro y z o v w hy hz ho hv hw
    have h := (hbase (8/5) y z o v w hI85 hy hz ho hv hw).2
    norm_num at h ⊢
    exact h
  have hpi := Real.pi_pos
  let n : ℝ := (Fintype.card (T × Fin 6) : ℝ)
  let t : ℝ := smallAngle T
  let c : ℝ := Real.cos t
  let d : ℝ := floorIncrement T
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hden : 0 < n+2 := by linarith
  have ht : 0 < t := by dsimp [t, smallAngle]; positivity
  have hthalf : t ≤ Real.pi/2 := by
    change Real.pi/(n+2) ≤ Real.pi/2
    exact div_le_div_of_nonneg_left hpi.le (by norm_num) (by linarith)
  have htpi : t ≤ Real.pi := by linarith
  have hct : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hthalf⟩
  have hc1 : c < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) htpi ht
    simpa only [Real.cos_zero] using h
  have hdpos : 0 < d := by
    change 0 < min (1/8:ℝ) ((1-c)/(2+c))
    exact lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have hd8 : d ≤ 1/8 := min_le_left _ _
  have hdc : d ≤ (1-c)/(2+c) := min_le_right _ _
  have hdc' : d*(2+c) ≤ 1-c := (le_div_iff₀ (by linarith)).mp hdc
  have hthreshold : c < 2*(2-(1+d))/((1+d)+1) := by
    apply (lt_div_iff₀ (by linarith)).2
    nlinarith
  have hnt : (n+2)*t = Real.pi := by
    change (n+2)*(Real.pi/(n+2)) = Real.pi
    field_simp [hden.ne']
  have htnt : n*t < Real.pi := by nlinarith
  -- Strict angular gaps from exact comparisons with sqrt(2)/2 and sqrt(3)/2.
  have hqlo : Real.cos (Real.pi/4) < (293:ℝ)/400 := by
    rw [Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  have hqup : (1577:ℝ)/2236 < Real.cos (Real.pi/4) := by
    rw [Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  have hqhi : (37:ℝ)/43 < Real.cos (Real.pi/6) := by
    rw [Real.cos_pi_div_six]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have halo : Real.arccos ((293:ℝ)/400) < Real.pi/4 := by
    have h := Real.arccos_lt_arccos (Real.neg_one_le_cos _) hqlo (by norm_num)
    rw [Real.arccos_cos (by positivity) (by linarith)] at h
    exact h
  have haup : Real.pi/4 < Real.arccos ((1577:ℝ)/2236) := by
    have h := Real.arccos_lt_arccos (by norm_num) hqup (Real.cos_le_one _)
    rw [Real.arccos_cos (by positivity) (by linarith)] at h
    exact h
  have hahi : Real.pi/6 < Real.arccos ((37:ℝ)/43) := by
    have h := Real.arccos_lt_arccos (by norm_num) hqhi (Real.cos_le_one _)
    rw [Real.arccos_cos (by positivity) (by linarith)] at h
    exact h
  have hmpos : 0 < margin := by
    unfold margin
    exact lt_min hpi (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hmpi : margin ≤ Real.pi := min_le_left _ _
  have hmlo : margin ≤ 2*Real.pi-8*Real.arccos ((293:ℝ)/400) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmup : margin ≤ 8*Real.arccos ((1577:ℝ)/2236)-2*Real.pi :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmhi : margin ≤ 12*Real.arccos ((37:ℝ)/43)-2*Real.pi :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hframe : ∀ i : Fin 6, frame i 0 = i := by decide
  have hpattern : ∀ i : Fin 6, lowSlot i = true →
      lowSlot (frame i 1) = true ∧ lowSlot (frame i 2) = false ∧
      lowSlot (frame i 3) = true ∧ lowSlot (frame i 4) = true ∧
      lowSlot (frame i 5) = false := by decide
  have hlowSlots : ∀ o : T × Fin 6, s.low (source s o) = true →
      s.low (coordinate s o 1) = true ∧ s.low (coordinate s o 2) = false ∧
      s.low (coordinate s o 3) = true ∧ s.low (coordinate s o 4) = true ∧
      s.low (coordinate s o 5) = false := by
    rintro ⟨tet,i⟩ hi
    change s.low (s.edge tet i) = true at hi
    rw [hcolour] at hi
    simp only [coordinate, hcolour]
    exact hpattern i hi
  have hlole : ∀ e, lower s e ≤ upper s e := by
    intro e
    by_cases he : s.low e = true
    · norm_num [lower, upper, he]
    · simp only [lower, upper, he]
      change 1+d ≤ 8/5
      linarith
  have hlopos : ∀ e, 1 < lower s e := by
    intro e
    by_cases he : s.low e = true
    · norm_num [lower, he]
    · simp only [lower, he]
      change 1 < 1+d
      linarith
  have hup2 : ∀ e, upper s e ≤ 2 := by
    intro e
    by_cases he : s.low e = true <;> norm_num [upper, he]
  have hncard : ∀ e, (degree s e : ℝ) ≤ n := by
    intro e
    have h : (star s e).card ≤ (Finset.univ : Finset (T × Fin 6)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa only [degree, Finset.card_univ, n] using
      (show ((star s e).card : ℝ) ≤ ((Finset.univ : Finset (T × Fin 6)).card : ℝ) by
        exact_mod_cast h)
  refine ⟨hdpos, hd8, hmpos, (fun e => ⟨le_rfl, hlole e⟩), ?_⟩
  intro x hx
  have hcube : ∀ e, x e ∈ Set.Icc (1:ℝ) 2 := fun e =>
    ⟨(hlopos e).le.trans (hx e).1, (hx e).2.trans (hup2 e)⟩
  have hgt : ∀ e, 1 < x e := fun e => (hlopos e).trans_le (hx e).1
  have hbaseO : ∀ o : T × Fin 6,
      2*(2-x (source s o))/(x (source s o)+1) ≤ localCosine s x o ∧
      localCosine s x o ≤ (9-x (source s o))/(7+x (source s o)) := by
    intro o
    have h := hbase (x (coordinate s o 0)) (x (coordinate s o 1))
      (x (coordinate s o 2)) (x (coordinate s o 3))
      (x (coordinate s o 4)) (x (coordinate s o 5))
      (hcube _) (hcube _) (hcube _) (hcube _) (hcube _) (hcube _)
    simpa only [localCosine, coordinate, hframe, source] using h
  constructor
  · intro o
    have hb := hbaseO o
    have hxe := hgt (source s o)
    have hx2 := (hcube (source s o)).2
    have hnonneg : 0 ≤ 2*(2-x (source s o))/(x (source s o)+1) := by
      apply div_nonneg <;> nlinarith
    have hlt : (9-x (source s o))/(7+x (source s o)) < 1 := by
      apply (div_lt_iff₀ (by linarith)).2
      linarith
    exact ⟨lt_of_lt_of_le (by linarith : (-1:ℝ) < 2*(2-x (source s o))/(x (source s o)+1)) hb.1,
      hb.2.trans_lt hlt⟩
  · intro e
    have hsource : ∀ o ∈ star s e, source s o = e := fun o ho => (Finset.mem_filter.mp ho).2
    have hcoord0 : ∀ o ∈ star s e, coordinate s o 0 = e := by
      intro o ho
      simpa only [coordinate, hframe, source] using hsource o ho
    by_cases he : s.low e = true
    · have hdeg : degree s e = 8 := hlowDegree e he
      have hface : ∀ o ∈ star s e,
          x (coordinate s o 1) ∈ Set.Icc (5/4:ℝ) 2 ∧
          x (coordinate s o 2) ∈ Set.Icc (1:ℝ) (8/5) ∧
          x (coordinate s o 3) ∈ Set.Icc (5/4:ℝ) 2 ∧
          x (coordinate s o 4) ∈ Set.Icc (5/4:ℝ) 2 ∧
          x (coordinate s o 5) ∈ Set.Icc (1:ℝ) (8/5) := by
        intro o ho
        obtain ⟨h1,h2,h3,h4,h5⟩ := hlowSlots o (by rw [hsource o ho]; exact he)
        have hx1 := hx (coordinate s o 1)
        have hx2 := hx (coordinate s o 2)
        have hx3 := hx (coordinate s o 3)
        have hx4 := hx (coordinate s o 4)
        have hx5 := hx (coordinate s o 5)
        simp only [lower, upper, h1, h2, h3, h4, h5, Bool.false_eq_true,
          if_true, if_false] at hx1 hx2 hx3 hx4 hx5
        exact ⟨hx1, ⟨(hcube _).1,hx2.2⟩, hx3, hx4, ⟨(hcube _).1,hx5.2⟩⟩
      constructor
      · intro hxe
        have hxv : x e = 5/4 := by simpa only [lower, he, if_true] using hxe
        have ha : ∀ o ∈ star s e, angle s x o ≤ Real.arccos ((293:ℝ)/400) := by
          intro o ho
          obtain ⟨h1,h2,h3,h4,h5⟩ := hface o ho
          have h := hlowFace _ _ _ _ _ h1 h2 h3 h4 h5
          have hv : (293:ℝ)/400 ≤ localCosine s x o := by
            simpa only [localCosine, hcoord0 o ho, hxv] using h
          exact Real.arccos_le_arccos hv
        have hsum : (∑ o ∈ star s e, angle s x o) ≤ 8*Real.arccos ((293:ℝ)/400) := by
          calc
            _ ≤ ∑ _o ∈ star s e, Real.arccos ((293:ℝ)/400) := Finset.sum_le_sum ha
            _ = _ := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              change (degree s e : ℝ)*_ = _
              rw [hdeg]
              norm_num
        unfold curvature
        linarith
      · intro hxe
        have hxv : x e = 2 := by simpa only [upper, he, if_true] using hxe
        have ha : ∀ o ∈ star s e, Real.arccos ((1577:ℝ)/2236) ≤ angle s x o := by
          intro o ho
          obtain ⟨h1,h2,h3,h4,h5⟩ := hface o ho
          have h := huppFace _ _ _ _ _ h1 h2 h3 h4 h5
          have hv : localCosine s x o ≤ (1577:ℝ)/2236 := by
            simpa only [localCosine, hcoord0 o ho, hxv] using h
          exact Real.arccos_le_arccos hv
        have hsum : 8*Real.arccos ((1577:ℝ)/2236) ≤ ∑ o ∈ star s e, angle s x o := by
          calc
            _ = ∑ _o ∈ star s e, Real.arccos ((1577:ℝ)/2236) := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              change _ = (degree s e : ℝ)*_
              rw [hdeg]
              norm_num
            _ ≤ _ := Finset.sum_le_sum ha
        unfold curvature
        linarith
    · have hef : s.low e = false := Bool.eq_false_iff.mpr he
      constructor
      · intro hxe
        have hxv : x e = 1+d := by
          simpa only [lower, hef, Bool.false_eq_true, if_false, d] using hxe
        have ha : ∀ o ∈ star s e, angle s x o ≤ t := by
          intro o ho
          have hb := (hbaseO o).1
          rw [hsource o ho, hxv] at hb
          have hc : c < localCosine s x o := hthreshold.trans_le hb
          have hac : Real.arccos (localCosine s x o) ≤ Real.arccos c :=
            Real.arccos_le_arccos hc.le
          have hact : Real.arccos c = t := Real.arccos_cos ht.le htpi
          exact hac.trans_eq hact
        have hsum : (∑ o ∈ star s e, angle s x o) ≤ (degree s e : ℝ)*t := by
          calc
            _ ≤ ∑ _o ∈ star s e, t := Finset.sum_le_sum ha
            _ = _ := by simp [degree, nsmul_eq_mul]
        have hdnt : (degree s e : ℝ)*t ≤ n*t :=
          mul_le_mul_of_nonneg_right (hncard e) ht.le
        unfold curvature
        linarith
      · intro hxe
        have hxv : x e = 8/5 := by
          simpa only [upper, hef, Bool.false_eq_true, if_false] using hxe
        have ha : ∀ o ∈ star s e, Real.arccos ((37:ℝ)/43) ≤ angle s x o := by
          intro o ho
          have h := hhighFace (x (coordinate s o 1)) (x (coordinate s o 2))
            (x (coordinate s o 3)) (x (coordinate s o 4)) (x (coordinate s o 5))
            (hcube _) (hcube _) (hcube _) (hcube _) (hcube _)
          have hv : localCosine s x o ≤ (37:ℝ)/43 := by
            simpa only [localCosine, hcoord0 o ho, hxv] using h
          exact Real.arccos_le_arccos hv
        have hdeg : (12:ℝ) ≤ degree s e := by exact_mod_cast (hhighDegree e hef)
        have hsum : 12*Real.arccos ((37:ℝ)/43) ≤ ∑ o ∈ star s e, angle s x o := by
          calc
            _ ≤ (degree s e : ℝ)*Real.arccos ((37:ℝ)/43) :=
              mul_le_mul_of_nonneg_right hdeg (Real.arccos_nonneg _)
            _ = ∑ _o ∈ star s e, Real.arccos ((37:ℝ)/43) := by simp [degree, nsmul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum ha
        unfold curvature
        linarith

#print axioms fourcycle_curvature_box
end D5.S3.Geometry.Hyperideal.FourCycleCurvature

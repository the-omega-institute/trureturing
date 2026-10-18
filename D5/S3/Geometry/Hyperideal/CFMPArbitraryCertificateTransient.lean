/-
ENTIRE CANDIDATE UNCOMPILED. Transient source application; zero canonical retention.
Original D5 source revision: 94af6e606b01320de8b9f36a9099de3268b57626.
Pinned mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.
Only the raw formula/incidence conclusion of original source.md Section 3.
The imported private cube/clamp proofs are used directly, never reproduced.
-/
import D5.S3.Geometry.Hyperideal.FourCycleExistence
import D5.S3.Geometry.Hyperideal.FourCycleCurvature
import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import D5.S3.Geometry.FixedPoint.Brouwer
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace TransientArbitraryAdjacency

open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

open private Cube cube_fixed_point clamp_fixed_zero from
  D5.S3.Geometry.Hyperideal.FourCycleExistence

variable {T E : Type*} [Fintype T] [Fintype E] [DecidableEq E]

/-- Exact actual-adjacency upper comparison, including repeated labels. -/
def u (s : Incidence T E) (b : E → ℝ) (o : T × Fin 6) : ℝ :=
  cosine (b (coordinate s o 0)) (b (coordinate s o 1))
    (b (coordinate s o 2)) 1 (b (coordinate s o 4)) (b (coordinate s o 5))

/-- The original occurrence fibre, with no deduplication of global labels. -/
def S (s : Incidence T E) (b : E → ℝ) (e : E) : ℝ :=
  ∑ o ∈ star s e, Real.arccos (u s b o)

private theorem rad_positive (x y z : ℝ) (hx : 1 ≤ x)
    (hy : 1 ≤ y) (hz : 1 ≤ z) : 0 < rad x y z := by
  have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
  have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y-1)]
  have hz2 : 1 ≤ z^2 := by nlinarith [sq_nonneg (z-1)]
  have hp : 0 ≤ 2*x*y*z := by positivity
  unfold rad
  linarith

/-- Endpoint algebra followed by direct reuse of the original comparison. -/
private theorem formula_bounds (x y z o v w : ℝ)
    (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2)
    (hz : z ∈ Set.Icc 1 2) (ho : o ∈ Set.Icc 1 2)
    (hv : v ∈ Set.Icc 1 2) (hw : w ∈ Set.Icc 1 2) :
    2*(2-x)/(x+1) ≤ cosine x y z o v w ∧
    cosine x y z o v w ≤ (9-x)/(7+x) := by
  have h1 : (1:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have h2 : (2:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hlo : cosine x 1 1 2 1 1 = 2*(2-x)/(x+1) := by
    have hs := Real.sq_sqrt (rad_positive x 1 1 hx.1 (by norm_num) (by norm_num)).le
    unfold cosine
    rw [div_div, ← pow_two, hs]
    have hr : rad x 1 1 = (x+1)^2 := by unfold rad; ring
    rw [hr]
    unfold numerator
    field_simp [show x+1 ≠ 0 by linarith [hx.1]]
    ring
  have hhi : cosine x 2 2 1 2 2 = (9-x)/(7+x) := by
    have hs := Real.sq_sqrt (rad_positive x 2 2 hx.1 (by norm_num) (by norm_num)).le
    unfold cosine
    rw [div_div, ← pow_two, hs]
    have hr : rad x 2 2 = (x+1)*(x+7) := by unfold rad; ring
    rw [hr]
    unfold numerator
    field_simp [show x+1 ≠ 0 by linarith [hx.1],
      show x+7 ≠ 0 by linarith [hx.1], show 7+x ≠ 0 by linarith [hx.1]]
    ring
  constructor
  · rw [← hlo]
    exact cosine_mixed_comparison x 1 1 2 1 1 y z o v w
      hx h1 h1 h2 h1 h1 hy hz ho hv hw hy.1 hz.1 ho.2 hv.1 hw.1
  · rw [← hhi]
    exact cosine_mixed_comparison x y z o v w 2 2 1 2 2
      hx hy hz ho hv hw h2 h2 h1 h2 h2 hy.2 hz.2 ho.1 hv.2 hw.2

private theorem formula_range (x y z o v w : ℝ)
    (hx : 1 < x ∧ x ≤ 2) (hy : y ∈ Set.Icc 1 2)
    (hz : z ∈ Set.Icc 1 2) (ho : o ∈ Set.Icc 1 2)
    (hv : v ∈ Set.Icc 1 2) (hw : w ∈ Set.Icc 1 2) :
    0 ≤ cosine x y z o v w ∧ cosine x y z o v w < 1 := by
  have hb := formula_bounds x y z o v w ⟨hx.1.le, hx.2⟩ hy hz ho hv hw
  have hlo : 0 ≤ 2*(2-x)/(x+1) := by
    apply div_nonneg <;> linarith [hx.1, hx.2]
  have hhi : (9-x)/(7+x) < 1 := by
    apply (div_lt_iff₀ (by linarith [hx.1])).2
    linarith [hx.1]
  exact ⟨hlo.trans hb.1, hb.2.trans_lt hhi⟩

/-- This is a derived range fact, not an extra certificate hypothesis. -/
theorem u_range (s : Incidence T E) (b : E → ℝ)
    (hb : ∀ e, 1 < b e ∧ b e ≤ 2) (o : T × Fin 6) :
    0 ≤ u s b o ∧ u s b o < 1 := by
  have hbc : ∀ e, b e ∈ Set.Icc (1:ℝ) 2 := fun e => ⟨(hb e).1.le, (hb e).2⟩
  exact formula_range _ _ _ _ _ _ (hb _) (hbc _) (hbc _)
    (by constructor <;> norm_num) (hbc _) (hbc _)

/-- Continuity chooses a single strict floor even when the finite types are empty. -/
private theorem common_floor (b : E → ℝ) (hb : ∀ e, 1 < b e) :
    ∃ a : ℝ, 1 < a ∧ a < 2 ∧ (∀ e, a < b e) ∧
      (Fintype.card (T × Fin 6) : ℝ) * Real.arccos (2*(2-a)/(a+1)) < 2*Real.pi := by
  let N : ℝ := Fintype.card (T × Fin 6)
  let g : ℝ → ℝ := fun a => N * Real.arccos (2*(2-a)/(a+1))
  have hc : ContinuousAt g 1 := by
    dsimp [g]
    apply continuousAt_const.mul
    apply Real.continuous_arccos.continuousAt.comp
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hg : g 1 = 0 := by norm_num [g]
  have hgap : g 1 < 2*Real.pi := by rw [hg]; positivity
  have hsmall : ∀ᶠ a in 𝓝 (1:ℝ), g a < 2*Real.pi :=
    hc.eventually_lt continuousAt_const hgap
  have hbelow : ∀ᶠ a in 𝓝 (1:ℝ), ∀ e, a < b e :=
    Filter.eventually_all.mpr (fun e => eventually_lt_nhds (hb e))
  have htwo : ∀ᶠ a in 𝓝 (1:ℝ), a < 2 := eventually_lt_nhds (by norm_num)
  obtain ⟨l, r, h1, hsub⟩ := ((hsmall.and hbelow).and htwo).exists_Ioo_subset
  let a : ℝ := (1+r)/2
  have ha : 1 < a := by dsimp [a]; linarith [h1.2]
  have har : a < r := by dsimp [a]; linarith [h1.2]
  have hh := hsub (show a ∈ Set.Ioo l r from ⟨h1.1.trans ha, har⟩)
  exact ⟨a, ha, hh.2, hh.1.2, hh.1.1⟩

/-- Exact arbitrary-adjacency raw zero-curvature conclusion.
No colouring, degree bound, assumed face sign, or geometric premise occurs. -/
theorem arbitrary_zero_curvature (s : Incidence T E) (b : E → ℝ)
    (hb : ∀ e, 1 < b e ∧ b e ≤ 2)
    (hS : ∀ e, 2*Real.pi < S s b e) :
    ∃ a : ℝ, ∃ x : E → ℝ,
      1 < a ∧ (∀ e, a < b e) ∧
      (∀ e, a < x e ∧ x e < b e) ∧
      (∀ o : T × Fin 6, -1 < localCosine s x o ∧ localCosine s x o < 1) ∧
      (∀ e, curvature s x e = 0) := by
  classical
  obtain ⟨a, ha, ha2, hab, hsmall⟩ := common_floor (T := T) b (fun e => (hb e).1)
  let theta : ℝ := Real.arccos (2*(2-a)/(a+1))
  have htheta : 0 ≤ theta := Real.arccos_nonneg _
  have hframe : ∀ i : Fin 6, frame i 0 = i := by decide
  have hcoord : ∀ o : T × Fin 6, coordinate s o 0 = source s o := by
    intro o
    simp only [coordinate, source, hframe]
  have hstar : ∀ e, ∀ o ∈ star s e, coordinate s o 0 = e := by
    intro e o ho
    exact (hcoord o).trans (Finset.mem_filter.mp ho).2
  have hbc : ∀ e, b e ∈ Set.Icc (1:ℝ) 2 := fun e => ⟨(hb e).1.le, (hb e).2⟩
  -- These signs are proved here from the certificate, not supplied as premises.
  have hfaces : ∀ x : E → ℝ, (∀ e, x e ∈ Set.Icc a (b e)) →
      (∀ o : T × Fin 6, -1 < localCosine s x o ∧ localCosine s x o < 1) ∧
      (∀ e, (x e = a → 0 < curvature s x e) ∧
        (x e = b e → curvature s x e < 0)) := by
    intro x hx
    have hxc : ∀ e, x e ∈ Set.Icc (1:ℝ) 2 := fun e =>
      ⟨ha.le.trans (hx e).1, (hx e).2.trans (hb e).2⟩
    have hxgt : ∀ e, 1 < x e := fun e => ha.trans_le (hx e).1
    constructor
    · intro o
      have hr := formula_range (x (coordinate s o 0)) _ _ _ _ _
        ⟨hxgt (coordinate s o 0), (hxc (coordinate s o 0)).2⟩
        (hxc (coordinate s o 1)) (hxc (coordinate s o 2))
        (hxc (coordinate s o 3)) (hxc (coordinate s o 4))
        (hxc (coordinate s o 5))
      change -1 < cosine (x (coordinate s o 0)) (x (coordinate s o 1))
        (x (coordinate s o 2)) (x (coordinate s o 3))
        (x (coordinate s o 4)) (x (coordinate s o 5)) ∧ _
      exact ⟨lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) hr.1, hr.2⟩
    · intro e
      constructor
      · intro hxe
        have hang : ∀ o ∈ star s e, angle s x o ≤ theta := by
          intro o ho
          have h := (formula_bounds _ _ _ _ _ _
            (hxc (coordinate s o 0)) (hxc (coordinate s o 1))
            (hxc (coordinate s o 2)) (hxc (coordinate s o 3))
            (hxc (coordinate s o 4)) (hxc (coordinate s o 5))).1
          have hv : 2*(2-a)/(a+1) ≤ localCosine s x o := by
            simpa only [localCosine, hstar e o ho, hxe] using h
          exact Real.arccos_le_arccos hv
        have hsum : (∑ o ∈ star s e, angle s x o) ≤ (degree s e : ℝ)*theta := by
          calc
            _ ≤ ∑ _o ∈ star s e, theta := Finset.sum_le_sum hang
            _ = _ := by simp [degree, nsmul_eq_mul]
        have hcard : degree s e ≤ Fintype.card (T × Fin 6) := by
          have h : (star s e).card ≤ (Finset.univ : Finset (T × Fin 6)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          simpa only [degree, Finset.card_univ] using h
        have hcardR : (degree s e : ℝ) ≤ (Fintype.card (T × Fin 6) : ℝ) := by
          exact_mod_cast hcard
        have hprod := mul_le_mul_of_nonneg_right hcardR htheta
        change (Fintype.card (T × Fin 6) : ℝ)*theta < 2*Real.pi at hsmall
        unfold curvature
        linarith
      · intro hxe
        have hang : ∀ o ∈ star s e, Real.arccos (u s b o) ≤ angle s x o := by
          intro o ho
          have h := cosine_mixed_comparison
            (x (coordinate s o 0)) (x (coordinate s o 1))
            (x (coordinate s o 2)) (x (coordinate s o 3))
            (x (coordinate s o 4)) (x (coordinate s o 5))
            (b (coordinate s o 1)) (b (coordinate s o 2)) 1
            (b (coordinate s o 4)) (b (coordinate s o 5))
            (hxc _) (hxc _) (hxc _) (hxc _) (hxc _) (hxc _)
            (hbc _) (hbc _) (by constructor <;> norm_num) (hbc _) (hbc _)
            (hx _).2 (hx _).2 (hxc _).1 (hx _).2 (hx _).2
          have hv : localCosine s x o ≤ u s b o := by
            simpa only [localCosine, u, hstar e o ho, hxe] using h
          exact Real.arccos_le_arccos hv
        have hsum : S s b e ≤ ∑ o ∈ star s e, angle s x o := Finset.sum_le_sum hang
        have hstrict := hS e
        unfold curvature
        linarith
  -- One shared global vector is transported from the original private cube.
  let n := Fintype.card E
  let q : E ≃ Fin n := Fintype.equivFin E
  let X : Cube n → E → ℝ := fun z e => a + (b e-a)*z.1 (q e)
  have hX : ∀ z : Cube n, ∀ e, X z e ∈ Set.Icc a (b e) := by
    intro z e
    have hz := z.2 (q e)
    have hw := hab e
    have hp := mul_nonneg (sub_nonneg.mpr hw.le) hz.1
    have hq := mul_nonneg (sub_nonneg.mpr hw.le) (sub_nonneg.mpr hz.2)
    change a ≤ a+(b e-a)*z.1 (q e) ∧ a+(b e-a)*z.1 (q e) ≤ b e
    constructor <;> nlinarith
  have hc : ∀ e, Continuous (fun z : Cube n => X z e) := by
    intro e
    exact continuous_const.add (continuous_const.mul
      ((continuous_apply (q e)).comp continuous_subtype_val))
  have hr : ∀ z : Cube n, ∀ i j k : E, 0 < rad (X z i) (X z j) (X z k) := by
    intro z i j k
    exact rad_positive _ _ _ (ha.le.trans (hX z i).1)
      (ha.le.trans (hX z j).1) (ha.le.trans (hX z k).1)
  have hcos : ∀ o, Continuous (fun z : Cube n => localCosine s (X z) o) := by
    intro o
    have hroot : ∀ i j k : E, Continuous (fun z : Cube n =>
        Real.sqrt (rad (X z i) (X z j) (X z k))) := by
      intro i j k
      apply Real.continuous_sqrt.comp
      unfold rad
      fun_prop
    have hnum : Continuous (fun z : Cube n =>
        numerator (X z (coordinate s o 0)) (X z (coordinate s o 1))
          (X z (coordinate s o 2)) (X z (coordinate s o 3))
          (X z (coordinate s o 4)) (X z (coordinate s o 5))) := by
      unfold numerator
      fun_prop
    unfold localCosine cosine
    exact (hnum.div (hroot _ _ _) (fun z => (Real.sqrt_pos.2 (hr z _ _ _)).ne')).div
      (hroot _ _ _) (fun z => (Real.sqrt_pos.2 (hr z _ _ _)).ne')
  have hK : ∀ e, Continuous (fun z : Cube n => curvature s (X z) e) := by
    intro e
    apply continuous_const.sub
    exact continuous_finsetSum _ (fun o _ => Real.continuous_arccos.comp (hcos o))
  let G : Cube n → Cube n := fun z =>
    ⟨fun i => max 0 (min 1 (z.1 i + curvature s (X z) (q.symm i))),
      fun i => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_const.max (continuous_const.min
      (((continuous_apply i).comp continuous_subtype_val).add (hK (q.symm i))))
  obtain ⟨z, hz⟩ := cube_fixed_point n G hG
  have hsol : ∀ e, 0 < z.1 (q e) ∧ z.1 (q e) < 1 ∧ curvature s (X z) e = 0 := by
    intro e
    have hfix := congrArg (fun v : Cube n => v.1 (q e)) hz
    change max 0 (min 1 (z.1 (q e) + curvature s (X z) (q.symm (q e)))) =
      z.1 (q e) at hfix
    simp only [Equiv.symm_apply_apply] at hfix
    apply clamp_fixed_zero _ _ (z.2 (q e)) hfix
    · intro heq
      have hface : X z e = a := by dsimp [X]; rw [heq]; ring
      exact ((hfaces (X z) (hX z)).2 e).1 hface
    · intro heq
      have hface : X z e = b e := by dsimp [X]; rw [heq]; ring
      exact ((hfaces (X z) (hX z)).2 e).2 hface
  refine ⟨a, X z, ha, hab, ?_, (hfaces (X z) (hX z)).1, fun e => (hsol e).2.2⟩
  intro e
  obtain ⟨h0, h1, _⟩ := hsol e
  have hp := mul_pos (sub_pos.mpr (hab e)) h0
  have hq := mul_pos (sub_pos.mpr (hab e)) (sub_pos.mpr h1)
  dsimp [X]
  constructor <;> nlinarith

end TransientArbitraryAdjacency

#check @TransientArbitraryAdjacency.u_range
#print axioms TransientArbitraryAdjacency.u_range
#check @TransientArbitraryAdjacency.arbitrary_zero_curvature
#print axioms TransientArbitraryAdjacency.arbitrary_zero_curvature

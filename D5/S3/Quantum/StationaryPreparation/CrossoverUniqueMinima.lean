/- GID: D5/S3/Quantum/StationaryPreparation/CrossoverUniqueMinima
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/CrossoverUniqueMinima
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two explicit crossover costs have unique ordered interior global minima. -/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert
open Set
set_option autoImplicit false

namespace D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima

/-- For the explicit square-root profile, the costs with denominator powers two
and one have unique strict global minima on the whole feasible interval.
The minimum for power two occurs strictly before the minimum for power one. -/
theorem result (c h γ : ℝ) (hc : 12 / 5 < c) (hh0 : 0 < h)
    (hh : h < 31 / 20) (hγ : 0 < γ) :
    let g := fun z : ℝ => 1+(z^2-Real.sqrt (z^4+4))/2
    let F := fun j : ℕ => fun z : ℝ => (c+(h-z)^2)/(1-γ*g z)^j
    let S := {z : ℝ | 0 ≤ z ∧ z ≤ h ∧ 0 < 1-γ*g z}
    ∃ z2 z1 : ℝ, 0 < z2 ∧ z2 < z1 ∧ z1 < h ∧ z2 ∈ S ∧ z1 ∈ S ∧
      (∀ z ∈ S, z ≠ z2 → F 2 z2 < F 2 z) ∧
      (∀ z ∈ S, z ≠ z1 → F 1 z1 < F 1 z) := by
  dsimp only
  let s := fun z : ℝ => Real.sqrt (z^4+4)
  let v := fun z : ℝ => z^2/s z
  let g := fun z : ℝ => 1+(z^2-s z)/2
  let p := fun z : ℝ => z*(1-v z)
  let q := fun z : ℝ => (1-v z)*(1-2*v z-2*(v z)^2)
  have hs (z : ℝ) : 0 < s z := Real.sqrt_pos.2 (by positivity)
  have hs2 (z : ℝ) : (s z)^2 = z^4+4 := Real.sq_sqrt (by positivity)
  have ds (z : ℝ) : HasDerivAt s (2*z^3/s z) z := by
    convert! (((hasDerivAt_id z).pow 4).add_const 4).sqrt (by dsimp; positivity) using 1
    dsimp [s]; ring
  have dg (z : ℝ) : HasDerivAt g (p z) z := by
    convert! ((((hasDerivAt_id z).pow 2).sub (ds z)).div_const 2).const_add 1 using 1
    dsimp [p, v]; ring
  have dp (z : ℝ) : HasDerivAt p (q z) z := by
    convert! (hasDerivAt_id z).mul
      ((((hasDerivAt_id z).pow 2).div (ds z) (hs z).ne').const_sub 1) using 1
    dsimp [q, v]
    field_simp [(hs z).ne']
    ring_nf
  have epos : ∀ z : ℝ, 0 < z → z < h →
      0 < z+(h-z)*(1+(h-z)^2/c)*(1-2*v z-2*(v z)^2) := by
    intro z hz hzh
    have hc0 : 0 < c := by linarith only [hc]
    let r := h-z
    let s := Real.sqrt (z^4+4)
    let v := z^2/s
    have hr : 0 < r := sub_pos.mpr hzh
    have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
    have hs2 : s^2 = z^4+4 := Real.sq_sqrt (by positivity)
    have hsge : 2 ≤ s := by nlinarith only [hs, hs2, sq_nonneg (z^2)]
    have hv : 0 ≤ v := div_nonneg (sq_nonneg z) hs.le
    have hvs : v*s = z^2 := div_mul_cancel₀ _ hs.ne'
    have hvrel : v^2*(z^4+4) = z^4 := by
      rw [← hs2, ← mul_pow, hvs]; ring
    have hv1 : v < 1 := by
      apply (div_lt_one hs).2
      nlinarith only [hs, hs2, sq_nonneg (s-z^2)]
    change 0 < z+r*(1+r^2/c)*(1-2*v-2*v^2)
    by_cases hk : 0 ≤ 1-2*v-2*v^2
    · exact add_pos_of_pos_of_nonneg hz (mul_nonneg (mul_nonneg hr.le (by positivity)) hk)
    have hkpos : 0 < 2*v+2*v^2-1 := by linarith only [hk]
    have bound (R T B : ℝ) (hR : r < R) (hR0 : 0 < R)
        (hT : r^2/c < T) (hB : 2*v+2*v^2-1 < B)
        (hB0 : 0 < B) (hn : R*(1+T)*B < z) :
        0 < z+r*(1+r^2/c)*(1-2*v-2*v^2) := by
      have ht0 : 0 ≤ r^2/c := by positivity
      have ht : r*(1+r^2/c) < R*(1+T) :=
        mul_lt_mul hR (by linarith only [hT]) (by positivity) hR0.le
      have hprod : r*(1+r^2/c)*(2*v+2*v^2-1) < R*(1+T)*B :=
        mul_lt_mul ht hB.le hkpos (mul_nonneg hR0.le (by linarith only [hT, ht0]))
      nlinarith only [hprod, hn]
    by_cases hz04 : z ≤ 4/5
    · have hz2 : z^2 ≤ 16/25 := by nlinarith only [hz, hz04]
      have hv04 : v ≤ 8/25 := by nlinarith only [hvs, hsge, hz2, hv]
      nlinarith only [hv, hv04, hk, sq_nonneg (v-8/25)]
    by_cases hz1 : z ≤ 1
    · have hz2 : z^2 ≤ 1 := by nlinarith only [hz, hz1]
      have hz4 : z^4 ≤ 1 := by nlinarith only [hz2, sq_nonneg (z^2)]
      have hv045 : v < 9/20 := by
        have : v^2*4 ≤ 1-v^2 := by
          nlinarith only [hvrel, mul_nonneg
            (by nlinarith only [hv,hv1] : 0 ≤ 1-v^2)
            (by linarith only [hz4] : 0 ≤ 1-z^4)]
        nlinarith only [this, hv]
      have hK : 2*v+2*v^2-1 < 1/3 := by nlinarith only [hv, hv045]
      have hrR : r < 3/4 := by dsimp [r]; linarith only [hh, hz04]
      have hr2 : r^2 < 9/16 := by nlinarith only [hr, hrR]
      have ht : r^2/c < 15/64 := (div_lt_iff₀ hc0).2 (by nlinarith only [hr2, hc])
      exact bound (3/4) (15/64) (1/3) hrR (by norm_num) ht hK
        (by norm_num) (by linarith only [hz04])
    by_cases hz12 : z ≤ 6/5
    · have hz2 : z^2 ≤ 36/25 := by nlinarith only [hz, hz12]
      have hz4 : z^4 ≤ 1296/625 := by nlinarith only [hz2, sq_nonneg (z^2)]
      have hv06 : v < 3/5 := by
        have : v^2*(1296/625+4) ≤ 1296/625 := by
          nlinarith only [hvrel, mul_nonneg
            (by nlinarith only [hv, hv1] : 0 ≤ 1-v^2)
            (by linarith only [hz4] : 0 ≤ 1296/625-z^4)]
        nlinarith only [this, hv]
      have hK : 2*v+2*v^2-1 < 1 := by nlinarith only [hv, hv06]
      have hrR : r < 11/20 := by dsimp [r]; linarith only [hh, hz1]
      have hr2 : r^2 < 121/400 := by nlinarith only [hr, hrR]
      have ht : r^2/c < 121/960 := (div_lt_iff₀ hc0).2 (by nlinarith only [hr2, hc])
      exact bound (11/20) (121/960) 1 hrR (by norm_num) ht hK (by norm_num) (by linarith only [hz1])
    · have hK : 2*v+2*v^2-1 < 3 := by nlinarith only [hv, hv1]
      have hrR : r < 7/20 := by dsimp [r]; linarith only [hh, hz12]
      have hr2 : r^2 < 49/400 := by nlinarith only [hr, hrR]
      have ht : r^2/c < 49/960 := (div_lt_iff₀ hc0).2 (by nlinarith only [hr2, hc])
      exact bound (7/20) (49/960) 3 hrR (by norm_num) ht hK (by norm_num) (by linarith only [hz12])
  have hc0 : 0 < c := by linarith only [hc]
  have vs (z : ℝ) : v z * s z = z^2 := div_mul_cancel₀ _ (hs z).ne'
  have vb (z : ℝ) : 0 ≤ v z ∧ v z < 1 := by
    constructor
    · exact div_nonneg (sq_nonneg z) (hs z).le
    · apply (div_lt_one (hs z)).2
      nlinarith only [hs z, hs2 z, sq_nonneg (s z-z^2)]
  have pp (z : ℝ) (hz : 0 < z) : 0 < p z := mul_pos hz (sub_pos.mpr (vb z).2)
  have gzero : g 0 = 0 := by
    have hs4 : Real.sqrt 4 = (2:ℝ) :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    norm_num [g,s,hs4]
  have pzero : p 0 = 0 := by simp [p]
  let A := fun z : ℝ => c+(h-z)^2
  let D := fun z : ℝ => 1-γ*g z
  let H := fun t z : ℝ => g z+t*A z*p z/(h-z)
  let F := fun j : ℕ => fun z : ℝ => A z/(D z)^j
  have ap (z : ℝ) : 0 < A z := by dsimp [A]; positivity
  have da (z : ℝ) : HasDerivAt A (-2*(h-z)) z := by
    convert! (((hasDerivAt_id z).const_sub h).pow 2).const_add c using 1
    simp only [id_eq]
    ring
  have dd (z : ℝ) : HasDerivAt D (-γ*p z) z := by
    convert! ((dg z).const_mul γ).const_sub 1 using 1
    ring
  have dH (t z : ℝ) (hz : z < h) : HasDerivAt (H t)
      ((1-t)*p z+t*(c*p z/(h-z)^2+((h-z)+c/(h-z))*q z)) z := by
    convert! (dg z).add ((((da z).const_mul t).mul (dp z)).div
      ((hasDerivAt_id z).const_sub h) (sub_pos.mpr hz).ne') using 1
    simp only [A, id_eq, Pi.mul_apply]
    field_simp [(sub_pos.mpr hz).ne']
    ring
  have hpos (z : ℝ) (hz : 0 < z) (hzh : z < h) :
      0 < c*p z/(h-z)^2+((h-z)+c/(h-z))*q z := by
    have he := epos z hz hzh
    have heq : c*p z/(h-z)^2+((h-z)+c/(h-z))*q z =
        ((1-v z)*c/(h-z)^2)*
          (z+(h-z)*(1+(h-z)^2/c)*(1-2*v z-2*(v z)^2)) := by
      dsimp [p,q]
      field_simp
      ring
    rw [heq]
    exact mul_pos (div_pos (mul_pos (sub_pos.mpr (vb z).2) hc0)
      (sq_pos_of_pos (sub_pos.mpr hzh))) he
  have Hmono (t : ℝ) (ht : 1/2 ≤ t) (ht1 : t ≤ 1) : StrictMonoOn (H t) (Ico 0 h) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 h)
    · intro z hz
      exact (dH t z hz.2).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      rw [(dH t z hz.2).deriv]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (pp z hz.1).le)
        (mul_pos (by linarith) (hpos z hz.1 hz.2))
  have root (t : ℝ) (ht : 1/2 ≤ t) (ht1 : t ≤ 1) :
      ∃ a : ℝ, 0 < a ∧ a < h ∧ γ*H t a = 1 ∧ 0 < D a := by
    let T := fun z : ℝ => (h-z)*(g z-1/γ)+t*A z*p z
    have ct : Continuous T := by
      have cg : Continuous g := continuous_iff_continuousAt.mpr fun z => (dg z).continuousAt
      have cp : Continuous p := continuous_iff_continuousAt.mpr fun z => (dp z).continuousAt
      have ca : Continuous A := continuous_iff_continuousAt.mpr fun z => (da z).continuousAt
      exact (continuous_const.sub continuous_id).mul (cg.sub continuous_const) |>.add
        ((continuous_const.mul ca).mul cp)
    have t0 : T 0 < 0 := by
      simp only [T,gzero,pzero,sub_zero,mul_zero,add_zero,zero_sub]
      exact mul_neg_of_pos_of_neg hh0 (neg_neg_of_pos (one_div_pos.mpr hγ))
    have th : 0 < T h := by simpa [T,A] using mul_pos (mul_pos (by linarith : 0 < t) hc0) (pp h hh0)
    obtain ⟨a, ha, hat⟩ := intermediate_value_Icc hh0.le ct.continuousOn
      (show 0 ∈ Icc (T 0) (T h) from ⟨t0.le,th.le⟩)
    have ha0 : 0 < a := lt_of_le_of_ne ha.1 (by intro e; subst a; linarith)
    have hah : a < h := lt_of_le_of_ne ha.2 (by intro e; subst a; linarith)
    have har : h-a ≠ 0 := (sub_pos.mpr hah).ne'
    have he : γ*H t a = 1 := by
      dsimp [T] at hat
      dsimp [H]
      field_simp
      field_simp at hat
      nlinarith [hat]
    have hg : g a < H t a := by
      dsimp [H]
      exact lt_add_of_pos_right _ (div_pos
        (mul_pos (mul_pos (by linarith) (ap a)) (pp a ha0)) (sub_pos.mpr hah))
    refine ⟨a,ha0,hah,he,?_⟩
    dsimp [D]
    nlinarith [mul_lt_mul_of_pos_left hg hγ]
  obtain ⟨a2,ha20,ha2h,ha2e,ha2D⟩ := root 1 (by norm_num) (by norm_num)
  obtain ⟨a1,ha10,ha1h,ha1e,ha1D⟩ := root (1/2) (by norm_num) (by norm_num)
  have order : a2 < a1 := by
    have hgap : H (1/2) a2 < H 1 a2 := by
      have hhpos : 0 < A a2*p a2/(h-a2) := div_pos (mul_pos (ap a2) (pp a2 ha20)) (sub_pos.mpr ha2h)
      dsimp [H]; ring_nf at hhpos ⊢; linarith
    by_contra hn
    have hm := (Hmono (1/2) (by norm_num) (by norm_num)).monotoneOn
      (show a1 ∈ Ico 0 h from ⟨ha10.le,ha1h⟩) ⟨ha20.le,ha2h⟩ (le_of_not_gt hn)
    nlinarith [mul_lt_mul_of_pos_left hgap hγ]
  have gm : StrictMonoOn g (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro z hz; exact (dg z).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      rw [(dg z).deriv]
      exact pp z hz
  have intervalD (x y : ℝ) (hx : 0 ≤ x) (hyD : 0 < D y) (hxy : x ≤ y) : 0 < D x := by
    have hm := gm.monotoneOn hx (le_trans hx hxy) hxy
    dsimp [D] at hyD ⊢
    nlinarith [mul_le_mul_of_nonneg_left hm hγ.le]
  have dF (j : ℕ) (hj : j = 1 ∨ j = 2) (z : ℝ) (hz : z < h) (hzD : 0 < D z) :
      HasDerivAt (F j) (2*(h-z)/(D z)^(j+1)*(γ*H ((j:ℝ)/2) z-1)) z := by
    have hd := (da z).div ((dd z).pow j) (pow_ne_zero j hzD.ne')
    rcases hj with rfl | rfl
    · convert! hd using 1
      dsimp [H,D,A]
      field_simp [(sub_pos.mpr hz).ne', hzD.ne']
      ring
    · convert! hd using 1
      dsimp [H,D,A]
      field_simp [(sub_pos.mpr hz).ne', hzD.ne']
      ring
  have global (j : ℕ) (hj : j = 1 ∨ j = 2) (a : ℝ)
      (ha0 : 0 < a) (hah : a < h) (haD : 0 < D a)
      (hae : γ*H ((j:ℝ)/2) a = 1) :
      ∀ x : ℝ, 0 ≤ x → x ≤ h → 0 < D x → x ≠ a → F j a < F j x := by
    have ht : 1/2 ≤ (j:ℝ)/2 := by rcases hj with rfl | rfl <;> norm_num
    have ht1 : (j:ℝ)/2 ≤ 1 := by rcases hj with rfl | rfl <;> norm_num
    have hmono := Hmono ((j:ℝ)/2) ht ht1
    have cf (z : ℝ) (hz : 0 < D z) : ContinuousAt (F j) z :=
      (da z).continuousAt.div ((dd z).continuousAt.pow j) (pow_ne_zero j hz.ne')
    intro x hx0 hxh hxD hxa
    rcases lt_or_gt_of_ne hxa with hxa | hax
    · have hm : StrictAntiOn (F j) (Icc x a) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc x a)
        · intro z hz
          exact (cf z (intervalD z a (le_trans hx0 hz.1) haD hz.2)).continuousWithinAt
        · intro z hz
          rw [interior_Icc] at hz
          have hz0 : 0 ≤ z := le_trans hx0 hz.1.le
          have hzh : z < h := lt_trans hz.2 hah
          have hzD := intervalD z a hz0 haD hz.2.le
          rw [(dF j hj z hzh hzD).deriv]
          apply mul_neg_of_pos_of_neg
          · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hzh)) (pow_pos hzD _)
          · have hm := hmono ⟨hz0,hzh⟩ ⟨ha0.le,hah⟩ hz.2
            nlinarith [mul_lt_mul_of_pos_left hm hγ]
      exact hm ⟨le_rfl,hxa.le⟩ ⟨hxa.le,le_rfl⟩ hxa
    · have hm : StrictMonoOn (F j) (Icc a x) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc a x)
        · intro z hz
          exact (cf z (intervalD z x (le_trans ha0.le hz.1) hxD hz.2)).continuousWithinAt
        · intro z hz
          rw [interior_Icc] at hz
          have hz0 : 0 ≤ z := le_trans ha0.le hz.1.le
          have hzh : z < h := lt_of_lt_of_le hz.2 hxh
          have hzD := intervalD z x hz0 hxD hz.2.le
          rw [(dF j hj z hzh hzD).deriv]
          apply mul_pos
          · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hzh)) (pow_pos hzD _)
          · have hm := hmono ⟨ha0.le,hah⟩ ⟨hz0,hzh⟩ hz.1
            nlinarith [mul_lt_mul_of_pos_left hm hγ]
      exact hm ⟨le_rfl,hax.le⟩ ⟨hax.le,le_rfl⟩ hax
  refine ⟨a2,a1,ha20,order,ha1h,⟨ha20.le,ha2h.le,ha2D⟩,⟨ha10.le,ha1h.le,ha1D⟩,?_,?_⟩
  · intro x hx hne
    exact global 2 (Or.inr rfl) a2 ha20 ha2h ha2D (by norm_num; exact ha2e) x hx.1 hx.2.1 hx.2.2 hne
  · intro x hx hne
    exact global 1 (Or.inl rfl) a1 ha10 ha1h ha1D (by norm_num; exact ha1e) x hx.1 hx.2.1 hx.2.2 hne


#print axioms result

end D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima

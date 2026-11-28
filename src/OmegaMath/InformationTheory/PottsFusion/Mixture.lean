module

public import OmegaMath.InformationTheory.PottsFusion
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Omega original.

Finite posterior-mixture form of the local subadditivity estimate of Gu and
Polyanskiy, arXiv:2303.14688v2, Lemma 20 and Appendix D.1, equations (138)--(142).
The mixture weights may vanish, and the number of mixture components is
unrestricted. The fusion expression averages the actual rational posterior
overlap over all input permutations.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace Omega.InformationTheory.PottsFusion

variable {I Y Z : Type*} [Fintype I] [Nonempty I] [Fintype Y] [Fintype Z]

/-- Mean chi-square capacity of a finite posterior mixture. -/
def mixtureCapacity (w : Y → ℝ) (p : Y → I → ℝ) : ℝ :=
  ∑ y, w y * posteriorCapacity (p y)

/-- Fusion of two finite mixtures of fully symmetric posterior orbits. -/
def mixtureFusion (w : Y → ℝ) (p : Y → I → ℝ)
    (v : Z → ℝ) (r : Z → I → ℝ) : ℝ :=
  ∑ z, v z * (∑ y, w y * orbitFusion (p y) (r z))

private lemma weighted_affine_sum {A : Type*} [Fintype A]
    (w f : A → ℝ) (a b : ℝ) (hw : ∑ i, w i = 1) :
    (∑ i, w i * (a * f i + b)) = a * (∑ i, w i * f i) + b := by
  calc
    _ = ∑ i, (a * (w i * f i) + b * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a * (∑ i, w i * f i) + b * (∑ i, w i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [hw, mul_one]

private lemma fixed_posterior_mixture_bound
    (w : Y → ℝ) (p : Y → I → ℝ) (r : I → ℝ) (t : ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1)
    (hp0 : ∀ y i, 0 ≤ p y i) (hp1 : ∀ y, ∑ i, p y i = 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∑ i, r i = 1)
    (ht : 0 < t) (hmean : mixtureCapacity w p ≤ t ^ 5) :
    (∑ y, w y * orbitFusion (p y) r) ≤
      (1 + (8 * (Fintype.card I : ℝ) ^ 4 + (Fintype.card I : ℝ)) * t) *
        (mixtureCapacity w p + posteriorCapacity r) := by
  classical
  let n : ℝ := Fintype.card I
  let K : ℝ := 8 * n ^ 4
  let a : ℝ := 1 + K * t
  let c : ℝ := mixtureCapacity w p
  let d : ℝ := posteriorCapacity r
  have hn : 0 ≤ n := by positivity
  have hK : 0 ≤ K := by positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hc : 0 ≤ c := Finset.sum_nonneg (fun y _ =>
    mul_nonneg (hw0 y) (posterior_capacity_nonneg (p y) (hp1 y)))
  have hd : 0 ≤ d := posterior_capacity_nonneg r hr1
  have ht2 : 0 < t ^ 2 := pow_pos ht _
  have hnt : 0 ≤ n * t := mul_nonneg hn ht.le
  have hsqrt : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht.le
  by_cases hsmall : d ≤ t ^ 2
  · have hpoint (y : Y) : orbitFusion (p y) r ≤
        a * posteriorCapacity (p y) + a * d := by
      have h := orbit_fusion_local_subadditivity (p y) r (t ^ 2)
        (hp0 y) (hp1 y) hr0 hr1 hsmall
      rw [hsqrt] at h
      dsimp only [a, K, n, d]
      nlinarith [h]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ =>
      mul_le_mul_of_nonneg_left (hpoint y) (hw0 y))
    rw [weighted_affine_sum w (fun y => posteriorCapacity (p y)) a (a * d) hw1]
      at hsum
    have hpos := mul_nonneg hnt (add_nonneg hc hd)
    change (∑ y, w y * orbitFusion (p y) r) ≤ (1 + (K + n) * t) * (c + d)
    change (∑ y, w y * orbitFusion (p y) r) ≤ a * c + a * d at hsum
    dsimp only [a] at hsum
    nlinarith
  · have hdlarge : t ^ 2 ≤ d := le_of_lt (lt_of_not_ge hsmall)
    have hfrac : 0 ≤ n / t ^ 2 := div_nonneg hn ht2.le
    have hpoint (y : Y) : orbitFusion (p y) r ≤
        (a + n / t ^ 2) * posteriorCapacity (p y) + a * d := by
      have hcy := posterior_capacity_nonneg (p y) (hp1 y)
      by_cases hgood : posteriorCapacity (p y) ≤ t ^ 2
      · have h := orbit_fusion_local_subadditivity r (p y) (t ^ 2)
          hr0 hr1 (hp0 y) (hp1 y) hgood
        rw [hsqrt, ← orbit_fusion_comm (p y) r] at h
        have hrem := mul_nonneg hfrac hcy
        change orbitFusion (p y) r ≤ (a + n / t ^ 2) * posteriorCapacity (p y) + a * d
        dsimp only [a, K, n, d] at *
        nlinarith
      · have hbad : t ^ 2 ≤ posteriorCapacity (p y) :=
          le_of_lt (lt_of_not_ge hgood)
        have hdom : n ≤ (n / t ^ 2) * posteriorCapacity (p y) := by
          calc
            n = (n / t ^ 2) * (t ^ 2) := by field_simp [ht.ne']
            _ ≤ (n / t ^ 2) * posteriorCapacity (p y) :=
              mul_le_mul_of_nonneg_left hbad hfrac
        have hglobal := orbit_fusion_le_card_sub_one (p y) r
          (hp0 y) (hp1 y) hr0 hr1
        have hpos := mul_nonneg ha (add_nonneg hcy hd)
        change orbitFusion (p y) r ≤ n - 1 at hglobal
        nlinarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ =>
      mul_le_mul_of_nonneg_left (hpoint y) (hw0 y))
    rw [weighted_affine_sum w (fun y => posteriorCapacity (p y))
      (a + n / t ^ 2) (a * d) hw1] at hsum
    have htail : (n / t ^ 2) * c ≤ n * t ^ 3 := by
      calc
        _ ≤ (n / t ^ 2) * t ^ 5 := mul_le_mul_of_nonneg_left hmean hfrac
        _ = n * t ^ 3 := by field_simp [ht.ne'] <;> ring
    have htail' : n * t ^ 3 ≤ n * t * d := by
      have h := mul_le_mul_of_nonneg_left hdlarge hnt
      nlinarith
    have hpos := mul_nonneg hnt hc
    change (∑ y, w y * orbitFusion (p y) r) ≤ (1 + (K + n) * t) * (c + d)
    change (∑ y, w y * orbitFusion (p y) r) ≤ (a + n / t ^ 2) * c + a * d at hsum
    dsimp only [a] at hsum
    nlinarith [htail.trans htail']

/-- The good/bad split for arbitrary finite posterior mixtures. The threshold is
`t²`, and the weak mixture has mean capacity at most `t⁵`. -/
theorem mixture_fusion_bound_fifth_power
    (w : Y → ℝ) (p : Y → I → ℝ) (v : Z → ℝ) (r : Z → I → ℝ) (t : ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∑ z, v z = 1)
    (hp0 : ∀ y i, 0 ≤ p y i) (hp1 : ∀ y, ∑ i, p y i = 1)
    (hr0 : ∀ z i, 0 ≤ r z i) (hr1 : ∀ z, ∑ i, r z i = 1)
    (ht : 0 < t) (hmean : mixtureCapacity w p ≤ t ^ 5) :
    mixtureFusion w p v r ≤
      (1 + (8 * (Fintype.card I : ℝ) ^ 4 + (Fintype.card I : ℝ)) * t) *
        (mixtureCapacity w p + mixtureCapacity v r) := by
  let a : ℝ := 1 + (8 * (Fintype.card I : ℝ) ^ 4 + (Fintype.card I : ℝ)) * t
  have hpoint (z : Z) : (∑ y, w y * orbitFusion (p y) (r z)) ≤
      a * posteriorCapacity (r z) + a * mixtureCapacity w p := by
    have h := fixed_posterior_mixture_bound w p (r z) t
      hw0 hw1 hp0 hp1 (hr0 z) (hr1 z) ht hmean
    dsimp only [a]
    nlinarith [h]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun z _ =>
    mul_le_mul_of_nonneg_left (hpoint z) (hv0 z))
  rw [weighted_affine_sum v (fun z => posteriorCapacity (r z)) a
    (a * mixtureCapacity w p) hv1] at hsum
  change mixtureFusion w p v r ≤ a * (mixtureCapacity w p + mixtureCapacity v r)
  change mixtureFusion w p v r ≤ a * mixtureCapacity v r + a * mixtureCapacity w p at hsum
  nlinarith

/-- Fifth-root local subadditivity of finite mixtures of symmetric posterior
orbits, with a constant independent of both finite mixture cardinalities. -/
theorem mixture_fusion_local_subadditivity
    (w : Y → ℝ) (p : Y → I → ℝ) (v : Z → ℝ) (r : Z → I → ℝ) (ε : ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∑ z, v z = 1)
    (hp0 : ∀ y i, 0 ≤ p y i) (hp1 : ∀ y, ∑ i, p y i = 1)
    (hr0 : ∀ z i, 0 ≤ r z i) (hr1 : ∀ z, ∑ i, r z i = 1)
    (hε0 : 0 < ε) (hε : mixtureCapacity w p ≤ ε) :
    mixtureFusion w p v r ≤
      (1 + (8 * (Fintype.card I : ℝ) ^ 4 + (Fintype.card I : ℝ)) *
        Real.rpow ε (1 / 5)) * (mixtureCapacity w p + mixtureCapacity v r) := by
  let t : ℝ := Real.rpow ε (1 / 5)
  have ht : 0 < t := Real.rpow_pos_of_pos hε0 _
  have ht5 : t ^ 5 = ε := by
    calc
      t ^ 5 = Real.rpow ε ((1 / 5 : ℝ) * (5 : ℝ)) := by
        rw [Real.rpow_mul hε0.le, Real.rpow_natCast]
      _ = ε := by norm_num
  exact mixture_fusion_bound_fifth_power w p v r t hw0 hw1 hv0 hv1 hp0 hp1 hr0 hr1 ht
    (by simpa only [ht5] using hε)

end Omega.InformationTheory.PottsFusion

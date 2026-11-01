/- GID: D5/S3/Analytic/Interpolation/PolynomialStrictTransition
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/PolynomialStrictTransition
   mirror-E: none(waiver:unfrozen-content)
   anchors: []
   utility: none
   digest: Polynomial sign boundaries give strict downward neighborhoods. -/

module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue

/-! Strict signed neighborhoods from polynomial zeros. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Analytic.Interpolation.PolynomialStrictTransition

open Set Filter Topology Polynomial

/-- Opposite signs of a function whose product with a positive multiplier is
polynomial give a strict transition with a closed neighborhood inside the interval.
No simplicity of the polynomial root or continuity of the multiplier is required. -/
theorem strict_downward_of_polynomial_multiplier
    (p : ℝ[X]) (g w : ℝ → ℝ) {l r : ℝ} (hlr : l < r)
    (hw : ∀ x ∈ Icc l r, 0 < w x)
    (heq : ∀ x ∈ Icc l r, w x * g x = p.eval x)
    (hl : 0 < g l) (hr : g r < 0) :
    ∃ ξ δ : ℝ, 0 < δ ∧ Icc (ξ - δ) (ξ + δ) ⊆ Ioo l r ∧
      g ξ = 0 ∧ (∀ x ∈ Ioo (ξ - δ) ξ, 0 < g x) ∧
      (∀ x ∈ Ioo ξ (ξ + δ), g x < 0) := by
  classical
  have hpl : 0 < p.eval l := by
    rw [← heq l ⟨le_rfl, hlr.le⟩]
    exact mul_pos (hw l ⟨le_rfl, hlr.le⟩) hl
  have hpr : p.eval r < 0 := by
    rw [← heq r ⟨hlr.le, le_rfl⟩]
    exact mul_neg_of_pos_of_neg (hw r ⟨hlr.le, le_rfl⟩) hr
  have hp : p ≠ 0 := by intro h; simp [h] at hpl
  let S : Set ℝ := {x | x ∈ Icc l r ∧ 0 < p.eval x}
  have hSl : l ∈ S := ⟨⟨le_rfl, hlr.le⟩, hpl⟩
  have hSne : S.Nonempty := ⟨l, hSl⟩
  have hSb : BddAbove S := ⟨r, fun x hx => hx.1.2⟩
  let ξ : ℝ := sSup S
  have hlξ : l ≤ ξ := le_csSup hSb hSl
  have hξr : ξ ≤ r := csSup_le hSne (fun x hx => hx.1.2)
  have hξcl : ξ ∈ closure S := csSup_mem_closure hSne hSb
  have hpξ : 0 ≤ p.eval ξ :=
    closure_minimal (fun x hx => hx.2.le)
      (isClosed_le continuous_const p.continuous) hξcl
  have hξr' : ξ < r := by
    refine lt_of_le_of_ne hξr ?_
    intro h
    rw [h] at hpξ
    exact (not_le_of_gt hpr) hpξ
  have hpξ0 : p.eval ξ = 0 := by
    apply le_antisymm _ hpξ
    by_contra h
    have hpos : 0 < p.eval ξ := lt_of_not_ge h
    obtain ⟨e, he, heS⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt continuous_const p.continuous).mem_nhds hpos)
    let d := min e (r - ξ) / 2
    have hd : 0 < d := div_pos (lt_min he (sub_pos.mpr hξr')) (by norm_num)
    have hde : d < e := by dsimp [d]; have := min_le_left e (r - ξ); linarith
    have hdr : d < r - ξ := by dsimp [d]; have := min_le_right e (r - ξ); linarith
    have hmem : ξ + d ∈ S := by
      refine ⟨⟨by linarith, by linarith⟩, heS ?_⟩
      change dist (ξ + d) ξ < e
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hd]
      exact hde
    have := le_csSup hSb hmem
    change ξ + d ≤ ξ at this
    linarith
  have hlξ' : l < ξ := by
    refine lt_of_le_of_ne hlξ ?_
    intro h
    rw [← h] at hpξ0
    linarith
  have hZ : Set.Finite {x : ℝ | p.eval x = 0} := p.finite_setOfPred_isRoot hp
  have hpunct : ({x : ℝ | p.eval x = 0} \ {ξ})ᶜ ∈ 𝓝 ξ :=
    (hZ.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨e, he, heZ⟩ := Metric.mem_nhds_iff.mp hpunct
  have hisol {x : ℝ} (hx : dist x ξ < e) (hne : x ≠ ξ) : p.eval x ≠ 0 := by
    intro hz
    exact (heZ hx) ⟨hz, by simpa using hne⟩
  let δ := min e (min (ξ - l) (r - ξ)) / 2
  have hδ : 0 < δ :=
    div_pos (lt_min he (lt_min (sub_pos.mpr hlξ') (sub_pos.mpr hξr'))) (by norm_num)
  have hδe : δ < e := by dsimp [δ]; have := min_le_left e (min (ξ-l) (r-ξ)); linarith
  have hδl : δ < ξ - l := by
    have := (min_le_right e (min (ξ-l) (r-ξ))).trans (min_le_left (ξ-l) (r-ξ))
    dsimp [δ]; linarith
  have hδr : δ < r - ξ := by
    have := (min_le_right e (min (ξ-l) (r-ξ))).trans (min_le_right (ξ-l) (r-ξ))
    dsimp [δ]; linarith
  have hinside : Icc (ξ - δ) (ξ + δ) ⊆ Ioo l r := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hleft : ∀ x ∈ Ioo (ξ - δ) ξ, 0 < p.eval x := by
    intro x hx
    have hxe : dist x ξ < e := by rw [Real.dist_eq, abs_of_neg (by linarith [hx.2] : x - ξ < 0)]; linarith [hx.1]
    have hxne : p.eval x ≠ 0 := hisol hxe (ne_of_lt hx.2)
    by_contra hnot
    have hxneg : p.eval x < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hxne
    obtain ⟨z, hzS, hxz⟩ := exists_lt_of_lt_csSup hSne hx.2
    have hzle : z ≤ ξ := le_csSup hSb hzS
    have hzlt : z < ξ := by
      refine lt_of_le_of_ne hzle ?_
      intro h
      have := hzS.2
      rw [h, hpξ0] at this
      exact (lt_irrefl 0) this
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Ioo hxz.le p.continuous.continuousOn
      (show (0 : ℝ) ∈ Ioo (p.eval x) (p.eval z) from ⟨hxneg, hzS.2⟩)
    have hte : dist t ξ < e := by
      rw [Real.dist_eq, abs_of_neg (by linarith [ht.2] : t - ξ < 0)]
      linarith [ht.1, hx.1]
    exact hisol hte (ne_of_lt (ht.2.trans hzlt)) ht0
  have hright : ∀ x ∈ Ioo ξ (ξ + δ), p.eval x < 0 := by
    intro x hx
    have hxe : dist x ξ < e := by rw [Real.dist_eq, abs_of_pos (by linarith [hx.1] : 0 < x - ξ)]; linarith [hx.2]
    have hxne := hisol hxe (ne_of_gt hx.1)
    by_contra hnot
    have hxpos : 0 < p.eval x := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hxne)
    have hxS : x ∈ S := ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hxpos⟩
    have := le_csSup hSb hxS
    change x ≤ ξ at this
    linarith [hx.1]
  refine ⟨ξ, δ, hδ, hinside, ?_, ?_, ?_⟩
  · have hξI : ξ ∈ Icc l r := ⟨hlξ, hξr⟩
    have := heq ξ hξI
    rw [hpξ0] at this
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt (hw ξ hξI))
  · intro x hx
    have hxI : x ∈ Icc l r := Ioo_subset_Icc_self (hinside ⟨hx.1.le, by linarith [hx.2]⟩)
    have hmul : 0 < w x * g x := by rw [heq x hxI]; exact hleft x hx
    exact (mul_pos_iff_of_pos_left (hw x hxI)).mp hmul
  · intro x hx
    have hxI : x ∈ Icc l r := Ioo_subset_Icc_self (hinside ⟨by linarith [hx.1], hx.2.le⟩)
    have hmul : w x * g x < 0 := by rw [heq x hxI]; exact hright x hx
    by_contra h
    have := mul_nonneg (hw x hxI).le (le_of_not_gt h)
    linarith

end D5.S3.Analytic.Interpolation.PolynomialStrictTransition

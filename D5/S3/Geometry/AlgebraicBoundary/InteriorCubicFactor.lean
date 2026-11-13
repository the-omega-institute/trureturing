/- GID: D5/S3/Geometry/AlgebraicBoundary/InteriorCubicFactor
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/InteriorCubicFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interior zeros of cubic boundary equations force removable hyperplane factors. -/

import D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion
import D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Order.IntermediateValue

/-! Polynomial line restrictions retain their actual affine points and multiplicities. -/

noncomputable section

open Set Filter
open scoped Topology Pointwise

namespace D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

variable {ι : Type*} [Fintype ι]

private def linePolynomial (p : MvPolynomial ι ℝ) (a v : ι → ℝ) : Polynomial ℝ :=
  p.eval₂ Polynomial.C (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)

private theorem eval_linePolynomial (p : MvPolynomial ι ℝ) (a v : ι → ℝ) (t : ℝ) :
    (linePolynomial p a v).eval t = MvPolynomial.eval (a + t • v) p := by
  simp only [linePolynomial, MvPolynomial.polynomial_eval_eval₂]
  congr 1
  · ext c
    simp
  · funext i
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem linePolynomial_degree (p : MvPolynomial ι ℝ) (a v : ι → ℝ) :
    (linePolynomial p a v).natDegree ≤ p.totalDegree := by
  classical
  rw [linePolynomial, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  calc
    _ ≤ 0 + (∏ i ∈ d.support,
        (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) ^ d i).natDegree :=
      (Polynomial.natDegree_mul_le).trans (by simp)
    _ ≤ ∑ i ∈ d.support, d i := by
      simp only [zero_add]
      apply (Polynomial.natDegree_prod_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have hlin : (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
        apply le_trans (Polynomial.natDegree_add_le _ _)
        exact max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp))
      simpa only [mul_one] using Polynomial.natDegree_pow_le_of_le (d i) hlin
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

private theorem eval_differentiable (p : MvPolynomial ι ℝ) :
    Differentiable ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (differentiable_const (c : ℝ))
  | add p q hp hq => simpa only [map_add] using! hp.add hq
  | mul_X p i hp =>
      simpa only [map_mul, MvPolynomial.eval_X] using! hp.mul (differentiable_apply i)

private theorem linePolynomial_coeff_one (p : MvPolynomial ι ℝ) (a v : ι → ℝ) :
    (linePolynomial p a v).coeff 1 =
      fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a v := by
  have hline : HasDerivAt (fun t : ℝ => a + t • v) v 0 := by
    simpa only [zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℝ) a).add ((hasDerivAt_id 0).smul_const v)
  have hcomp := (eval_differentiable p a).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have hpoly := (linePolynomial p a v).hasDerivAt (0 : ℝ)
  have heq : (fun t => (linePolynomial p a v).eval t) =
      (fun t : ℝ => MvPolynomial.eval (a + t • v) p) :=
    funext (eval_linePolynomial p a v)
  rw [heq] at hpoly
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using hpoly.unique hcomp

private theorem compact_line_endpoints {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B) (hc : IsCompact B)
    {a : E} (ha : a ∈ interior B) {v : E} (hv : v ≠ 0) :
    ∃ α β : ℝ, α < 0 ∧ 0 < β ∧
      a + α • v ∈ frontier B ∧ a + β • v ∈ frontier B := by
  let A : Set E := (fun x => a + x) ⁻¹' B
  have hA : Convex ℝ A := hB.translate_preimage_right a
  have hA0 : A ∈ 𝓝 (0 : E) := by
    exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using mem_interior_iff_mem_nhds.mp ha)
  have hAc : IsCompact A := (Homeomorph.addLeft a).isCompact_preimage.mpr hc
  have hb : Bornology.IsVonNBounded ℝ A := hAc.isVonNBounded ℝ
  have hp : 0 < gauge A v := (gauge_pos (absorbent_nhds_zero hA0) hb).mpr hv
  have hn : 0 < gauge A (-v) :=
    (gauge_pos (absorbent_nhds_zero hA0) hb).mpr (neg_ne_zero.mpr hv)
  have hfront : ∀ x, x ∈ frontier A ↔ a + x ∈ frontier B := by
    intro x
    exact Set.ext_iff.mp ((Homeomorph.addLeft a).preimage_frontier B).symm x
  refine ⟨-(gauge A (-v))⁻¹, (gauge A v)⁻¹, neg_neg_of_pos (inv_pos.mpr hn),
    inv_pos.mpr hp, ?_, ?_⟩
  · apply (hfront _).mp
    apply (gauge_eq_one_iff_mem_frontier hA hA0).mp
    rw [neg_smul, ← smul_neg, gauge_smul_of_nonneg (inv_nonneg.mpr hn.le)]
    exact inv_mul_cancel₀ hn.ne'
  · apply (hfront _).mp
    apply (gauge_eq_one_iff_mem_frontier hA hA0).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hp.le)]
    exact inv_mul_cancel₀ hp.ne'

private theorem cubic_four_root_obstruction {p : Polynomial ℝ} (hd : p.natDegree ≤ 3)
    (h0 : p.eval 0 = 0) (h1 : p.coeff 1 = 0) {α β : ℝ}
    (ha : α < 0) (hb : 0 < β) (hα : p.eval α = 0) (hβ : p.eval β = 0) : p = 0 := by
  have hc0 : p.coeff 0 = 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hexp4 : p = ∑ i ∈ Finset.range 4, Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
    exact Polynomial.as_sum_range_C_mul_X_pow' p (by omega)
  have hp : p = Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 +
      Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 := by
    simpa [Finset.sum_range_succ, hc0, h1] using hexp4
  have hα' : p.coeff 2 + α * p.coeff 3 = 0 := by
    have hh := hα
    rw [hp] at hh
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hh
    have : α ^ 2 * (p.coeff 2 + α * p.coeff 3) = 0 := by nlinarith [hh]
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ ha.ne)
  have hβ' : p.coeff 2 + β * p.coeff 3 = 0 := by
    have hh := hβ
    rw [hp] at hh
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hh
    have : β ^ 2 * (p.coeff 2 + β * p.coeff 3) = 0 := by nlinarith [hh]
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hb.ne')
  have h3 : p.coeff 3 = 0 := by nlinarith
  have h2 : p.coeff 2 = 0 := by simpa [h3] using hα'
  rw [hp, h2, h3]
  simp

private theorem interior_zero_hyperplane {B : Set (ι → ℝ)} (hB : Convex ℝ B)
    (hc : IsCompact B) (p : MvPolynomial ι ℝ) (hp : p ≠ 0) (hd : p.totalDegree ≤ 3)
    (hvan : ∀ x ∈ frontier B, MvPolynomial.eval x p = 0)
    {a : ι → ℝ} (ha : a ∈ interior B) (hpa : MvPolynomial.eval a p = 0) :
    fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a ≠ 0 ∧
      ∀ x : ι → ℝ,
        fderiv ℝ (fun y : ι → ℝ => MvPolynomial.eval y p) a (x - a) = 0 →
        MvPolynomial.eval x p = 0 := by
  let L := fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a
  have hker : ∀ v : ι → ℝ, L v = 0 → linePolynomial p a v = 0 := by
    intro v hLv
    by_cases hv : v = 0
    · subst v
      apply Polynomial.funext
      intro t
      simpa [eval_linePolynomial] using hpa
    obtain ⟨α, β, hα, hβ, hαf, hβf⟩ := compact_line_endpoints hB hc ha hv
    apply cubic_four_root_obstruction ((linePolynomial_degree p a v).trans hd)
      (by simpa [eval_linePolynomial] using hpa)
      (by simpa [linePolynomial_coeff_one, L] using hLv) hα hβ
    · simpa [eval_linePolynomial] using hvan _ hαf
    · simpa [eval_linePolynomial] using hvan _ hβf
  have hx : ∀ x : ι → ℝ, L (x - a) = 0 → MvPolynomial.eval x p = 0 := by
    intro x hx
    have h := congrArg (fun q : Polynomial ℝ => q.eval 1) (hker (x - a) hx)
    simpa [eval_linePolynomial] using h
  refine ⟨?_, hx⟩
  intro hL
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa using hx x (by simp [L, hL])

private def affineLinearPolynomial (a : ι → ℝ) (L : (ι → ℝ) →L[ℝ] ℝ) :
    MvPolynomial ι ℝ := by
  classical
  exact ∑ i, MvPolynomial.C (L (Pi.single i 1)) *
    (MvPolynomial.X i - MvPolynomial.C (a i))

private theorem eval_affineLinearPolynomial (a x : ι → ℝ)
    (L : (ι → ℝ) →L[ℝ] ℝ) :
    MvPolynomial.eval x (affineLinearPolynomial a L) = L (x - a) := by
  classical
  have hx : (∑ i, (x i - a i) • Pi.single i (1 : ℝ)) = x - a := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = ∑ i, L (Pi.single i 1) * (x i - a i) := by
      simp [affineLinearPolynomial]
    _ = L (∑ i, (x i - a i) • Pi.single i (1 : ℝ)) := by
      simp [map_sum, map_smul, mul_comm]
    _ = L (x - a) := by rw [hx]

private theorem hyperplane_factorization (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (a : ι → ℝ) (L : (ι → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0)
    (hvan : ∀ x, L (x - a) = 0 → MvPolynomial.eval x p = 0) :
    ∃ g : MvPolynomial ι ℝ, g ≠ 0 ∧ p = affineLinearPolynomial a L * g ∧
      g.totalDegree + 1 = p.totalDegree := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : ι → ℝ, L w ≠ 0 := by
    by_contra! h
    exact hL (ContinuousLinearMap.ext h)
  let v : ι → ℝ := (L w)⁻¹ • w
  have hv : L v = 1 := by simp [v, map_smul, hw]
  let l := affineLinearPolynomial a L
  have hel : ∀ x, MvPolynomial.eval x l = L (x - a) :=
    fun x => eval_affineLinearPolynomial a x L
  have hl0 : l ≠ 0 := by
    intro h
    have hh := hel (a + v)
    rw [h, map_zero] at hh
    simpa [hv] using hh
  have hldeg : l.totalDegree = 1 := by
    have hle : l.totalDegree ≤ 1 := by
      apply (MvPolynomial.totalDegree_finsetSum _ _).trans
      apply Finset.sup_le
      intro i hi
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simpa only [MvPolynomial.totalDegree_C, zero_add] using
        (MvPolynomial.totalDegree_sub (MvPolynomial.X i) (MvPolynomial.C (a i))).trans
          (by simp)
    have hne : l.totalDegree ≠ 0 := by
      intro h
      have hconst := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
      have hh : MvPolynomial.eval a l = MvPolynomial.eval (a + v) l := by
        rw [hconst]
        simp
      rw [hel, hel] at hh
      simpa [hv] using hh
    omega
  let r : ι → MvPolynomial ι ℝ := fun i => MvPolynomial.X i - MvPolynomial.C (v i) * l
  let q : MvPolynomial ι ℝ := p.eval₂ MvPolynomial.C r
  have hq : q = 0 := by
    apply MvPolynomial.funext
    intro x
    have hr : (fun i => MvPolynomial.eval x (r i)) = x - L (x - a) • v := by
      funext i
      simp [r, hel, mul_comm]
    have hcoeff : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℝ := by
      ext c
      simp
    change MvPolynomial.eval x (p.eval₂ MvPolynomial.C r) = MvPolynomial.eval x 0
    rw [MvPolynomial.eval_eval₂, hcoeff, map_zero]
    change MvPolynomial.eval (fun i => MvPolynomial.eval x (r i)) p = 0
    rw [hr]
    apply hvan
    have heq : x - L (x - a) • v - a = (x - a) - L (x - a) • v := by abel
    rw [heq, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  let I : Ideal (MvPolynomial ι ℝ) := Ideal.span {l}
  have hlI : Ideal.Quotient.mk I l = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hmap : (Ideal.Quotient.mk I).comp (MvPolynomial.eval₂Hom MvPolynomial.C r) =
      Ideal.Quotient.mk I := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp [r, hlI]
  have hpI : Ideal.Quotient.mk I p = 0 := by
    have hh := congrArg (fun f : MvPolynomial ι ℝ →+* (MvPolynomial ι ℝ ⧸ I) => f p) hmap
    change Ideal.Quotient.mk I q = Ideal.Quotient.mk I p at hh
    rw [hq, map_zero] at hh
    exact hh.symm
  obtain ⟨g, hpg⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hpI)
  have hg : g ≠ 0 := by
    intro h
    apply hp
    rw [hpg, h, mul_zero]
  refine ⟨g, hg, hpg, ?_⟩
  rw [hpg, MvPolynomial.totalDegree_mul_of_isDomain hl0 hg, hldeg]
  omega

/-- The complete affine polynomial factor and degree drop, with deletion on the
entire boundary. -/
private theorem interior_zero_factor {B : Set (ι → ℝ)} (hB : Convex ℝ B)
    (hc : IsCompact B) (p : MvPolynomial ι ℝ) (hp : p ≠ 0) (hd : p.totalDegree ≤ 3)
    (hvan : ∀ x ∈ frontier B, MvPolynomial.eval x p = 0)
    {a : ι → ℝ} (ha : a ∈ interior B) (hpa : MvPolynomial.eval a p = 0) :
    let L := fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a
    L ≠ 0 ∧ ∃ g : MvPolynomial ι ℝ, g ≠ 0 ∧ p = affineLinearPolynomial a L * g ∧
      g.totalDegree + 1 = p.totalDegree ∧
      ∀ x ∈ frontier B, MvPolynomial.eval x g = 0 := by
  dsimp only
  let L := fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a
  obtain ⟨hL, hker⟩ := interior_zero_hyperplane hB hc p hp hd hvan ha hpa
  obtain ⟨g, hg, hpg, hdeg⟩ := hyperplane_factorization p hp a L hL hker
  refine ⟨hL, g, hg, hpg, hdeg, ?_⟩
  apply InteriorFactorDeletion.whole_boundary_factor_delete hB ha L hL
    (eval_differentiable g).continuous
  intro x hx
  have hh := hvan x hx
  rw [hpg, map_mul, eval_affineLinearPolynomial] at hh
  exact hh

private theorem exists_minimum_boundary_equation {B : Set (ι → ℝ)}
    (hB : Convex ℝ B) (hc : IsCompact B) (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hd : p.totalDegree ≤ 3) (hvan : ∀ x ∈ frontier B, MvPolynomial.eval x p = 0) :
    ∃ f : MvPolynomial ι ℝ, f ≠ 0 ∧ f.totalDegree ≤ 3 ∧
      (∀ x ∈ frontier B, MvPolynomial.eval x f = 0) ∧
      (∀ q : MvPolynomial ι ℝ, q ≠ 0 →
        (∀ x ∈ frontier B, MvPolynomial.eval x q = 0) → f.totalDegree ≤ q.totalDegree) ∧
      ∀ a ∈ interior B, MvPolynomial.eval a f ≠ 0 := by
  classical
  have hex : ∃ d : ℕ, ∃ f : MvPolynomial ι ℝ, f ≠ 0 ∧ f.totalDegree = d ∧
      ∀ x ∈ frontier B, MvPolynomial.eval x f = 0 := ⟨p.totalDegree, p, hp, rfl, hvan⟩
  obtain ⟨f, hf, hfd, hfv⟩ := Nat.find_spec hex
  have hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ x ∈ frontier B, MvPolynomial.eval x q = 0) → f.totalDegree ≤ q.totalDegree := by
    intro q hq hqv
    rw [hfd]
    exact Nat.find_min' hex ⟨q, hq, rfl, hqv⟩
  have hdf : f.totalDegree ≤ 3 := (hmin p hp hvan).trans hd
  refine ⟨f, hf, hdf, hfv, hmin, ?_⟩
  intro a ha hfa
  obtain ⟨_, g, hg, _, hdeg, hgv⟩ := interior_zero_factor hB hc f hf hdf hfv ha hfa
  have hh := hmin g hg hgv
  omega

private theorem exists_positive_minimum_on_original {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : E ≃L[ℝ] (ι → ℝ)) {B : Set E}
    (hB : Convex ℝ B) (hc : IsCompact B) (hne : (interior B).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) (hd : p.totalDegree ≤ 3)
    (hvan : ∀ x ∈ frontier B, MvPolynomial.eval (e x) p = 0) :
    ∃ f : MvPolynomial ι ℝ, f ≠ 0 ∧ f.totalDegree ≤ 3 ∧
      (∀ x ∈ frontier B, MvPolynomial.eval (e x) f = 0) ∧
      (∀ q : MvPolynomial ι ℝ, q ≠ 0 →
        (∀ x ∈ frontier B, MvPolynomial.eval (e x) q = 0) → f.totalDegree ≤ q.totalDegree) ∧
      ∀ a ∈ interior B, 0 < MvPolynomial.eval (e a) f := by
  let A : Set (ι → ℝ) := e '' B
  have hA : Convex ℝ A := hB.linear_image e.toLinearMap
  have hAc : IsCompact A := hc.image e.continuous
  have hboundary : ∀ q : MvPolynomial ι ℝ,
      (∀ x ∈ frontier B, MvPolynomial.eval (e x) q = 0) ↔
        ∀ y ∈ frontier A, MvPolynomial.eval y q = 0 := by
    intro q
    rw [show frontier A = e '' frontier B from (e.toHomeomorph.image_frontier B).symm]
    simp only [forall_mem_image]
  have hinterior : ∀ x, x ∈ interior B → e x ∈ interior A := by
    intro x hx
    rw [show interior A = e '' interior B from (e.toHomeomorph.image_interior B).symm]
    exact ⟨x, hx, rfl⟩
  obtain ⟨f, hf, hdf, hfv, hmin, hno⟩ :=
    exists_minimum_boundary_equation hA hAc p hp hd ((hboundary p).mp hvan)
  have hnf : ∀ x ∈ interior B, MvPolynomial.eval (e x) f ≠ 0 :=
    fun x hx => hno (e x) (hinterior x hx)
  have hmf : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ x ∈ frontier B, MvPolynomial.eval (e x) q = 0) → f.totalDegree ≤ q.totalDegree :=
    fun q hq hqv => hmin q hq ((hboundary q).mp hqv)
  have hcont : Continuous (fun x : E => MvPolynomial.eval (e x) f) :=
    (eval_differentiable f).continuous.comp e.continuous
  obtain ⟨a, ha⟩ := hne
  by_cases hpos : 0 < MvPolynomial.eval (e a) f
  · refine ⟨f, hf, hdf, (hboundary f).mpr hfv, hmf, ?_⟩
    intro x hx
    by_contra! hx0
    obtain ⟨z, hz, hz0⟩ := hB.interior.isPreconnected.intermediate_value hx ha
      hcont.continuousOn ⟨hx0, hpos.le⟩
    exact hnf z hz hz0
  · have hneg : MvPolynomial.eval (e a) f < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) (hnf a ha)
    refine ⟨-f, neg_ne_zero.mpr hf, ?_, ?_, ?_, ?_⟩
    · simpa using hdf
    · intro x hx
      simp [(hboundary f).mpr hfv x hx]
    · intro q hq hqv
      simpa using hmf q hq hqv
    · intro x hx
      have hxneg : MvPolynomial.eval (e x) f < 0 := by
        by_contra! hx0
        obtain ⟨z, hz, hz0⟩ := hB.interior.isPreconnected.intermediate_value ha hx
          hcont.continuousOn ⟨hneg.le, hx0⟩
        exact hnf z hz hz0
      simpa using neg_pos.mpr hxneg

private theorem homogeneous_eval_smul (p : MvPolynomial ι ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) (r : ℝ) (x : ι → ℝ) :
    MvPolynomial.eval (r • x) p = r ^ d * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hp.degree_eq_sum_deg_support hm]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

private theorem coeff_prod_top {κ : Type*} (s : Finset κ)
    (f : κ → Polynomial ℝ) (n : κ → ℕ) (hn : ∀ i ∈ s, (f i).natDegree ≤ n i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (f i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hn i (by simp))
        ((Polynomial.natDegree_prod_le _ _).trans
          (Finset.sum_le_sum (fun j hj => hn j (by simp [hj]))))]
      rw [ih (fun j hj => hn j (by simp [hj]))]

private theorem linePolynomial_top_coeff (p : MvPolynomial ι ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) (a v : ι → ℝ) :
    (linePolynomial p a v).coeff d = MvPolynomial.eval v p := by
  classical
  rw [linePolynomial, MvPolynomial.eval₂_eq, MvPolynomial.eval_eq]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  rw [hp.degree_eq_sum_deg_support hm]
  have hlin (i : ι) :
      (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp))
  rw [coeff_prod_top m.support _ (fun i => m i)
    (fun i hi => by simpa using Polynomial.natDegree_pow_le_of_le (m i) (hlin i))]
  apply Finset.prod_congr rfl
  intro i hi
  simpa using Polynomial.coeff_pow_of_natDegree_le (m := m i) (hlin i)

private theorem cubic_splits_of_two_roots {q : Polynomial ℝ} (hd : q.natDegree ≤ 3)
    {a b : ℝ} (hab : a ≠ b) (ha : q.eval a = 0) (hb : q.eval b = 0) : q.Splits := by
  let r := q /ₘ (Polynomial.X - Polynomial.C a)
  have hfac : (Polynomial.X - Polynomial.C a) * r = q :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
  have hr : r.natDegree ≤ 2 := by
    dsimp [r]
    rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C a),
      Polynomial.natDegree_X_sub_C]
    omega
  have hrb : r.eval b = 0 := by
    rw [← hfac, Polynomial.eval_mul] at hb
    exact (mul_eq_zero.mp hb).resolve_left (by simpa using sub_ne_zero.mpr hab.symm)
  rw [← hfac]
  apply (Polynomial.Splits.X_sub_C a).mul
  by_cases h : r.natDegree = 2
  · exact Polynomial.Splits.of_natDegree_eq_two h hrb
  · exact Polynomial.Splits.of_natDegree_le_one (by omega)

private theorem cone_line_splits_on_original {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ConvexCone ℝ E)
    (hclosed : IsClosed (C : Set E)) (hs : C.Salient)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.IsHomogeneous d) (hd : d ≤ 3)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0)
    {e : E} (he : e ∈ interior (C : Set E)) (hpe : MvPolynomial.eval (c e) p ≠ 0)
    (x : E) :
    (linePolynomial p (-c x) (c e)).natDegree = d ∧
      (linePolynomial p (-c x) (c e)).Splits ∧
      (∀ s : ℝ, x = s • e → linePolynomial p (-c x) (c e) =
        Polynomial.C (MvPolynomial.eval (c e) p) * (Polynomial.X - Polynomial.C s) ^ d) := by
  have hdegree : (linePolynomial p (-c x) (c e)).natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · exact (linePolynomial_degree p _ _).trans hp.totalDegree_le
    · rwa [linePolynomial_top_coeff p hp]
  have haxis : ∀ s : ℝ, x = s • e → linePolynomial p (-c x) (c e) =
      Polynomial.C (MvPolynomial.eval (c e) p) * (Polynomial.X - Polynomial.C s) ^ d := by
    intro s hx
    apply Polynomial.funext
    intro t
    rw [eval_linePolynomial]
    have hy : -c x + t • c e = (t - s) • c e := by
      rw [hx, map_smul]
      module
    rw [hy, homogeneous_eval_smul p hp]
    simp [mul_comm]
  refine ⟨hdegree, ?_, haxis⟩
  by_cases hx : ∃ s : ℝ, x = s • e
  · obtain ⟨s, hs⟩ := hx
    rw [haxis s hs]
    exact ((Polynomial.Splits.X_sub_C s).pow d).C_mul _
  · have hxa : ∀ s : ℝ, x ≠ s • e := by simpa using hx
    obtain ⟨a, b, hab, _, _, haf, hbf⟩ :=
      ConeLineEndpoints.off_axis_closed_rays C hclosed hs he hxa
    apply cubic_splits_of_two_roots (hdegree ▸ hd) hab.ne
    · rw [eval_linePolynomial]
      have hzero := hvan _ haf
      have hneg := homogeneous_eval_smul p hp (-1) (c (a • e - x))
      have hcz : c (-(a • e - x)) = (-1 : ℝ) • c (a • e - x) := by simp
      rw [hcz, hneg] at hzero
      have hroot := (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by norm_num))
      simpa [map_sub, map_smul, sub_eq_add_neg, add_comm] using hroot
    · rw [eval_linePolynomial]
      simpa [map_sub, map_smul, sub_eq_add_neg, add_comm] using hvan _ hbf

private theorem cone_interior_add_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ProperCone ℝ E)
    {e x : E} (he : e ∈ interior (C : Set E)) (hx : x ∈ C)
    {r : ℝ} (hr : 0 < r) : x + r • e ∈ interior (C : Set E) := by
  have hsub : r • (C : Set E) ⊆ (C : Set E) := by
    rintro _ ⟨y, hy, rfl⟩
    exact C.smul_mem hy hr.le
  have hri : r • e ∈ interior (C : Set E) := by
    apply interior_mono hsub
    rw [interior_smul₀ hr.ne']
    exact ⟨e, he, rfl⟩
  apply interior_mono (show (C : Set E) + (C : Set E) ⊆ (C : Set E) from ?_)
    (subset_interior_add_right ⟨x, hx, r • e, hri, rfl⟩)
  rintro _ ⟨y, hy, z, hz, rfl⟩
  exact C.add_mem hy hz

/-- Conditional analytic assembly: the homogeneous equation and its absence of
interior zeros must still be obtained from the arbitrary original equation. -/
private theorem cone_line_roots_and_branch {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) (p : MvPolynomial ι ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : d ≤ 3) (hdpos : 0 < d)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0)
    (hno : ∀ y ∈ interior (C : Set E), MvPolynomial.eval (c y) p ≠ 0)
    {e : E} (he : e ∈ interior (C : Set E)) :
    (∀ x : E, (linePolynomial p (-c x) (c e)).natDegree = d ∧
      (linePolynomial p (-c x) (c e)).Splits ∧
      (∀ s : ℝ, x = s • e → linePolynomial p (-c x) (c e) =
        Polynomial.C (MvPolynomial.eval (c e) p) * (Polynomial.X - Polynomial.C s) ^ d)) ∧
    {x : E | ∀ t : ℝ, (linePolynomial p (-c x) (c e)).eval t = 0 → 0 ≤ t} =
      (C : Set E) := by
  have hlines := cone_line_splits_on_original c (C : ConvexCone ℝ E)
    C.isClosed hs p hp hd hvan he (hno e he)
  refine ⟨hlines, Set.ext fun x => ?_⟩
  constructor
  · intro hx
    by_contra hxC
    by_cases haxis : ∃ s : ℝ, x = s • e
    · obtain ⟨s, hsx⟩ := haxis
      have hsneg : s < 0 := by
        by_contra! h
        apply hxC
        rw [hsx]
        exact C.smul_mem (interior_subset he) h
      have hroot : (linePolynomial p (-c x) (c e)).eval s = 0 := by
        rw [(hlines x).2.2 s hsx]
        simp [hdpos.ne']
      exact (not_le_of_gt hsneg) (hx s hroot)
    · have hxa : ∀ s : ℝ, x ≠ s • e := by simpa using haxis
      obtain ⟨a, b, hab, haray, _, haf, _⟩ :=
        ConeLineEndpoints.off_axis_closed_rays (C : ConvexCone ℝ E) C.isClosed hs he hxa
      have haneg : a < 0 := by
        by_contra! ha
        have hzero : (0 : ℝ) ∈ {t : ℝ | -(t • e - x) ∈ (C : ConvexCone ℝ E)} := by
          rw [haray]
          exact ha
        exact hxC (by simpa using hzero)
      have hroot : (linePolynomial p (-c x) (c e)).eval a = 0 := by
        rw [eval_linePolynomial]
        have hzero := hvan _ haf
        have hneg := homogeneous_eval_smul p hp (-1) (c (a • e - x))
        have hcz : c (-(a • e - x)) = (-1 : ℝ) • c (a • e - x) := by simp
        rw [hcz, hneg] at hzero
        have hroot := (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by norm_num))
        simpa [map_sub, map_smul, sub_eq_add_neg, add_comm] using hroot
      exact (not_le_of_gt haneg) (hx a hroot)
  · intro hx t ht
    by_contra! htneg
    have hz := cone_interior_add_positive C he hx (neg_pos.mpr htneg)
    have hnon := hno (x + (-t) • e) hz
    have hline : -c x + t • c e = (-1 : ℝ) • c (x + (-t) • e) := by
      simp [map_add, map_smul]
    rw [eval_linePolynomial, hline, homogeneous_eval_smul p hp] at ht
    exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hnon) ht

private theorem cone_boundary_homogeneous_equation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧
      ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0 := by
  classical
  have hscale : ∀ r : ℝ, 0 < r → r • (C : Set E) = (C : Set E) := by
    intro r hr
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact C.smul_mem hy hr.le
    · intro y hy
      refine ⟨r⁻¹ • y, C.smul_mem hy (inv_nonneg.mpr hr.le), ?_⟩
      simp [smul_smul, hr.ne']
  have hfront : ∀ r : ℝ, 0 < r → ∀ y ∈ frontier (C : Set E),
      r • y ∈ frontier (C : Set E) := by
    intro r hr y hy
    have hf := (Homeomorph.smulOfNeZero r hr.ne' : E ≃ₜ E).image_frontier (C : Set E)
    have heq : r • frontier (C : Set E) = frontier (C : Set E) := by
      simpa [hscale r hr] using hf
    rw [← heq]
    exact ⟨y, hy, rfl⟩
  have hcomp : ∀ d : ℕ, ∀ y ∈ frontier (C : Set E),
      MvPolynomial.eval (c y) (MvPolynomial.homogeneousComponent d p) = 0 := by
    intro d y hy
    by_cases hd : p.totalDegree < d
    · rw [MvPolynomial.homogeneousComponent_eq_zero d p hd, map_zero]
    let Q : Polynomial ℝ := ∑ k ∈ Finset.range (p.totalDegree + 1),
      Polynomial.monomial k (MvPolynomial.eval (c y) (MvPolynomial.homogeneousComponent k p))
    have hQ : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.Ioi_infinite (0 : ℝ)).mono
      intro r hr
      change Q.eval r = 0
      have hh := hvan (r • y) (hfront r hr y hy)
      rw [← MvPolynomial.sum_homogeneousComponent p, map_sum] at hh
      simpa only [Q, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
        map_smul, homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _),
        mul_comm] using hh
    have hc := congrArg (fun f : Polynomial ℝ => f.coeff d) hQ
    simpa [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_of_le (le_of_not_gt hd)] using hc
  obtain ⟨d, hd, hq⟩ : ∃ d ∈ Finset.range (p.totalDegree + 1),
      MvPolynomial.homogeneousComponent d p ≠ 0 := by
    by_contra! h
    apply hp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    exact Finset.sum_eq_zero h
  have hz : (0 : E) ∈ frontier (C : Set E) := by
    rw [C.isClosed.frontier_eq]
    refine ⟨C.toPointedCone.zero_mem, ?_⟩
    intro hzero
    obtain ⟨z, hz⟩ := exists_ne (0 : E)
    obtain ⟨y, hy⟩ : ∃ y : E, y ∉ C := by
      by_cases hzc : z ∈ C
      · exact ⟨-z, hs z hzc hz⟩
      · exact ⟨z, hzc⟩
    have htend : Tendsto (fun t : ℝ => t⁻¹ • y) atTop (𝓝 (0 : E)) := by
      simpa using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul_const y
    have hm := htend.eventually (mem_interior_iff_mem_nhds.mp hzero)
    obtain ⟨t, ht, hty⟩ := ((eventually_gt_atTop (0 : ℝ)).and hm).exists
    apply hy
    simpa [smul_smul, ht.ne'] using C.smul_mem hty ht.le
  have hdpos : 0 < d := by
    by_contra! hd0
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd0
    subst d
    have hc := hcomp 0 0 hz
    simp only [map_zero, MvPolynomial.homogeneousComponent_zero, MvPolynomial.eval_C] at hc
    exact hq (by simp [hc])
  exact ⟨d, MvPolynomial.homogeneousComponent d p, hdpos,
    Nat.le_of_lt_succ (Finset.mem_range.mp hd), hq,
    MvPolynomial.homogeneousComponent_isHomogeneous d p, hcomp d⟩

end D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

/- GID: D5/S3/Geometry/AlgebraicBoundary/InteriorCubicFactor
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/InteriorCubicFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interior zeros of cubic boundary equations force removable hyperplane factors. -/

import D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion
import D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints
import D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Squarefree.Basic
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
import Batteries.Tactic.OpenPrivate

/-! Polynomial line restrictions retain their actual affine points and multiplicities. -/

noncomputable section

open Set Filter
open scoped Topology Pointwise

namespace D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

open private exists_full_compact_base base_chart_geometry
  from D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase

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

private theorem cone_frontier_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ProperCone ℝ E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : y ∈ frontier (C : Set E)) : r • y ∈ frontier (C : Set E) := by
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
  exact hfront r hr y hy

private theorem cone_vertex_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) : (0 : E) ∈ frontier (C : Set E) := by
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

private theorem cone_boundary_component {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (p : MvPolynomial ι ℝ)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    ∀ d : ℕ, ∀ y ∈ frontier (C : Set E),
      MvPolynomial.eval (c y) (MvPolynomial.homogeneousComponent d p) = 0 := by
  classical
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
    have hh := hvan (r • y) (cone_frontier_smul C hr hy)
    rw [← MvPolynomial.sum_homogeneousComponent p, map_sum] at hh
    simpa only [Q, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
      map_smul, homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _),
      mul_comm] using hh
  have hc := congrArg (fun f : Polynomial ℝ => f.coeff d) hQ
  simpa [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_of_le (le_of_not_gt hd)] using hc

private theorem cone_boundary_homogeneous_equation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧
      ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0 := by
  classical
  have hcomp := cone_boundary_component c C p hvan
  obtain ⟨d, hd, hq⟩ : ∃ d ∈ Finset.range (p.totalDegree + 1),
      MvPolynomial.homogeneousComponent d p ≠ 0 := by
    by_contra! h
    apply hp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    exact Finset.sum_eq_zero h
  have hz := cone_vertex_frontier C hs
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

private theorem substitution_degree {κ : Type*} (p : MvPolynomial κ ℝ)
    (f : κ → MvPolynomial ι ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (p.eval₂ MvPolynomial.C f).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ d.support, (f i ^ d i).totalDegree) ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

private def affinePullback {κ : Type*} (p : MvPolynomial κ ℝ) (a : κ → ℝ)
    (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) : MvPolynomial ι ℝ :=
  p.eval₂ MvPolynomial.C (fun j => MvPolynomial.C (a j) +
    affineLinearPolynomial 0 ((ContinuousLinearMap.proj j).comp A))

private theorem eval_affinePullback {κ : Type*} (p : MvPolynomial κ ℝ)
    (a : κ → ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : ι → ℝ) :
    MvPolynomial.eval x (affinePullback p a A) = MvPolynomial.eval (a + A x) p := by
  rw [affinePullback, MvPolynomial.eval_eval₂]
  congr 1
  · ext r
    simp
  · funext j
    simp [eval_affineLinearPolynomial]

private theorem affinePullback_degree {κ : Type*} (p : MvPolynomial κ ℝ)
    (a : κ → ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) :
    (affinePullback p a A).totalDegree ≤ p.totalDegree := by
  apply substitution_degree
  intro j
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp

/-- Homogenization uses a linear normalization and a linear kernel chart.
The formula is polynomial on the whole carrier, including normalization zero. -/
private def chartHomogenize {κ : Type*} (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) : MvPolynomial ι ℝ :=
  ∑ k ∈ Finset.range (p.totalDegree + 1),
    affineLinearPolynomial 0 u ^ (p.totalDegree - k) *
      affinePullback (MvPolynomial.homogeneousComponent k p) 0 A

private theorem chartHomogenize_homogeneous {κ : Type*} (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) :
    (chartHomogenize p u A).IsHomogeneous p.totalDegree := by
  classical
  have hlin : ∀ L : (ι → ℝ) →L[ℝ] ℝ,
      (affineLinearPolynomial 0 L).IsHomogeneous 1 := by
    intro L
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    simpa using MvPolynomial.isHomogeneous_C_mul_X (L (Pi.single i 1)) i
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  have hk : k ≤ p.totalDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hcomp : (affinePullback (MvPolynomial.homogeneousComponent k p) 0 A).IsHomogeneous k := by
    simpa [affinePullback] using
      (MvPolynomial.homogeneousComponent_isHomogeneous k p).eval₂ MvPolynomial.C
        (fun j => affineLinearPolynomial 0 ((ContinuousLinearMap.proj j).comp A))
        (fun r => MvPolynomial.isHomogeneous_C ι r)
        (fun j => hlin _)
  simpa [Nat.sub_add_cancel hk] using ((hlin u).pow (p.totalDegree - k)).mul hcomp

private theorem eval_chartHomogenize {κ : Type*} [Fintype κ] (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (x : ι → ℝ) (hx : u x ≠ 0) :
    MvPolynomial.eval x (chartHomogenize p u A) =
      u x ^ p.totalDegree * MvPolynomial.eval ((u x)⁻¹ • A x) p := by
  classical
  have hsum : MvPolynomial.eval ((u x)⁻¹ • A x) p =
      ∑ k ∈ Finset.range (p.totalDegree + 1),
        MvPolynomial.eval ((u x)⁻¹ • A x) (MvPolynomial.homogeneousComponent k p) := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
  rw [chartHomogenize, map_sum, hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk : k ≤ p.totalDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [map_mul, map_pow, eval_affineLinearPolynomial, sub_zero, eval_affinePullback,
    zero_add, homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous k p)]
  rw [← mul_assoc]
  congr 1
  rw [inv_pow, pow_sub₀ _ hx hk]

private theorem homogeneous_restriction_ne_zero {κ : Type*} [Fintype κ]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) {d : ℕ} (hhom : p.IsHomogeneous d)
    (u : (ι → ℝ) →L[ℝ] ℝ) (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hdecomp : ∀ x, J (A x) = x - u x • b) :
    affinePullback p b J ≠ 0 := by
  intro hf
  have hnon : ∀ x : ι → ℝ, u x ≠ 0 → MvPolynomial.eval x p = 0 := by
    intro x hx
    have heval := eval_affinePullback p b J ((u x)⁻¹ • A x)
    have heq : b + J ((u x)⁻¹ • A x) = (u x)⁻¹ • x := by
      rw [map_smul, hdecomp, smul_sub, smul_smul, inv_mul_cancel₀ hx, one_smul]
      module
    rw [hf, map_zero, heq, homogeneous_eval_smul p hhom] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left (pow_ne_zero _ (inv_ne_zero hx))
  apply hp
  apply MvPolynomial.funext
  intro x
  by_cases hx : u x ≠ 0
  · simpa using hnon x hx
  · have hx : u x = 0 := not_ne_iff.mp hx
    have hline : linePolynomial p x b = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.Ioi_infinite (0 : ℝ)).mono
      intro t ht
      change (linePolynomial p x b).eval t = 0
      rw [eval_linePolynomial]
      apply hnon
      simpa [map_add, map_smul, hx, hb] using ht.ne'
    have hh := congrArg (fun q : Polynomial ℝ => q.eval 0) hline
    simpa [eval_linePolynomial] using hh

private theorem chartHomogenize_section {κ : Type*} [Fintype κ] (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hJ : ∀ v, u (J v) = 0) (hAb : A b = 0) (hAJ : ∀ v, A (J v) = v)
    (v : κ → ℝ) :
    MvPolynomial.eval (b + J v) (chartHomogenize p u A) = MvPolynomial.eval v p := by
  have hu : u (b + J v) = 1 := by simp [hb, hJ]
  rw [eval_chartHomogenize p u A _ (by rw [hu]; norm_num)]
  simp [hu, map_add, hAb, hAJ]

private theorem chartHomogenize_ne_zero {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (hp : p ≠ 0)
    (u : (ι → ℝ) →L[ℝ] ℝ) (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hJ : ∀ v, u (J v) = 0) (hAb : A b = 0) (hAJ : ∀ v, A (J v) = v) :
    chartHomogenize p u A ≠ 0 := by
  intro h
  apply hp
  apply MvPolynomial.funext
  intro v
  have hh := chartHomogenize_section p u b hb J A hJ hAb hAJ v
  simpa [h] using hh.symm

private theorem chart_boundary_lift {κ : Type*} [Fintype κ]
    (C : ProperCone ℝ (ι → ℝ))
    (u : (ι → ℝ) →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hdecomp : ∀ x, J (A x) = x - u x • b)
    (hfront : ∀ v, v ∈ frontier {v : κ → ℝ | b + J v ∈ C} ↔
      b + J v ∈ frontier (C : Set (ι → ℝ)))
    (g : MvPolynomial κ ℝ) (hd : 0 < g.totalDegree)
    (hgv : ∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v g = 0) :
    ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y (chartHomogenize g u A) = 0 := by
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    have hh := homogeneous_eval_smul (chartHomogenize g u A)
      (chartHomogenize_homogeneous g u A) 0 b
    simpa [hd.ne'] using hh
  · have huy : 0 < u y := hu y ((C.isClosed.frontier_eq ▸ hy).1) hy0
    have hnorm : (u y)⁻¹ • y ∈ frontier (C : Set (ι → ℝ)) :=
      cone_frontier_smul C (inv_pos.mpr huy) hy
    have heq : b + J ((u y)⁻¹ • A y) = (u y)⁻¹ • y := by
      rw [map_smul, hdecomp, smul_sub, smul_smul, inv_mul_cancel₀ huy.ne', one_smul]
      module
    have hv := hgv ((u y)⁻¹ • A y) ((hfront _).mpr (heq.symm ▸ hnorm))
    rw [eval_chartHomogenize g u A y huy.ne', hv, mul_zero]

private theorem chart_minimum_correspondence {κ : Type*} [Fintype κ]
    (C : ProperCone ℝ (ι → ℝ))
    (u : (ι → ℝ) →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hJ : ∀ v, u (J v) = 0) (hAb : A b = 0) (hAJ : ∀ v, A (J v) = v)
    (hdecomp : ∀ x, J (A x) = x - u x • b)
    (hfront : ∀ v, v ∈ frontier {v : κ → ℝ | b + J v ∈ C} ↔
      b + J v ∈ frontier (C : Set (ι → ℝ)))
    (hne : (frontier {v : κ → ℝ | b + J v ∈ C}).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) {d : ℕ} (hhom : p.IsHomogeneous d)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    let f := affinePullback p b J
    f ≠ 0 ∧ f.totalDegree = p.totalDegree ∧
      (∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v f = 0) ∧
      ∀ g : MvPolynomial κ ℝ, g ≠ 0 →
        (∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v g = 0) →
          f.totalDegree ≤ g.totalDegree := by
  dsimp only
  have hf : affinePullback p b J ≠ 0 :=
    homogeneous_restriction_ne_zero p hp hhom u b hb J A hdecomp
  have hfv : ∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C},
      MvPolynomial.eval v (affinePullback p b J) = 0 := by
    intro v hv
    rw [eval_affinePullback]
    exact hvan _ ((hfront v).mp hv)
  have hbound : ∀ g : MvPolynomial κ ℝ, g ≠ 0 →
      (∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v g = 0) →
        p.totalDegree ≤ g.totalDegree := by
    intro g hg hgv
    have hgpos : 0 < g.totalDegree := by
      by_contra! h
      have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
      obtain ⟨v, hv⟩ := hne
      have hh := hgv v hv
      rw [heq, MvPolynomial.eval_C] at hh
      exact hg (heq.trans (by rw [hh, map_zero]))
    have hG := chartHomogenize_ne_zero g hg u b hb J A hJ hAb hAJ
    have hGd := (chartHomogenize_homogeneous g u A).totalDegree hG
    rw [← hGd]
    exact hmin _ hG (chart_boundary_lift C u hu b hb J A hdecomp hfront g hgpos hgv)
  have hdeg := (hbound _ hf hfv).antisymm (affinePullback_degree p b J)
  exact ⟨hf, hdeg.symm, hfv, fun g hg hgv => hdeg.symm.trans_le (hbound g hg hgv)⟩

private theorem minimum_equation_squarefree (S : Set (ι → ℝ))
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ S, MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ S, MvPolynomial.eval y q = 0) → p.totalDegree ≤ q.totalDegree) :
    Squarefree p := by
  intro a ha
  obtain ⟨r, hpr⟩ := ha
  have ha0 : a ≠ 0 := by
    intro h
    exact hp (by simp [h] at hpr ⊢; exact hpr)
  have hr0 : r ≠ 0 := by
    intro h
    exact hp (by simpa [h] using hpr)
  have hdeg : p.totalDegree = 2 * a.totalDegree + r.totalDegree := by
    rw [hpr, MvPolynomial.totalDegree_mul_of_isDomain (mul_ne_zero ha0 ha0) hr0,
      MvPolynomial.totalDegree_mul_of_isDomain ha0 ha0]
    omega
  have har : ∀ y ∈ S, MvPolynomial.eval y (a * r) = 0 := by
    intro y hy
    have hh := hvan y hy
    rw [hpr, map_mul, map_mul] at hh
    rw [map_mul]
    rcases mul_eq_zero.mp hh with h | h
    · exact mul_eq_zero.mpr (Or.inl ((mul_self_eq_zero.mp h)))
    · exact mul_eq_zero.mpr (Or.inr h)
  have hm := hmin (a * r) (mul_ne_zero ha0 hr0) har
  rw [MvPolynomial.totalDegree_mul_of_isDomain ha0 hr0, hdeg] at hm
  have hda : a.totalDegree = 0 := by omega
  have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hda
  have hc : a.coeff 0 ≠ 0 := by
    intro h
    exact ha0 (heq.trans (by rw [h, map_zero]))
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

private theorem exists_homogeneous_minimum [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0) :
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧ Squarefree q ∧
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) ∧
      ∀ r : MvPolynomial ι ℝ, r ≠ 0 →
        (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
          q.totalDegree ≤ r.totalDegree := by
  classical
  have hex : ∃ d : ℕ, ∃ f : MvPolynomial ι ℝ, f ≠ 0 ∧ f.totalDegree = d ∧
      ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y f = 0 :=
    ⟨p.totalDegree, p, hp, rfl, hvan⟩
  obtain ⟨f, hf, hfd, hfv⟩ := Nat.find_spec hex
  have hmin : ∀ r : MvPolynomial ι ℝ, r ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
        f.totalDegree ≤ r.totalDegree := by
    intro r hr hrv
    rw [hfd]
    exact Nat.find_min' hex ⟨r, hr, rfl, hrv⟩
  obtain ⟨d, q, hd, hdf, hq, hhom, hqv⟩ := cone_boundary_homogeneous_equation
    (ContinuousLinearEquiv.refl ℝ (ι → ℝ)) C hs f hf hfv
  have hqd := hhom.totalDegree hq
  have hqmin : ∀ r : MvPolynomial ι ℝ, r ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
        q.totalDegree ≤ r.totalDegree := by
    intro r hr hrv
    rw [hqd]
    exact hdf.trans (hmin r hr hrv)
  exact ⟨d, q, hd, hdf.trans (hmin p hp hvan), hq, hhom,
    minimum_equation_squarefree _ q hq hqv hqmin, hqv, hqmin⟩

private theorem minimum_cone_no_interior_zero [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : p.totalDegree ≤ 3)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    ∀ y ∈ interior (C : Set (ι → ℝ)), MvPolynomial.eval y p ≠ 0 := by
  classical
  obtain ⟨u, b, hu, hb, hbi, hKc, hKn, hint, hfront⟩ :=
    exists_full_compact_base C hs hfull
  let P : (ι → ℝ) →L[ℝ] u.ker :=
    (ContinuousLinearMap.id ℝ (ι → ℝ) - u.smulRight b).codRestrict u.ker
      (by intro x; simp [hb])
  have hP : ∀ x, (P x : ι → ℝ) = x - u x • b := fun _ => rfl
  let κ := Fin (Module.finrank ℝ u.ker)
  let k : u.ker ≃L[ℝ] (κ → ℝ) := (Module.finBasis ℝ u.ker).equivFunL
  let J : (κ → ℝ) →L[ℝ] (ι → ℝ) := u.ker.subtypeL.comp k.symm.toContinuousLinearMap
  let A : (ι → ℝ) →L[ℝ] (κ → ℝ) := k.toContinuousLinearMap.comp P
  have hJ : ∀ v, u (J v) = 0 := fun v => (k.symm v).property
  have hAb : A b = 0 := by
    have hh : P b = 0 := by apply Subtype.ext; simp [hP, hb]
    simp [A, hh]
  have hAJ : ∀ v, A (J v) = v := by
    intro v
    have hh : P (J v) = k.symm v := by
      apply Subtype.ext
      simp [hP, hJ, J]
    simp [A, hh]
  have hdecomp : ∀ x, J (A x) = x - u x • b := by
    intro x
    simpa [J, A] using hP x
  let K : Set u.ker := {v | b + (v : ι → ℝ) ∈ C}
  let B : Set (κ → ℝ) := {v | b + J v ∈ C}
  have hKB : k '' K = B := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [B, J, K] using hw
    · intro hv
      exact ⟨k.symm v, hv, k.apply_symm_apply v⟩
  have hBc : IsCompact B := hKB ▸ hKc.image k.continuous
  have hBconv : Convex ℝ B := by
    intro x hx y hy a c ha hc hac
    change b + J (a • x + c • y) ∈ C
    have hh := C.convex hx hy ha hc hac
    have heq : b + J (a • x + c • y) = a • (b + J x) + c • (b + J y) := by
      simp only [map_add, map_smul, smul_add]
      calc
        b + (a • J x + c • J y) = (a + c) • b + (a • J x + c • J y) := by rw [hac, one_smul]
        _ = a • b + a • J x + (c • b + c • J y) := by module
    exact heq ▸ hh
  have hfr : ∀ v, v ∈ frontier B ↔ b + J v ∈ frontier (C : Set (ι → ℝ)) := by
    intro v
    have hh : frontier B = k '' frontier K := by
      rw [← hKB]
      exact (k.toHomeomorph.image_frontier K).symm
    rw [hh]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [J] using (hfront w).mp hw
    · intro hv
      exact ⟨k.symm v, (hfront _).mpr hv, k.apply_symm_apply v⟩
  rcases subsingleton_or_nontrivial u.ker with hsub | hnontriv
  · have hx : ∀ x, x = u x • b := by
      intro x
      have hh : P x = 0 := Subsingleton.elim _ _
      have hh' := congrArg Subtype.val hh
      simpa [hP, sub_eq_zero] using hh'
    have hpb : MvPolynomial.eval b p ≠ 0 := by
      intro h
      apply hp
      apply MvPolynomial.funext
      intro x
      conv_lhs => rw [hx x, homogeneous_eval_smul p hhom, h, mul_zero]
      simp
    intro y hy hpy
    have hy0 : y ≠ 0 := by
      intro h
      have hz := (C.isClosed.frontier_eq ▸ cone_vertex_frontier C hs).2
      exact hz (h ▸ hy)
    rw [hx y, homogeneous_eval_smul p hhom] at hpy
    exact (mul_ne_zero (pow_ne_zero _ (hu y (interior_subset hy) hy0).ne') hpb) hpy
  · letI : Nontrivial u.ker := hnontriv
    letI : Nontrivial (κ → ℝ) := k.toEquiv.symm.nontrivial
    have hne : (frontier B).Nonempty := nonempty_frontier_iff.mpr
      ⟨⟨0, by simpa [B] using interior_subset hbi⟩, hBc.ne_univ⟩
    obtain ⟨hf, hdeg, hfv, hmf⟩ :=
      chart_minimum_correspondence C u hu b hb J A hJ hAb hAJ hdecomp hfr hne p hp hhom hvan hmin
    have hno : ∀ v ∈ interior B, MvPolynomial.eval v (affinePullback p b J) ≠ 0 := by
      intro v hv hpv
      obtain ⟨_, g, hg, _, hgd, hgv⟩ := interior_zero_factor hBconv hBc
        (affinePullback p b J) hf (hdeg ▸ hd) hfv hv hpv
      have hm := hmf g hg hgv
      omega
    intro y hy hpy
    have hy0 : y ≠ 0 := by
      intro h
      have hz := (C.isClosed.frontier_eq ▸ cone_vertex_frontier C hs).2
      exact hz (h ▸ hy)
    have huy := hu y (interior_subset hy) hy0
    let v := (u y)⁻¹ • A y
    have heq : b + J v = (u y)⁻¹ • y := by
      change b + J ((u y)⁻¹ • A y) = (u y)⁻¹ • y
      rw [map_smul, hdecomp, smul_sub, smul_smul, inv_mul_cancel₀ huy.ne', one_smul]
      module
    have hnorm : (u y)⁻¹ • y ∈ interior (C : Set (ι → ℝ)) := by
      have hh := cone_interior_add_positive C hy C.toPointedCone.zero_mem (inv_pos.mpr huy)
      simpa using hh
    have hv : v ∈ interior B := by
      have hh : interior B = k '' interior K := by
        rw [← hKB]
        exact (k.toHomeomorph.image_interior K).symm
      rw [hh]
      exact ⟨k.symm v, (hint _).mpr (by simpa [J] using heq.symm ▸ hnorm), k.apply_symm_apply v⟩
    apply hno v hv
    rw [eval_affinePullback, heq, homogeneous_eval_smul p hhom, hpy, mul_zero]

private theorem minimum_equation_homogeneous
    (C : ProperCone ℝ (ι → ℝ)) (p : MvPolynomial ι ℝ)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) : p.IsHomogeneous p.totalDegree := by
  classical
  have hcomp := cone_boundary_component (ContinuousLinearEquiv.refl ℝ (ι → ℝ)) C p hvan
  have hlow : ∀ k, k < p.totalDegree → MvPolynomial.homogeneousComponent k p = 0 := by
    intro k hk
    by_contra hn
    have hm := hmin _ hn (hcomp k)
    have hd := (MvPolynomial.homogeneousComponent_isHomogeneous k p).totalDegree_le
    omega
  have heq : MvPolynomial.homogeneousComponent p.totalDegree p = p := by
    have hh : (∑ k ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent k p) =
        MvPolynomial.homogeneousComponent p.totalDegree p := by
      apply Finset.sum_eq_single p.totalDegree
      · intro k hk hne
        exact hlow k (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hne)
      · simp
    exact hh.symm.trans (MvPolynomial.sum_homogeneousComponent p)
  have hh := MvPolynomial.homogeneousComponent_isHomogeneous p.totalDegree p
  rw [heq] at hh
  exact hh

private theorem minimum_homogeneous_scalar_unique [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (p r : MvPolynomial ι ℝ) (hp : p ≠ 0) (hr : r ≠ 0) {d : ℕ}
    (hhom : p.IsHomogeneous d) (hrhom : r.IsHomogeneous d)
    (hd : p.totalDegree ≤ 3)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hrvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * p := by
  obtain ⟨e, he⟩ := hfull
  have hpe := minimum_cone_no_interior_zero C hs ⟨e, he⟩ p hp hhom hd hvan hmin e he
  let a := MvPolynomial.eval e r / MvPolynomial.eval e p
  let q := r - MvPolynomial.C a * p
  have hqhom : q.IsHomogeneous d := hrhom.sub (hhom.C_mul a)
  have hqvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0 := by
    intro y hy
    simp [q, hvan y hy, hrvan y hy]
  have hqdeg : q.totalDegree ≤ p.totalDegree := by
    rw [hhom.totalDegree hp]
    exact hqhom.totalDegree_le
  have hqzero : q = 0 := by
    by_contra hq
    have hqmin : ∀ s : MvPolynomial ι ℝ, s ≠ 0 →
        (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y s = 0) →
          q.totalDegree ≤ s.totalDegree :=
      fun s hs hsv => hqdeg.trans (hmin s hs hsv)
    have hqe := minimum_cone_no_interior_zero C hs ⟨e, he⟩ q hq hqhom
      (hqdeg.trans hd) hqvan hqmin e he
    apply hqe
    simp [q, a, div_mul_cancel₀ _ hpe]
  have hrp : r = MvPolynomial.C a * p := sub_eq_zero.mp hqzero
  refine ⟨a, ?_, hrp⟩
  intro ha
  exact hr (by simpa [ha] using hrp)

private theorem minimum_scalar_unique [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (p r : MvPolynomial ι ℝ) (hp : p ≠ 0) (hr : r ≠ 0)
    (hd : p.totalDegree ≤ 3) (hrd : r.totalDegree ≤ p.totalDegree)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hrvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * p := by
  have heq : r.totalDegree = p.totalDegree := hrd.antisymm (hmin r hr hrvan)
  have hrmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        r.totalDegree ≤ q.totalDegree := fun q hq hqv => hrd.trans (hmin q hq hqv)
  have hphom := minimum_equation_homogeneous C p hvan hmin
  have hrhom := minimum_equation_homogeneous C r hrvan hrmin
  rw [heq] at hrhom
  exact minimum_homogeneous_scalar_unique C hs hfull p r hp hr hphom hrhom hd hvan hrvan hmin

private theorem positive_finset_lower_bound (s : Finset ℝ) (hs : ∀ r ∈ s, 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ s, ε ≤ r := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨ε, hε, hεs⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
    refine ⟨min a ε, lt_min (hs a (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hεs r hr)

/-- The converse uses the whole original root branch. A polynomial merely
covering the boundary does not supply this hypothesis. -/
private theorem whole_branch_boundary_vanishing {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.IsHomogeneous d)
    {e : E} (he : e ∈ interior (C : Set E)) (hpe : MvPolynomial.eval (c e) p ≠ 0)
    (hbranch : {x : E | ∀ t : ℝ, (linePolynomial p (-c x) (c e)).eval t = 0 → 0 ≤ t} =
      (C : Set E)) :
    ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0 := by
  classical
  intro y hy
  by_contra hpy
  let q := linePolynomial p (-c y) (c e)
  have hq : q ≠ 0 := by
    intro h
    have hh := congrArg (fun Q : Polynomial ℝ => Q.coeff d) h
    rw [linePolynomial_top_coeff p hp] at hh
    exact hpe (by simpa using hh)
  have hq0 : q.eval 0 ≠ 0 := by
    rw [eval_linePolynomial]
    have hh : MvPolynomial.eval ((-1 : ℝ) • c y) p ≠ 0 := by
      rw [homogeneous_eval_smul p hp]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hpy
    simpa using hh
  have hyC : y ∈ C := (C.isClosed.frontier_eq ▸ hy).1
  have hroots : ∀ r ∈ q.roots.toFinset, 0 < r := by
    intro r hr
    have hr0 := (Polynomial.mem_roots hq).mp (Multiset.mem_toFinset.mp hr)
    have hnon : 0 ≤ r := (show y ∈ {x : E | ∀ t : ℝ,
        (linePolynomial p (-c x) (c e)).eval t = 0 → 0 ≤ t} from hbranch ▸ hyC) r hr0
    exact lt_of_le_of_ne hnon (by intro h; apply hq0; simpa [← h] using hr0)
  obtain ⟨ε, hε, hεroots⟩ := positive_finset_lower_bound q.roots.toFinset hroots
  have hshift : y - ε • e ∈ C := by
    change y - ε • e ∈ (C : Set E)
    rw [← hbranch]
    intro t ht
    have hroot : q.eval (t + ε) = 0 := by
      rw [eval_linePolynomial] at ht ⊢
      have heq : -c y + (t + ε) • c e = -c (y - ε • e) + t • c e := by
        rw [map_sub, map_smul]
        module
      rw [heq]
      exact ht
    have hmem : t + ε ∈ q.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hroot)
    linarith [hεroots (t + ε) hmem]
  have hinside := cone_interior_add_positive C he hshift hε
  have hyi : y ∈ interior (C : Set E) := by simpa using hinside
  exact (C.isClosed.frontier_eq ▸ hy).2 hyi

private theorem cone_component_and_closure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (p : MvPolynomial ι ℝ)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0)
    (hno : ∀ y ∈ interior (C : Set E), MvPolynomial.eval (c y) p ≠ 0)
    {e : E} (he : e ∈ interior (C : Set E)) :
    connectedComponentIn {x : E | MvPolynomial.eval (c x) p ≠ 0} e =
        interior (C : Set E) ∧
      closure (connectedComponentIn {x : E | MvPolynomial.eval (c x) p ≠ 0} e) =
        (C : Set E) := by
  let U : Set E := {x | MvPolynomial.eval (c x) p ≠ 0}
  let F := connectedComponentIn U e
  have heU : e ∈ U := hno e he
  have hUF : F ⊆ U := connectedComponentIn_subset U e
  have hcover : F ⊆ interior (C : Set E) ∪ (C : Set E)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior (C : Set E)
    · exact Or.inl hxi
    · right
      intro hxC
      have hxf : x ∈ frontier (C : Set E) := C.isClosed.frontier_eq ▸ ⟨hxC, hxi⟩
      exact hUF hx (hvan x hxf)
  have hFsub : F ⊆ interior (C : Set E) := by
    rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
      C.isClosed.isOpen_compl (by
        apply Set.disjoint_left.mpr
        intro x hx hx'
        exact hx' (interior_subset hx)) hcover with h | h
    · exact h
    · exact False.elim ((h (mem_connectedComponentIn heU)) (interior_subset he))
  have hsubF : interior (C : Set E) ⊆ F :=
    C.convex.interior.isPreconnected.subset_connectedComponentIn he (fun x hx => hno x hx)
  have hF : F = interior (C : Set E) := hFsub.antisymm hsubF
  refine ⟨hF, ?_⟩
  change closure F = (C : Set E)
  rw [hF, C.convex.closure_interior_eq_closure_of_nonempty_interior ⟨e, he⟩,
    C.isClosed.closure_eq]

private theorem ray_boundary_ideal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (hfull : (interior (C : Set E)).Nonempty)
    (hdim : Module.finrank ℝ E = 1) :
    ∃ (u : E →L[ℝ] ℝ) (b : E) (l : MvPolynomial ι ℝ),
      u b = 1 ∧ b ∈ interior (C : Set E) ∧
      (∀ x, x = u x • b) ∧ (∀ x, x ∈ C ↔ 0 ≤ u x) ∧
      frontier (C : Set E) = {0} ∧ l ≠ 0 ∧ l.IsHomogeneous 1 ∧ l.totalDegree = 1 ∧
      (∀ x, MvPolynomial.eval (c x) l = u x) ∧
      (∀ q : MvPolynomial ι ℝ,
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0) ↔ l ∣ q) := by
  classical
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ hdim
  obtain ⟨u, b, hu, hb, hbi, _⟩ := exists_full_compact_base C hs hfull
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hspan : ∀ x, x = u x • b := by
    intro x
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hb0 x
    have hux : u x = a := by rw [← ha]; simp [hb]
    rw [hux, ha]
  have hcone : ∀ x, x ∈ C ↔ 0 ≤ u x := by
    intro x
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · exact (hu x hx hx0).le
    · intro hx
      rw [hspan x]
      exact C.smul_mem (interior_subset hbi) hx
  have hfr : frontier (C : Set E) = {0} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxC := (C.isClosed.frontier_eq ▸ hx).1
      by_contra hx0
      have hxne : x ≠ 0 := by simpa using hx0
      have hxi := cone_interior_add_positive C hbi C.toPointedCone.zero_mem (hu x hxC hxne)
      have hxi' : x ∈ interior (C : Set E) := by simpa [← hspan x] using hxi
      exact (C.isClosed.frontier_eq ▸ hx).2 hxi'
    · intro x hx
      have hx0 : x = 0 := hx
      simpa [hx0] using cone_vertex_frontier C hs
  let L : (ι → ℝ) →L[ℝ] ℝ := u.comp c.symm.toContinuousLinearMap
  have hL : L ≠ 0 := by
    intro h
    have hh : L (c b) = 1 := by simp [L, hb]
    simp [h] at hh
  let l := affineLinearPolynomial 0 L
  have hlhom : l.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    simpa using MvPolynomial.isHomogeneous_C_mul_X (L (Pi.single i 1)) i
  have hleval : ∀ x, MvPolynomial.eval (c x) l = u x := by
    intro x
    simpa [l, L] using eval_affineLinearPolynomial 0 (c x) L
  have hl : l ≠ 0 := by
    intro h
    have hh := hleval b
    simp [h, hb] at hh
  refine ⟨u, b, l, hb, hbi, hspan, hcone, hfr, hl, hlhom, hlhom.totalDegree hl, hleval, ?_⟩
  intro q
  constructor
  · intro hq
    by_cases hq0 : q = 0
    · simp [hq0]
    obtain ⟨g, _, hqg, _⟩ := hyperplane_factorization q hq0 0 L hL (by
      intro z hz
      have hux : u (c.symm z) = 0 := by simpa [L] using hz
      have hx0 : c.symm z = 0 := by rw [hspan (c.symm z), hux, zero_smul]
      have hh := hq (c.symm z) (hfr ▸ (by simpa [hx0]))
      simpa using hh)
    exact ⟨g, hqg⟩
  · rintro ⟨g, rfl⟩ x hx
    have hx0 : x = 0 := by simpa [hfr] using hx
    rw [map_mul, hleval, hx0, map_zero, zero_mul]

/-- The analytic conclusions are obtained from the arbitrary entire-boundary
equation on the original carrier. Principality of the boundary ideal is not
asserted by this statement. -/
private theorem original_minimum_roots_and_branch {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (hfull : (interior (C : Set E)).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) (hd : p.totalDegree ≤ 3)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧ Squarefree q ∧
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          q.totalDegree ≤ r.totalDegree) ∧
      (∀ y ∈ interior (C : Set E), 0 < MvPolynomial.eval (c y) q) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 → r.totalDegree ≤ d →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * q) ∧
      (Module.finrank ℝ E = 1 →
        ∃ (u : E →L[ℝ] ℝ) (b : E) (l : MvPolynomial ι ℝ),
          u b = 1 ∧ b ∈ interior (C : Set E) ∧
          (∀ x, x = u x • b) ∧ (∀ x, x ∈ C ↔ 0 ≤ u x) ∧
          frontier (C : Set E) = {0} ∧ l ≠ 0 ∧ l.IsHomogeneous 1 ∧ l.totalDegree = 1 ∧
          (∀ x, MvPolynomial.eval (c x) l = u x) ∧
          (∀ r : MvPolynomial ι ℝ,
            (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔ l ∣ r)) ∧
      (∀ (h : MvPolynomial ι ℝ) (k : ℕ) (e : E), h.IsHomogeneous k →
        e ∈ interior (C : Set E) → MvPolynomial.eval (c e) h ≠ 0 →
        {x : E | ∀ t : ℝ, (linePolynomial h (-c x) (c e)).eval t = 0 → 0 ≤ t} =
          (C : Set E) →
        ∃ r : MvPolynomial ι ℝ, r ≠ 0 ∧ r.totalDegree = h.totalDegree ∧
          ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ∧
      ∀ e ∈ interior (C : Set E),
        (∀ x : E, (linePolynomial q (-c x) (c e)).natDegree = d ∧
          (linePolynomial q (-c x) (c e)).Splits ∧
          (∀ s : ℝ, x = s • e → linePolynomial q (-c x) (c e) =
            Polynomial.C (MvPolynomial.eval (c e) q) * (Polynomial.X - Polynomial.C s) ^ d)) ∧
        {x : E | ∀ t : ℝ, (linePolynomial q (-c x) (c e)).eval t = 0 → 0 ≤ t} =
          (C : Set E) ∧
        connectedComponentIn {x : E | MvPolynomial.eval (c x) q ≠ 0} e =
          interior (C : Set E) ∧
        closure (connectedComponentIn {x : E | MvPolynomial.eval (c x) q ≠ 0} e) =
          (C : Set E) := by
  classical
  letI : Nontrivial (ι → ℝ) := c.toEquiv.symm.nontrivial
  let D := C.comap c.symm.toContinuousLinearMap
  have hi : interior (D : Set (ι → ℝ)) = c.symm ⁻¹' interior (C : Set E) :=
    (c.symm.toHomeomorph.preimage_interior (C : Set E)).symm
  have hf : frontier (D : Set (ι → ℝ)) = c.symm ⁻¹' frontier (C : Set E) :=
    (c.symm.toHomeomorph.preimage_frontier (C : Set E)).symm
  have hsD : (D : ConvexCone ℝ (ι → ℝ)).Salient := by
    intro x hx hx0 hneg
    apply hs (c.symm x) hx
    · intro h
      have hh := congrArg c h
      exact hx0 (by simpa using hh)
    · simpa [D] using hneg
  have hfullD : (interior (D : Set (ι → ℝ))).Nonempty := by
    obtain ⟨a, ha⟩ := hfull
    exact ⟨c a, by simpa [hi] using ha⟩
  have hboundary : ∀ r : MvPolynomial ι ℝ,
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔
        ∀ z ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval z r = 0 := by
    intro r
    constructor
    · intro h z hz
      simpa using h (c.symm z) (by simpa [hf] using hz)
    · intro h y hy
      exact h (c y) (by simpa [hf] using hy)
  obtain ⟨d, f, hdpos, hdp, hfn, hfhom, _, hfv, hfm⟩ :=
    exists_homogeneous_minimum D hsD p hp ((hboundary p).mp hvan)
  have hfd : f.totalDegree ≤ 3 := (hfhom.totalDegree hfn) ▸ hdp.trans hd
  have hfno := minimum_cone_no_interior_zero D hsD hfullD f hfn hfhom hfd hfv hfm
  have hcont : Continuous (fun x : ι → ℝ => MvPolynomial.eval x f) :=
    (eval_differentiable f).continuous
  have horient : ∃ q : MvPolynomial ι ℝ, q ≠ 0 ∧ q.IsHomogeneous d ∧
      (∀ y ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval y q = 0) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 →
        (∀ y ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
          q.totalDegree ≤ r.totalDegree) ∧
      ∀ y ∈ interior (D : Set (ι → ℝ)), 0 < MvPolynomial.eval y q := by
    rcases D.convex.interior.isPreconnected.mapsTo_Ioi_or_Iio hcont.continuousOn hfno with h | h
    · exact ⟨f, hfn, hfhom, hfv, hfm, h⟩
    · refine ⟨-f, neg_ne_zero.mpr hfn, hfhom.neg, ?_, ?_, ?_⟩
      · intro y hy
        simp [hfv y hy]
      · intro r hr hrv
        simpa using hfm r hr hrv
      · intro y hy
        have hh : MvPolynomial.eval y f < 0 := h hy
        simpa using neg_pos.mpr hh
  obtain ⟨q, hq, hqhom, hqv, hqm, hqpos⟩ := horient
  have hqd : q.totalDegree ≤ 3 := (hqhom.totalDegree hq) ▸ hdp.trans hd
  have hqvo := (hboundary q).mpr hqv
  have hqpo : ∀ y ∈ interior (C : Set E), 0 < MvPolynomial.eval (c y) q := by
    intro y hy
    exact hqpos (c y) (by simpa [hi] using hy)
  refine ⟨d, q, hdpos, hdp, hq, hqhom,
    minimum_equation_squarefree _ q hq hqv hqm, hqvo, ?_, hqpo, ?_, ?_, ?_, ?_⟩
  · intro r hr hrv
    exact hqm r hr ((hboundary r).mp hrv)
  · intro r hr hrd hrv
    have hrd' : r.totalDegree ≤ q.totalDegree := by rwa [hqhom.totalDegree hq]
    exact minimum_scalar_unique D hsD hfullD q r hq hr hqd hrd'
      hqv ((hboundary r).mp hrv) hqm
  · intro hdim
    exact ray_boundary_ideal c C hs hfull hdim
  · intro h k e hhom he hhe hbranch
    refine ⟨h, ?_, rfl, whole_branch_boundary_vanishing c C h hhom he hhe hbranch⟩
    intro hz
    exact hhe (by rw [hz, map_zero])
  · intro e he
    obtain ⟨hline, hbranch⟩ := cone_line_roots_and_branch c C hs q hqhom (hdp.trans hd)
      hdpos hqvo (fun y hy => (hqpo y hy).ne') he
    obtain ⟨hcomp, hclosure⟩ := cone_component_and_closure c C q hqvo
      (fun y hy => (hqpo y hy).ne') he
    exact ⟨hline, hbranch, hcomp, hclosure⟩

end D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

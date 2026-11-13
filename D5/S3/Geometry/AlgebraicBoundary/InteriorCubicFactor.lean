/- GID: D5/S3/Geometry/AlgebraicBoundary/InteriorCubicFactor
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/InteriorCubicFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interior zeros of cubic boundary equations force removable hyperplane factors. -/

import D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion
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

/-! Polynomial line restrictions retain their actual affine points and multiplicities. -/

noncomputable section

open Set Filter
open scoped Topology

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
        apply le_trans Polynomial.natDegree_add_le
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
  simp only [zero_smul, add_zero] at hcomp
  have heq : (fun t => (linePolynomial p a v).eval t) =
      (fun t : ℝ => MvPolynomial.eval (a + t • v) p) :=
    funext (eval_linePolynomial p a v)
  rw [heq] at hpoly
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    zero_add, Nat.cast_one, mul_one] using hpoly.unique hcomp

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
    rw [MvPolynomial.eval_eval₂, hcoeff, MvPolynomial.eval_zero]
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
entire boundary. Kept private until the original cone theorem consumes it. -/
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

end D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

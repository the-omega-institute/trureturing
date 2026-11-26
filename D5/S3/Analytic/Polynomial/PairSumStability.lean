/- GID: D5/S3/Analytic/Polynomial/PairSumStability
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/PairSumStability
   mirror-E: none(waiver:symbolic-resultant-identity)
   anchors: []
   utility: none
   digest: Pairwise root sums yield a finite coefficient test for closed and strict stability. -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
# An integer resultant criterion for closed stability

The resultant in the root variable of `p(Y)` and `p(T - Y)` has roots given by
pairwise sums of roots of `p`. Real coefficients ensure every root can be paired
with its conjugate, so instability produces a positive real root of the resultant.
-/

compile_only_with_mathlib

open Polynomial

namespace D5.S3.Analytic.Polynomial.PairSumStability

noncomputable section

/-- The resultant with respect to `Y` of `p(Y)` and `p(T - Y)`,
where the resulting polynomial variable is `T`. -/
def sumResultant {R : Type*} [CommRing R] (p : R[X]) : R[X] :=
  let q := p.map (C : R →+* R[X])
  resultant q (q.comp (C (X : R[X]) - X)) p.natDegree p.natDegree

private theorem eval₂_sumResultant {R : Type*} [CommRing R]
    (f : R →+* ℂ) (hf : Function.Injective f) (p : R[X]) (z : ℂ) :
    let q := p.map f
    (sumResultant p).eval₂ f z =
      q.leadingCoeff ^ p.natDegree * (q.roots.map fun w => q.eval (z - w)).prod := by
  let q := p.map f
  let g := eval₂RingHom f z
  have hc : g.comp (C : R →+* R[X]) = f := by
    ext r
    exact eval₂_C _ _
  have hx : g (X : R[X]) = z := eval₂_X _ _
  have hd : q.natDegree = p.natDegree := natDegree_map_eq_of_injective hf p
  have hdegree : (q.comp (C z - X)).natDegree ≤ p.natDegree := by
    have hlin : (C z - X : ℂ[X]).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) natDegree_X_le)
    exact natDegree_comp_le.trans (by simpa only [hd, mul_one] using
      (Nat.mul_le_mul_left q.natDegree hlin))
  change g (sumResultant p) = _
  unfold sumResultant
  rw [← resultant_map_map, map_comp, Polynomial.map_sub, map_C, map_X,
    map_map, hc, hx]
  change resultant q (q.comp (C z - X)) p.natDegree p.natDegree = _
  nth_rw 1 [← hd]
  rw [resultant_eq_prod_eval _ _ _ hdegree (IsAlgClosed.splits q)]
  simp only [eval_comp, eval_sub, eval_C, eval_X, q]

private theorem map_sumResultant_eq_prod {R : Type*} [CommRing R]
    (f : R →+* ℂ) (hf : Function.Injective f) (p : R[X]) :
    let q := p.map f
    (sumResultant p).map f = C (q.leadingCoeff ^ p.natDegree) *
      (q.roots.map fun w => q.comp (X - C w)).prod := by
  apply Polynomial.funext
  intro z
  rw [eval_map, eval₂_sumResultant f hf]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
    Function.comp_apply, eval_comp, eval_sub, eval_X]

theorem eval2_sumResultant_eq_zero_iff {R : Type*} [CommRing R]
    (f : R →+* ℂ) (hf : Function.Injective f) (p : R[X]) (hp : p ≠ 0) (z : ℂ) :
    (sumResultant p).eval₂ f z = 0 ↔
      ∃ u v : ℂ, p.eval₂ f u = 0 ∧ p.eval₂ f v = 0 ∧ u + v = z := by
  let q := p.map f
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hp
  rw [eval₂_sumResultant f hf]
  change q.leadingCoeff ^ p.natDegree * (q.roots.map fun w => q.eval (z - w)).prod = 0 ↔ _
  simp only [mul_eq_zero, pow_ne_zero _ (leadingCoeff_ne_zero.mpr hq), false_or,
    Multiset.prod_eq_zero_iff, Multiset.mem_map, mem_roots hq, IsRoot]
  simp only [q, eval_map]
  constructor
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, z - u, hu, hv, by rw [add_comm, sub_add_cancel]⟩
  · rintro ⟨u, v, hu, hv, rfl⟩
    exact ⟨u, hu, by rwa [add_sub_cancel_left]⟩

theorem sumResultant_degree_leading {R : Type*} [CommRing R]
    (f : R →+* ℂ) (hf : Function.Injective f) (p : R[X]) (hp : p ≠ 0) :
    (sumResultant p).natDegree = p.natDegree ^ 2 ∧
      (sumResultant p).leadingCoeff = p.leadingCoeff ^ (2 * p.natDegree) := by
  let q := p.map f
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hp
  have hl : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hd : q.natDegree = p.natDegree := natDegree_map_eq_of_injective hf p
  have hr : q.roots.card = p.natDegree := by
    rw [← hd, (IsAlgClosed.splits q).natDegree_eq_card_roots]
  have hcomp (w : ℂ) : (q.comp (X - C w)).leadingCoeff = q.leadingCoeff := by
    rw [leadingCoeff_comp (by simp), (monic_X_sub_C w).leadingCoeff, one_pow, mul_one]
  have hprod : (0 : ℂ[X]) ∉ q.roots.map (fun w => q.comp (X - C w)) := by
    rw [Multiset.mem_map]
    rintro ⟨w, _, hw⟩
    exact hl (by rw [← hcomp w, hw, leadingCoeff_zero])
  constructor
  · rw [← natDegree_map_eq_of_injective hf (sumResultant p), map_sumResultant_eq_prod f hf]
    change (C (q.leadingCoeff ^ p.natDegree) *
      (q.roots.map fun w => q.comp (X - C w)).prod).natDegree = _
    rw [natDegree_C_mul (pow_ne_zero _ hl), natDegree_multiset_prod _ hprod]
    simp only [Multiset.map_map, Function.comp_apply, natDegree_comp, natDegree_X_sub_C,
      mul_one, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hr, hd, pow_two]
    rfl
  · apply hf
    rw [← leadingCoeff_map_of_injective hf, map_sumResultant_eq_prod f hf]
    change (C (q.leadingCoeff ^ p.natDegree) *
      (q.roots.map fun w => q.comp (X - C w)).prod).leadingCoeff = _
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_multiset_prod]
    simp only [Multiset.map_map, Function.comp_apply, hcomp, Multiset.map_const',
      Multiset.prod_replicate, hr, map_pow, ← leadingCoeff_map_of_injective hf (p := p),
      ← pow_add, two_mul]
    rfl

private theorem coeff_nonneg_of_closed
    (p : ℝ[X]) (hp : 0 < p.leadingCoeff)
    (h : ∀ z : ℂ, p.eval₂ Complex.ofRealHom z = 0 → z.re ≤ 0) (n : ℕ) :
    0 ≤ p.coeff n := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p n with
  | h d ih =>
    by_cases hd0 : d = 0
    · have hp0 : p = C p.leadingCoeff := by
        simpa only [leadingCoeff, hd, hd0] using eq_C_of_natDegree_eq_zero (hd.trans hd0)
      rw [hp0]
      by_cases hn : n = 0 <;> simp [coeff_C, hn, hp.le]
    have hpdeg : p.degree ≠ 0 :=
      (natDegree_pos_iff_degree_pos.mp (hd.symm ▸ Nat.pos_of_ne_zero hd0)).ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p hpdeg
    have hzre := h z hz
    have hfactor : ∃ a : ℝ[X], a.Monic ∧ 0 < a.natDegree ∧
        (∀ j, 0 ≤ a.coeff j) ∧ a ∣ p := by
      by_cases hzi : z.im = 0
      · refine ⟨X - C z.re, monic_X_sub_C _, by simp, ?_, ?_⟩
        · intro j
          rw [coeff_sub]
          have h0 : (C z.re).coeff j ≤ 0 := by
            by_cases hj : j = 0 <;> simp [coeff_C, hj, hzre]
          have h1 : 0 ≤ (X : ℝ[X]).coeff j := by
            by_cases hj : 1 = j <;> simp [coeff_X, hj]
          exact sub_nonneg_of_le (h0.trans h1)
        · apply dvd_iff_isRoot.mpr
          have hreal : (z.re : ℂ) = z := Complex.ext rfl (by simpa using hzi.symm)
          apply Complex.ofReal_injective
          change Complex.ofRealHom (p.eval z.re) = Complex.ofRealHom 0
          rw [map_zero, ← eval₂_at_apply]
          change p.eval₂ Complex.ofRealHom (z.re : ℂ) = 0
          rwa [hreal]
      · let a : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
        have ha : a = X ^ 2 + (C (-(2 * z.re)) * X + C (‖z‖ ^ 2)) := by
          simp only [map_neg, neg_mul, sub_eq_add_neg, a]
          ring
        have had : (C (-(2 * z.re)) * X + C (‖z‖ ^ 2)).natDegree ≤ 1 := by
          exact (natDegree_add_le _ _).trans
            (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
        have hab : (C (-(2 * z.re)) * X + C (‖z‖ ^ 2)).degree < 2 :=
          (natDegree_le_iff_degree_le.mp had).trans_lt (by decide)
        have ham : a.Monic := ha ▸ monic_X_pow_add hab
        refine ⟨a, ham, ?_, ?_, p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hzi⟩
        · rw [ha, natDegree_add_eq_left_of_natDegree_lt (had.trans_lt (by simp))]
          simp
        · intro j
          rw [ha, coeff_add, coeff_add, coeff_C_mul]
          have h0 : 0 ≤ (X ^ 2 : ℝ[X]).coeff j := by by_cases hj : j = 2 <;> simp [coeff_X_pow, hj]
          have h1 : 0 ≤ (X : ℝ[X]).coeff j := by by_cases hj : 1 = j <;> simp [coeff_X, hj]
          have h2 : 0 ≤ (C (‖z‖ ^ 2 : ℝ)).coeff j := by
            by_cases hj : j = 0
            · simpa only [coeff_C, ite_eq_left hj] using sq_nonneg ‖z‖
            · simp only [coeff_C, ite_eq_right hj, le_refl]
          exact add_nonneg h0 (add_nonneg (mul_nonneg (by linarith) h1) h2)
    obtain ⟨a, ham, hap, hac, b, hb⟩ := hfactor
    have hb0 : b ≠ 0 := by
      intro he
      rw [hb, he, mul_zero, leadingCoeff_zero] at hp
      exact (lt_irrefl 0) hp
    have hbd : b.natDegree < d := by
      rw [← hd, hb, ham.natDegree_mul' hb0]
      omega
    have hbl : 0 < b.leadingCoeff := by simpa [hb, leadingCoeff_mul, ham.leadingCoeff] using hp
    have hbr (w : ℂ) (hw : b.eval₂ Complex.ofRealHom w = 0) : w.re ≤ 0 := by
      apply h
      rw [hb, eval₂_mul, hw, mul_zero]
    rw [hb, coeff_mul]
    exact Finset.sum_nonneg fun ij _ => mul_nonneg (hac ij.1) (ih _ hbd b hbl hbr ij.2 rfl)

private theorem eval₂_int_conj (p : ℤ[X]) (z : ℂ)
    (hz : p.eval₂ (Int.castRingHom ℂ) z = 0) :
    p.eval₂ (Int.castRingHom ℂ) (star z) = 0 := by
  let g := Int.castRingHom ℝ
  have hcomp : Complex.ofRealHom.comp g = Int.castRingHom ℂ := Subsingleton.elim _ _
  have hz' : (p.map g).aeval z = 0 := by
    change (p.map g).eval₂ Complex.ofRealHom z = 0
    rwa [eval₂_map, hcomp]
  have h := aeval_conj (p := p.map g) (z := z)
  rw [hz', map_zero] at h
  change (p.map g).eval₂ Complex.ofRealHom (star z) = 0 at h
  rwa [eval₂_map, hcomp] at h

/-- Closed stability is equivalent to finitely many nonnegative integer coefficients of
the pairwise-sum resultant. The scan includes degrees zero through `(natDegree p)^2`. -/
theorem closed_iff_sumResultant_coeff_nonneg
    (p : ℤ[X]) (hp : p ≠ 0) :
    (∀ z : ℂ, p.eval₂ (Int.castRingHom ℂ) z = 0 → z.re ≤ 0) ↔
      ∀ j : Fin (p.natDegree ^ 2 + 1), 0 ≤ (sumResultant p).coeff j.val := by
  let f := Int.castRingHom ℂ
  let g := Int.castRingHom ℝ
  have hf : Function.Injective f := Int.cast_injective
  have hg : Function.Injective g := Int.cast_injective
  have hcomp : Complex.ofRealHom.comp g = f := Subsingleton.elim _ _
  obtain ⟨hdegree, hleading⟩ := sumResultant_degree_leading f hf p hp
  have hl : 0 < (sumResultant p).leadingCoeff := by
    rw [hleading, pow_mul]
    exact pow_pos (sq_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp)) _
  have hc (z : ℂ) : (sumResultant p).eval₂ f z = 0 ↔
      ∃ u v : ℂ, p.eval₂ f u = 0 ∧ p.eval₂ f v = 0 ∧ u + v = z :=
    eval2_sumResultant_eq_zero_iff f hf p hp z
  constructor
  · intro hpclosed j
    have hl' : 0 < ((sumResultant p).map g).leadingCoeff := by
      rw [leadingCoeff_map_of_injective hg]
      exact Int.cast_pos.mpr hl
    have hclosed (z : ℂ) (hz : ((sumResultant p).map g).eval₂ Complex.ofRealHom z = 0) :
        z.re ≤ 0 := by
      rw [eval₂_map, hcomp] at hz
      obtain ⟨u, v, hu, hv, rfl⟩ := (hc z).mp hz
      exact Complex.add_re u v ▸ add_nonpos (hpclosed u hu) (hpclosed v hv)
    have h := coeff_nonneg_of_closed _ hl' hclosed j.val
    rw [coeff_map] at h
    exact Int.cast_nonneg_iff.mp h
  · intro hcoeff z hz
    by_contra! hpos
    have hconj := eval₂_int_conj p z hz
    have heval : (sumResultant p).eval₂ g (2 * z.re) = 0 := by
      apply Complex.ofReal_injective
      change Complex.ofRealHom ((sumResultant p).eval₂ g (2 * z.re)) = Complex.ofRealHom 0
      rw [map_zero, ringHom_eval₂_intCastRingHom]
      change (sumResultant p).eval₂ f ((2 * z.re : ℝ) : ℂ) = 0
      exact (hc _).mpr ⟨z, star z, hz, hconj, Complex.add_conj z⟩
    have hevalpos : 0 < (sumResultant p).eval₂ g (2 * z.re) := by
      rw [eval₂_eq_sum_range' _ (show (sumResultant p).natDegree < p.natDegree ^ 2 + 1 by
        rw [hdegree]; exact Nat.lt_succ_self _)]
      apply Finset.sum_pos'
      · intro j hj
        exact mul_nonneg (Int.cast_nonneg_iff.mpr (hcoeff ⟨j, Finset.mem_range.mp hj⟩))
          (pow_nonneg (by linarith) _)
      · refine ⟨p.natDegree ^ 2, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
        rw [← hdegree, coeff_natDegree]
        exact mul_pos (Int.cast_pos.mpr hl) (pow_pos (by linarith) _)
    exact hevalpos.ne' heval

/-- For strict stability, the same coefficient test also requires a positive constant term. -/
theorem strict_iff_sumResultant_coeff_nonneg
    (p : ℤ[X]) (hp : p ≠ 0) :
    (∀ z : ℂ, p.eval₂ (Int.castRingHom ℂ) z = 0 → z.re < 0) ↔
      (∀ j : Fin (p.natDegree ^ 2 + 1), 0 ≤ (sumResultant p).coeff j.val) ∧
        0 < (sumResultant p).coeff 0 := by
  let f := Int.castRingHom ℂ
  have hf : Function.Injective f := Int.cast_injective
  have htest := closed_iff_sumResultant_coeff_nonneg p hp
  have hzero :
      (sumResultant p).coeff 0 = 0 ↔
        ∃ u v : ℂ, p.eval₂ f u = 0 ∧ p.eval₂ f v = 0 ∧ u + v = 0 := by
    rw [← eval2_sumResultant_eq_zero_iff f hf p hp, eval₂_at_zero]
    exact map_eq_zero_iff f hf |>.symm
  constructor
  · intro hstrict
    have hcoeff := htest.mp (fun z hz => (hstrict z hz).le)
    refine ⟨hcoeff, lt_of_le_of_ne (hcoeff 0) ?_⟩
    intro hz
    obtain ⟨u, v, hu, hv, huv⟩ := hzero.mp hz.symm
    have hsum := congrArg Complex.re huv
    rw [Complex.add_re, Complex.zero_re] at hsum
    linarith [hstrict u hu, hstrict v hv]
  · rintro ⟨hcoeff, hconstant⟩ z hz
    have hle := htest.mpr hcoeff z hz
    refine lt_of_le_of_ne hle ?_
    intro hre
    apply hconstant.ne'
    apply hzero.mpr
    exact ⟨z, star z, hz, eval₂_int_conj p z hz, by simp [Complex.add_conj, hre]⟩


end

end D5.S3.Analytic.Polynomial.PairSumStability

/- GID: D5/S3/Analytic/AnchoredTelescopingSquares
   generality: G
   mirror-B: D5/B/S3/Analytic/AnchoredTelescopingSquares
   mirror-E: none(waiver:qualitative-polynomial-existence)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Polynomial.Basic]
   utility: none
   digest: Strictly positive even-degree polynomials admit anchored telescoping squares. -/

import D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
import D5.S3.Geometry.Hyperideal.FourCycleExistence
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Taylor
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.AnchoredTelescopingSquares

open Polynomial
open scoped ComplexConjugate
open private Cube cube_fixed_point from D5.S3.Geometry.Hyperideal.FourCycleExistence

/-- Strict positivity constructs the monic lower factor; none is assumed.
The root multiset is split with multiplicities, including collisions. -/
theorem exists_monic_lower_factor (d : ℝ[X]) (m : ℕ)
    (hdegree : d.natDegree = 2 * m) (hpositive : ∀ t : ℝ, 0 < d.eval t) :
    0 < d.coeff (2 * m) ∧ ∃ B : ℂ[X], B.Monic ∧ B.natDegree = m ∧
      (∀ z : ℂ, B.eval z = 0 → z.im < 0) ∧
      d.map Complex.ofRealHom =
        C (d.coeff (2 * m) : ℂ) * (B * B.map (starRingEnd ℂ)) := by
  classical
  let P : ℂ[X] := d.map Complex.ofRealHom
  have hd0 : d ≠ 0 := by
    intro h
    simpa [h] using hpositive 0
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofReal_injective).2 hd0
  have hreal : P.map (starRingEnd ℂ) = P := by
    ext k
    simp only [P, Polynomial.coeff_map]
    exact Complex.conj_ofReal _
  have hroots : P.roots.map (starRingEnd ℂ) = P.roots := by
    rw [Polynomial.roots_map_of_injective_of_card_eq_natDegree
      (starRingEnd ℂ).injective IsAlgClosed.card_roots_eq_natDegree, hreal]
  have hnoreal (z : ℂ) (hz : z ∈ P.roots) : z.im ≠ 0 := by
    intro him
    have he : P.eval z = 0 := (Polynomial.mem_roots hP0).1 hz
    have hzreal : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [him]
    rw [← hzreal] at he
    have he' : Complex.ofRealHom (d.eval (z.re)) = 0 :=
      (Polynomial.eval_map_apply (p := d) Complex.ofRealHom z.re).symm.trans he
    have : d.eval z.re = 0 := Complex.ofReal_injective he'
    exact (hpositive z.re).ne' this
  let L := P.roots.filter (fun z : ℂ => z.im < 0)
  have hconj : L.map (starRingEnd ℂ) =
      P.roots.filter (fun z : ℂ => 0 < z.im) := by
    calc
      L.map (starRingEnd ℂ) =
          (P.roots.map (starRingEnd ℂ)).filter (fun z : ℂ => 0 < z.im) := by
        rw [Multiset.filter_map]
        apply congrArg (Multiset.map (starRingEnd ℂ))
        apply Multiset.filter_congr
        intro z hz
        change z.im < 0 ↔ 0 < (conj z).im
        simp only [Complex.conj_im, neg_pos]
      _ = _ := by rw [hroots]
  have hpartition : L + L.map (starRingEnd ℂ) = P.roots := by
    rw [hconj]
    have hu : P.roots.filter (fun z : ℂ => 0 < z.im) =
        P.roots.filter (fun z : ℂ => ¬ z.im < 0) := by
      apply Multiset.filter_congr
      intro z hz
      have hne := hnoreal z hz
      constructor
      · intro h
        exact not_lt_of_ge h.le
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    rw [hu]
    exact Multiset.filter_add_not (fun z : ℂ => z.im < 0) P.roots
  have hcard : L.card = m := by
    have h := congrArg Multiset.card hpartition
    simp only [Multiset.card_add, Multiset.card_map,
      IsAlgClosed.card_roots_eq_natDegree] at h
    rw [show P.natDegree = 2*m by
      simpa [P] using hdegree] at h
    omega
  let B : ℂ[X] := (L.map (fun z => X - C z)).prod
  have hBm : B.Monic := Polynomial.monic_multisetProd_X_sub_C L
  have hBd : B.natDegree = m := by
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]
  have hBlower : ∀ z : ℂ, B.eval z = 0 → z.im < 0 := by
    intro z hz
    simp only [B, Polynomial.eval_multiset_prod, Multiset.map_map,
      Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨w, hw, he⟩ := hz
    have hzw : z = w := sub_eq_zero.mp he
    simpa [hzw] using (Multiset.mem_filter.mp hw).2
  have hproduct : B * B.map (starRingEnd ℂ) =
      (P.roots.map (fun z => X - C z)).prod := by
    have hbconj : B.map (starRingEnd ℂ) =
        ((L.map (starRingEnd ℂ)).map (fun z => X - C z)).prod := by
      simp [B, Polynomial.map_multiset_prod, Multiset.map_map]
    rw [hbconj]
    change (L.map (fun z => X - C z)).prod *
      ((L.map (starRingEnd ℂ)).map (fun z => X - C z)).prod = _
    rw [← Multiset.prod_add, ← Multiset.map_add, hpartition]
  have hfactor : P = C (d.leadingCoeff : ℂ) * (B * B.map (starRingEnd ℂ)) := by
    rw [hproduct]
    have hlc : P.leadingCoeff = (d.leadingCoeff : ℂ) := by
      simp [P]
    rw [← hlc]
    exact (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      IsAlgClosed.card_roots_eq_natDegree).symm
  have heval := congrArg (fun f : ℂ[X] => (f.eval 0).re) hfactor
  have hconj0 : (B.map (starRingEnd ℂ)).eval 0 = conj (B.eval 0) := by
    simpa using (Polynomial.eval_map_apply (p := B) (starRingEnd ℂ) 0)
  have heval' : d.eval 0 = d.leadingCoeff * Complex.normSq (B.eval 0) := by
    simpa [P, Polynomial.eval_mul, Polynomial.eval_C, hconj0,
      Complex.mul_re, Complex.normSq_apply] using heval
  have hleading : 0 < d.leadingCoeff := by
    have hp := hpositive 0
    have hn := Complex.normSq_nonneg (B.eval 0)
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hn
    linarith
  have hlc : d.coeff (2*m) = d.leadingCoeff := by
    rw [← hdegree]
    rfl
  refine ⟨by rw [hlc]; exact hleading, B, hBm, hBd, hBlower, ?_⟩
  simpa [hlc] using hfactor

/- Strict positivity and exact even degree construct the complete anchored identity. -/
set_option maxHeartbeats 800000 in
theorem exists_anchored_telescoping_squares (d : ℝ[X]) (m : ℕ) (_hm : 1 ≤ m)
    (hdegree : d.natDegree = 2 * m) (hpositive : ∀ t : ℝ, 0 < d.eval t) :
    ∃ p s : ℝ[X], p.natDegree = m ∧ s.natDegree ≤ m ∧ s.eval 0 = 0 ∧
      (∀ t : ℝ, d.eval t = (p.eval t)^2 + (s.eval (t+1))^2 - (s.eval t)^2) ∧
      (p.coeff m)^2 = d.coeff (2*m) ∧ 0 < d.coeff (2*m) := by
  classical
  have hfixed :
    ∃ s : ℝ[X], ∃ a : ℂ[X], s.natDegree ≤ m ∧ s.eval 0 = 0 ∧
      a.natDegree = m ∧
      (∀ t : ℝ, (a.eval (t : ℂ)).im = s.eval (t+1)) ∧
      ∀ t : ℝ, Complex.normSq (a.eval (t : ℂ)) = d.eval t + (s.eval t)^2 := by
    classical
    let c : ℕ → ℝ := fun j => ∑ i ∈ Finset.range j, d.eval (i : ℝ)
    have hc0 : c 0 = 0 := by simp [c]
    have hcs (j : ℕ) : c (j+1) = c j + d.eval (j : ℝ) := by
      simp [c, Finset.sum_range_succ]
    have hcp (j : ℕ) (hj : 0 < j) : 0 < c j := by
      exact Finset.sum_pos (fun i _ => hpositive i) (Finset.nonempty_range_iff.mpr hj.ne')
    let nodes : Fin (m+1) → ℝ := fun i => (i.val : ℝ)
    have hnodes : Set.InjOn nodes (Finset.univ : Finset (Fin (m+1))) := by
      intro i hi j hj h
      exact Fin.ext (Nat.cast_injective h)
    let values : Cube m → Fin (m+1) → ℝ := fun x =>
      Fin.cons 0 (fun i : Fin m => (2*x.val i-1)*Real.sqrt (c (i.val+1)))
    let S : Cube m → ℝ[X] := fun x => Lagrange.interpolate Finset.univ nodes (values x)
    have hSd (x : Cube m) : (S x).natDegree ≤ m := by
      apply Polynomial.natDegree_le_iff_degree_le.mpr
      simpa [S] using (Lagrange.degree_interpolate_le (r := values x) hnodes)
    have hSe (x : Cube m) (i : Fin (m+1)) : (S x).eval (i.val : ℝ) = values x i :=
      Lagrange.eval_interpolate_at_node (values x) hnodes (Finset.mem_univ i)
    have hS0 (x : Cube m) : (S x).eval 0 = 0 := by
      simpa [values] using hSe x 0
    have hSs (x : Cube m) (i : Fin m) :
        (S x).eval ((i.val : ℝ)+1) = (2*x.val i-1)*Real.sqrt (c (i.val+1)) := by
      simpa [values, Nat.cast_add, Nat.cast_one] using hSe x i.succ
    have hvc (i : Fin (m+1)) : Continuous (fun x : Cube m => values x i) := by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · change Continuous (fun x : Cube m => (2*x.val j-1)*Real.sqrt (c (j.val+1)))
        exact ((continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)).sub
          continuous_const).mul continuous_const
    have hSc (k : ℕ) : Continuous (fun x : Cube m => (S x).coeff k) := by
      simp only [S, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul]
      exact continuous_finsetSum _ fun i _ => (hvc i).mul continuous_const
    have hSb (x : Cube m) (j : ℕ) (hj : j ≤ m) : ((S x).eval (j : ℝ))^2 ≤ c j := by
      cases j with
      | zero => simp [hS0, hc0]
      | succ j =>
        let i : Fin m := ⟨j, by omega⟩
        have he := hSs x i
        change (S x).eval ((j : ℝ)+1) = _ at he
        simp only [Nat.cast_add, Nat.cast_one]
        rw [he, mul_pow, Real.sq_sqrt (hcp (j+1) (by omega)).le]
        have hw : (2*x.val i-1)^2 ≤ 1 := by
          have hlo := (x.property i).1
          have hhi := (x.property i).2
          nlinarith
        nlinarith [hcp (j+1) (by omega)]
    let H : Cube m → ℝ[X] := fun x => d + (S x)^2
    have hHp (x : Cube m) (t : ℝ) : 0 < (H x).eval t := by
      simp only [H, Polynomial.eval_add, Polynomial.eval_pow]
      exact add_pos_of_pos_of_nonneg (hpositive t) (sq_nonneg _)
    have hHd (x : Cube m) : (H x).natDegree = 2*m := by
      have htop : (H x).coeff (2*m) = d.coeff (2*m) + ((S x).coeff m)^2 := by
        simp only [H, Polynomial.coeff_add, pow_two]
        rw [show 2*m = m+m by omega,
          Polynomial.coeff_mul_add_eq_of_natDegree_le (hSd x) (hSd x)]
      have htoppos : 0 < (H x).coeff (2*m) := by
        rw [htop]
        exact add_pos_of_pos_of_nonneg
          (exists_monic_lower_factor d m hdegree hpositive).1 (sq_nonneg _)
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ htoppos.ne'
      exact Polynomial.natDegree_add_le_of_degree_le (by omega)
        (Polynomial.natDegree_pow_le_of_le 2 (hSd x))
    have hHc (k : ℕ) : Continuous (fun x : Cube m => (H x).coeff k) := by
      simp only [H, Polynomial.coeff_add, pow_two, Polynomial.coeff_mul]
      exact continuous_const.add (continuous_finsetSum _ fun ij _ => (hSc ij.1).mul (hSc ij.2))
    have hanchored :
      ∃ F : Cube m → ℂ[X], (∀ k, Continuous (fun a => (F a).coeff k)) ∧
        ∀ a, (F a).natDegree = m ∧
          0 < ((F a).eval (-1)).re ∧ ((F a).eval (-1)).im = 0 ∧
          ∀ t : ℝ, Complex.normSq ((F a).eval (t : ℂ)) = (H a).eval t := by
      classical
      have hell (a : Cube m) : 0 < (H a).coeff (2*m) :=
        (exists_monic_lower_factor (H a) m (hHd a) (hHp a)).1
      choose B hBm hBd hBl hBf using fun a =>
        (exists_monic_lower_factor (H a) m (hHd a) (hHp a)).2
      let ell : Cube m → ℝ := fun a => (H a).coeff (2*m)
      have hellc : Continuous ell := hHc (2*m)
      have hellz (a : Cube m) : (ell a : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (hell a).ne'
      let N : Cube m → ℂ[X] := fun a => C (ell a : ℂ)⁻¹ * (H a).map Complex.ofRealHom
      have hNf (a : Cube m) : N a = B a * (B a).map (starRingEnd ℂ) := by
        dsimp [N]
        rw [hBf a, ← mul_assoc, ← Polynomial.C_mul]
        simp only [ell, inv_mul_cancel₀ (hellz a), Polynomial.C_1, one_mul]
      have hNc (k : ℕ) : Continuous (fun a => (N a).coeff k) := by
        simp only [N, Polynomial.coeff_C_mul, Polynomial.coeff_map]
        exact ((Complex.continuous_ofReal.comp hellc).inv₀ hellz).mul
          (Complex.continuous_ofReal.comp (hHc k))
      have hBc := ClosedLowerHalfPlaneFactorContinuity.continuous_coeff_of_monic_closed_lower_factor
        N B m hBm hBd (fun a z hz => (hBl a z hz).le) hNf hNc
      let b : Cube m → ℂ[X] := fun a => C (Real.sqrt (ell a) : ℂ) * B a
      have hbc (k : ℕ) : Continuous (fun a => (b a).coeff k) := by
        simp only [b, Polynomial.coeff_C_mul]
        exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hellc)).mul (hBc k)
      have hbdegree (a : Cube m) : (b a).natDegree = m := by
        dsimp only [b]
        rw [Polynomial.natDegree_C_mul]
        · exact hBd a
        · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hell a)).ne'
      have hbeval (a : Cube m) (t : ℝ) :
          Complex.normSq ((b a).eval (t : ℂ)) = (H a).eval t := by
        have h := congrArg (fun f : ℂ[X] => (f.eval (t : ℂ)).re) (hBf a)
        have hconj : ((B a).map (starRingEnd ℂ)).eval (t : ℂ) =
            conj ((B a).eval (t : ℂ)) := by
          simpa using (Polynomial.eval_map_apply (p := B a) (starRingEnd ℂ) (t : ℂ))
        have he : (H a).eval t = ell a * Complex.normSq ((B a).eval (t : ℂ)) := by
          have heH : ((H a).map Complex.ofRealHom).eval (t : ℂ) = Complex.ofReal ((H a).eval t) :=
            Polynomial.eval_map_apply (p := H a) Complex.ofRealHom t
          rw [heH] at h
          simpa [Polynomial.eval_mul, Polynomial.eval_C, hconj,
            Complex.mul_re, Complex.normSq_apply, ell] using h
        dsimp only [b]
        rw [Polynomial.eval_mul, Polynomial.eval_C, Complex.normSq_mul,
          Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (hell a).le]
        exact he.symm
      have hbev (t : ℂ) : Continuous (fun a => (b a).eval t) := by
        have he (a : Cube m) : (b a).eval t =
            ∑ k ∈ Finset.range (m+1), (b a).coeff k * t^k := by
          rw [Polynomial.eval_eq_sum_range, hbdegree a]
        simp_rw [he]
        exact continuous_finsetSum _ fun k _ => (hbc k).mul continuous_const
      let v : Cube m → ℂ := fun a => (b a).eval (-1)
      have hvc : Continuous v := hbev (-1)
      have hvz (a : Cube m) : v a ≠ 0 := by
        intro h
        have he := hbeval a (-1)
        simp only [Complex.ofReal_neg, Complex.ofReal_one] at he
        change Complex.normSq (v a) = _ at he
        rw [h, Complex.normSq_zero] at he
        linarith [hHp a (-1)]
      have hvnorm (a : Cube m) : 0 < ‖v a‖ := norm_pos_iff.mpr (hvz a)
      let u : Cube m → ℂ := fun a => conj (v a) / (‖v a‖ : ℂ)
      have huc : Continuous u :=
        (Complex.continuous_conj.comp hvc).div
          (Complex.continuous_ofReal.comp hvc.norm)
          (fun a => Complex.ofReal_ne_zero.mpr (hvnorm a).ne')
      have hunorm (a : Cube m) : Complex.normSq (u a) = 1 := by
        dsimp only [u]
        rw [Complex.normSq_div, Complex.normSq_conj, Complex.normSq_ofReal,
          ← pow_two, ← Complex.normSq_eq_norm_sq]
        exact div_self (Complex.normSq_pos.mpr (hvz a)).ne'
      have huz (a : Cube m) : u a ≠ 0 := by
        intro he
        have h := hunorm a
        simp [he] at h
      let F : Cube m → ℂ[X] := fun a => C (u a) * b a
      refine ⟨F, ?_, ?_⟩
      · intro k
        simp only [F, Polynomial.coeff_C_mul]
        exact huc.mul (hbc k)
      · intro a
        have hanchor : (F a).eval (-1) = (‖v a‖ : ℂ) := by
          simp only [F, Polynomial.eval_mul, Polynomial.eval_C]
          change u a * v a = _
          dsimp only [u]
          rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
            Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
          exact (div_eq_iff (Complex.ofReal_ne_zero.mpr (hvnorm a).ne')).2 (pow_two _)
        refine ⟨?_, ?_, ?_, ?_⟩
        · dsimp only [F]
          rw [Polynomial.natDegree_C_mul (huz a), hbdegree a]
        · rw [hanchor]
          exact hvnorm a
        · rw [hanchor]
          rfl
        · intro t
          dsimp only [F]
          rw [Polynomial.eval_mul, Polynomial.eval_C, Complex.normSq_mul,
            hunorm a, one_mul]
          exact hbeval a t
    obtain ⟨F, hFc, hF⟩ := hanchored
    have hFe (t : ℂ) : Continuous (fun x : Cube m => (F x).eval t) := by
      have he (x : Cube m) : (F x).eval t =
          ∑ k ∈ Finset.range (m+1), (F x).coeff k * t^k := by
        rw [Polynomial.eval_eq_sum_range, (hF x).1]
      simp_rw [he]
      exact continuous_finsetSum _ fun k _ => (hFc k).mul continuous_const
    have hFi (x : Cube m) (i : Fin m) :
        (((F x).eval (i.val : ℂ)).im)^2 ≤ c (i.val+1) := by
      have hb := Complex.im_sq_le_normSq ((F x).eval (i.val : ℂ))
      have hn := (hF x).2.2.2 (i.val : ℝ)
      simp only [H, Polynomial.eval_add, Polynomial.eval_pow, Complex.ofReal_natCast] at hn
      have hs := hSb x i.val (by omega)
      rw [hcs]
      nlinarith
    let g : Cube m → Cube m := fun x =>
      ⟨fun i => ((((F x).eval (i.val : ℂ)).im / Real.sqrt (c (i.val+1)))+1)/2, by
        intro i
        have hp := Real.sqrt_pos.2 (hcp (i.val+1) (by omega))
        have hs := Real.sq_sqrt (hcp (i.val+1) (by omega)).le
        have hb := hFi x i
        have hlo : -Real.sqrt (c (i.val+1)) ≤ ((F x).eval (i.val : ℂ)).im := by nlinarith
        have hhi : ((F x).eval (i.val : ℂ)).im ≤ Real.sqrt (c (i.val+1)) := by nlinarith
        have hdlo : -1 ≤ ((F x).eval (i.val : ℂ)).im / Real.sqrt (c (i.val+1)) :=
          (le_div_iff₀ hp).2 (by linarith)
        have hdhi : ((F x).eval (i.val : ℂ)).im / Real.sqrt (c (i.val+1)) ≤ 1 :=
          (div_le_iff₀ hp).2 (by linarith)
        exact ⟨by linarith, by linarith⟩⟩
    have hgc : Continuous g := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      change Continuous (fun x : Cube m =>
        ((((F x).eval (i.val : ℂ)).im / Real.sqrt (c (i.val+1)))+1)/2)
      exact (((Complex.continuous_im.comp (hFe _)).div_const _).add continuous_const).div_const _
    obtain ⟨x, hx⟩ := cube_fixed_point m g hgc
    have hfix (i : Fin m) : (S x).eval ((i.val : ℝ)+1) = ((F x).eval (i.val : ℂ)).im := by
      have hi := congrArg (fun y : Cube m => y.val i) hx
      change ((((F x).eval (i.val : ℂ)).im / Real.sqrt (c (i.val+1)))+1)/2 = x.val i at hi
      rw [hSs]
      have hp := (Real.sqrt_pos.2 (hcp (i.val+1) (by omega))).ne'
      have he : ((F x).eval (i.val : ℂ)).im / Real.sqrt (c (i.val+1)) = 2*x.val i-1 := by
        linarith
      exact (div_eq_iff hp).1 he |>.symm
    let Q : ℂ[X] := C (2*Complex.I)⁻¹ * (F x - (F x).map (starRingEnd ℂ))
    have hQe (t : ℝ) : Q.eval (t : ℂ) = Complex.ofReal (((F x).eval (t : ℂ)).im) := by
      have he : ((F x).map (starRingEnd ℂ)).eval (t : ℂ) =
          conj ((F x).eval (t : ℂ)) := by
        simpa using (Polynomial.eval_map_apply (p := F x) (starRingEnd ℂ) (t : ℂ))
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, he]
      rw [mul_comm, ← div_eq_mul_inv, ← Complex.im_eq_sub_conj]
    have hQd : Q.natDegree ≤ m := by
      dsimp only [Q]
      apply (Polynomial.natDegree_mul_le).trans
      simp only [Polynomial.natDegree_C, zero_add]
      have hmap : ((F x).map (starRingEnd ℂ)).natDegree ≤ m := by
        rw [Polynomial.natDegree_map_eq_of_injective (starRingEnd ℂ).injective]
        exact (hF x).1.le
      simpa only [max_self] using
        (Polynomial.natDegree_sub_le_of_le (hF x).1.le hmap)
    let T : ℂ[X] := ((S x).comp (X + C 1)).map Complex.ofRealHom
    have hTd : T.natDegree ≤ m := by
      dsimp only [T]
      rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective,
        Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
      exact hSd x
    have hQT : Q = T := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
        (s := Finset.univ) (v := fun i : Fin (m+1) => (i.val : ℂ)-1)
      · intro i hi j hj he
        apply Fin.ext
        exact_mod_cast (sub_left_injective he : (i.val : ℂ) = (j.val : ℂ))
      · exact lt_of_le_of_lt (Polynomial.natDegree_le_iff_degree_le.mp hQd) (by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self m))
      · exact lt_of_le_of_lt (Polynomial.natDegree_le_iff_degree_le.mp hTd) (by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self m))
      · intro i hi
        have hTe (t : ℝ) : T.eval (t : ℂ) = Complex.ofReal ((S x).eval (t+1)) := by
          have hh := Polynomial.eval_map_apply (p := (S x).comp (X+C 1)) Complex.ofRealHom t
          simpa [T, Polynomial.eval_comp] using hh
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.val_zero, Nat.cast_zero, zero_sub]
          have hq : Q.eval (-1) = 0 := by
            simpa only [Complex.ofReal_neg, Complex.ofReal_one,
              (hF x).2.2.1, Complex.ofReal_zero] using hQe (-1)
          have ht : T.eval (-1) = 0 := by
            simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_add_cancel,
              hS0, Complex.ofReal_zero] using hTe (-1)
          exact hq.trans ht.symm
        · have he := congrArg Complex.ofReal (hfix j)
          have hcj : ((j.succ.val : ℂ)-1) = (j.val : ℂ) := by simp
          rw [hcj]
          have htj : (j.val : ℂ) = ((j.val : ℝ) : ℂ) := by simp
          rw [htj, hQe, hTe]
          exact he.symm
    refine ⟨S x, F x, hSd x, hS0 x, (hF x).1, ?_, ?_⟩
    · intro t
      have he := congrArg (fun f : ℂ[X] => f.eval (t : ℂ)) hQT
      rw [hQe] at he
      have ht := Polynomial.eval_map_apply (p := (S x).comp (X+C 1)) Complex.ofRealHom t
      have ht' : T.eval (t : ℂ) = Complex.ofReal ((S x).eval (t+1)) := by
        simpa [T, Polynomial.eval_comp] using ht
      rw [ht'] at he
      exact Complex.ofReal_injective he
    · intro t
      simpa [H] using (hF x).2.2.2 t
  obtain ⟨s, a, hsd, hs0, had, hai, han⟩ := hfixed
  let p : ℝ[X] := ∑ k ∈ Finset.range (m+1), C ((a.coeff k).re) * X^k
  have hpd : p.natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    exact (Polynomial.natDegree_C_mul_X_pow_le ((a.coeff k).re) k).trans (by
      have := Finset.mem_range.mp hk
      omega)
  have hpe (t : ℝ) : p.eval t = (a.eval (t : ℂ)).re := by
    rw [Polynomial.eval_eq_sum_range (p := a), had]
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Complex.re_sum, Complex.mul_re,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have heval (t : ℝ) : d.eval t =
      (p.eval t)^2 + (s.eval (t+1))^2 - (s.eval t)^2 := by
    have he := han t
    rw [Complex.normSq_apply, ← hpe t, hai t] at he
    nlinarith
  let r : ℝ[X] := s.comp (X+C 1)
  have hrd : r.natDegree ≤ m := by
    simpa only [r, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C,
      mul_one] using hsd
  have hre : r.coeff m = s.coeff m := by
    by_cases he : s.natDegree = m
    · rw [← he]
      exact Polynomial.coeff_taylor_natDegree 1 s
    · have hlt : s.natDegree < m := lt_of_le_of_ne hsd he
      have hrd' : r.natDegree = s.natDegree := by
        simp only [r, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hrd'.trans_lt hlt),
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  have hpoly : d = p^2+r^2-s^2 := by
    apply Polynomial.funext
    intro t
    simpa [r, Polynomial.eval_comp] using heval t
  have htop := congrArg (fun f : ℝ[X] => f.coeff (m+m)) hpoly
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, pow_two] at htop
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpd hpd,
    Polynomial.coeff_mul_add_eq_of_natDegree_le hrd hrd,
    Polynomial.coeff_mul_add_eq_of_natDegree_le hsd hsd, hre] at htop
  have htop' : (p.coeff m)^2 = d.coeff (2*m) := by
    rw [show 2*m=m+m by omega]
    nlinarith
  have hpos := (exists_monic_lower_factor d m hdegree hpositive).1
  have hpm : p.coeff m ≠ 0 := by
    intro he
    rw [he, zero_pow (by norm_num)] at htop'
    linarith
  exact ⟨p, s, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hpd hpm,
    hsd, hs0, heval, htop', hpos⟩

#print axioms exists_anchored_telescoping_squares

#print axioms exists_monic_lower_factor

end D5.S3.Analytic.AnchoredTelescopingSquares

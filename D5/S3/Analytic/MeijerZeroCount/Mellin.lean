/- GID: D5/S3/Analytic/MeijerZeroCount/Mellin
   generality: G
   mirror-B: D5/B/S3/Analytic/MeijerZeroCount/Mellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Beta, mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals, mathlib/module/Mathlib.Topology.Algebra.Polynomial, mathlib/module/Mathlib.LinearAlgebra.Lagrange, mathlib/module/Mathlib.Data.Nat.Factorial.BigOperators]
   utility: none
   digest: Mellin inversion identifies the Gamma quotient with its Rodrigues kernel. -/

import D5.S3.Analytic.MeijerZeroCount.Rodrigues
import D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Factorial.BigOperators
open Polynomial Finset Complex MeasureTheory Set Filter
open scoped BigOperators Topology
namespace D5.S3.Analytic.MeijerZeroCount.Mellin
open Defs
set_option maxHeartbeats 800000

private theorem gammaQuot_pochhammer (n d : ℕ) (c : ℝ) (s : ℂ)
    (hc : 0 < c) (hs : 0 < s.re) :
    gammaQuot ![(n : ℝ) + c, (n : ℝ) + c] ![c, (2 * n + d : ℕ) + c] s =
      (ascPochhammer ℂ n).eval (s + c) /
        (ascPochhammer ℂ (n + d)).eval (s + c + n) := by
  have hz : 0 < (s + (c : ℂ)).re := by simpa using add_pos hs hc
  have hzn : 0 < (s + (c : ℂ) + n).re := by
    simpa using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg n)
  have hg := Complex.Gamma_ne_zero_of_re_pos hz
  have hgn := Complex.Gamma_ne_zero_of_re_pos hzn
  have havoid (z : ℂ) (hz : 0 < z.re) : ∀ k : ℕ, z ≠ -k := by
    intro k hk
    have := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [← Complex.Gamma_add_nat_div_Gamma_eq _ (havoid _ hz),
    ← Complex.Gamma_add_nat_div_Gamma_eq _ (havoid _ hzn)]
  simp only [gammaQuot, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  push_cast
  have e₁ : (n : ℂ) + c + s = s + c + n := by ring
  have e₂ : 2 * (n : ℂ) + d + c + s = s + c + n + (n + d) := by ring
  rw [e₁, e₂, show (c : ℂ) + s = s + c by ring]
  field_simp

set_option maxHeartbeats 800000
private lemma residue_denominator (N k : ℕ) (hk : k ≤ N) :
    (∏ j ∈ (range (N+1)).erase k, ((j : ℂ) - k)) =
      (-1 : ℂ)^k * (k.factorial : ℂ) * ((N-k).factorial : ℂ) := by
  induction N generalizing k with
  | zero => have : k = 0 := by omega
            subst k
            simp
  | succ N ih =>
    by_cases he : k = N+1
    · subst k
      rw [show range (N+1+1) = insert (N+1) (range (N+1)) from range_add_one,
        erase_insert (show N+1 ∉ range (N+1) by simp)]
      rw [← prod_range_reflect]
      have heq : ∀ j ∈ range (N+1),
          (((N+1-1-j : ℕ) : ℂ) - ((N+1 : ℕ) : ℂ)) = -((j : ℂ)+1) := by
        intro j hj
        rw [Nat.cast_sub (by simpa using Nat.le_of_lt_succ (mem_range.mp hj))]
        push_cast
        ring
      rw [prod_congr rfl heq]
      have hf : (∏ j ∈ range (N+1), ((j : ℂ)+1)) = ((N+1).factorial : ℂ) := by
        exact_mod_cast (prod_range_add_one_eq_factorial (N+1))
      rw [prod_neg, card_range, hf]
      simp
    · have hkN : k ≤ N := by omega
      rw [show range (N+1+1) = insert (N+1) (range (N+1)) from range_add_one,
        erase_insert_of_ne (Ne.symm he), prod_insert (by simp), ih k hkN]
      rw [show N+1-k = (N-k)+1 by omega, Nat.factorial_succ]
      push_cast
      rw [Nat.cast_sub hkN]
      ring

private lemma asc_eval_prod (m : ℕ) (z : ℂ) :
    (ascPochhammer ℂ m).eval z = ∏ j ∈ range m, (z+j) := by
  have h := ascPochhammer_eval_neg_eq_descPochhammer ℂ (-z) m
  rw [neg_neg, descPochhammer_eval_eq_prod_range] at h
  rw [h]
  have he : (∏ j ∈ range m, (-z - (j : ℂ))) =
      (-1 : ℂ)^m * ∏ j ∈ range m, (z+j) := by
    calc
      _ = ∏ j ∈ range m, -(z + (j : ℂ)) := by
        apply prod_congr rfl
        intro j hj
        ring
      _ = _ := by rw [prod_neg, card_range]
  rw [he, ← mul_assoc, ← mul_pow]
  norm_num

private lemma negative_numerator (n k : ℕ) :
    (ascPochhammer ℂ n).eval (-((n+k : ℕ) : ℂ)) =
      (-1 : ℂ)^n * ((n+k).factorial : ℂ) / (k.factorial : ℂ) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  have he : (k.factorial : ℂ) * ((n+k).descFactorial n : ℂ) =
      ((n+k).factorial : ℂ) := by
    exact_mod_cast (by simpa using Nat.factorial_mul_descFactorial (show n ≤ n+k by omega))
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [← he]
  field_simp
  <;> ring


private lemma pochhammer_partial_fractions (n N : ℕ) (hn : n ≤ N) (z : ℂ)
    (hz : ∀ k ∈ range (N+1), z ≠ -(k : ℂ)) :
    (ascPochhammer ℂ n).eval (z-n) / (ascPochhammer ℂ (N+1)).eval z =
      ∑ k ∈ range (N+1),
        ((-1 : ℂ)^(n+k) * ((n+k).factorial : ℂ) /
          ((k.factorial : ℂ)^2 * ((N-k).factorial : ℂ))) / (z+k) := by
  let P : ℂ[X] := (ascPochhammer ℂ n).comp (X-C (n : ℂ))
  let v : ℕ → ℂ := fun k => -(k : ℂ)
  have hv : Set.InjOn v (Finset.range (N+1)) := by
    intro i hi j hj he
    exact_mod_cast (neg_injective he)
  have hdeg : P.degree < ((range (N+1)).card : ℕ) := by
    apply (degree_le_natDegree).trans_lt
    rw [card_range]
    have hd : P.natDegree ≤ n := by
      dsimp [P]
      have hh := natDegree_comp_le (p := ascPochhammer ℂ n) (q := X-C (n : ℂ))
      rw [ascPochhammer_natDegree, natDegree_X_sub_C, mul_one] at hh
      exact hh
    exact_mod_cast (show P.natDegree < N+1 by omega)
  have hinterp := congrArg (Polynomial.eval z) (Lagrange.eq_interpolate hv hdeg)
  rw [Lagrange.eval_interpolate_not_at_node _ hz] at hinterp
  have hnodal : (Lagrange.nodal (range (N+1)) v).eval z =
      (ascPochhammer ℂ (N+1)).eval z := by
    rw [Lagrange.eval_nodal, asc_eval_prod]
    simp [v]
  rw [hnodal] at hinterp
  have hden : (ascPochhammer ℂ (N+1)).eval z ≠ 0 := by
    rw [asc_eval_prod]
    exact prod_ne_zero_iff.mpr (fun k hk => by simpa [sub_eq_add_neg] using sub_ne_zero.mpr (hz k hk))
  have hP : P.eval z = (ascPochhammer ℂ n).eval (z-n) := by simp [P]
  rw [hP, mul_comm] at hinterp
  rw [div_eq_iff hden]
  refine hinterp.trans ?_
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt_succ (mem_range.mp hk)
  have hweight : Lagrange.nodalWeight (range (N+1)) v k =
      ((-1 : ℂ)^k * (k.factorial : ℂ) * ((N-k).factorial : ℂ))⁻¹ := by
    rw [Lagrange.nodalWeight, prod_inv_distrib]
    congr 1
    convert residue_denominator N k hkN using 1
    apply prod_congr rfl
    intro j hj
    simp [v]
    ring
  have hPk : P.eval (v k) = (-1 : ℂ)^n * ((n+k).factorial : ℂ) /
      (k.factorial : ℂ) := by
    simp only [P, eval_comp, eval_sub, eval_X, eval_C, v]
    rw [show -(k : ℂ) - n = -((n+k : ℕ) : ℂ) by push_cast; ring]
    exact negative_numerator n k
  rw [hweight, hPk, pow_add]
  simp only [mul_inv_rev, inv_pow, inv_neg, inv_one, div_eq_mul_inv, sub_neg_eq_add]
  ring_nf
  <;> norm_num <;> ring



/-- The Gamma quotient has the finite residue expansion of the Rodrigues family. -/
theorem gammaQuot_family (n d : ℕ) (c : ℝ) (hd : 2 ≤ d) (hc : 0 < c)
    (s : ℂ) (hs : 0 < s.re) :
    gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] s =
      ∑ k ∈ range (n+d-1+1),
        ((-1 : ℂ)^(n+k) * ((n+k).factorial : ℂ) /
          ((k.factorial : ℂ)^2 * ((n+d-1-k).factorial : ℂ))) / (s+c+n+k) := by
  rw [gammaQuot_pochhammer n d c s hc hs]
  have hp := pochhammer_partial_fractions n (n+d-1) (by omega) (s+c+n) (by
    intro k hk he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re,
      Complex.neg_re] at hre
    have hn := Nat.cast_nonneg (α := ℝ) n
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith)
  have hlen : n+d-1+1 = n+d := by omega
  simpa only [hlen, add_sub_cancel_right] using hp
set_option maxHeartbeats 800000
private lemma shifted_norm_mono (a b t : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖(a : ℂ) + t * I‖ ≤ ‖(b : ℂ) + t * I‖ := by
  rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I]
  exact Real.sqrt_le_sqrt (add_le_add
    ((sq_le_sq₀ ha (ha.trans hab)).mpr hab) le_rfl)

private lemma shifted_norm_ge_one (a t : ℝ) (ha : 1 ≤ a) :
    1 ≤ ‖(a : ℂ) + t * I‖ := by
  exact ha.trans (by simpa using Complex.re_le_norm ((a : ℂ) + t * I))

private lemma shifted_pair_norm (a b t : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    1 + t^2 ≤ ‖(a : ℂ) + t * I‖ * ‖(b : ℂ) + t * I‖ := by
  have hm := shifted_norm_mono a b t (by linarith) hab
  have h := Complex.sq_norm ((a : ℂ) + t * I)
  simp [Complex.normSq_apply] at h
  have hmul := mul_le_mul_of_nonneg_left hm (norm_nonneg ((a : ℂ) + t * I))
  nlinarith

private lemma rational_vertical_bound (n d : ℕ) (hd : 2 ≤ d) (c t : ℝ) (hc : 0 < c) :
    ‖(∏ j ∈ range n, ((1 : ℂ) + t * I + c + j)) /
      (∏ j ∈ range (n+d), ((1 : ℂ) + t * I + c + n + j))‖ ≤
        1 / (1+t^2) := by
  let A : ℝ := ∏ j ∈ range n, ‖((1 : ℂ) + t * I + c + j)‖
  let B : ℝ := ∏ j ∈ range n, ‖((1 : ℂ) + t * I + c + n + j)‖
  let C : ℝ := ∏ j ∈ range d, ‖((1 : ℂ) + t * I + c + n + (n+j : ℕ))‖
  have hA : A ≤ B := by
    apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j hj
    convert shifted_norm_mono (1+c+j) (1+c+n+j) t (by positivity) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) using 1 <;>
      congr 1 <;> push_cast <;> ring
  have hB : 0 < B := by
    apply prod_pos
    intro j hj
    have h := shifted_norm_ge_one (1+c+n+j) t (by have := Nat.cast_nonneg (α := ℝ) n; have := Nat.cast_nonneg (α := ℝ) j; linarith)
    have he : (((1+c+n+j : ℝ) : ℂ) + t * I) =
        (1 : ℂ) + t * I + c + n + j := by push_cast; ring
    rw [he] at h
    linarith
  have hC : 1+t^2 ≤ C := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
    dsimp [C]
    rw [prod_range_add]
    have htail : 1 ≤ ∏ j ∈ range e,
        ‖((1 : ℂ) + t * I + c + n + (n+(2+j) : ℕ))‖ := by
      apply one_le_prod₀
      intro j hj
      convert shifted_norm_ge_one (1+c+n+(n+(2+j))) t (by have := Nat.cast_nonneg (α := ℝ) n; have := Nat.cast_nonneg (α := ℝ) j; linarith) using 1 <;>
        congr 1 <;> push_cast <;> ring
    have hpair : 1+t^2 ≤ ∏ j ∈ range 2,
        ‖((1 : ℂ) + t * I + c + n + (n+j : ℕ))‖ := by
      simp only [prod_range_succ, prod_range_zero, one_mul]
      convert shifted_pair_norm (1+c+2*n) (1+c+2*n+1) t (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith) using 1 <;>
        congr 1 <;> push_cast <;> ring
    have hp : 0 ≤ ∏ j ∈ range 2,
        ‖((1 : ℂ) + t * I + c + n + (n+j : ℕ))‖ := prod_nonneg (by intros; positivity)
    nlinarith
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hC
  rw [norm_div, norm_prod, norm_prod, prod_range_add]
  change A / (B*C) ≤ _
  apply (div_le_div_iff₀ (mul_pos hB hCpos) (by positivity : 0 < 1+t^2)).mpr
  have hh : A * (1+t^2) ≤ B*C :=
    (mul_le_mul_of_nonneg_right hA (by positivity)).trans
      (mul_le_mul_of_nonneg_left hC hB.le)
  simpa using hh

private lemma gammaQuot_vertical_bound (n d : ℕ) (c : ℝ) (hd : 2 ≤ d) (hc : 0 < c)
    (t : ℝ) :
    ‖gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c]
      (1 + t * I)‖ ≤ 1 / (1+t^2) := by
  rw [gammaQuot_pochhammer n d c _ hc (by simp)]
  rw [asc_eval_prod, asc_eval_prod]
  exact rational_vertical_bound n d hd c t hc

private lemma gammaQuot_verticalIntegrable (n d : ℕ) (c : ℝ)
    (hd : 2 ≤ d) (hc : 0 < c) :
    VerticalIntegrable
      (gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c]) 1 := by
  change Integrable (fun t : ℝ =>
    gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] (1+t*I))
  have hm : Measurable (fun t : ℝ =>
      gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] (1+t*I)) := by
    have he : (fun t : ℝ =>
        gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] (1+t*I)) =
        fun t : ℝ => (ascPochhammer ℂ n).eval (1+t*I+c) /
          (ascPochhammer ℂ (n+d)).eval (1+t*I+c+n) := by
      funext t
      exact gammaQuot_pochhammer n d c _ hc (by simp)
    rw [he]
    exact ((ascPochhammer ℂ n).continuous.measurable.comp (by fun_prop)).div
      ((ascPochhammer ℂ (n+d)).continuous.measurable.comp (by fun_prop))
  exact integrable_inv_one_add_sq.mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      simpa only [one_div] using gammaQuot_vertical_bound n d c hd hc t))
open Defs Rodrigues
set_option maxHeartbeats 800000

private lemma hasMellin_f_sum (n d : ℕ) (c : ℝ) (hc : 0 < c) (s : ℂ)
    (hs : 0 < s.re) :
    HasMellin (f n d c) s
      (∑ k ∈ range (n+d-1+1), (coeffA n d k : ℂ) / (s+c+n+k)) := by
  let u := range (n+d-1+1)
  let g : ℕ → ℝ → ℂ := fun k =>
    (coeffA n d k : ℂ) • indicator (Ioc 0 1)
      (fun x : ℝ => (x : ℂ)^(((n : ℝ)+c+k : ℝ) : ℂ))
  have hg (k : ℕ) : HasMellin (g k) s
      ((coeffA n d k : ℂ) / (s+c+n+k)) := by
    have hh := hasMellin_cpow_Ioc (((n : ℝ)+c+k : ℝ) : ℂ)
      (s := s) (by simp only [Complex.ofReal_re]; positivity)
    have hh' := hasMellin_const_smul hh.1 (coeffA n d k : ℂ)
    rw [hh.2] at hh'
    convert hh' using 1 <;> simp only [g, smul_eq_mul] <;> push_cast <;> ring
  have he : (f n d c) =ᵐ[volume.restrict (Ioi 0)] fun x => ∑ k ∈ u, g k x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with x hx hxone
    by_cases hxl : x < 1
    · rw [f_eq_sum n d c x ⟨hx, hxl⟩]
      apply sum_congr rfl
      intro k hk
      dsimp only [g]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx, hxl.le⟩)]
      rw [Complex.ofReal_cpow hx.le]
    · have hxout : x ∉ Ioo (0 : ℝ) 1 := by intro h; exact hxl h.2
      have hxout' : x ∉ Ioc (0 : ℝ) 1 := by
        intro h
        exact hxone (le_antisymm h.2 (le_of_not_gt hxl))
      simp [f, hxout, g, hxout']
  have hsum :=
    D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation.hasMellin_finset_sum
      (u := u) (fun k _ => hg k)
  constructor
  · exact hsum.1.congr (by filter_upwards [he] with x hx; simp [hx])
  · exact (integral_congr_ae (by filter_upwards [he] with x hx; simp [hx])).trans hsum.2

private lemma continuousAt_f (n d : ℕ) (c : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : ContinuousAt (f n d c) x := by
  have hp : ContinuousAt (fun y : ℝ =>
      ((y^((n : ℝ)+c) : ℝ) : ℂ) * (((rodriguesPoly n d).eval y : ℝ) : ℂ)) x :=
    (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const x _ (.inl hx.1.ne'))).mul
      (Complex.continuous_ofReal.continuousAt.comp (rodriguesPoly n d).continuous.continuousAt)
  apply hp.congr
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  simp [f, hy]

/-- The Mellin transform of the compactly supported Rodrigues kernel is the Gamma quotient. -/
theorem mellin_f (n d : ℕ) (c : ℝ) (hd : 2 ≤ d) (hc : 0 < c) (s : ℂ)
    (hs : 0 < s.re) :
    mellin (f n d c) s =
      gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] s := by
  rw [(hasMellin_f_sum n d c hc s hs).2, gammaQuot_family n d c hd hc s hs]
  apply sum_congr rfl
  intro k hk
  congr 1
  simp only [coeffA]
  push_cast
  rfl

/-- Mellin inversion identifies the contour integral with the Rodrigues kernel. -/
theorem meijerG_eq_f (n d : ℕ) (c : ℝ) (hd : 2 ≤ d) (hc : 0 < c)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    meijerG ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x = f n d c x := by
  have hEq (t : ℝ) : mellin (f n d c) (1+t*I) =
      gammaQuot ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] (1+t*I) :=
    mellin_f n d c hd hc _ (by simp)
  have hF : VerticalIntegrable (mellin (f n d c)) 1 := by
    exact (gammaQuot_verticalIntegrable n d c hd hc).congr
      (Eventually.of_forall (fun t => (hEq t).symm))
  have hInv : meijerG ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x =
      mellinInv 1 (mellin (f n d c)) x := by
    unfold meijerG mellinInv
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      dsimp only
      simp only [Complex.ofReal_one]
      rw [hEq t])
  exact hInv.trans (mellinInv_mellin_eq 1 (f n d c) hx.1
    (hasMellin_f_sum n d c hc 1 (by simp)).1 hF (continuousAt_f n d c hx))
end D5.S3.Analytic.MeijerZeroCount.Mellin

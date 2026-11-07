/- GID: D5/S3/Quantum/Analysis/ActualOutputClosedGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/ActualOutputClosedGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Operator.Banach, mathlib/module/Mathlib.Analysis.Normed.Operator.BanachSteinhaus]
   utility: none
   digest: Uniform finite readback on actual outputs forces the same raw relation to be bounded bilinear. -/

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Automatic bounded bilinearity from uniform readback on actual outputs. -/

namespace D5.S3.Quantum.Analysis.ActualOutputClosedGraph

open Filter
open scoped Topology BigOperators
noncomputable section
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One finite formula, chosen before the actual output, with empty and repeated tests allowed. -/
def UniformActualReadback (P : Set (E →L[ℝ] ℝ)) (D : E → E → E) : Prop :=
  ∀ α : P, ∀ η : ℝ, 0 < η →
    ∃ (m : ℕ) (t : Fin m → E) (β : Fin m → P) (c : Fin m → ℝ),
      (∀ j, t j ∈ Set.range (Function.uncurry D)) ∧
      ∀ p ∈ Set.range (Function.uncurry D),
        |α.val p - ∑ j, c j * (β j).val (D p (t j))| ≤ η * ‖p‖

/-- Vanishing against arbitrarily small multiples of a fixed nonnegative constant. -/
private theorem small_bound_zero {x C : ℝ} (hC : 0 ≤ C)
    (h : ∀ η : ℝ, 0 < η → |x| ≤ η * C) : x = 0 := by
  apply abs_eq_zero.mp
  by_contra hn
  have hx : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm hn)
  have hd : 0 < C + 1 := by linarith
  have he : 0 < |x| / (C + 1) / 2 := by positivity
  have hh := h _ he
  have hm : |x| / (C + 1) / 2 * (C + 1) = |x| / 2 := by field_simp
  have hh' : |x| ≤ |x| / (C + 1) / 2 * (C + 1) :=
    hh.trans (mul_le_mul_of_nonneg_left (by linarith) he.le)
  rw [hm] at hh'
  linarith

/-- A finite signed combination of convergent actual outputs is identified by its limiting rows.
The limiting vectors are never supplied to the readback hypothesis. -/
private theorem actual_output_limit (P : Set (E →L[ℝ] ℝ)) (D : E → E → E)
    (hsep : ∀ x y : E, (∀ α : P, α.val x = α.val y) → x = y)
    (hr : UniformActualReadback P D)
    {k : ℕ} (r : Fin k → ℝ) (p : Fin k → ℕ → E) (z : Fin k → E)
    (hp : ∀ i n, p i n ∈ Set.range (Function.uncurry D))
    (hz : ∀ i, Tendsto (p i) atTop (𝓝 (z i)))
    (hrow : ∀ t ∈ Set.range (Function.uncurry D), ∀ β : P,
      Tendsto (fun n => ∑ i, r i * β.val (D (p i n) t)) atTop (𝓝 0)) :
    ∑ i, r i • z i = 0 := by
  apply hsep
  intro α
  rw [map_zero, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply small_bound_zero (C := ∑ i, |r i| * ‖z i‖)
    (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  intro η hη
  obtain ⟨m, t, β, c, ht, ha⟩ := hr α η hη
  have heq (n : ℕ) :
      (∑ i, r i * (α.val (p i n) - ∑ j, c j * (β j).val (D (p i n) (t j)))) =
      (∑ i, r i * α.val (p i n)) - ∑ j, c j * (∑ i, r i * (β j).val (D (p i n) (t j))) := by
    simp_rw [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb (n : ℕ) :
      |(∑ i, r i * α.val (p i n)) - ∑ j, c j * (∑ i, r i * (β j).val (D (p i n) (t j)))| ≤
        η * ∑ i, |r i| * ‖p i n‖ := by
    rw [← heq]
    calc
      _ ≤ ∑ i, |r i * (α.val (p i n) - ∑ j, c j * (β j).val (D (p i n) (t j)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |r i| * |α.val (p i n) - ∑ j, c j * (β j).val (D (p i n) (t j))| := by
        simp_rw [abs_mul]
      _ ≤ ∑ i, |r i| * (η * ‖p i n‖) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha _ (hp i n)) (abs_nonneg _)
      _ = η * ∑ i, |r i| * ‖p i n‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hl : Tendsto (fun n => (∑ i, r i * α.val (p i n)) -
      ∑ j, c j * (∑ i, r i * (β j).val (D (p i n) (t j)))) atTop
      (𝓝 (∑ i, r i * α.val (z i))) := by
    have h1 := tendsto_finsetSum Finset.univ (fun i _ =>
      ((tendsto_const_nhds (x := r i)).mul ((α.val.continuous.tendsto _).comp (hz i))))
    have h2 := tendsto_finsetSum Finset.univ (fun j _ =>
      (tendsto_const_nhds (x := c j)).mul (hrow (t j) (ht j) (β j)))
    simpa using h1.sub h2
  have hu : Tendsto (fun n => η * ∑ i, |r i| * ‖p i n‖) atTop
      (𝓝 (η * ∑ i, |r i| * ‖z i‖)) :=
    tendsto_const_nhds.mul (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_const_nhds.mul (hz i).norm)
  exact le_of_tendsto_of_tendsto' hl.abs hu hb

private theorem reflect_actual_relation (P : Set (E →L[ℝ] ℝ)) (D : E → E → E)
    (hsep : ∀ x y : E, (∀ α : P, α.val x = α.val y) → x = y)
    (hr : UniformActualReadback P D) {k : ℕ} (r : Fin k → ℝ) (p : Fin k → E)
    (hp : ∀ i, p i ∈ Set.range (Function.uncurry D))
    (hrow : ∀ t ∈ Set.range (Function.uncurry D), ∑ i, r i • D (p i) t = 0) :
    ∑ i, r i • p i = 0 := by
  apply actual_output_limit P D hsep hr r (fun i _ => p i) p (fun i _ => hp i)
    (fun _ => tendsto_const_nhds)
  intro t ht β
  have hh := congrArg β.val (hrow t ht)
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hh
  simpa only [hh] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Cyclic elimination uses no input linearity of the raw relation. -/
private theorem raw_cycle (P : Set (E →L[ℝ] ℝ)) (S : E →L[ℝ] E →L[ℝ] E)
    (D : E → E → E)
    (hsep : ∀ x y : E, (∀ α : P, α.val x = α.val y) → x = y)
    (hs : ∀ a b, S a b = S b a) (hd : ∀ a b, D a b = -D b a)
    (hassoc : ∀ a b c, S (S a b) c - S a (S b c) = D (D a b) c - D a (D b c))
    (a b c : E) : D (D a b) c = S b (S a c) - S a (S b c) := by
  apply hsep
  intro α
  have h1 := congrArg α.val (hassoc a b c)
  have h2 := congrArg α.val (hassoc b c a)
  have h3 := congrArg α.val (hassoc c a b)
  rw [hs (S a b) c, hd a (D b c)] at h1
  rw [hs (S b c) a, hs c a, hd b (D c a)] at h2
  rw [hs (S c a) b, hs c a, hd c (D a b)] at h3
  simp only [map_sub, map_neg] at h1 h2 h3 ⊢
  linarith

/-- On the original Banach carrier, actual conjugacy, the real associator and uniform actual-output
readback force the same total function to be real bilinear with one finite nonnegative joint bound.
Order-unit structure and positivity of the separating continuous evaluations are unnecessary here. -/
theorem raw_relation_bounded_bilinear [CompleteSpace E]
    (P : Set (E →L[ℝ] ℝ)) (S : E →L[ℝ] E →L[ℝ] E) (D : E → E → E)
    (hsep : ∀ x y : E, (∀ α : P, α.val x = α.val y) → x = y)
    (hs : ∀ a b, S a b = S b a)
    (hconj : ∀ (α : P) (a b : E),
      (α.val (S b a) : ℂ) - Complex.I * (α.val (D b a) : ℂ) =
        star ((α.val (S a b) : ℂ) - Complex.I * (α.val (D a b) : ℂ)))
    (hassoc : ∀ a b c, S (S a b) c - S a (S b c) = D (D a b) c - D a (D b c))
    (hr : UniformActualReadback P D) :
    ∃ B : E →L[ℝ] E →L[ℝ] E, (∀ a b, B a b = D a b) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ a b, ‖D a b‖ ≤ K * ‖a‖ * ‖b‖ := by
  have hd (a b : E) : D a b = -D b a := by
    apply hsep
    intro α
    have hh := congrArg Complex.im (hconj α a b)
    simpa using hh.symm
  have hc := raw_cycle P S D hsep hs hd hassoc
  have hadd (a b c : E) : D (a + b) c = D a c + D b c := by
    have hh := reflect_actual_relation P D hsep hr (![1, -1, -1] : Fin 3 → ℝ)
      ![D (a + b) c, D a c, D b c] (by
        intro i
        fin_cases i
        · exact ⟨(a + b, c), rfl⟩
        · exact ⟨(a, c), rfl⟩
        · exact ⟨(b, c), rfl⟩) (by
        intro t _
        simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, one_smul, neg_smul]
        simp only [hc, map_add, ContinuousLinearMap.add_apply]
        abel)
    simp [Fin.sum_univ_succ] at hh
    apply sub_eq_zero.mp
    calc
      D (a + b) c - (D a c + D b c) = D (a + b) c + (-D a c + -D b c) := by abel
      _ = 0 := hh
  have hsmul (r : ℝ) (a c : E) : D (r • a) c = r • D a c := by
    have hh := reflect_actual_relation P D hsep hr (![1, -r] : Fin 2 → ℝ)
      ![D (r • a) c, D a c] (by
        intro i
        fin_cases i
        · exact ⟨(r • a, c), rfl⟩
        · exact ⟨(a, c), rfl⟩) (by
        intro t _
        simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, one_smul, neg_smul]
        simp only [hc, map_smul, ContinuousLinearMap.smul_apply, smul_sub]
        abel)
    have hz : D (r • a) c - r • D a c = 0 := by
      simpa [Fin.sum_univ_succ, sub_eq_add_neg] using hh
    exact sub_eq_zero.mp hz
  have hadd2 (a b c : E) : D a (b + c) = D a b + D a c := by
    rw [hd a (b + c), hadd, neg_add, ← hd a b, ← hd a c]
  have hsmul2 (r : ℝ) (a b : E) : D a (r • b) = r • D a b := by
    rw [hd a (r • b), hsmul, ← smul_neg, ← hd a b]
  let L : E →ₗ[ℝ] E →ₗ[ℝ] E := LinearMap.mk₂ ℝ D hadd hsmul hadd2 hsmul2
  have hclosed (a : E) : Continuous (L a) := by
    apply LinearMap.continuous_of_seq_closed_graph
    intro b x y hx hy
    have hh := actual_output_limit P D hsep hr (![1, -1] : Fin 2 → ℝ)
      ![fun n => D a (b n), fun _ => D a x] ![y, D a x] (by
        intro i n
        fin_cases i
        · exact ⟨(a, b n), rfl⟩
        · exact ⟨(a, x), rfl⟩) (by
        intro i
        fin_cases i
        · exact hy
        · exact tendsto_const_nhds) (by
        intro t _ β
        have hv : Tendsto (fun n => S (b n) (S a t) - S a (S (b n) t)) atTop
            (𝓝 (S x (S a t) - S a (S x t))) := by
          exact (((S.flip (S a t)).continuous.tendsto _).comp hx).sub
            (((S a).continuous.tendsto _).comp (((S.flip t).continuous.tendsto _).comp hx))
        have hw := ((β.val.continuous.tendsto _).comp hv).sub
          (tendsto_const_nhds (x := β.val (S x (S a t) - S a (S x t))))
        have hw0 : Tendsto (fun n =>
            β.val (S (b n) (S a t) - S a (S (b n) t)) -
              β.val (S x (S a t) - S a (S x t))) atTop (𝓝 0) := by
          simpa using hw
        convert hw0 using 1
        funext n
        simp [Fin.sum_univ_succ, hc, map_sub]
        <;> ring)
    have hz : y - D a x = 0 := by simpa [Fin.sum_univ_succ, sub_eq_add_neg] using hh
    exact sub_eq_zero.mp hz
  let A (a : E) : E →L[ℝ] E := ⟨L a, hclosed a⟩
  have hA (a b : E) : A a b = D a b := rfl
  let I := {a : E // ‖a‖ ≤ 1}
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun a : I => A a.val) (by
    intro b
    refine ⟨‖A b‖, ?_⟩
    intro a
    rw [hA, hd, norm_neg, ← hA]
    exact (A b).le_opNorm a.val |>.trans (by
      simpa using mul_le_mul_of_nonneg_left a.property (norm_nonneg (A b))))
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  have hb (a b : E) : ‖D a b‖ ≤ K * ‖a‖ * ‖b‖ := by
    by_cases ha : a = 0
    · subst a
      simp [← hA, A]
    have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hu : ‖(‖a‖⁻¹ : ℝ) • a‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
    have hc' := (A ((‖a‖⁻¹ : ℝ) • a)).le_opNorm b
    have hop : ‖A ((‖a‖⁻¹ : ℝ) • a)‖ ≤ K :=
      (hC ⟨_, hu⟩).trans (le_max_left _ _)
    have hv : ‖D ((‖a‖⁻¹ : ℝ) • a) b‖ ≤ K * ‖b‖ :=
      hc'.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
    rw [hsmul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)] at hv
    have hv' := mul_le_mul_of_nonneg_left hv (norm_nonneg a)
    calc
      ‖D a b‖ = ‖a‖ * (‖a‖⁻¹ * ‖D a b‖) := by rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      _ ≤ ‖a‖ * (K * ‖b‖) := hv'
      _ = K * ‖a‖ * ‖b‖ := by ring
  exact ⟨L.mkContinuous₂ K hb, (fun _ _ => rfl), K, hK, hb⟩

#print axioms raw_relation_bounded_bilinear

end
end D5.S3.Quantum.Analysis.ActualOutputClosedGraph


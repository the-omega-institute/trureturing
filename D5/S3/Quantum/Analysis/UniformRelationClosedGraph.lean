/- GID: D5/S3/Quantum/Analysis/UniformRelationClosedGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/UniformRelationClosedGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Operator.Banach, mathlib/module/Mathlib.Analysis.Normed.Operator.BanachSteinhaus]
   utility: none
   digest: Uniform finite readouts on actual outputs recover bilinearity and Banach graph bounds. -/

module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic

/-! A uniform approximation on the actual range of a total relation controls graph limits
without applying the approximation to a limit outside that range. No regularity of the
relation is assumed. The cone and unit of an order-unit application are not needed. -/

@[expose] public section
noncomputable section
open Filter Topology
open scoped BigOperators

namespace D5.S3.Quantum.Analysis.UniformRelationClosedGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual range of the original total map, without taking a span or closure. -/
def outputs (D : E → E → E) : Set E := Set.range (Function.uncurry D)

/-- One finite formula, chosen before the output, uniformly approximates all actual outputs.
The finite index may be empty; tests and evaluations may repeat. -/
def UniformReadout (P : Set (E →L[ℝ] ℝ)) (D : E → E → E) : Prop :=
  ∀ α ∈ P, ∀ η : ℝ, 0 < η → ∃ (m : ℕ) (t : Fin m → E)
    (β : Fin m → E →L[ℝ] ℝ) (c : Fin m → ℝ),
    (∀ j, t j ∈ outputs D) ∧ (∀ j, β j ∈ P) ∧
    ∀ p ∈ outputs D, |α p - ∑ j, c j * β j (D p (t j))| ≤ η * ‖p‖

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma actual (D : E → E → E) (a b : E) : D a b ∈ outputs D :=
  ⟨(a,b), rfl⟩

private lemma small_error_zero {x M : ℝ} (hM : 0 ≤ M)
    (h : ∀ η : ℝ, 0 < η → |x| ≤ η * M) : x = 0 := by
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg x)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hp : 0 < M + 1 := by linarith
  have he := h (ε / (M + 1)) (div_pos hε hp)
  have hc : ε / (M + 1) * (M + 1) = ε := div_mul_cancel₀ _ hp.ne'
  have hn : 0 ≤ ε / (M + 1) := le_of_lt (div_pos hε hp)
  simp only [zero_add]
  nlinarith

private lemma separate {P : Set (E →L[ℝ] ℝ)}
    (hs : ∀ x : E, (∀ α ∈ P, α x = 0) → x = 0) {x y : E}
    (h : ∀ α ∈ P, α x = α y) : x = y := by
  apply sub_eq_zero.mp
  apply hs
  intro α hα
  simp only [map_sub, h α hα, sub_self]

private lemma skew {P : Set (E →L[ℝ] ℝ)} (S : E →L[ℝ] E →L[ℝ] E)
    (D : E → E → E) (hs : ∀ x : E, (∀ α ∈ P, α x = 0) → x = 0)
    (hc : ∀ α ∈ P, ∀ a b : E,
      (α (S b a) : ℂ) - Complex.I * (α (D b a) : ℂ) =
        star ((α (S a b) : ℂ) - Complex.I * (α (D a b) : ℂ))) :
    ∀ a b, D a b = -D b a := by
  intro a b
  apply separate hs
  intro α hα
  have h := congrArg Complex.im (hc α hα a b)
  simp at h
  simp only [map_neg]
  linarith

private lemma nested {P : Set (E →L[ℝ] ℝ)} (S : E →L[ℝ] E →L[ℝ] E)
    (D : E → E → E) (hs : ∀ x : E, (∀ α ∈ P, α x = 0) → x = 0)
    (hS : ∀ a b, S a b = S b a) (hD : ∀ a b, D a b = -D b a)
    (hR : ∀ a b c, S (S a b) c - S a (S b c) =
      D (D a b) c - D a (D b c)) (a b c : E) :
    D (D a b) c = S b (S a c) - S a (S b c) := by
  apply separate hs
  intro α hα
  have h₁ := congrArg α (hR a b c)
  have h₂ := congrArg α (hR b c a)
  have h₃ := congrArg α (hR c a b)
  rw [hD a (D b c)] at h₁
  rw [hD b (D c a)] at h₂
  rw [hD c (D a b)] at h₃
  simp only [map_sub, map_neg] at *
  rw [hS (S a b) c, hS (S b c) a, hS (S c a) b, hS c a] at *
  linarith

private lemma finite_reflection {P : Set (E →L[ℝ] ℝ)} (D : E → E → E)
    (hs : ∀ x : E, (∀ α ∈ P, α x = 0) → x = 0) (hr : UniformReadout P D)
    {n : ℕ} (p : Fin n → E) (r : Fin n → ℝ) (hp : ∀ i, p i ∈ outputs D)
    (hz : ∀ t ∈ outputs D, ∑ i, r i • D (p i) t = 0) :
    ∑ i, r i • p i = 0 := by
  apply hs
  intro α hα
  simp only [map_sum, map_smul, smul_eq_mul]
  apply small_error_zero (show 0 ≤ ∑ i, |r i| * ‖p i‖ from
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  intro η hη
  obtain ⟨m,t,β,c,ht,hβ,happrox⟩ := hr α hα η hη
  have hz' (j : Fin m) : ∑ i, r i * β j (D (p i) (t j)) = 0 := by
    have h := congrArg (β j) (hz (t j) (ht j))
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using h
  have hsum : ∑ i, r i * (∑ j, c j * β j (D (p i) (t j))) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [show ∀ i j, r i * (c j * β j (D (p i) (t j))) =
      c j * (r i * β j (D (p i) (t j))) by intros; ring,
      ← Finset.mul_sum, hz', mul_zero, Finset.sum_const_zero]
  calc
    |∑ i, r i * α (p i)| =
        |∑ i, r i * (α (p i) - ∑ j, c j * β j (D (p i) (t j)))| := by
          congr 1
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          rw [hsum, sub_zero]
    _ ≤ ∑ i, |r i * (α (p i) - ∑ j, c j * β j (D (p i) (t j)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |r i| * (η * ‖p i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (happrox (p i) (hp i)) (abs_nonneg _)
    _ = η * ∑ i, |r i| * ‖p i‖ := by rw [Finset.mul_sum]; congr 1; funext i; ring

private lemma recover_linear {P : Set (E →L[ℝ] ℝ)} (S : E →L[ℝ] E →L[ℝ] E)
    (D : E → E → E) (hs : ∀ x : E, (∀ α ∈ P, α x = 0) → x = 0)
    (hr : UniformReadout P D)
    (hn : ∀ a b c, D (D a b) c = S b (S a c) - S a (S b c)) :
    (∀ a b c, D (a+b) c = D a c + D b c) ∧
    (∀ (r : ℝ) a b, D (r • a) b = r • D a b) := by
  constructor
  · intro a b c
    have h := finite_reflection D hs hr ![D (a+b) c, D a c, D b c]
      ![(1:ℝ),-1,-1] (by intro i; fin_cases i <;> exact actual D _ _) (by
        intro t ht
        simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, one_smul, neg_smul]
        simp only [hn, map_add, add_apply]
        module)
    exact sub_eq_zero.mp (by
      simpa [Fin.sum_univ_succ, sub_eq_add_neg, neg_add, add_assoc, add_comm, add_left_comm] using h)
  · intro r a b
    have h := finite_reflection D hs hr ![D (r • a) b, D a b]
      ![(1:ℝ),-r] (by intro i; fin_cases i <;> exact actual D _ _) (by
        intro t ht
        simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, one_smul, neg_smul]
        simp only [hn, map_smul, smul_apply]
        module)
    exact sub_eq_zero.mp (by simpa [Fin.sum_univ_succ, sub_eq_add_neg] using h)

private def row (D : E → E → E)
    (ha : ∀ a b c, D (a+b) c = D a c + D b c)
    (hm : ∀ (r : ℝ) a b, D (r • a) b = r • D a b)
    (hD : ∀ a b, D a b = -D b a) (a : E) : E →ₗ[ℝ] E where
  toFun := D a
  map_add' b c := by rw [hD a (b+c), ha, neg_add, ← hD a b, ← hD a c]
  map_smul' r b := by
    change D a (r • b) = r • D a b
    rw [hD a (r • b), hm, ← smul_neg, ← hD a b]

private lemma graph_limit {P : Set (E →L[ℝ] ℝ)} (S : E →L[ℝ] E →L[ℝ] E)
    (D : E → E → E) (hs : ∀ x : E, (∀ α ∈ P, α x = 0) → x = 0)
    (hr : UniformReadout P D)
    (hn : ∀ a b c, D (D a b) c = S b (S a c) - S a (S b c))
    (a : E) (b : ℕ → E) (x y : E)
    (hb : Tendsto b atTop (𝓝 x)) (hy : Tendsto (fun n => D a (b n)) atTop (𝓝 y)) :
    y = D a x := by
  apply separate hs
  intro α hα
  apply sub_eq_zero.mp
  apply small_error_zero (add_nonneg (norm_nonneg y) (norm_nonneg (D a x)))
  intro η hη
  obtain ⟨m,t,β,c,ht,hβ,happrox⟩ := hr α hα η hη
  let f : E → ℝ := fun z => ∑ j, c j * β j (S z (S a (t j)) - S a (S z (t j)))
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul ((β j).continuous.comp
      (((S.flip (S a (t j))).continuous).sub
        ((S a).continuous.comp (S.flip (t j)).continuous)))
  have hpn (n : ℕ) : |α (D a (b n)) - f (b n)| ≤ η * ‖D a (b n)‖ := by
    simpa only [f, ← hn] using happrox (D a (b n)) (actual D _ _)
  have hq : |α (D a x) - f x| ≤ η * ‖D a x‖ := by
    simpa only [f, ← hn] using happrox (D a x) (actual D _ _)
  have hlim : |α y - f x| ≤ η * ‖y‖ :=
    le_of_tendsto_of_tendsto (((α.continuous.tendsto y).comp hy).sub
      ((hf.tendsto x).comp hb)).abs (tendsto_const_nhds.mul hy.norm)
      (Filter.Eventually.of_forall hpn)
  calc
    |α y - α (D a x)| ≤ |α y - f x| + |α (D a x) - f x| := by
      simpa only [abs_sub_comm (f x) (α (D a x))] using
        abs_sub_le (α y) (f x) (α (D a x))
    _ ≤ η * ‖y‖ + η * ‖D a x‖ := add_le_add hlim hq
    _ = η * (‖y‖ + ‖D a x‖) := by ring

/-- Actual conjugacy, the real rebracketing identity and a uniform finite readout on
actual outputs force the same total map to be a bounded real bilinear map. -/
theorem bilinear_bounded [CompleteSpace E] (P : Set (E →L[ℝ] ℝ))
    (S : E →L[ℝ] E →L[ℝ] E) (D : E → E → E)
    (hs : ∀ x : E, (∀ α ∈ P, α x = 0) → x = 0)
    (hS : ∀ a b, S a b = S b a)
    (hc : ∀ α ∈ P, ∀ a b : E,
      (α (S b a) : ℂ) - Complex.I * (α (D b a) : ℂ) =
        star ((α (S a b) : ℂ) - Complex.I * (α (D a b) : ℂ)))
    (hR : ∀ a b c, S (S a b) c - S a (S b c) =
      D (D a b) c - D a (D b c)) (hr : UniformReadout P D) :
    ∃ B : E →L[ℝ] E →L[ℝ] E, (∀ a b, B a b = D a b) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ a b, ‖D a b‖ ≤ K * ‖a‖ * ‖b‖ := by
  have hD := skew S D hs hc
  have hn := nested S D hs hS hD hR
  obtain ⟨ha,hm⟩ := recover_linear S D hs hr hn
  let R : E → E →L[ℝ] E := fun a =>
    ⟨row D ha hm hD a, (row D ha hm hD a).continuous_of_seq_closed_graph
      (fun b x y hb hy => graph_limit S D hs hr hn a b x y hb hy)⟩
  let F : E →ₗ[ℝ] E →L[ℝ] E :=
    { toFun := R
      map_add' := fun a b => by ext c; exact ha a b c
      map_smul' := fun r a => by ext b; exact hm r a b }
  have hpoint (b : E) : ∃ C : ℝ, ∀ a : {a : E // ‖a‖ ≤ 1}, ‖R a b‖ ≤ C := by
    refine ⟨‖R b‖, fun a => ?_⟩
    change ‖D a b‖ ≤ ‖R b‖
    rw [hD, norm_neg]
    exact ((R b).le_opNorm a).trans
      ((mul_le_mul_of_nonneg_left a.property (norm_nonneg _)).trans_eq (mul_one _))
  obtain ⟨K,hK⟩ := banach_steinhaus (g := fun a : {a : E // ‖a‖ ≤ 1} => R a) hpoint
  have hFb : ∀ a : E, ‖F a‖ ≤ max K 0 * ‖a‖ := by
    intro a
    by_cases h0 : a = 0
    · simp [h0]
    have hn0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    let v : {a : E // ‖a‖ ≤ 1} := ⟨‖a‖⁻¹ • a, by simp [norm_smul, norm_inv, hn0]⟩
    have hv : ‖a‖ • (v : E) = a := by simp [v, smul_smul, hn0]
    calc
      ‖F a‖ = ‖F (‖a‖ • (v : E))‖ := by rw [hv]
      _ = ‖a‖ * ‖F (v : E)‖ := by rw [map_smul, norm_smul, norm_norm]
      _ ≤ ‖a‖ * max K 0 :=
        mul_le_mul_of_nonneg_left ((hK v).trans (le_max_left _ _)) (norm_nonneg _)
      _ = max K 0 * ‖a‖ := mul_comm _ _
  let B := F.mkContinuous (max K 0) hFb
  refine ⟨B, fun a b => rfl, max K 0, le_max_right _ _, fun a b => ?_⟩
  exact ((R a).le_opNorm b).trans (mul_le_mul_of_nonneg_right (hFb a) (norm_nonneg _))

end D5.S3.Quantum.Analysis.UniformRelationClosedGraph

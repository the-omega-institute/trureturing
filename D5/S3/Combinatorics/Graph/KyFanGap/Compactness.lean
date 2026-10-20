/- GID: D5/S3/Combinatorics/Graph/KyFanGap/Compactness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/Compactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Sequences, mathlib/module/Mathlib.Topology.Instances.Real.Lemmas, mathlib/module/Mathlib.Topology.Instances.Matrix, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Compactness separates bounded weighted symmetric models from nonsquare constant row sums. -/

import D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-! The two nonnegative defects retain the same weights and symmetric matrix.
Zero-weight nodes are removed only after both defects vanish. -/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace D5.S3.Combinatorics.Graph.KyFanGap

/-- The weighted sign defect and the weighted constant-row-sum defect. -/
def modelDefect {R : ℕ} (p : Fin R → ℝ) (S : Matrix (Fin R) (Fin R) ℝ)
    (c : ℝ) : ℝ :=
  (∑ a, ∑ b, p a * p b * (S a b ^ 2 - 1) ^ 2) +
    ∑ a, p a * ((∑ b, S a b * p b) - c) ^ 2

private theorem modelDefect_nonneg {R : ℕ} (p : Fin R → ℝ)
    (S : Matrix (Fin R) (Fin R) ℝ) (c : ℝ) (hp : ∀ a, 0 ≤ p a) :
    0 ≤ modelDefect p S c := by
  unfold modelDefect
  exact add_nonneg
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (mul_nonneg (hp a) (hp b)) (sq_nonneg _))
    (Finset.sum_nonneg fun a _ => mul_nonneg (hp a) (sq_nonneg _))

private theorem modelDefect_ne_zero {R k : ℕ} (hk : ¬ IsSquare k)
    (p : Fin R → ℝ) (S : Matrix (Fin R) (Fin R) ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (hS : S.IsSymm) :
    modelDefect p S (1 / Real.sqrt k) ≠ 0 := by
  classical
  intro hz
  have hf : (∑ a, ∑ b, p a * p b * (S a b ^ 2 - 1) ^ 2) = 0 := by
    have h1 : 0 ≤ ∑ a, ∑ b, p a * p b * (S a b ^ 2 - 1) ^ 2 :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
        mul_nonneg (mul_nonneg (hp a) (hp b)) (sq_nonneg _)
    have h2 : 0 ≤ ∑ a, p a * ((∑ b, S a b * p b) - 1 / Real.sqrt k) ^ 2 :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hp a) (sq_nonneg _)
    change _ + _ = 0 at hz
    linarith
  have hg : (∑ a, p a * ((∑ b, S a b * p b) - 1 / Real.sqrt k) ^ 2) = 0 := by
    change _ + _ = 0 at hz
    linarith
  have hsign (a b : Fin R) (ha : 0 < p a) (hb : 0 < p b) :
      S a b = 1 ∨ S a b = -1 := by
    have hfa := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun b _ =>
        mul_nonneg (mul_nonneg (hp a) (hp b)) (sq_nonneg _))).mp hf a
        (Finset.mem_univ a)
    have hfab := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => mul_nonneg (mul_nonneg (hp a) (hp b)) (sq_nonneg _))).mp hfa b
        (Finset.mem_univ b)
    have hs : S a b ^ 2 - 1 = 0 :=
      (sq_eq_zero_iff).mp ((mul_eq_zero.mp hfab).resolve_left (mul_pos ha hb).ne')
    have hh : (S a b - 1) * (S a b + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hh with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hrow (a : Fin R) (ha : 0 < p a) :
      (∑ b, S a b * p b) = 1 / Real.sqrt k := by
    have hga := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => mul_nonneg (hp a) (sq_nonneg _))).mp hg a (Finset.mem_univ a)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hga).resolve_left ha.ne'))
  let I := {a : Fin R // 0 < p a}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hrestrict (f : Fin R → ℝ) :
      (∑ b : Fin (Fintype.card I), f (e b).val * p (e b).val) =
        ∑ b, f b * p b := by
    rw [e.sum_comp (fun b : I => f b.val * p b.val)]
    apply Fintype.sum_of_injective (fun b : I => b.val) Subtype.val_injective
    · intro b hb
      have hpb : p b = 0 := le_antisymm (not_lt.mp (fun h => hb ⟨⟨b, h⟩, rfl⟩)) (hp b)
      simp [hpb]
    · intro b
      rfl
  let Q : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℚ :=
    fun a b => if S (e a).val (e b).val = 1 then 1 else -1
  have hQ (a b : Fin (Fintype.card I)) :
      (Q a b : ℝ) = S (e a).val (e b).val := by
    rcases hsign (e a).val (e b).val (e a).property (e b).property with h | h
    · norm_num [Q, h]
    · norm_num [Q, h]
  have hQsym : Q.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    apply Rat.cast_injective (α := ℝ)
    rw [hQ, hQ]
    exact hS.apply _ _
  have hpsum : (∑ a, p (e a).val) = 1 := by
    simpa only [one_mul, hsum] using hrestrict (fun _ => 1)
  apply RationalRowSum.nonsquare_row_sum_ne Q hQsym hk (fun a => p (e a).val) hpsum
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one]
  simp_rw [hQ]
  rw [hrestrict]
  exact hrow (e a).val (e a).property

private theorem continuous_modelDefect (R : ℕ) (c : ℝ) :
    Continuous (fun z : (Fin R → ℝ) × Matrix (Fin R) (Fin R) ℝ =>
      modelDefect z.1 z.2 c) := by
  unfold modelDefect
  fun_prop

/-- At fixed order and a fixed entry bound, the two defects have a strictly
positive common lower bound for a nonsquare inverse-square-root row sum. -/
theorem exists_model_defect_gap (R : ℕ) (M : ℝ) {k : ℕ} (hk : ¬ IsSquare k) :
    ∃ η > 0, ∀ (p : Fin R → ℝ) (S : Matrix (Fin R) (Fin R) ℝ),
      (∀ a, 0 ≤ p a) → (∑ a, p a) = 1 → S.IsSymm →
      (∀ a b, |S a b| ≤ M) → η ≤ modelDefect p S (1 / Real.sqrt k) := by
  classical
  by_contra h
  push Not at h
  have hex (j : ℕ) :
      ∃ (p : Fin R → ℝ) (S : Matrix (Fin R) (Fin R) ℝ),
        (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧ S.IsSymm ∧
        (∀ a b, |S a b| ≤ M) ∧
        modelDefect p S (1 / Real.sqrt k) < 1 / ((j : ℝ) + 1) :=
    h (1 / ((j : ℝ) + 1)) (by positivity)
  choose p S hp hsum hsym hbound hsmall using hex
  letI : FirstCountableTopology (Matrix (Fin R) (Fin R) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin R → Fin R → ℝ))
  let K : Set ((Fin R → ℝ) × Matrix (Fin R) (Fin R) ℝ) :=
    {p | ∀ a, p a ∈ Set.Icc (0 : ℝ) 1} ×ˢ (Set.Icc (-M) M).matrix
  have hK : IsCompact K :=
    (isCompact_pi_infinite (fun _ => isCompact_Icc)).prod
      isCompact_Icc.matrix
  have hmem (j : ℕ) : (p j, S j) ∈ K := by
    constructor
    · intro a
      refine ⟨hp j a, ?_⟩
      calc
        p j a ≤ ∑ b, p j b := Finset.single_le_sum (fun b _ => hp j b) (Finset.mem_univ a)
        _ = 1 := hsum j
    · intro a b
      exact abs_le.mp (hbound j a b)
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hpz : ∀ a, 0 ≤ z.1 a := fun a => (hz.1 a).1
  have hsumz : ∑ a, z.1 a = 1 := by
    have ht := (show Continuous (fun z : (Fin R → ℝ) × Matrix (Fin R) (Fin R) ℝ =>
      ∑ a, z.1 a) by fun_prop).continuousAt.tendsto.comp hlim
    have ht' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (∑ a, z.1 a)) :=
      ht.congr (fun j => hsum (φ j))
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hsymz : z.2.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    have h1 := (show Continuous (fun z : (Fin R → ℝ) × Matrix (Fin R) (Fin R) ℝ =>
      z.2 a b) by fun_prop).continuousAt.tendsto.comp hlim
    have h2 := (show Continuous (fun z : (Fin R → ℝ) × Matrix (Fin R) (Fin R) ℝ =>
      z.2 b a) by fun_prop).continuousAt.tendsto.comp hlim
    apply tendsto_nhds_unique h2
    exact h1.congr (fun j => (hsym (φ j)).apply _ _)
  have hzero : Tendsto (fun j => modelDefect (p j) (S j) (1 / Real.sqrt k)) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => modelDefect_nonneg _ _ _ (hp j))
      (fun j => (hsmall j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hdz : modelDefect z.1 z.2 (1 / Real.sqrt k) = 0 := by
    apply tendsto_nhds_unique
      ((continuous_modelDefect R (1 / Real.sqrt k)).continuousAt.tendsto.comp hlim)
    exact hzero.comp hφ.tendsto_atTop
  exact modelDefect_ne_zero hk z.1 z.2 hpz hsumz hsymz hdz

end D5.S3.Combinatorics.Graph.KyFanGap

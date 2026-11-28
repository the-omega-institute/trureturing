/- GID: D5/S3/Combinatorics/IntervalReconstruction/Occurrences/MonotoneIntervalStability
   generality: G
   mirror-B: none(waiver:covered-by-monotone-interval-stability-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform stability of the full inclusive interval-occurrence observation map on nonnegative nondecreasing real tuples. -/

module

public import D5.S3.Combinatorics.IntervalReconstruction.Occurrences.MonotoneIntervalReconstruction
public import D5.S3.Geometry.Convex.Cone.ErrorBound
public import Mathlib.Data.Fintype.BigOperators

/-!
Uniform stability of the full inclusive interval-occurrence observation map on
nonnegative nondecreasing real tuples. The constant is uniform over all tuples,
noise levels, and occurrence permutations of a fixed length.

The proof applies the homogeneous Hoffman bound of the Tau Ceti contributors to
the cone cut out by monotonicity, nonnegativity, and exact matched observations.
Exact reconstruction is supplied by `MonotoneIntervalReconstruction.reconstruct`.
No algorithm or optimal constant is asserted.
-/

@[expose] public section

namespace Omega.MonotoneIntervalStability

open Finset MonotoneIntervalReconstruction

/-- Actual endpoint occurrences, retaining ties in their observed values. -/
abbrev Occurrence (n : ℕ) := {p // p ∈ intervals n}

private abbrev PairSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- Extend a finite tuple by zero outside its actual index range. -/
def extend {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then a ⟨k, h⟩ else 0

private def coordinate {n : ℕ} (side : Bool) (i : Fin n) :
    PairSpace n →ₗ[ℝ] ℝ where
  toFun w := (if side then w.2 else w.1) i
  map_add' _ _ := by cases side <;> rfl
  map_smul' _ _ := by cases side <;> rfl

private noncomputable def intervalForm {n : ℕ} (side : Bool) (p : ℕ × ℕ) :
    PairSpace n →ₗ[ℝ] ℝ :=
  ∑ k ∈ Icc p.1 p.2, if h : k < n then coordinate side ⟨k, h⟩ else 0

private theorem intervalForm_apply {n : ℕ} (side : Bool) (p : ℕ × ℕ)
    (w : PairSpace n) :
    intervalForm side p w = intervalSum (extend (if side then w.2 else w.1)) p := by
  simp only [intervalForm, LinearMap.sum_apply, intervalSum, extend]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all [coordinate]

private abbrev Constraint (n : ℕ) :=
  (Bool × Fin n) ⊕ ((Bool × Fin n × Fin n) ⊕ (Bool × Occurrence n))

private noncomputable def forms {n : ℕ} (π : Equiv.Perm (Occurrence n)) :
    Constraint n → Module.Dual ℝ (PairSpace n)
  | .inl (side, i) => coordinate side i
  | .inr (.inl (side, i, j)) => if i ≤ j then coordinate side j - coordinate side i else 0
  | .inr (.inr (sign, p)) =>
      if sign then intervalForm false p.val - intervalForm true (π p).val
      else -(intervalForm false p.val - intervalForm true (π p).val)

private def difference {n : ℕ} (i : Fin n) : Module.Dual ℝ (PairSpace n) :=
  coordinate false i - coordinate true i

private theorem observations_eq_of_matching {n : ℕ} (π : Equiv.Perm (Occurrence n))
    (a b : ℕ → ℝ)
    (h : ∀ p : Occurrence n, intervalSum a p.val = intervalSum b (π p).val) :
    observations a n = observations b n := by
  classical
  unfold observations
  apply Multiset.map_eq_map_of_bij_of_nodup _ _ (intervals n).nodup (intervals n).nodup
    (fun p hp => (π ⟨p, hp⟩).val)
  · intro p hp
    exact (π ⟨p, hp⟩).property
  · intro p hp q hq he
    exact congrArg Subtype.val (π.injective (Subtype.ext he))
  · intro q hq
    refine ⟨(π.symm ⟨q, hq⟩).val, (π.symm ⟨q, hq⟩).property, ?_⟩
    exact congrArg Subtype.val (π.apply_symm_apply ⟨q, hq⟩)
  · intro p hp
    exact h ⟨p, hp⟩

private theorem exact_cone_difference_zero {n : ℕ} (hn : 3 ≤ n)
    (π : Equiv.Perm (Occurrence n)) (w : PairSpace n)
    (hw : ∀ j, 0 ≤ forms π j w) : ∀ i, difference i w = 0 := by
  have hn0 (s : Bool) (k : ℕ) (hk : k < n) :
      0 ≤ extend (if s then w.2 else w.1) k := by
    simpa [forms, coordinate, extend, hk] using hw (.inl (s, ⟨k, hk⟩))
  have hmono (s : Bool) (u v : ℕ) (huv : u ≤ v) (hv : v < n) :
      extend (if s then w.2 else w.1) u ≤ extend (if s then w.2 else w.1) v := by
    have hu : u < n := lt_of_le_of_lt huv hv
    have hij : (⟨u, hu⟩ : Fin n) ≤ ⟨v, hv⟩ := huv
    have h := hw (.inr (.inl (s, ⟨u, hu⟩, ⟨v, hv⟩)))
    simpa [forms, hij, coordinate, extend, hu, hv, sub_nonneg] using h
  have hm (p : Occurrence n) :
      intervalSum (extend w.1) p.val = intervalSum (extend w.2) (π p).val := by
    have hpos := hw (.inr (.inr (true, p)))
    have hneg := hw (.inr (.inr (false, p)))
    simp only [forms, Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply,
      LinearMap.neg_apply, intervalForm_apply] at hpos hneg
    linarith
  have he := observations_eq_of_matching π (extend w.1) (extend w.2) hm
  have hr := reconstruct hn (hn0 false) (hn0 true) (hmono false) (hmono true) he
  intro i
  have h := hr.2 i.val i.isLt
  simpa [difference, coordinate, extend, i.isLt, sub_eq_zero] using h

private theorem bound_for_permutation {n : ℕ} (hn : 3 ≤ n)
    (π : Equiv.Perm (Occurrence n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Fin n → ℝ,
      (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → Monotone a → Monotone b →
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ p : Occurrence n,
        |intervalSum (extend a) p.val - intervalSum (extend b) (π p).val| ≤ ε) →
      ∀ i, |a i - b i| ≤ C * ε := by
  obtain ⟨C, hC, hbound⟩ :=
    TauCeti.exists_forall_abs_apply_sub_le_of_forall_neg_le (forms π) (difference (n := n))
  refine ⟨C, hC, fun a b ha hb hsa hsb ε hε hm => ?_⟩
  have hw : ∀ j, -ε ≤ forms π j (a, b) := by
    intro j
    rcases j with ⟨s, i⟩ | (⟨s, i, j⟩ | ⟨s, p⟩)
    · cases s
      · change -ε ≤ a i
        linarith [ha i]
      · change -ε ≤ b i
        linarith [hb i]
    · by_cases hij : i ≤ j
      · cases s <;> simp only [forms, hij, ↓reduceIte, LinearMap.sub_apply, coordinate,
          LinearMap.coe_mk, AddHom.coe_mk, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        · linarith [hsa hij]
        · linarith [hsb hij]
      · simp [forms, hij, hε]
    · have h := abs_le.mp (hm p)
      cases s <;> simp only [forms, Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply,
        LinearMap.neg_apply, intervalForm_apply]
      · linarith [h.2]
      · exact h.1
  obtain ⟨w', hw', hdist⟩ := hbound ε hε (a, b) hw
  intro i
  have hz := exact_cone_difference_zero hn π w' hw' i
  have hd := hdist i
  rw [map_sub, hz, sub_zero] at hd
  simpa [difference, coordinate] using hd

/-- Full uniform noisy recovery, with a constant chosen before tuples, noise and matching.
Every actual inclusive interval of at least two entries occurs once in `Occurrence n`. -/
theorem exists_uniform_recovery_constant (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Fin n → ℝ,
      (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → Monotone a → Monotone b →
      ∀ ε : ℝ, 0 ≤ ε → ∀ π : Equiv.Perm (Occurrence n),
      (∀ p : Occurrence n,
        |intervalSum (extend a) p.val - intervalSum (extend b) (π p).val| ≤ ε) →
      ∀ i, |a i - b i| ≤ C * ε := by
  classical
  choose C hC hbound using bound_for_permutation hn
  refine ⟨∑ π, C π, Finset.sum_nonneg fun π _ => hC π,
    fun a b ha hb hsa hsb ε hε π hm i => ?_⟩
  exact (hbound π a b ha hb hsa hsb ε hε hm i).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun σ _ => hC σ) (Finset.mem_univ π)) hε)

end Omega.MonotoneIntervalStability

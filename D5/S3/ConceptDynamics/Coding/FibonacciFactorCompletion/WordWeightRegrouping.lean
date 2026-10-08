/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual path regrouping identifies the original factor-rate spectral abscissa. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors

private theorem retained_walk_live {side : MemorySide} {n K : ℕ} {d : ℝ}
    (v : MemoryVertex n) (w : List CuLetter) :
    RetainedWalk side K d v w → LiveVertex side K d v := by
  cases w with
  | nil => intro h; exact h
  | cons a w => intro h; exact h.1

def CorePathWitnessDictionary (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ) :=
  {x : Σ k : ℕ, CoreVertex side n K d ×
      (Fin k → CuLetter × CoreVertex side n K d) //
    CorePath side K d x.1 x.2.1 x.2.2 ∧
      wordWeight (List.ofFn (fun i => (x.2.2 i).1)) = T}

private def choicesOfWalk {side : MemorySide} {n K : ℕ} {d : ℝ}
    (v : MemoryVertex n) : (w : List CuLetter) →
      RetainedWalk side K d v w →
      (Fin w.length → CuLetter × CoreVertex side n K d)
  | [], _ => fun i => Fin.elim0 i
  | a :: w, walk =>
      Fin.cons (a, ⟨memoryShift v a, retained_walk_live _ _ walk.2.2⟩)
        (choicesOfWalk (memoryShift v a) w walk.2.2)

private theorem choicesOfWalk_path {side : MemorySide} {n K : ℕ} {d : ℝ}
    (v : MemoryVertex n) (w : List CuLetter)
    (walk : RetainedWalk side K d v w) :
    CorePath side K d w.length ⟨v, retained_walk_live v w walk⟩
      (choicesOfWalk v w walk) := by
  induction w generalizing v with
  | nil => simp [CorePath, choicesOfWalk]
  | cons a w ih =>
    rcases walk with ⟨live, edge, tail⟩
    refine ⟨?_, ih (memoryShift v a) tail⟩
    simpa [choicesOfWalk] using edge

private theorem choicesOfWalk_letters {side : MemorySide} {n K : ℕ} {d : ℝ}
    (v : MemoryVertex n) (w : List CuLetter)
    (walk : RetainedWalk side K d v w) :
    List.ofFn (fun i => (choicesOfWalk v w walk i).1) = w := by
  induction w generalizing v with
  | nil => simp [choicesOfWalk]
  | cons a w ih =>
    rcases walk with ⟨live, edge, tail⟩
    simpa [choicesOfWalk] using congrArg (List.cons a)
      (ih (memoryShift v a) tail)

private theorem every_retained_has_core_path (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ)
    (x : RetainedPathDictionary side n K d T) :
    ∃ y : CorePathWitnessDictionary side n K d T,
      y.1.1 = x.1.2.length ∧ y.1.2.1.1 = x.1.1 ∧
        List.ofFn (fun i => (y.1.2.2 i).1) = x.1.2 := by
  let v : CoreVertex side n K d :=
    ⟨x.1.1, retained_walk_live x.1.1 x.1.2 x.2.1⟩
  let c := choicesOfWalk x.1.1 x.1.2 x.2.1
  have cp := choicesOfWalk_path x.1.1 x.1.2 x.2.1
  have letters := choicesOfWalk_letters x.1.1 x.1.2 x.2.1
  refine ⟨⟨⟨x.1.2.length,(v,c)⟩,cp,?_⟩,rfl,rfl,letters⟩
  simpa [c, letters] using x.2.2

private def actualToRetained (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ)
    (x : CorePathWitnessDictionary side n K d T) :
    RetainedPathDictionary side n K d T :=
  ⟨((x.1.2.1).1, List.ofFn (fun i => (x.1.2.2 i).1)),
    (original_weighted_adjacency_paths side n K d 1).1 x.1.1 x.1.2.1 x.1.2.2 x.2.1,
    x.2.2⟩

private theorem core_path_choice_unique {side : MemorySide} {n K : ℕ} {d : ℝ}
    : ∀ k (v : CoreVertex side n K d)
      (c e : Fin k → CuLetter × CoreVertex side n K d),
      CorePath side K d k v c → CorePath side K d k v e →
      List.ofFn (fun i => (c i).1) = List.ofFn (fun i => (e i).1) → c = e := by
  intro k
  induction k with
  | zero =>
    intro v c e _ _ _
    funext i
    exact Fin.elim0 i
  | succ k ih =>
    intro v c e hc he hletters
    simp only [CorePath] at hc he
    have hcons : (c 0).1 :: List.ofFn (fun i => (c i.succ).1) =
        (e 0).1 :: List.ofFn (fun i => (e i.succ).1) := by
      simpa only [List.ofFn_succ] using hletters
    have hhead : (c 0).1 = (e 0).1 := (List.cons.inj hcons).1
    have htarget : (c 0).2 = (e 0).2 := by
      apply Subtype.ext
      rw [hc.1.1, he.1.1, hhead]
    have hpair : c 0 = e 0 := Prod.ext hhead htarget
    have htail : (fun i => c (Fin.succ i)) = (fun i => e (Fin.succ i)) := by
      apply ih (c 0).2
      · exact hc.2
      · simpa [hpair] using he.2
      · exact (List.cons.inj hcons).2
    funext i
    exact Fin.cases hpair (fun j => congrFun htail j) i

private theorem actualToRetained_injective (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ) :
    Function.Injective (actualToRetained side n K d T) := by
  rintro ⟨⟨kx, vx, cx⟩, hcx, hwx⟩ ⟨⟨ky, vy, cy⟩, hcy, hwy⟩ h
  have hv : vx.val = vy.val := by
    simpa [actualToRetained] using congrArg (fun q => q.val.1) h
  have hw : List.ofFn (fun i => (cx i).1) =
      List.ofFn (fun i => (cy i).1) := by
    simpa [actualToRetained] using congrArg (fun q => q.val.2) h
  have hk : kx = ky := by
    simpa using congrArg List.length hw
  cases hk
  have hvertex : vx = vy := Subtype.ext hv
  cases hvertex
  have hchoices : cx = cy := core_path_choice_unique kx vx cx cy hcx hcy hw
  cases hchoices
  rfl

/-- The actual CorePath choice witness is present for every retained dictionary;
the map forgetting that witness is a bijection, including empty walks and
finite walks crossing transient bridges. -/
theorem core_path_witness_dictionary_equiv (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ)
    (positive : 0 < K) (memory : K ≤ n) :
    Nonempty (CorePathWitnessDictionary side n K d T ≃
      RetainedPathDictionary side n K d T) := by
  letI : Finite (RetainedPathDictionary side n K d T) :=
    (original_weighted_path_count side n K d positive memory T).1
  let f : CorePathWitnessDictionary side n K d T →
      RetainedPathDictionary side n K d T := actualToRetained side n K d T
  have fin : Finite (CorePathWitnessDictionary side n K d T) :=
    Finite.of_injective f (actualToRetained_injective side n K d T)
  letI : Finite (CorePathWitnessDictionary side n K d T) := fin
  exact ⟨Equiv.ofBijective f ⟨
    (actualToRetained_injective side n K d T),
    (fun x => by
      rcases every_retained_has_core_path side n K d T x with ⟨y, _, hv, hw⟩
      refine ⟨y, Subtype.ext ?_⟩
      exact Prod.ext hv hw)⟩⟩

theorem core_path_witness_dictionary_card (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ)
    (positive : 0 < K) (memory : K ≤ n) :
    Nat.card (CorePathWitnessDictionary side n K d T) =
      Nat.card (RetainedPathDictionary side n K d T) := by
  exact Nat.card_congr (Classical.choice
    (core_path_witness_dictionary_equiv side n K d T positive memory))

/-- At one fixed actual weight, the finite witness dictionary sums the
constant monomial z^T once for each retained path. -/
theorem actual_weight_regrouping (side : MemorySide) (n K : ℕ) (d z : ℝ) (T : ℕ)
    (positive : 0 < K) (memory : K ≤ n) :
    (∑' x : CorePathWitnessDictionary side n K d T, z ^ T) =
      (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T := by
  classical
  letI : Finite (RetainedPathDictionary side n K d T) :=
    (original_weighted_path_count side n K d positive memory T).1
  let f : CorePathWitnessDictionary side n K d T →
      RetainedPathDictionary side n K d T := actualToRetained side n K d T
  letI : Fintype (RetainedPathDictionary side n K d T) := Fintype.ofFinite _
  letI : Finite (CorePathWitnessDictionary side n K d T) :=
    Finite.of_injective f (actualToRetained_injective side n K d T)
  letI : Fintype (CorePathWitnessDictionary side n K d T) := Fintype.ofFinite _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have card : Fintype.card (CorePathWitnessDictionary side n K d T) =
      Fintype.card (RetainedPathDictionary side n K d T) := by
    simpa only [Nat.card_eq_fintype_card] using
      core_path_witness_dictionary_card side n K d T positive memory
  rw [card]
  simp [nsmul_eq_mul]

private abbrev ActualCorePath (side : MemorySide) (n K : ℕ) (d : ℝ) :=
  {x : Σ k : ℕ, CoreVertex side n K d ×
      (Fin k → CuLetter × CoreVertex side n K d) //
    CorePath side K d x.1 x.2.1 x.2.2}

private def coreWeightFiberEquiv (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ) :
    {x : ActualCorePath side n K d //
      wordWeight (List.ofFn (fun i => (x.val.2.2 i).1)) = T} ≃
      CorePathWitnessDictionary side n K d T where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The whole actual path series, indexed by letter length, is summable iff
its regrouping by the original total word weight is summable. Zero monomials
from invalid choices are removed, and each genuine path occurs exactly once. -/
theorem actual_monomial_series_regrouping (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (positive : 0 < K) (memory : K ≤ n) (nonnegative : 0 ≤ z) :
    (Summable (fun k : ℕ => ∑ v : CoreVertex side n K d,
      ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
        coreMonomial side K d z k v choices) ↔
    Summable (fun T : ℕ =>
      (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T)) ∧
    ((∑' k : ℕ, ∑ v : CoreVertex side n K d,
      ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
        coreMonomial side K d z k v choices) =
      ∑' T : ℕ, (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T) := by
  classical
  let A := Σ k : ℕ, CoreVertex side n K d ×
    (Fin k → CuLetter × CoreVertex side n K d)
  let P : A → Prop := fun x => CorePath side K d x.1 x.2.1 x.2.2
  let f : A → ℝ := fun x => z ^ wordWeight (List.ofFn (fun i => (x.2.2 i).1))
  let g : A → ℝ := fun x => coreMonomial side K d z x.1 x.2.1 x.2.2
  have gn : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g, coreMonomial]
    split_ifs <;> positivity
  have byLength : Summable g ↔ Summable (fun k : ℕ =>
      ∑ v : CoreVertex side n K d,
        ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
          coreMonomial side K d z k v choices) := by
    rw [summable_sigma_of_nonneg gn]
    have all : ∀ k : ℕ, Summable (fun y : CoreVertex side n K d ×
        (Fin k → CuLetter × CoreVertex side n K d) => g ⟨k, y⟩) :=
      fun _ => Summable.of_finite
    rw [and_iff_right all]
    simp only [tsum_fintype, Fintype.sum_prod_type]
    rfl
  have support : Function.support g ⊆ {x : A | P x} := by
    intro x hx
    by_contra hp
    change ¬ CorePath side K d x.1 x.2.1 x.2.2 at hp
    exact hx (by simp only [g, coreMonomial, if_neg hp])
  have values : ∀ x : ActualCorePath side n K d, f x.val = g x.val := by
    intro x
    dsimp only [f, g, coreMonomial]
    rw [if_pos x.property]
  have restrict : Summable (fun x : ActualCorePath side n K d => f x.val) ↔
      Summable g := by
    have sub : Summable (fun x : {x : A | P x} => g x.val) ↔ Summable g :=
      exists_congr (fun a => hasSum_subtype_iff_of_support_subset (f := g) (a := a) support)
    exact (summable_congr values).trans sub

  let weight : ActualCorePath side n K d → ℕ := fun x =>
    wordWeight (List.ofFn (fun i => (x.val.2.2 i).1))
  have fiberFinite (T : ℕ) : Finite {x : ActualCorePath side n K d // weight x = T} := by
    letI : Finite (RetainedPathDictionary side n K d T) :=
      (original_weighted_path_count side n K d positive memory T).1
    let e := Classical.choice (core_path_witness_dictionary_equiv side n K d T positive memory)
    exact Finite.of_injective (e ∘ coreWeightFiberEquiv side n K d T)
      (e.injective.comp (coreWeightFiberEquiv side n K d T).injective)
  have fiberSum (T : ℕ) :
      (∑' x : {x : ActualCorePath side n K d // weight x = T}, f x.val.val) =
      (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T := by
    have eqn : (fun x : {x : ActualCorePath side n K d // weight x = T} =>
        f x.val.val) = (fun _ => z ^ T) := by
      funext x
      exact congrArg (fun t => z ^ t) x.property
    rw [eqn]
    exact ((coreWeightFiberEquiv side n K d T).tsum_eq (fun _ => z ^ T)).trans
      (actual_weight_regrouping side n K d z T positive memory)
  have byWeight : Summable (fun x : ActualCorePath side n K d => f x.val) ↔
      Summable (fun T : ℕ =>
        (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T) := by
    rw [← (Equiv.sigmaFiberEquiv weight).summable_iff]
    change Summable (fun x : Σ T : ℕ, {x : ActualCorePath side n K d // weight x = T} =>
      f x.2.val.val) ↔ _
    rw [summable_sigma_of_nonneg (fun x => pow_nonneg nonnegative _)]
    have finiteSums : ∀ T : ℕ, Summable (fun x : {x // weight x = T} => f x.val.val) := by
      intro T
      letI := fiberFinite T
      exact Summable.of_finite
    rw [and_iff_right finiteSums]
    exact summable_congr fiberSum
  have convergence := byLength.symm.trans (restrict.symm.trans byWeight)
  refine ⟨convergence, ?_⟩
  by_cases h : Summable g
  · have byLengthSum : (∑' x : A, g x) = ∑' k : ℕ,
        ∑ v : CoreVertex side n K d,
          ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
            coreMonomial side K d z k v choices := by
      simpa only [tsum_fintype, Fintype.sum_prod_type] using h.tsum_sigma
    have subSum : (∑' x : ActualCorePath side n K d, f x.val) = ∑' x : A, g x :=
      (tsum_congr values).trans (tsum_subtype_eq_of_support_subset support)
    have actual := restrict.mpr h
    have reindexed := (Equiv.sigmaFiberEquiv weight).summable_iff.mpr actual
    calc
      _ = ∑' x : A, g x := byLengthSum.symm
      _ = ∑' x : ActualCorePath side n K d, f x.val := subSum.symm
      _ = ∑' x : Σ T : ℕ, {x : ActualCorePath side n K d // weight x = T},
          f x.2.val.val := ((Equiv.sigmaFiberEquiv weight).tsum_eq (fun x => f x.val)).symm
      _ = ∑' T : ℕ, ∑' x : {x : ActualCorePath side n K d // weight x = T},
          f x.val.val := reindexed.tsum_sigma
      _ = _ := tsum_congr fiberSum
  · rw [tsum_eq_zero_of_not_summable (fun hs => h (byLength.mpr hs)),
      tsum_eq_zero_of_not_summable (fun hs => h (byLength.mpr (convergence.mpr hs)))]

/-- The actual factor and retained-path power series have the same convergence
set, using the uniform original initial-memory multiplicity at every weight. -/
theorem actual_factor_path_summability (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (positive : 0 < K) (memory : K ≤ n) (nonnegative : 0 ≤ z) :
    Summable (fun T : ℕ =>
      (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T) ↔
    Summable (fun T : ℕ =>
      (factorCount (MemoryLanguage side n K d) T : ℝ) * z ^ T) := by
  constructor
  · intro paths
    apply paths.of_nonneg_of_le (fun T => by positivity)
    intro T
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast (original_weighted_path_count side n K d positive memory T).2.1)
      (pow_nonneg nonnegative T)
  · intro factors
    apply (factors.mul_left (2 ^ n : ℝ)).of_nonneg_of_le (fun T => by positivity)
    intro T
    calc
      _ ≤ ((2 ^ n * factorCount (MemoryLanguage side n K d) T : ℕ) : ℝ) * z ^ T :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast (original_weighted_path_count side n K d positive memory T).2.2)
          (pow_nonneg nonnegative T)
      _ = _ := by push_cast; ring

/-- The spectral convergence criterion applies to the original factor series,
with the actual finite-memory language and its twenty/six word weights. -/
theorem original_factor_series_boundary (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (positive : 0 < K) (memory : K ≤ n) (nonnegative : 0 ≤ z) :
    Summable (fun T : ℕ =>
      (factorCount (MemoryLanguage side n K d) T : ℝ) * z ^ T) ↔
    SpectralBoundary.weightedRadius side n K d z < 1 := by
  rw [← actual_factor_path_summability side n K d z positive memory nonnegative,
    ← (actual_monomial_series_regrouping side n K d z positive memory nonnegative).1]
  exact SpectralBoundary.original_weighted_series_boundary side n K d z nonnegative

open Filter

noncomputable abbrev factorLogRate (X : Set (ℤ → CuLetter)) (T : ℕ) : ℝ :=
  Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) / (T : ℝ)

theorem factor_log_rate_bounds (X : Set (ℤ → CuLetter)) :
    (∀ T, 0 ≤ factorLogRate X T) ∧
    IsBoundedUnder (· ≤ ·) atTop (factorLogRate X) := by
  have nonneg (T : ℕ) : 0 ≤ factorLogRate X T := by
    exact div_nonneg (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast Nat.le_max_left 1 (factorCount X T))) (by positivity)
  refine ⟨nonneg, ?_⟩
  apply isBoundedUnder_of_eventually_le (a := 2 * Real.logb 2 3)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with T hT
  have tp : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have log3 : 0 ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have cb := (factor_dictionary_bound X T).2
  have maxbound : ((max 1 (factorCount X T) : ℕ) : ℝ) ≤ (3 : ℝ) ^ (T+1) := by
    exact_mod_cast max_le (Nat.one_le_pow _ _ (by decide : 0 < 3)) cb
  have estimate := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (by omega : 0 < max 1 (factorCount X T))) maxbound
  rw [Real.logb_pow] at estimate
  have scale : ((T+1 : ℕ) : ℝ) * Real.logb 2 3 ≤
      (2 * (T : ℝ)) * Real.logb 2 3 := by
    apply mul_le_mul_of_nonneg_right _ log3
    exact_mod_cast (by omega : T+1 ≤ 2*T)
  change Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) / (T : ℝ) ≤ _
  rw [div_le_iff₀ tp]
  nlinarith

theorem factor_rate_nonneg (X : Set (ℤ → CuLetter)) :
    0 ≤ weightedFactorRate X :=
  le_limsup_of_frequently_le (Frequently.of_forall (factor_log_rate_bounds X).1)
    (factor_log_rate_bounds X).2

/-- The max-one logarithmic limsup gives the convergence abscissa for positive
binary exponents. Zero coefficients need no logarithm and remain in the series. -/
theorem factor_rate_convergence (X : Set (ℤ → CuLetter)) (s : ℝ) (positive : 0 < s) :
    (weightedFactorRate X < s →
      Summable (fun T : ℕ => (factorCount X T : ℝ) * ((2 : ℝ) ^ (-s)) ^ T)) ∧
    (Summable (fun T : ℕ => (factorCount X T : ℝ) * ((2 : ℝ) ^ (-s)) ^ T) →
      weightedFactorRate X ≤ s) := by
  constructor
  · intro gap
    obtain ⟨b, above, below⟩ := exists_between gap
    have eventual : ∀ᶠ T in atTop, factorLogRate X T < b :=
      eventually_lt_of_limsup_lt above (factor_log_rate_bounds X).2
    let q : ℝ := (2 : ℝ) ^ (b-s)
    have qp : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
    have qsmall : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    apply (summable_geometric_of_lt_one qp qsmall).of_norm_bounded_eventually_nat
    filter_upwards [eventual, eventually_ge_atTop (1 : ℕ)] with T hT hpos
    have tp : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
    have logbound : Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) < b * (T : ℝ) :=
      (div_lt_iff₀ tp).mp hT
    have cb : (factorCount X T : ℝ) ≤ ((2 : ℝ) ^ b) ^ T := by
      refine le_trans (show (factorCount X T : ℝ) ≤
        ((max 1 (factorCount X T) : ℕ) : ℝ) from ?_) ?_
      · exact_mod_cast Nat.le_max_right 1 (factorCount X T)
      · have bound := ((Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2)
          (by exact_mod_cast (by omega : 0 < max 1 (factorCount X T)))).mp logbound).le
        simpa only [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] using bound
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (((2 : ℝ) ^ b) ^ T) * (((2 : ℝ) ^ (-s)) ^ T) :=
        mul_le_mul_of_nonneg_right cb (by positivity)
      _ = q ^ T := by
        rw [← mul_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rfl
  · intro converges
    have eventual : ∀ᶠ T in atTop,
        (factorCount X T : ℝ) * ((2 : ℝ) ^ (-s)) ^ T ≤ 1 :=
      (converges.tendsto_atTop_zero.eventually (eventually_lt_nhds
        (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
    have base : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) positive.le
    have reciprocal : (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    have rates : ∀ᶠ T in atTop, factorLogRate X T ≤ s := by
      filter_upwards [eventual, eventually_ge_atTop (1 : ℕ)] with T hT hpos
      have tp : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
      have countbound : (factorCount X T : ℝ) ≤ ((2 : ℝ) ^ s) ^ T := by
        calc
          _ = ((factorCount X T : ℝ) * ((2 : ℝ) ^ (-s)) ^ T) *
              ((2 : ℝ) ^ s) ^ T := by rw [mul_assoc, ← mul_pow, reciprocal]; simp
          _ ≤ 1 * ((2 : ℝ) ^ s) ^ T := mul_le_mul_of_nonneg_right hT (by positivity)
          _ = _ := one_mul _
      have maxbound : ((max 1 (factorCount X T) : ℕ) : ℝ) ≤ ((2 : ℝ) ^ s) ^ T := by
        rw [Nat.cast_max, Nat.cast_one]
        exact max_le (one_le_pow₀ base) countbound
      have logs := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by exact_mod_cast (by omega : 0 < max 1 (factorCount X T))) maxbound
      rw [Real.logb_pow, Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)] at logs
      change Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) / (T : ℝ) ≤ s
      rw [div_le_iff₀ tp]
      nlinarith
    exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop (factor_log_rate_bounds X).1) rates

/-- The original weightedFactorRate, including its max-one convention at sparse
weights, is exactly the binary spectral convergence abscissa of the actual
retained adjacency. This does not assume or assert an interior root exists. -/
theorem original_weighted_rate_abscissa (side : MemorySide) (n K : ℕ) (d : ℝ)
    (positive : 0 < K) (memory : K ≤ n) :
    weightedFactorRate (MemoryLanguage side n K d) =
      sInf {s : ℝ | 0 < s ∧
        SpectralBoundary.weightedRadius side n K d ((2 : ℝ) ^ (-s)) < 1} := by
  let X := MemoryLanguage side n K d
  let S := {s : ℝ | 0 < s ∧
    SpectralBoundary.weightedRadius side n K d ((2 : ℝ) ^ (-s)) < 1}
  have rn : 0 ≤ weightedFactorRate X := factor_rate_nonneg X
  have enters (s : ℝ) (above : weightedFactorRate X < s) : s ∈ S := by
    have sp : 0 < s := rn.trans_lt above
    refine ⟨sp, ?_⟩
    exact (original_factor_series_boundary side n K d ((2 : ℝ) ^ (-s)) positive memory
      (Real.rpow_pos_of_pos (by norm_num) _).le).mp
      ((factor_rate_convergence X s sp).1 above)
  have occupied : S.Nonempty := ⟨weightedFactorRate X + 1, enters _ (by linarith)⟩
  have bounded : BddBelow S := ⟨0, fun s hs => hs.1.le⟩
  apply le_antisymm
  · apply le_csInf occupied
    intro s hs
    exact (factor_rate_convergence X s hs.1).2
      ((original_factor_series_boundary side n K d ((2 : ℝ) ^ (-s)) positive memory
        (Real.rpow_pos_of_pos (by norm_num) _).le).mpr hs.2)
  · apply le_of_forall_gt
    intro s hs
    obtain ⟨b, above, below⟩ := exists_between hs
    exact (csInf_le bounded (enters b above)).trans_lt below

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping

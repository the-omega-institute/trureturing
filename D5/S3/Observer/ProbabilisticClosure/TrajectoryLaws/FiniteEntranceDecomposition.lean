/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteEntranceDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteEntranceDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual first-entry weights for the transient block of a finite stochastic matrix. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClassLimits

open Finset Matrix Filter Topology
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition
open FiniteClosedClasses FiniteGenuinePeriods FiniteCyclicBlocks FiniteClosedClassLimits
noncomputable section
universe u
variable {X : Type u} [Fintype X] [DecidableEq X]
variable {P : Matrix X X ℝ}
local instance (P : Matrix X X ℝ) : DecidablePred (Recurrent P) := Classical.decPred _

/-- The weight of staying transient for n steps and entering C at step n+1 at z. -/
def entrance (P : Matrix X X ℝ) (C : ClosedClass P) (n : ℕ)
    (x : Transient P) (z : C.val) : ℝ :=
  ∑ v : Transient P, (transientMatrix P ^ n) x v * P v.val z.val

private theorem entrance_nonnegative (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) (n : ℕ) (x : Transient P) (y : C.val) :
    0 ≤ entrance P C n x y := by
  unfold entrance
  exact sum_nonneg fun v _ => mul_nonneg
    ((actual_structure P hP).substochastic.pow_nonneg n x v)
    (hP.1 _ _)

/-- The actual first-entry phase mass, with the entrance state label minus total entrance time. -/
def psiTransient (K : ClassPeriods P C) (x : Transient P)
    (j : ZMod (period (restriction P C.val) K.base)) : ℝ :=
  ∑ y : C.val, ∑' n : ℕ,
    if K.phase y - ((n + 1 : ℕ) : ZMod (period (restriction P C.val) K.base)) = j
    then entrance P C n x y else 0


private theorem recurrent_sum (hP : P ∈ rowStochastic ℝ X) (f : X → ℝ) :
    (∑ C : ClosedClass P, ∑ z : C.val, f z.val) =
      ∑ z : {z // Recurrent P z}, f z.val := by
  classical
  have hd : (↑(univ : Finset (ClosedClass P)) : Set (ClosedClass P)).PairwiseDisjoint
      (fun C => C.val) := by
    intro C _ D _ hne
    exact (actual_structure P hP).disjoint C D hne
  have hu : (univ : Finset (ClosedClass P)).biUnion (fun C => C.val) =
      univ.filter (Recurrent P) := by
    ext z
    simp [Recurrent]
  simp_rw [Finset.sum_coe_sort]
  rw [← sum_biUnion hd, hu]
  exact Finset.sum_subtype _ (fun _ => by simp) _

private theorem partition_sum (hP : P ∈ rowStochastic ℝ X) (f : X → ℝ) :
    (∑ z : Transient P, f z.val) + (∑ C : ClosedClass P, ∑ z : C.val, f z.val) =
      ∑ z, f z := by
  rw [recurrent_sum hP]
  exact (Fintype.sum_subtype_add_sum_subtype (Recurrent P) f).symm.trans
    (by rw [add_comm]) |>.symm

private theorem cross_class_zero (hP : P ∈ rowStochastic ℝ X)
    (C D : ClosedClass P) (hne : D ≠ C) (z : D.val) (y : C.val) : P z.val y.val = 0 := by
  have hy : y.val ∉ D.val := by
    intro hy
    exact Finset.disjoint_left.mp ((actual_structure P hP).disjoint D C hne)
      hy y.property
  simpa using (actual_structure P hP).class_no_exit D 1 z y.val hy

private theorem step_into_class (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) (T : ℕ) (x : Transient P) (y : C.val) :
    (P ^ (T + 1)) x.val y.val = entrance P C T x y +
      ∑ z : C.val, (P ^ T) x.val z.val * restriction P C.val z y := by
  classical
  rw [pow_succ, Matrix.mul_apply, ← partition_sum hP]
  congr 1
  · unfold entrance
    apply sum_congr rfl
    intro v _
    rw [(actual_structure P hP).transient_powers T x v]
  · rw [Finset.sum_eq_single C]
    · rfl
    · intro D _ hne
      apply sum_eq_zero
      intro z _
      rw [cross_class_zero hP C D hne z y, mul_zero]
    · simp

private theorem finite_decomposition (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) (T : ℕ) (x : Transient P) (y : C.val) :
    (P ^ T) x.val y.val =
      ∑ n ∈ range T, ∑ z : C.val,
        entrance P C n x z * (restriction P C.val ^ (T - (n + 1))) z y := by
  classical
  induction T generalizing y with
  | zero =>
    have hne : x.val ≠ y.val := fun he => x.property (he ▸ ⟨C, y.property⟩)
    simp [hne]
  | succ T ih =>
    rw [step_into_class hP C T x y, sum_range_succ]
    have hn (n : ℕ) (hn : n ∈ range T) : T + 1 - (n + 1) = (T - (n + 1)) + 1 := by
      have := mem_range.mp hn
      omega
    have hlast : (∑ z : C.val, entrance P C T x z *
        (restriction P C.val ^ (T + 1 - (T + 1))) z y) = entrance P C T x y := by
      simp [Matrix.one_apply]
    rw [hlast, add_comm]
    congr 1
    simp_rw [ih, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro n hnt
    rw [hn n hnt, pow_succ]
    simp only [Matrix.mul_apply, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro w _
    exact mul_assoc _ _ _

private theorem entrance_hasSum (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) (x : Transient P) (z : C.val) :
    HasSum (fun n => entrance P C n x z)
      (∑ v : Transient P, (1 - transientMatrix P)⁻¹ x v * P v.val z.val) := by
  obtain ⟨h, c, hh, hc, hb⟩ := (actual_structure P hP).escape
  exact hasSum_sum fun v _ =>
    ((actual_structure P hP).substochastic.hasSum_pow_entry hh hc hb x v).mul_right _

private theorem mass_step (hP : P ∈ rowStochastic ℝ X)
    (n : ℕ) (x : Transient P) :
    (∑ C : ClosedClass P, ∑ z : C.val, entrance P C n x z) =
      SubstochasticEscape.rowSum (transientMatrix P) n x -
      SubstochasticEscape.rowSum (transientMatrix P) (n + 1) x := by
  classical
  have he : (∑ C : ClosedClass P, ∑ z : C.val, entrance P C n x z) =
      ∑ v : Transient P, (transientMatrix P ^ n) x v *
        (∑ C : ClosedClass P, ∑ z : C.val, P v.val z.val) := by
    unfold entrance
    calc
      _ = ∑ C : ClosedClass P, ∑ v : Transient P, ∑ z : C.val,
          (transientMatrix P ^ n) x v * P v.val z.val := by
        apply sum_congr rfl
        intro C _
        rw [sum_comm]
      _ = _ := by rw [sum_comm]; simp_rw [mul_sum]
  rw [he]
  have hr (v : Transient P) :
      (∑ C : ClosedClass P, ∑ z : C.val, P v.val z.val) =
        1 - ∑ w : Transient P, transientMatrix P v w := by
    have h := partition_sum hP (P v.val)
    rw [sum_row_of_mem_rowStochastic hP v.val] at h
    change (∑ w : Transient P, transientMatrix P v w) + _ = 1 at h
    linarith
  simp_rw [hr, mul_sub, mul_one]
  rw [sum_sub_distrib, SubstochasticEscape.rowSum_add]
  simp [SubstochasticEscape.rowSum]

private theorem mass_partial (hP : P ∈ rowStochastic ℝ X)
    (T : ℕ) (x : Transient P) :
    (∑ n ∈ range T, ∑ C : ClosedClass P, ∑ z : C.val, entrance P C n x z) =
      1 - SubstochasticEscape.rowSum (transientMatrix P) T x := by
  simp_rw [mass_step hP]
  rw [sum_range_sub']
  simp [SubstochasticEscape.rowSum_zero]

private theorem survival_tendsto (hP : P ∈ rowStochastic ℝ X) (x : Transient P) :
    Tendsto (fun T => SubstochasticEscape.rowSum (transientMatrix P) T x)
      atTop (𝓝 0) := by
  simpa [SubstochasticEscape.rowSum] using
    tendsto_finsetSum univ (fun z _ => (actual_structure P hP).transient_decay x z)

private theorem mass_hasSum (hP : P ∈ rowStochastic ℝ X) (x : Transient P) :
    HasSum (fun n => ∑ C : ClosedClass P, ∑ z : C.val, entrance P C n x z) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => sum_nonneg fun C _ =>
    sum_nonneg fun z _ => entrance_nonnegative hP C n x z)]
  simp_rw [mass_partial hP]
  simpa using tendsto_const_nhds.sub (survival_tendsto hP x)

private theorem mass_tail (hP : P ∈ rowStochastic ℝ X) (T : ℕ) (x : Transient P) :
    (∑' n : ℕ, ∑ C : ClosedClass P, ∑ z : C.val, entrance P C (n + T) x z) =
      SubstochasticEscape.rowSum (transientMatrix P) T x := by
  have h := (mass_hasSum hP x).summable.sum_add_tsum_nat_add T
  rw [(mass_hasSum hP x).tsum_eq, mass_partial hP] at h
  linarith

private theorem class_occupancy (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) (T : ℕ) (x : Transient P) :
    (∑ n ∈ range T, ∑ z : C.val, entrance P C n x z) =
      ∑ y : C.val, (P ^ T) x.val y.val := by
  classical
  symm
  simp_rw [finite_decomposition hP C T x]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [sum_comm]
  simp_rw [← mul_sum, sum_row_of_mem_rowStochastic
    ((rowStochastic ℝ C.val).pow_mem ((actual_structure P hP).class_stochastic C) _), mul_one]

private theorem late_contribution (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) (T M : ℕ) (x : Transient P) (y : C.val) :
    0 ≤ (∑ n ∈ range (T - M), ∑ z : C.val,
      entrance P C (n + M) x z *
        (restriction P C.val ^ (T - (n + M + 1))) z y) ∧
    (∑ n ∈ range (T - M), ∑ z : C.val,
      entrance P C (n + M) x z *
        (restriction P C.val ^ (T - (n + M + 1))) z y) ≤
      SubstochasticEscape.rowSum (transientMatrix P) M x := by
  classical
  have hs k := (rowStochastic ℝ C.val).pow_mem
    ((actual_structure P hP).class_stochastic C) k
  have hn n : 0 ≤ ∑ D : ClosedClass P, ∑ z : D.val, entrance P D (n + M) x z :=
    sum_nonneg fun D _ => sum_nonneg fun z _ => entrance_nonnegative hP D _ x z
  constructor
  · exact sum_nonneg fun n _ => sum_nonneg fun z _ =>
      mul_nonneg (entrance_nonnegative hP C _ x z) ((hs _).1 z y)
  · calc
      _ ≤ ∑ n ∈ range (T - M), ∑ z : C.val, entrance P C (n + M) x z := by
        apply sum_le_sum
        intro n _
        apply sum_le_sum
        intro z _
        have hb : (restriction P C.val ^ (T - (n + M + 1))) z y ≤ 1 := by
          rw [← sum_row_of_mem_rowStochastic (hs _) z]
          exact single_le_sum (fun w _ => (hs _).1 z w) (mem_univ y)
        exact mul_le_of_le_one_right (entrance_nonnegative hP C _ x z) hb
      _ ≤ ∑ n ∈ range (T - M), ∑ D : ClosedClass P, ∑ z : D.val,
          entrance P D (n + M) x z := by
        apply sum_le_sum
        intro n _
        exact single_le_sum (f := fun D : ClosedClass P =>
          ∑ z : D.val, entrance P D (n + M) x z)
          (fun D _ => sum_nonneg fun z _ => entrance_nonnegative hP D _ x z)
          (mem_univ C)
      _ ≤ ∑' n : ℕ, ∑ D : ClosedClass P, ∑ z : D.val,
          entrance P D (n + M) x z :=
        ((summable_nat_add_iff M).mpr (mass_hasSum hP x).summable).sum_le_tsum
          (range (T - M)) (fun n _ => hn n)
      _ = _ := mass_tail hP M x

private theorem phase_summable (hP : P ∈ rowStochastic ℝ X)
    (K : ClassPeriods P C) (x : Transient P) (z : C.val)
    (j : ZMod (period (restriction P C.val) K.base)) :
    Summable (fun n : ℕ =>
      if K.phase z - ((n + 1 : ℕ) : ZMod (period (restriction P C.val) K.base)) = j
      then entrance P C n x z else 0) := by
  apply Summable.of_nonneg_of_le _ _ (entrance_hasSum hP C x z).summable
  · intro n
    split_ifs
    · exact entrance_nonnegative hP C n x z
    · exact le_rfl
  · intro n
    split_ifs
    · exact le_rfl
    · exact entrance_nonnegative hP C n x z

private theorem phase_nonnegative (hP : P ∈ rowStochastic ℝ X)
    (K : ClassPeriods P C) (x : Transient P)
    (j : ZMod (period (restriction P C.val) K.base)) : 0 ≤ psiTransient K x j := by
  unfold psiTransient
  apply sum_nonneg
  intro z _
  apply tsum_nonneg
  intro n
  split_ifs
  · exact entrance_nonnegative hP C n x z
  · exact le_rfl

private theorem phase_total (hP : P ∈ rowStochastic ℝ X)
    (K : ClassPeriods P C) (x : Transient P) :
    letI : NeZero (period (restriction P C.val) K.base) := ⟨ne_of_gt K.positive⟩
    (∑ j : ZMod (period (restriction P C.val) K.base), psiTransient K x j) =
      ∑ z : C.val, ∑' n : ℕ, entrance P C n x z := by
  classical
  unfold psiTransient
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  rw [← Summable.tsum_finsetSum (fun j _ => phase_summable hP K x z j)]
  congr 1
  funext n
  simp

/-- Exact entrance convolution and the normalized first-entry law, derived from P. -/
structure EntranceLaw (P : Matrix X X ℝ) : Prop where
  nonnegative : ∀ C n x z, 0 ≤ entrance P C n x z
  decomposition : ∀ (C : ClosedClass P) T (x : Transient P) (y : C.val),
    (P ^ T) x.val y.val = ∑ n ∈ range T, ∑ z : C.val,
      entrance P C n x z * (restriction P C.val ^ (T - (n + 1))) z y
  class_occupancy : ∀ (C : ClosedClass P) T (x : Transient P),
    (∑ n ∈ range T, ∑ z : C.val, entrance P C n x z) =
      ∑ y : C.val, (P ^ T) x.val y.val
  entry_hasSum : ∀ (C : ClosedClass P) (x : Transient P) (z : C.val),
    HasSum (fun n => entrance P C n x z)
      (∑ v : Transient P, (1 - transientMatrix P)⁻¹ x v * P v.val z.val)
  mass_step : ∀ n x,
    (∑ C : ClosedClass P, ∑ z : C.val, entrance P C n x z) =
      SubstochasticEscape.rowSum (transientMatrix P) n x -
      SubstochasticEscape.rowSum (transientMatrix P) (n + 1) x
  mass_partial : ∀ T x,
    (∑ n ∈ range T, ∑ C : ClosedClass P, ∑ z : C.val, entrance P C n x z) =
      1 - SubstochasticEscape.rowSum (transientMatrix P) T x
  total_mass : ∀ x,
    HasSum (fun n => ∑ C : ClosedClass P, ∑ z : C.val, entrance P C n x z) 1
  tail_mass : ∀ T x,
    (∑' n : ℕ, ∑ C : ClosedClass P, ∑ z : C.val, entrance P C (n + T) x z) =
      SubstochasticEscape.rowSum (transientMatrix P) T x
  tail_tendsto : ∀ x,
    Tendsto (fun T => ∑' n : ℕ, ∑ C : ClosedClass P, ∑ z : C.val,
      entrance P C (n + T) x z) atTop (𝓝 0)
  late_contribution : ∀ (C : ClosedClass P) T M (x : Transient P) (y : C.val),
    0 ≤ (∑ n ∈ range (T - M), ∑ z : C.val, entrance P C (n + M) x z *
      (restriction P C.val ^ (T - (n + M + 1))) z y) ∧
    (∑ n ∈ range (T - M), ∑ z : C.val, entrance P C (n + M) x z *
      (restriction P C.val ^ (T - (n + M + 1))) z y) ≤
      SubstochasticEscape.rowSum (transientMatrix P) M x
  phase_summable : ∀ (C : ClosedClass P) (K : ClassPeriods P C) x z j,
    Summable (fun n : ℕ =>
      if K.phase z - ((n + 1 : ℕ) : ZMod (period (restriction P C.val) K.base)) = j
      then entrance P C n x z else 0)
  phase_nonnegative : ∀ (C : ClosedClass P) (K : ClassPeriods P C) x j,
    0 ≤ psiTransient K x j
  phase_total : ∀ (C : ClosedClass P) (K : ClassPeriods P C) x,
    letI : NeZero (period (restriction P C.val) K.base) := ⟨ne_of_gt K.positive⟩
    (∑ j : ZMod (period (restriction P C.val) K.base), psiTransient K x j) =
      ∑ z : C.val, ∑' n : ℕ, entrance P C n x z

/-- The finite first-entry decomposition and mass/tail interface for every actual chain. -/
theorem actual_entrance (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X) :
    EntranceLaw P := by
  classical
  exact {
    nonnegative := entrance_nonnegative hP
    decomposition := finite_decomposition hP
    class_occupancy := class_occupancy hP
    entry_hasSum := entrance_hasSum hP
    mass_step := mass_step hP
    mass_partial := mass_partial hP
    total_mass := mass_hasSum hP
    tail_mass := mass_tail hP
    tail_tendsto := fun x => by simp_rw [mass_tail hP]; exact survival_tendsto hP x
    late_contribution := late_contribution hP
    phase_summable := fun _ => phase_summable hP
    phase_nonnegative := fun _ => phase_nonnegative hP
    phase_total := fun _ => phase_total hP }

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition

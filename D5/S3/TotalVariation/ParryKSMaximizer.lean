/- GID: D5/S3/TotalVariation/ParryKSMaximizer
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryKSMaximizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rigidity of the maximizing measure for the bilateral Parry shift. -/

import D5.S3.TotalVariation.ParryKSEntropy
import D5.S3.Divergence.GibbsEquality
import D5.S3.DivergenceSupport.LogSumInequality
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateGhost

/-! Stationary marginal rigidity for the unsigned suffix chain. -/

namespace D5.S3.TotalVariation.ParryKSMaximizer

open Filter Function MeasureTheory Set Topology
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.Divergence.GibbsEquality
open D5.S3.DivergenceSupport.LogSumInequality (log_sum_inequality)
open D5.S3.TotalVariation.ParryInducedEntropy (relationPath_standardBorel)
open D5.S3.Entropy.KolmogorovSinai
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw (visibleCylinder)
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateGhost (visible_eq_of_cylinders)
open D5.S3.TotalVariation.ParryBilateralLaw
open D5.S3.TotalVariation.ParryFirstReturn
open D5.S3.TotalVariation.ParryKSEntropy
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.TwistedResetPaths
open scoped BigOperators

variable {k : ℕ}

private theorem suffix_stationary_unique (hk : 2 ≤ k) (u : Fin k → ℝ)
    (hsum : ∑ j, u j = 1)
    (hstat : ∀ j, ∑ i, u i * suffixKernel k i j = u j) :
    u = suffixLaw k := by
  classical
  let p := parryParameter k
  let R := suffixWeight k p
  let z : Fin k := ⟨0, by omega⟩
  have hpara := parry_stationary_law k hk
  have hp : 0 < p := lt_trans (by norm_num) hpara.1.1
  have hpos (j : Fin k) : 0 < R j := hp.trans_le (hpara.2.1 j).1
  have hRz : R z = 1 := by simpa [R, suffixWeight, z, rootSum] using hpara.1.2.2
  have hform (n : ℕ) (hn : n < k) : u ⟨n, hn⟩ = u z * p ^ n * R ⟨n, hn⟩ := by
    induction n with
    | zero => simp [z, hRz]
    | succ n ih =>
      let j : Fin k := ⟨n + 1, hn⟩
      let i : Fin k := ⟨n, by omega⟩
      have hQ : suffixKernel k i j = p * R j / R i := by
        simp [suffixKernel, i, j, p, R]
      have hpre : (∑ a, u a * suffixKernel k a j) = u i * suffixKernel k i j := by
        apply Finset.sum_eq_single i
        · intro a _ ha
          have hav : a.val ≠ n := fun he => ha (Fin.ext he)
          simp [suffixKernel, j, Ne.symm hav]
        · simp
      change u j = u z * p ^ (n + 1) * R j
      rw [← hstat j, hpre, hQ, ih i.isLt, pow_succ]
      field_simp [(hpos i).ne']
      change u z * R i * R j = u z * R j * R i
      ring
  have hform' (j : Fin k) : u j = u z * (p ^ j.val * R j) := by
    rcases j with ⟨j, hj⟩
    rw [hform j hj, mul_assoc]
  have hnormal : u z * normalizer k = 1 := by
    rw [normalizer, Finset.mul_sum]
    change (∑ j, u z * (p ^ j.val * R j)) = 1
    simp_rw [← hform']
    exact hsum
  have hN : normalizer k ≠ 0 := (zero_lt_one.trans_le hpara.2.2.1).ne'
  have hz : u z = 1 / normalizer k := (eq_div_iff hN).2 hnormal
  funext j
  rw [hform', hz]
  unfold suffixLaw
  ring


private theorem history_defect {W A : Type*} [Fintype W] [Fintype A]
    (joint : W × A → ℝ) (history : W → ℝ) (next : W → A → ℝ)
    (hrow : ∀ w, ∑ j, joint (w, j) = history w)
    (hsupport : ∀ w j, history w * next w j = 0 → joint (w, j) = 0) :
    klDivergence joint (fun wj => history wj.1 * next wj.1 wj.2) =
      (∑ w, Real.negMulLog (history w)) - (∑ x, Real.negMulLog (joint x)) -
        ∑ w, ∑ j, joint (w, j) * Real.log (next w j) := by
  have hterm (w : W) (j : A) :
      joint (w, j) * Real.log (joint (w, j) / (history w * next w j)) =
        -Real.negMulLog (joint (w, j)) -
          joint (w, j) * Real.log (history w) -
          joint (w, j) * Real.log (next w j) := by
    by_cases hz : joint (w, j) = 0
    · simp [hz]
    · have hb : history w * next w j ≠ 0 := fun h => hz (hsupport w j h)
      have hm : history w ≠ 0 := left_ne_zero_of_mul hb
      have hn : next w j ≠ 0 := right_ne_zero_of_mul hb
      rw [Real.log_div hz hb, Real.log_mul hm hn, Real.negMulLog]
      ring
  rw [klDivergence, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, Real.negMulLog]
  simp only [Finset.sum_neg_distrib, neg_mul]
  ring


private theorem stationary_cross_entropy {W A : Type*} [Fintype W] [Fintype A]
    (joint : W × A → ℝ) (next : W → A → ℝ) (last : W → A)
    (c : ℝ) (potential : A → ℝ)
    (hnorm : ∑ x, joint x = 1)
    (hlog : ∀ w j, joint (w, j) ≠ 0 →
      Real.log (next w j) = c + potential j - potential (last w))
    (hstat : (∑ x, joint x * potential x.2) = ∑ x, joint x * potential (last x.1)) :
    (∑ w, ∑ j, joint (w, j) * Real.log (next w j)) = c := by
  have hterm (x : W × A) :
      joint x * Real.log (next x.1 x.2) =
        joint x * c + joint x * potential x.2 - joint x * potential (last x.1) := by
    by_cases hz : joint x = 0
    · simp [hz]
    · rw [hlog x.1 x.2 hz]
      ring
  let term (x : W × A) := joint x * Real.log (next x.1 x.2)
  change (∑ w, ∑ j, term (w, j)) = c
  rw [← Fintype.sum_prod_type term]
  dsimp only [term]
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hstat, ← Finset.sum_mul, hnorm, one_mul, add_sub_cancel_right]

private theorem limit_le_of_defect {h : ℕ → ℝ} {d : ℕ → ℝ} (c rate : ℝ)
    (hlimit : Filter.Tendsto (fun m : ℕ => h m / (m : ℝ)) Filter.atTop (nhds rate))
    (hstep : ∀ n ≥ 1, h (n + 1) = h n + c - d n)
    (hmono : Monotone d) (m : ℕ) (hm : 1 ≤ m) : rate ≤ c - d m := by
  let C := h m - (m : ℝ) * (c - d m)
  have hbound (n : ℕ) (hn : m ≤ n) : h n ≤ (n : ℝ) * (c - d m) + C := by
    induction n, hn using Nat.le_induction with
    | base => dsimp [C]; linarith
    | succ n hn ih =>
      have hd := hmono hn
      rw [hstep n (hm.trans hn), Nat.cast_succ]
      linarith
  have hright : Filter.Tendsto (fun n : ℕ => c - d m + C / (n : ℝ)) Filter.atTop
      (nhds (c - d m)) := by
    simpa using (tendsto_const_nhds (x := c - d m)).add
      (tendsto_const_div_atTop_nhds_zero_nat C)
  refine le_of_tendsto_of_tendsto hlimit hright ?_
  filter_upwards [Filter.eventually_ge_atTop m] with n hn
  have hnonzero : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc
    h n / (n : ℝ) ≤ ((n : ℝ) * (c - d m) + C) / n :=
      div_le_div_of_nonneg_right (hbound n hn) (Nat.cast_nonneg n)
    _ = c - d m + C / n := by rw [add_div, mul_comm (n : ℝ), mul_div_cancel_right₀ _ hnonzero]


private theorem split_measure {X W I : Type*} [MeasurableSpace X] [Fintype I]
    [MeasurableSpace W] [MeasurableSingletonClass W] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ : Measure X) [IsFiniteMeasure ρ]
    {read : X → W} {other : X → I} (hread : Measurable read) (hother : Measurable other)
    (w : W) :
    (∑ i, ρ.real {x | read x = w ∧ other x = i}) = ρ.real {x | read x = w} := by
  let C (i : I) := {x | read x = w ∧ other x = i}
  have hset : {x | read x = w} = ⋃ i ∈ (Finset.univ : Finset I), C i := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_univ, iUnion_true, mem_iUnion, C]
    exact ⟨fun hx => ⟨other x, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
  rw [hset, measureReal_biUnion_finset]
  · intro i _ j _ hij
    exact disjoint_left.2 fun x hi hj => hij (hi.2.symm.trans hj.2)
  · intro i _
    exact (hread (measurableSet_singleton w)).inter (hother (measurableSet_singleton i))

private noncomputable def cylinder (ρ : Measure (RelationPath k))
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (t : ℤ) {n : ℕ} (w : Fin n → Fin k) : ℝ :=
  ρ.real ((blockPartition ρ e t n).cells w)

private theorem cylinder_sum (ρ : Measure (RelationPath k)) [IsProbabilityMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (t : ℤ) (n : ℕ) :
    (∑ w : Fin n → Fin k, cylinder ρ e t w) = 1 :=
  (blockPartition ρ e t n).sum_toReal_measure_eq_one

private theorem split_last (ρ : Measure (RelationPath k)) [IsFiniteMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (t : ℤ) {n : ℕ} (w : Fin n → Fin k) :
    (∑ j : Fin k, cylinder ρ e t (Fin.snoc w j)) = cylinder ρ e t w := by
  have hcell (j : Fin k) :
      (blockPartition ρ e t (n + 1)).cells (Fin.snoc w j) =
        {x | suffixBlock e t n x = w ∧ suffixAt e (t + n) x = j} := by
    ext x
    change suffixBlock e t (n + 1) x = Fin.snoc w j ↔ _
    constructor
    · intro hx
      refine ⟨funext fun i => ?_, ?_⟩
      · have hi := congrFun hx i.castSucc
        simpa [suffixBlock] using hi
      · have hl := congrFun hx (Fin.last n)
        simpa [suffixBlock, suffixAt] using hl
    · rintro ⟨hw, hj⟩
      funext i
      refine Fin.lastCases ?_ (fun q => ?_) i
      · simpa [suffixBlock, suffixAt] using hj
      · simpa [suffixBlock] using congrFun hw q
  unfold cylinder
  simp_rw [hcell]
  exact split_measure ρ (measurable_suffixBlock e t n) (measurable_suffixAt e _) w


private theorem split_first (ρ : Measure (RelationPath k)) [IsFiniteMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (t : ℤ) {n : ℕ} (w : Fin n → Fin k) :
    (∑ j : Fin k, cylinder ρ e t (Fin.cons j w)) = cylinder ρ e (t + 1) w := by
  have hcell (j : Fin k) :
      (blockPartition ρ e t (n + 1)).cells (Fin.cons j w) =
        {x | suffixBlock e (t + 1) n x = w ∧ suffixAt e t x = j} := by
    ext x
    change suffixBlock e t (n + 1) x = Fin.cons j w ↔ _
    constructor
    · intro hx
      refine ⟨funext fun i => ?_, ?_⟩
      · simpa [suffixBlock, add_comm, add_left_comm, add_assoc] using congrFun hx i.succ
      · simpa [suffixBlock, suffixAt] using congrFun hx 0
    · rintro ⟨hw, hj⟩
      funext i
      refine Fin.cases ?_ (fun q => ?_) i
      · simpa [suffixBlock, suffixAt] using hj
      · simpa [suffixBlock, add_comm, add_left_comm, add_assoc] using congrFun hw q
  unfold cylinder
  simp_rw [hcell]
  exact split_measure ρ (measurable_suffixBlock e (t + 1) n) (measurable_suffixAt e t) w

private theorem cylinder_shift (ρ : Measure (RelationPath k))
    (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r)
    (t : ℤ) (m : ℕ) {n : ℕ} (w : Fin n → Fin k) :
    cylinder ρ e (t + m) w = cylinder ρ e t w := by
  have hpre : (relationShift^[m]) ⁻¹' (blockPartition ρ e t n).cells w =
      (blockPartition ρ e (t + m) n).cells w := by
    ext x
    change suffixBlock e t n (relationShift^[m] x) = w ↔ suffixBlock e (t + m) n x = w
    have hn : suffixBlock e t n (relationShift^[m] x) = suffixBlock e (t + m) n x := by
      funext i
      change suffixAt e (t + i.val) (relationShift^[m] x) = suffixAt e (t + m + i.val) x
      rw [hshift, add_right_comm]
    rw [hn]
  unfold cylinder Measure.real
  rw [← hpre, (T.iterate m).measure_preimage
    ((blockPartition ρ e t n).measurable _).nullMeasurableSet]

private def snocName (n : ℕ) : ((Fin n → Fin k) × Fin k) ≃ (Fin (n + 1) → Fin k) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin k))

private theorem block_sum_snoc {B : Type*} [AddCommMonoid B] (n : ℕ)
    (f : (Fin (n + 1) → Fin k) → B) :
    (∑ w, f w) = ∑ history : Fin n → Fin k, ∑ j : Fin k, f (Fin.snoc history j) := by
  let g (x : (Fin n → Fin k) × Fin k) := f (snocName n x)
  rw [← Fintype.sum_equiv (snocName n) g f (fun _ => rfl), Fintype.sum_prod_type g]
  rfl


private theorem cylinder_eval (ρ : Measure (RelationPath k)) [IsFiniteMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (t : ℤ) {n : ℕ}
    (i : Fin n) (j : Fin k) :
    (∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin k => w i = j), cylinder ρ e t w) =
      ρ.real {r | suffixAt e (t + i.val) r = j} := by
  classical
  let words := Finset.univ.filter (fun w : Fin n → Fin k => w i = j)
  have hset : (suffixBlock e t n) ⁻¹' (words : Set (Fin n → Fin k)) =
      {r | suffixAt e (t + i.val) r = j} := by
    ext r
    simp [words, suffixBlock, suffixAt]
  change (∑ w ∈ words, ρ.real ((suffixBlock e t n) ⁻¹' {w})) = _
  rw [sum_measureReal_preimage_singleton words
    (fun w _ => measurable_suffixBlock e t n (measurableSet_singleton w)), hset]

private theorem weighted_coordinate (ρ : Measure (RelationPath k)) [IsFiniteMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (t : ℤ) {n : ℕ} (i : Fin n)
    (f : Fin k → ℝ) :
    (∑ w : Fin n → Fin k, cylinder ρ e t w * f (w i)) =
      ∑ j : Fin k, ρ.real {r | suffixAt e (t + i.val) r = j} * f j := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n → Fin k)) (fun w => w i)]
  apply Finset.sum_congr rfl
  intro j _
  have heq (w : Fin n → Fin k) (hw : w ∈ Finset.univ.filter (fun w => w i = j)) :
      cylinder ρ e t w * f (w i) = cylinder ρ e t w * f j := by
    rw [(Finset.mem_filter.mp hw).2]
  rw [Finset.sum_congr rfl heq, ← Finset.sum_mul, cylinder_eval ρ e t i j]


private theorem suffix_row_sum (hk : 2 ≤ k) (i : Fin k) :
    ∑ j, suffixKernel k i j = 1 := by
  let f (s : State k) := kernel k (parryParameter k) (false, i) s
  have hf (j : Fin k) : suffixKernel k i j = ∑ a : Bool, f (a, j) := by
    rw [Fintype.sum_bool]
    by_cases h₀ : j.val = 0
    · simp [f, kernel, suffixKernel, h₀, -Fin.val_eq_zero_iff]
    · by_cases h₁ : j.val = i.val + 1
      · simp [f, kernel, suffixKernel, h₁]
      · simp [f, kernel, suffixKernel, h₀, h₁, -Fin.val_eq_zero_iff]
  simp_rw [hf]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type f]
  exact (parry_stationary_law k hk).2.2.2.2.1 (false, i)

private noncomputable def actualJoint (ρ : Measure (RelationPath k))
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ)
    (wj : (Fin (m + 1) → Fin k) × Fin k) : ℝ :=
  cylinder ρ e 0 (Fin.snoc wj.1 wj.2)

private noncomputable def referenceJoint (ρ : Measure (RelationPath k))
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ)
    (wj : (Fin (m + 1) → Fin k) × Fin k) : ℝ :=
  cylinder ρ e 0 wj.1 * suffixKernel k (wj.1 (Fin.last m)) wj.2


private theorem actual_joint_edge (ρ : Measure (RelationPath k)) [IsFiniteMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ) (w : Fin (m + 1) → Fin k)
    (j : Fin k) (hpos : actualJoint ρ e m (w, j) ≠ 0) :
    j.val = 0 ∨ j.val = (w (Fin.last m)).val + 1 := by
  have hnonempty : ((blockPartition ρ e 0 (m + 2)).cells (Fin.snoc w j)).Nonempty := by
    refine Set.nonempty_iff_ne_empty.2 fun h => hpos ?_
    simp [actualJoint, cylinder, h]
  obtain ⟨x, hx⟩ := hnonempty
  change suffixBlock e 0 (m + 2) x = Fin.snoc w j at hx
  have hi : suffixAt e (m : ℤ) x = w (Fin.last m) := by
    simpa [suffixBlock, suffixAt] using congrFun hx (Fin.last m).castSucc
  have hj : suffixAt e ((m : ℤ) + 1) x = j := by
    simpa [suffixBlock, suffixAt] using congrFun hx (Fin.last (m + 1))
  have hedge := suffix_edge e x (m : ℤ)
  change (suffixAt e ((m : ℤ) + 1) x).val = 0 ∨
    (suffixAt e ((m : ℤ) + 1) x).val = (suffixAt e (m : ℤ) x).val + 1 at hedge
  rwa [hi, hj] at hedge

private theorem joint_absolute_continuity (hk : 2 ≤ k) (ρ : Measure (RelationPath k))
    [IsFiniteMeasure ρ] (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ)
    (wj : (Fin (m + 1) → Fin k) × Fin k) (hz : referenceJoint ρ e m wj = 0) :
    actualJoint ρ e m wj = 0 := by
  rcases mul_eq_zero.mp hz with hmass | hQ
  · apply measureReal_mono_null ?_ hmass
    intro x hx
    change suffixBlock e 0 (m + 2) x = Fin.snoc wj.1 wj.2 at hx
    change suffixBlock e 0 (m + 1) x = wj.1
    funext i
    simpa [suffixBlock] using congrFun hx i.castSucc
  · by_contra hpos
    exact (kernel_log_on_edge hk _ _ (actual_joint_edge ρ e m wj.1 wj.2 hpos)).1.ne' hQ

private theorem actual_joint_sum (ρ : Measure (RelationPath k)) [IsProbabilityMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ) :
    ∑ x, actualJoint ρ e m x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [actualJoint, split_last]
  exact cylinder_sum ρ e 0 (m + 1)

private theorem reference_joint_sum (hk : 2 ≤ k)
    (ρ : Measure (RelationPath k)) [IsProbabilityMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ) :
    ∑ x, referenceJoint ρ e m x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [referenceJoint, ← Finset.mul_sum, suffix_row_sum hk, mul_one]
  exact cylinder_sum ρ e 0 (m + 1)

private theorem joint_potential_eq (ρ : Measure (RelationPath k)) [IsProbabilityMeasure ρ]
    (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r)
    (m : ℕ) (f : Fin k → ℝ) :
    (∑ x, actualJoint ρ e m x * f x.2) =
      ∑ x, actualJoint ρ e m x * f (x.1 (Fin.last m)) := by
  have hlast :
      (∑ x, actualJoint ρ e m x * f x.2) =
        ∑ w : Fin (m + 2) → Fin k, cylinder ρ e 0 w * f (w (Fin.last (m + 1))) := by
    rw [Fintype.sum_prod_type, block_sum_snoc (m + 1)]
    simp [actualJoint]
  have hprev :
      (∑ x, actualJoint ρ e m x * f (x.1 (Fin.last m))) =
        ∑ w : Fin (m + 1) → Fin k, cylinder ρ e 0 w * f (w (Fin.last m)) := by
    rw [Fintype.sum_prod_type]
    simp_rw [actualJoint, ← Finset.sum_mul, split_last]
  rw [hlast, hprev, weighted_coordinate, weighted_coordinate]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hmass : cylinder ρ e ((m : ℤ) + 1) (fun _ : Fin 1 => j) =
      cylinder ρ e (m : ℤ) (fun _ : Fin 1 => j) := by
    simpa using cylinder_shift ρ T e hshift (m : ℤ) 1 (fun _ : Fin 1 => j)
  have single (t : ℤ) :
      cylinder ρ e t (fun _ : Fin 1 => j) = ρ.real {r | suffixAt e t r = j} := by
    unfold cylinder
    apply congrArg ρ.real
    ext r
    change suffixBlock e t 1 r = (fun _ => j) ↔ _
    simp [funext_iff, suffixBlock, suffixAt]
  simpa only [single, Fin.val_last, Nat.cast_add, Nat.cast_one, zero_add] using hmass


private noncomputable def defect (ρ : Measure (RelationPath k))
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) : ℕ → ℝ
  | 0 => 0
  | m + 1 => klDivergence (actualJoint ρ e m) (referenceJoint ρ e m)

private theorem actual_joint_law (ρ : Measure (RelationPath k)) [IsProbabilityMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ) :
    (∀ x, 0 ≤ actualJoint ρ e m x) ∧ ∑ x, actualJoint ρ e m x = 1 :=
  ⟨fun _ => ENNReal.toReal_nonneg, actual_joint_sum ρ e m⟩

private theorem reference_joint_law (hk : 2 ≤ k)
    (ρ : Measure (RelationPath k)) [IsProbabilityMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (m : ℕ) :
    (∀ x, 0 ≤ referenceJoint ρ e m x) ∧ ∑ x, referenceJoint ρ e m x = 1 :=
  ⟨fun _ => mul_nonneg ENNReal.toReal_nonneg (kernel_nonneg hk _ _), reference_joint_sum hk ρ e m⟩

private theorem defect_nonneg (hk : 2 ≤ k) (ρ : Measure (RelationPath k)) [IsProbabilityMeasure ρ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (n : ℕ) : 0 ≤ defect ρ e n := by
  cases n with
  | zero => exact le_rfl
  | succ m =>
    exact kl_divergence_nonneg _ _ (actual_joint_law ρ e m) (reference_joint_law hk ρ e m)
      (fun wj => joint_absolute_continuity hk ρ e m wj)

private noncomputable def entropyBlock (ρ : Measure (RelationPath k))
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (n : ℕ) :=
  entropy ρ (blockPartition ρ e 0 n).cells

private theorem entropy_step (hk : 2 ≤ k) (ρ : Measure (RelationPath k))
    [IsProbabilityMeasure ρ] (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r)
    (n : ℕ) (hn : 1 ≤ n) :
    entropyBlock ρ e (n + 1) = entropyBlock ρ e n - Real.log (parryParameter k) - defect ρ e n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let a := actualJoint ρ e m
  let b := referenceJoint ρ e m
  let q (w : Fin (m + 1) → Fin k) (j : Fin k) := suffixKernel k (w (Fin.last m)) j
  let f (j : Fin k) := Real.log (suffixWeight k (parryParameter k) j)
  have hcross :=
    stationary_cross_entropy a q (fun w => w (Fin.last m)) (Real.log (parryParameter k)) f
      (actual_joint_sum ρ e m)
      (fun w j hp => (kernel_log_on_edge hk _ _ (actual_joint_edge ρ e m w j hp)).2)
      (joint_potential_eq ρ T e hshift m f)
  have hid := history_defect a (cylinder ρ e 0) q (split_last ρ e 0)
    (fun w j hz => joint_absolute_continuity hk ρ e m (w, j) hz)
  have hentropy : (∑ x, Real.negMulLog (a x)) = entropyBlock ρ e (m + 2) := by
    rw [entropyBlock, entropy_def, Fintype.sum_prod_type, block_sum_snoc (m + 1)]
    rfl
  change klDivergence a b =
    entropyBlock ρ e (m + 1) - (∑ x, Real.negMulLog (a x)) -
      (∑ w, ∑ j, a (w, j) * Real.log (q w j)) at hid
  rw [hcross, hentropy] at hid
  change entropyBlock ρ e (m + 2) =
    entropyBlock ρ e (m + 1) - Real.log (parryParameter k) - klDivergence a b
  linarith only [hid]


private theorem block_sum_cons {B : Type*} [AddCommMonoid B] (n : ℕ)
    (f : (Fin (n + 1) → Fin k) → B) :
    (∑ w, f w) = ∑ a : Fin k, ∑ w : Fin n → Fin k, f (Fin.cons a w) := by
  let E := Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)
  let g (x : Fin k × (Fin n → Fin k)) := f (E x)
  rw [← Fintype.sum_equiv E g f (fun _ => rfl), Fintype.sum_prod_type g]
  rfl

private theorem defect_monotone (hk : 2 ≤ k) (ρ : Measure (RelationPath k))
    [IsProbabilityMeasure ρ] (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r) :
    Monotone (defect ρ e) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => exact defect_nonneg hk ρ e 1
  | succ m =>
    let a := actualJoint ρ e m
    let b := referenceJoint ρ e m
    let a' := actualJoint ρ e (m + 1)
    let b' := referenceJoint ρ e (m + 1)
    let W := Fin (m + 1) → Fin k
    have hA (w : W) (j : Fin k) : (∑ x : Fin k, a' (Fin.cons x w, j)) = a (w, j) := by
      simp_rw [a', actualJoint, ← Fin.cons_snoc_eq_snoc_cons, split_first]
      simpa [a, actualJoint] using cylinder_shift ρ T e hshift 0 1 (Fin.snoc w j)
    have hB (w : W) (j : Fin k) : (∑ x : Fin k, b' (Fin.cons x w, j)) = b (w, j) := by
      have hlast : Fin.last (m + 1) = (Fin.last m).succ := by apply Fin.ext; rfl
      simp_rw [b', referenceJoint, hlast, Fin.cons_succ, ← Finset.sum_mul, split_first]
      have hm := cylinder_shift ρ T e hshift 0 1 w
      simpa [b, referenceJoint] using congrArg
        (fun x => x * suffixKernel k (w (Fin.last m)) j) hm
    have hle (w : W) (j : Fin k) :
        a (w, j) * Real.log (a (w, j) / b (w, j)) ≤
          ∑ x : Fin k, a' (Fin.cons x w, j) *
            Real.log (a' (Fin.cons x w, j) / b' (Fin.cons x w, j)) := by
      have hl := log_sum_inequality (fun x => a' (Fin.cons x w, j)) (fun x => b' (Fin.cons x w, j))
        (fun x => (actual_joint_law ρ e (m + 1)).1 _)
        (fun x => (reference_joint_law hk ρ e (m + 1)).1 _)
        (fun x => joint_absolute_continuity hk ρ e (m + 1) _)
      rw [hA, hB] at hl
      exact hl
    change klDivergence a b ≤ klDivergence a' b'
    rw [klDivergence, klDivergence, Fintype.sum_prod_type, Fintype.sum_prod_type,
      block_sum_cons (m + 1)]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => hle w j


private theorem transition_of_maximal (hk : 2 ≤ k) (ρ : Measure (RelationPath k))
    [IsProbabilityMeasure ρ] (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hbits : ∀ r : RelationPath k, ∀ t : ℤ,
      (suffixAt e t r).val = 0 ↔ r.val (t - 1) = false)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r)
    (hmax : ksEntropy T = ((-Real.log (parryParameter k) : ℝ) : EReal))
    (m : ℕ) (w : Fin (m + 1) → Fin k) (j : Fin k) :
    cylinder ρ e 0 (Fin.snoc w j) =
      cylinder ρ e 0 w * suffixKernel k (w (Fin.last m)) j := by
  let c := -Real.log (parryParameter k)
  have hrate : ksEntropyPartition T (suffixPartition ρ e 0) = c :=
    EReal.coe_eq_coe_iff.mp ((ks_eq_suffix_partition T e hbits hshift).symm.trans hmax)
  have ht : Tendsto (fun n : ℕ => entropyBlock ρ e n / (n : ℝ)) atTop (nhds c) := by
    have hlim := tendsto_ksEntropySeq T (suffixPartition ρ e 0)
    rw [hrate] at hlim
    simpa only [suffix_seq_eq_block T e hshift, entropyBlock] using hlim
  have hle : c ≤ c - defect ρ e (m + 1) :=
    limit_le_of_defect c c ht (entropy_step hk ρ T e hshift) (defect_monotone hk ρ T e hshift)
      (m + 1) (by omega)
  have hzero : defect ρ e (m + 1) = 0 := le_antisymm (by linarith) (defect_nonneg hk ρ e _)
  have hjoint := (kl_divergence_eq_zero_iff _ _ (actual_joint_law ρ e m)
    (reference_joint_law hk ρ e m) (joint_absolute_continuity hk ρ e m)).1 hzero
  exact congrFun hjoint (w, j)


private theorem cylinders_of_transition (hk : 2 ≤ k) (ρ : Measure (RelationPath k))
    [IsProbabilityMeasure ρ] (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r)
    (htrans : ∀ (m : ℕ) (w : Fin (m + 1) → Fin k) (j : Fin k),
      cylinder ρ e 0 (Fin.snoc w j) = cylinder ρ e 0 w * suffixKernel k (w (Fin.last m)) j)
    (t : ℤ) (n : ℕ) (w : Fin (n + 1) → Fin k) :
    cylinder ρ e t w = suffixLaw k (w 0) *
      ∏ i : Fin n, suffixKernel k (w i.castSucc) (w i.succ) := by
  let u (j : Fin k) := cylinder ρ e 0 (fun _ : Fin 1 => j)
  have hsum : ∑ j, u j = 1 := by
    rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin k)) (fun w => cylinder ρ e 0 w) u]
    · exact cylinder_sum ρ e 0 1
    · intro w
      apply congrArg (cylinder ρ e 0)
      funext i
      exact congrArg w (Subsingleton.elim i 0)
  have hstat (j : Fin k) : (∑ i, u i * suffixKernel k i j) = u j := by
    have hstep (i : Fin k) :
        u i * suffixKernel k i j = cylinder ρ e 0 (Fin.cons i (fun _ : Fin 1 => j)) := by
      have hword : Fin.cons i (fun _ : Fin 1 => j) =
          (Fin.snoc (fun _ : Fin 1 => i) j : Fin 2 → Fin k) := by
        funext a
        fin_cases a <;> rfl
      rw [hword, htrans 0]
    simp_rw [hstep, split_first]
    simpa [u] using cylinder_shift ρ T e hshift 0 1 (fun _ : Fin 1 => j)
  have hu := suffix_stationary_unique hk u hsum hstat
  suffices h0 : ∀ n (w : Fin (n + 1) → Fin k),
      cylinder ρ e 0 w = suffixLaw k (w 0) *
        ∏ i : Fin n, suffixKernel k (w i.castSucc) (w i.succ) by
    rw [← h0]
    rcases le_total 0 t with h | h
    · have hnat : (t.toNat : ℤ) = t := Int.toNat_of_nonneg h
      simpa [hnat] using cylinder_shift ρ T e hshift 0 t.toNat w
    · have hnat : ((-t).toNat : ℤ) = -t := Int.toNat_of_nonneg (by omega)
      simpa [hnat] using (cylinder_shift ρ T e hshift t (-t).toNat w).symm
  intro m
  induction m with
  | zero =>
    intro v
    have hv : (v : Fin 1 → Fin k) = fun _ => v 0 := by
      funext i
      apply congrArg v
      apply Fin.ext
      have := i.isLt
      omega
    rw [Fin.prod_univ_zero, mul_one]
    exact (congrArg (cylinder ρ e 0) hv).trans (congrFun hu (v 0))
  | succ m ih =>
    intro v
    let w := Fin.init v
    let j := v (Fin.last (m + 1))
    have hv : Fin.snoc w j = v := Fin.snoc_init_self v
    rw [← hv, htrans m, ih]
    simp [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, -Fin.castSucc_succ,
      Fin.succ_castSucc, mul_assoc]


private theorem path_measure_eq (ρ μ : Measure (RelationPath k))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hbits : ∀ r : RelationPath k, ∀ t : ℤ,
      (suffixAt e t r).val = 0 ↔ r.val (t - 1) = false)
    (hcyl : ∀ (t : ℤ) (n : ℕ) (w : Fin (n + 1) → Fin k),
      cylinder ρ e t w = cylinder μ e t w) : ρ = μ := by
  classical
  let embed : RelationPath k → ℤ → Bool := Subtype.val
  have : StandardBorelSpace (RelationPath k) := relationPath_standardBorel
  have hemb : MeasurableEmbedding embed :=
    (measurable_subtype_coe : Measurable embed).measurableEmbedding Subtype.val_injective
  apply hemb.map_injective
  apply visible_eq_of_cylinders
  intro t n w
  cases n with
  | zero =>
    have hempty : visibleCylinder t 0 w = Set.univ := by ext r; simp [visibleCylinder]
    simp [hempty, Measure.real]
  | succ m =>
    let read (v : Fin (m + 1) → Fin k) (i : Fin (m + 1)) : Bool :=
      decide ((v i).val ≠ 0)
    let words := Finset.univ.filter fun v => read v = w
    have hword : embed ⁻¹' visibleCylinder t (m + 1) w =
        (suffixBlock e (t + 1) (m + 1)) ⁻¹' (words : Set _) := by
      ext r
      have hb (i : Fin (m + 1)) : r.val (t + i.val) = read (suffixBlock e (t + 1) (m + 1) r) i := by
        have hz := hbits r (t + 1 + i.val)
        rw [show t + 1 + (i.val : ℤ) - 1 = t + i.val by omega] at hz
        change (suffixAt e (t + 1 + i.val) r).val = 0 ↔ _ at hz
        change r.val (t + i.val) = decide ((suffixAt e (t + 1 + i.val) r).val ≠ 0)
        cases hr : r.val (t + i.val) <;> simp_all
      change (∀ i, r.val (t + i.val) = w i) ↔
        suffixBlock e (t + 1) (m + 1) r ∈ (words : Set _)
      simp only [words, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
      simp_rw [hb]
    have hmeas : MeasurableSet (visibleCylinder t (m + 1) w) := by
      change MeasurableSet {z : ℤ → Bool | ∀ i : Fin (m + 1), z (t + i.val) = w i}
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurable_pi_apply (t + i.val) (measurableSet_singleton _)
    have hm (M : Measure (RelationPath k)) [IsFiniteMeasure M] :
        (M.map embed).real (visibleCylinder t (m + 1) w) =
          ∑ v ∈ words, cylinder M e (t + 1) v := by
      rw [Measure.real, Measure.map_apply hemb.measurable hmeas, hword]
      exact (sum_measureReal_preimage_singleton words
        (fun v _ => measurable_suffixBlock e (t + 1) (m + 1)
          (measurableSet_singleton v))).symm
    rw [hm ρ, hm μ]
    exact Finset.sum_congr rfl fun v _ => hcyl (t + 1) m v


/-- The equality case of the full entropy bound determines the native bilateral Parry law. -/
theorem bilateral_parry_maximizer (hk : 2 ≤ k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (μ : ProbabilityMeasure (RelationPath k))
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
        ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (hcyl : ∀ (t : ℤ) (n : ℕ) (w : Fin (n + 1) → Fin k),
      (μ : Measure (RelationPath k))
        {r | (fun i : Fin (n + 1) => ((e (false, r)).val (t + i.val)).2) = w} =
        ENNReal.ofReal (suffixLaw k (w 0)) *
          ∏ i : Fin n, ENNReal.ofReal (suffixKernel k (w i.castSucc) (w i.succ)))
    (ρ : ProbabilityMeasure (RelationPath k))
    (Tρ : MeasurePreserving (@relationShift k) ρ ρ) :
    ksEntropy Tρ ≤ ((-Real.log (parryParameter k) : ℝ) : EReal) ∧
      (ksEntropy Tρ = ((-Real.log (parryParameter k) : ℝ) : EReal) ↔ ρ = μ) := by
  have hbits (r : RelationPath k) (t : ℤ) := suffix_zero_iff e hsuffix r t
  have hshift (r : RelationPath k) (n : ℕ) (t : ℤ) := suffix_iterate_shift e hsuffix r n t
  have unique (η : ProbabilityMeasure (RelationPath k))
      (Tη : MeasurePreserving (@relationShift k) η η)
      (hη : ksEntropy Tη = ((-Real.log (parryParameter k) : ℝ) : EReal)) : η = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    refine path_measure_eq η μ e hbits fun t n w => ?_
    rw [cylinders_of_transition hk η Tη e hshift (transition_of_maximal hk η Tη e hbits hshift hη)]
    symm
    change ((μ : Measure (RelationPath k))
      {r | (fun i : Fin (n + 1) => ((e (false, r)).val (t + i.val)).2) = w}).toReal = _
    rw [hcyl, ENNReal.toReal_mul, ENNReal.toReal_ofReal (suffixLaw_pos hk _).le,
      ENNReal.toReal_prod]
    simp_rw [ENNReal.toReal_ofReal (kernel_nonneg hk _ _)]
  obtain ⟨_, η, Tη, _, hη, hupper⟩ := bilateral_parry_entropy k hk
  refine ⟨hupper ρ Tρ, ⟨unique ρ Tρ, ?_⟩⟩
  have hμ : η = μ := unique η Tη hη
  intro hρ
  have heq : η = ρ := hμ.trans hρ.symm
  cases heq
  exact hη

end D5.S3.TotalVariation.ParryKSMaximizer

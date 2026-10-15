/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteAllStateLimits
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteAllStateLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-matrix periodic limits from actual first-entry laws. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition
import Mathlib.Analysis.Normed.Group.Tannery

open Finset Matrix Filter Topology
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits
open FiniteClosedClasses FiniteGenuinePeriods FiniteCyclicBlocks FiniteClosedClassLimits
open FiniteEntranceDecomposition
noncomputable section
universe u
variable {X : Type u} [Fintype X] [DecidableEq X]
variable {P : Matrix X X ℝ} {C : ClosedClass P}
local instance (P : Matrix X X ℝ) : DecidablePred (Recurrent P) := Classical.decPred _

private theorem shifted_class_limit (hP : P ∈ rowStochastic ℝ X)
    (K : ClassPeriods P C) (L : ClassLimit K) (d : ℕ) (hd : 0 < d)
    (hpd : period (restriction P C.val) K.base ∣ d) (i m : ℕ) (z y : C.val) :
    Tendsto (fun t : ℕ => (restriction P C.val ^ (d * t + i - m)) z y) atTop
      (𝓝 (if K.phase z + (i : ZMod (period (restriction P C.val) K.base)) -
          (m : ZMod (period (restriction P C.val) K.base)) = K.phase y
        then (period (restriction P C.val) K.base : ℝ) * L.stationaryRow y else 0)) := by
  classical
  let p := period (restriction P C.val) K.base
  have hm : m ≤ d * m + i := le_trans (Nat.le_mul_of_pos_left m hd) (Nat.le_add_right _ _)
  have hc : ((d * m + i - m : ℕ) : ZMod p) = (i : ZMod p) - (m : ZMod p) := by
    obtain ⟨q, hq⟩ := hpd
    rw [Nat.cast_sub hm, Nat.cast_add, Nat.cast_mul, hq]
    simp [p, Nat.cast_mul]
  have ht := (L.convergence d hd hpd (d * m + i - m) z y).comp (tendsto_sub_atTop_nat m)
  simp_rw [← (actual_structure P hP).class_powers C] at ht
  rw [hc] at ht
  have he : (fun t : ℕ => (restriction P C.val ^ (d * t + i - m)) z y) =ᶠ[atTop]
      (fun t : ℕ => (restriction P C.val ^ (d * (t - m) + (d * m + i - m))) z y) := by
    filter_upwards [eventually_ge_atTop m] with t ht
    have hexp : d*t+i-m = d*(t-m)+(d*m+i-m) := by
      rw [Nat.mul_sub_left_distrib]
      have hmul := Nat.mul_le_mul_left d ht
      omega
    rw [hexp]
  simpa only [add_sub_assoc] using ht.congr' he.symm


private theorem phase_entry_iff (K : ClassPeriods P C) (i n : ℕ) (z y : C.val) :
    K.phase z + (i : ZMod (period (restriction P C.val) K.base)) - (n + 1 : ℕ) = K.phase y ↔
    K.phase z - (n + 1 : ℕ) = K.phase y - (i : ℕ) := by
  constructor <;> intro h <;> linear_combination h

private theorem transient_class_limit (hP : P ∈ rowStochastic ℝ X) (H : EntranceLaw P)
    (K : ClassPeriods P C) (L : ClassLimit K) (d : ℕ) (hd : 0 < d)
    (hpd : period (restriction P C.val) K.base ∣ d) (i : ℕ)
    (x : Transient P) (y : C.val) :
    Tendsto (fun t : ℕ => (P ^ (d * t + i)) x.val y.val) atTop
      (𝓝 ((period (restriction P C.val) K.base : ℝ) * L.stationaryRow y *
        psiTransient K x (K.phase y - (i : ZMod (period (restriction P C.val) K.base))))) := by
  classical
  let a := (period (restriction P C.val) K.base : ℝ) * L.stationaryRow y
  let f (z : C.val) (t n : ℕ) : ℝ :=
    if n < d * t + i then entrance P C n x z *
      (restriction P C.val ^ (d * t + i - (n + 1))) z y else 0
  let g (z : C.val) (n : ℕ) : ℝ :=
    if K.phase z - (n + 1 : ℕ) = K.phase y - (i : ℕ)
    then entrance P C n x z * a else 0
  have hpoint (z : C.val) (n : ℕ) :
      Tendsto (fun t => f z t n) atTop (𝓝 (g z n)) := by
    have ht := (shifted_class_limit hP K L d hd hpd i (n+1) z y).const_mul
      (entrance P C n x z)
    simp only [phase_entry_iff, mul_ite, mul_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (n+1)] with t ht
    have hdt := Nat.le_mul_of_pos_left t hd
    simp [f, show n < d*t+i by omega]
  have hbound (z : C.val) (t n : ℕ) : ‖f z t n‖ ≤ entrance P C n x z := by
    have hn := H.nonnegative C n x z
    have hs := (rowStochastic ℝ C.val).pow_mem
      ((actual_structure P hP).class_stochastic C) (d*t+i-(n+1))
    have hb : (restriction P C.val ^ (d*t+i-(n+1))) z y ≤ 1 := by
      rw [← sum_row_of_mem_rowStochastic hs z]
      exact single_le_sum (fun w _ => hs.1 z w) (mem_univ y)
    dsimp only [f]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (hs.1 z y))]
      exact mul_le_of_le_one_right hn hb
    · simpa using hn
  have hmass (z : C.val) (t n : ℕ) :
      ‖f z t n‖ ≤ ∑ D : ClosedClass P, ∑ w : D.val, entrance P D n x w := by
    calc
      _ ≤ entrance P C n x z := hbound z t n
      _ ≤ ∑ w : C.val, entrance P C n x w :=
        single_le_sum (fun w _ => H.nonnegative C n x w) (mem_univ z)
      _ ≤ _ := single_le_sum (f := fun D : ClosedClass P =>
        ∑ w : D.val, entrance P D n x w)
        (fun D _ => sum_nonneg fun w _ => H.nonnegative D n x w) (mem_univ C)
  have ht (z : C.val) :
      Tendsto (fun t => ∑' n, f z t n) atTop (𝓝 (∑' n, g z n)) :=
    tendsto_tsum_of_dominated_convergence (H.total_mass x).summable
      (hpoint z) (Eventually.of_forall (fun t n => hmass z t n))
  have hs := tendsto_finsetSum univ (fun z _ => ht z)
  have he (t : ℕ) : (∑ z : C.val, ∑' n, f z t n) = (P ^ (d*t+i)) x.val y.val := by
    rw [H.decomposition C (d*t+i) x y, sum_comm]
    apply sum_congr rfl
    intro z _
    rw [tsum_eq_sum (s := range (d*t+i))]
    · apply sum_congr rfl
      intro n hn
      simp [f, mem_range.mp hn]
    · intro n hn
      simp [f, show ¬ n < d*t+i by simpa using hn]
  have hg : (∑ z : C.val, ∑' n, g z n) = a *
      psiTransient K x (K.phase y - (i : ZMod (period (restriction P C.val) K.base))) := by
    unfold psiTransient
    rw [mul_sum]
    apply sum_congr rfl
    intro z _
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [g]
    split_ifs <;> ring
  rw [hg] at hs
  exact hs.congr he


/-- The original-matrix limit entry: closed target phases use the physical first-entry law. -/
def periodicEntry (K : ∀ C : ClosedClass P, ClassPeriods P C)
    (L : ∀ C, ClassLimit (K C)) (i : ℕ) (x y : X) : ℝ :=
  if hy : Recurrent P y then
    let C := hy.choose
    let yy : C.val := ⟨y, hy.choose_spec⟩
    let p := period (restriction P C.val) (K C).base
    if hx : x ∈ C.val then
      if (K C).phase ⟨x, hx⟩ + (i : ZMod p) = (K C).phase yy
      then (p : ℝ) * (L C).stationaryRow yy else 0
    else if hxt : ¬ Recurrent P x then
      (p : ℝ) * (L C).stationaryRow yy *
        psiTransient (K C) ⟨x, hxt⟩ ((K C).phase yy - (i : ZMod p))
    else 0
  else 0

private theorem transient_target_limit (hP : P ∈ rowStochastic ℝ X)
    (d : ℕ) (hd : 0 < d) (i : ℕ) (x : X) (y : Transient P) :
    Tendsto (fun t : ℕ => (P ^ (d*t+i)) x y.val) atTop (𝓝 0) := by
  classical
  have hS := actual_structure P hP
  by_cases hx : Recurrent P x
  · obtain ⟨C, hx⟩ := hx
    have hy : y.val ∉ C.val := fun he => y.property ⟨C, he⟩
    exact tendsto_const_nhds.congr (fun t =>
      (hS.class_no_exit C (d*t+i) ⟨x, hx⟩ y.val hy).symm)
  · have ht : Tendsto (fun t : ℕ => d*t+i) atTop atTop :=
      tendsto_atTop_mono (fun t => le_trans (Nat.le_mul_of_pos_left t hd)
        (Nat.le_add_right _ _)) tendsto_id
    have hh := (hS.transient_decay ⟨x, hx⟩ y).comp ht
    exact hh.congr (fun t => hS.transient_powers (d*t+i) ⟨x, hx⟩ y)

private theorem entrywise_limit (hP : P ∈ rowStochastic ℝ X) (H : EntranceLaw P)
    (K : ∀ C : ClosedClass P, ClassPeriods P C) (L : ∀ C, ClassLimit (K C))
    (d : ℕ) (hd : 0 < d) (hpd : ∀ C, period (restriction P C.val) (K C).base ∣ d)
    (i : ℕ) (x y : X) :
    Tendsto (fun t : ℕ => (P ^ (d*t+i)) x y) atTop (𝓝 (periodicEntry K L i x y)) := by
  classical
  by_cases hy : Recurrent P y
  · let C := hy.choose
    let yy : C.val := ⟨y, hy.choose_spec⟩
    simp only [periodicEntry, dif_pos hy]
    change Tendsto (fun t : ℕ => (P ^ (d*t+i)) x y) atTop
      (𝓝 (if hx : x ∈ C.val then
        if (K C).phase ⟨x, hx⟩ + (i : ZMod (period (restriction P C.val) (K C).base)) =
          (K C).phase yy then (period (restriction P C.val) (K C).base : ℝ) *
          (L C).stationaryRow yy else 0
        else if hxt : ¬ Recurrent P x then
          (period (restriction P C.val) (K C).base : ℝ) * (L C).stationaryRow yy *
            psiTransient (K C) ⟨x, hxt⟩ ((K C).phase yy - (i : ℕ)) else 0))
    by_cases hx : x ∈ C.val
    · simpa only [dif_pos hx] using
        (L C).convergence d hd (hpd C) i ⟨x, hx⟩ yy
    · by_cases hxt : ¬ Recurrent P x
      · simpa only [dif_neg hx, dif_pos hxt] using
          transient_class_limit hP H (K C) (L C) d hd (hpd C) i ⟨x, hxt⟩ yy
      · have hxr : Recurrent P x := Classical.not_not.mp hxt
        obtain ⟨D, hxD⟩ := hxr
        have hne : D ≠ C := by rintro rfl; exact hx hxD
        have hyD : y ∉ D.val := fun he =>
          Finset.disjoint_left.mp ((actual_structure P hP).disjoint D C hne) he yy.property
        simpa only [dif_neg hx, dif_neg hxt] using
          (tendsto_const_nhds.congr (fun t =>
            ((actual_structure P hP).class_no_exit D (d*t+i) ⟨x, hxD⟩ y hyD).symm) :
            Tendsto (fun t : ℕ => (P ^ (d*t+i)) x y) atTop (𝓝 0))
  · simpa only [periodicEntry, dif_neg hy] using
      transient_target_limit hP d hd i x ⟨y, hy⟩

/-- All original-matrix state limits with actual classes, genuine phases and first-entry tails. -/
structure AllStateLimits (P : Matrix X X ℝ) where
  periods : ∀ C : ClosedClass P, ClassPeriods P C
  classes : ∀ C, ClassLimit (periods C)
  entranceLaw : EntranceLaw P
  transient_class : ∀ (C : ClosedClass P) (d : ℕ), 0 < d →
    period (restriction P C.val) (periods C).base ∣ d →
    ∀ (i : ℕ) (x : Transient P) (y : C.val),
    Tendsto (fun t : ℕ => (P ^ (d*t+i)) x.val y.val) atTop
      (𝓝 ((period (restriction P C.val) (periods C).base : ℝ) *
        (classes C).stationaryRow y * psiTransient (periods C) x
          ((periods C).phase y - (i : ZMod (period (restriction P C.val) (periods C).base)))))
  transient_target : ∀ (d : ℕ), 0 < d → ∀ (i : ℕ) (x : X) (y : Transient P),
    Tendsto (fun t : ℕ => (P ^ (d*t+i)) x y.val) atTop (𝓝 0)
  late_control : ∀ (C : ClosedClass P) (M : ℕ) (x : Transient P) (y : C.val),
    (∀ T : ℕ, ‖∑ n ∈ range (T-M), ∑ z : C.val, entrance P C (n+M) x z *
      (restriction P C.val ^ (T-(n+M+1))) z y‖ ≤
        ∑' n : ℕ, ∑ D : ClosedClass P, ∑ z : D.val, entrance P D (n+M) x z) ∧
    Tendsto (fun M : ℕ => ∑' n : ℕ, ∑ D : ClosedClass P, ∑ z : D.val,
      entrance P D (n+M) x z) atTop (𝓝 0)
  class_no_exit : ∀ (C : ClosedClass P) (n : ℕ) (x : C.val) (y : X),
    y ∉ C.val → (P ^ n) x.val y = 0
  convergence : ∀ (d : ℕ), 0 < d →
    (∀ C, period (restriction P C.val) (periods C).base ∣ d) →
    ∀ (i : ℕ) (x y : X),
    Tendsto (fun t : ℕ => (P ^ (d*t+i)) x y) atTop
      (𝓝 (periodicEntry periods classes i x y))

/-- Every finite real stochastic matrix has all-state periodic limits under each positive
common multiple of its genuine closed-class periods and every natural residue. -/
theorem actual_all_state_limits (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X) :
    Nonempty (AllStateLimits P) := by
  classical
  let K (C : ClosedClass P) : ClassPeriods P C := (actual_limits P hP C).choose
  let L (C : ClosedClass P) : ClassLimit (K C) :=
    Classical.choice (actual_limits P hP C).choose_spec.2
  have H := actual_entrance P hP
  exact ⟨{
    periods := K
    classes := L
    entranceLaw := H
    transient_class := fun C d hd hpd i x y =>
      transient_class_limit hP H (K C) (L C) d hd hpd i x y
    transient_target := transient_target_limit hP
    late_control := fun C M x y => ⟨fun T => by
      rw [Real.norm_eq_abs, abs_of_nonneg (H.late_contribution C T M x y).1,
        H.tail_mass M x]
      exact (H.late_contribution C T M x y).2, H.tail_tendsto x⟩
    class_no_exit := (actual_structure P hP).class_no_exit
    convergence := entrywise_limit hP H K L }⟩

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits

/- GID: D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-exit bounds for unrestricted generated laws retain finite survivor mass. -/

import D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw

/-! Finite first-exit partitions of the actual complete generated word laws. -/

namespace D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators
noncomputable section

/-- Probability of surviving the first n generated symbols without leaving B. -/
def survival {Z : Type*} (O : GeneratedObserver Z) : Z → Nat → ℝ
  | _, 0 => 1
  | z, n+1 => O.row z B * survival O (O.update z B) n

/-- Probability of the first non-B symbol at n, grouped into {0} or {1,3}. -/
def exitCoefficient {Z : Type*} (O : GeneratedObserver Z) : Z → Nat → Bool → ℝ
  | z, 0, true => O.row z 0
  | z, 0, false => O.row z 1 + O.row z 3
  | z, n+1, t => O.row z B * exitCoefficient O (O.update z B) n t

private lemma exit_nonneg {Z : Type*} (O : GeneratedObserver Z) (z : Z) (n : Nat) (t : Bool) :
    0 ≤ exitCoefficient O z n t := by
  induction n generalizing z with
  | zero =>
    cases t with
    | false => exact add_nonneg (O.row_nonneg _ _) (O.row_nonneg _ _)
    | true => exact O.row_nonneg _ _
  | succ n ih => exact mul_nonneg (O.row_nonneg _ _) (ih _)

private lemma normalized_abs_sum {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∑ i, f i = 1) (hg : ∑ i, g i = 1) (A C : ℝ) :
    |A-C| ≤ ∑ i, |A*f i-C*g i| := by
  have hs : (∑ i, (A*f i-C*g i)) = A-C := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hf, hg, mul_one]
  rw [← hs]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Coarsening retains both exit categories and the all-B survivor atom. The
continuation of the generated process after an exit is unrestricted. -/
private theorem generated_exit_coarsening {Z : Type*} (O : GeneratedObserver Z)
    {p q r : ℝ} (hp : admissible p q r) (z : Z) (A C E : ℝ) (H : Nat) :
    (∑ n ∈ Finset.range H,
      (|C*r*(b r)^n-E*exitCoefficient O z n true| +
       |A*(p+q)*(a p q)^n-E*exitCoefficient O z n false|)) +
      |A*(a p q)^H+C*(b r)^H-E*survival O z H| ≤
    ∑ w : Fin H → Visible,
      |A*pureLaw p q r 2 H w+C*pureLaw p q r 4 H w-
        E*generatedLaw O.update O.row z H w| := by
  classical
  induction H generalizing z A C E with
  | zero => simp [pure_zero, generatedLaw, survival]
  | succ H ih =>
    let z' := O.update z B
    let e := O.row z B
    have hb := ih z' (A*a p q) (C*b r) (E*e)
    have h0 := normalized_abs_sum (pureLaw p q r 0 H)
      (generatedLaw O.update O.row (O.update z 0) H)
      (pure_probability hp 0 H).2 (generated_sum _ _ O.row_sum _ H) (C*r) (E*O.row z 0)
    have h1 := normalized_abs_sum (pureLaw p q r 1 H)
      (generatedLaw O.update O.row (O.update z 1) H)
      (pure_probability hp 1 H).2 (generated_sum _ _ O.row_sum _ H) (A*q) (E*O.row z 1)
    have h3 := normalized_abs_sum (pureLaw p q r 3 H)
      (generatedLaw O.update O.row (O.update z 3) H)
      (pure_probability hp 3 H).2 (generated_sum _ _ O.row_sum _ H) (A*p) (E*O.row z 3)
    have h13 : |A*(p+q)-E*(O.row z 1+O.row z 3)| ≤
        |A*q-E*O.row z 1|+|A*p-E*O.row z 3| := by
      convert abs_add_le (A*q-E*O.row z 1) (A*p-E*O.row z 3) using 1 <;> congr 1 <;> ring
    have hrhs : (∑ w : Fin (H+1) → Visible,
        |A*pureLaw p q r 2 (H+1) w+C*pureLaw p q r 4 (H+1) w-
          E*generatedLaw O.update O.row z (H+1) w|) =
        (∑ w : Fin H → Visible, |C*r*pureLaw p q r 0 H w-
          (E*O.row z 0)*generatedLaw O.update O.row (O.update z 0) H w|) +
        (∑ w : Fin H → Visible, |A*q*pureLaw p q r 1 H w-
          (E*O.row z 1)*generatedLaw O.update O.row (O.update z 1) H w|) +
        (∑ w : Fin H → Visible, |(A*a p q)*pureLaw p q r 2 H w+
          (C*b r)*pureLaw p q r 4 H w-(E*e)*generatedLaw O.update O.row z' H w|) +
        (∑ w : Fin H → Visible, |A*p*pureLaw p q r 3 H w-
          (E*O.row z 3)*generatedLaw O.update O.row (O.update z 3) H w|) := by
      rw [sum_words_succ]
      simp [branch2_cons, branch4_cons, generated_cons, B, Fin.sum_univ_succ,
        mul_assoc, add_assoc, e, z']
    rw [hrhs]
    have hlhs : (∑ n ∈ Finset.range (H+1),
        (|C*r*(b r)^n-E*exitCoefficient O z n true|+
         |A*(p+q)*(a p q)^n-E*exitCoefficient O z n false|))+
        |A*(a p q)^(H+1)+C*(b r)^(H+1)-E*survival O z (H+1)| =
        |C*r-E*O.row z 0|+|A*(p+q)-E*(O.row z 1+O.row z 3)|+
        ((∑ n ∈ Finset.range H,
          (|(C*b r)*r*(b r)^n-(E*e)*exitCoefficient O z' n true|+
           |(A*a p q)*(p+q)*(a p q)^n-(E*e)*exitCoefficient O z' n false|))+
          |(A*a p q)*(a p q)^H+(C*b r)*(b r)^H-(E*e)*survival O z' H|) := by
      rw [Finset.sum_range_succ']
      simp only [exitCoefficient, survival, pow_zero, mul_one, pow_succ]
      dsimp [e, z']
      have heq (n : Nat) :
          |C*r*((b r)^n*b r)-E*(O.row z B*exitCoefficient O (O.update z B) n true)|+
          |A*(p+q)*((a p q)^n*a p q)-E*(O.row z B*exitCoefficient O (O.update z B) n false)| =
          |C*b r*r*(b r)^n-E*O.row z B*exitCoefficient O (O.update z B) n true|+
          |A*a p q*(p+q)*(a p q)^n-E*O.row z B*exitCoefficient O (O.update z B) n false| := by
        congr 1 <;> congr 1 <;> ring
      simp_rw [heq]
      have hr :
          |A*((a p q)^H*a p q)+C*((b r)^H*b r)-E*(O.row z B*survival O (O.update z B) H)| =
          |(A*a p q)*(a p q)^H+(C*b r)*(b r)^H-(E*O.row z B)*survival O (O.update z B) H| := by
        congr 1 <;> ring
      rw [hr]
      ring
    rw [hlhs]
    linarith only [hb, h0, h1, h3, h13]


private def partitionNorm (f g : Nat → Bool → ℝ) (s t : Nat → ℝ) (H : Nat) : ℝ :=
  (∑ n ∈ Finset.range H, ∑ c : Bool, |f n c-g n c|)+|s H-t H|

private def defect (a b c : ℝ) : ℝ := |a-c|+|b-c|-|a-b|

private lemma defect_nonneg (a b c : ℝ) : 0 ≤ defect a b c := by
  have h := abs_add_le (a-c) (c-b)
  rw [show a-c+(c-b) = a-b by ring, abs_sub_comm c b] at h
  exact sub_nonneg.mpr h

private lemma coordinate_defect_le (f g q : Nat → Bool → ℝ) (s t r : Nat → ℝ)
    (H n : Nat) (hn : n < H) (c : Bool) :
    defect (f n c) (g n c) (q n c) ≤
      partitionNorm f q s r H+partitionNorm g q t r H-partitionNorm f g s t H := by
  classical
  have h1 : defect (f n c) (g n c) (q n c) ≤
      ∑ d : Bool, defect (f n d) (g n d) (q n d) :=
    Finset.single_le_sum (fun d _ => defect_nonneg _ _ _) (Finset.mem_univ c)
  have h2 : (∑ d : Bool, defect (f n d) (g n d) (q n d)) ≤
      ∑ k ∈ Finset.range H, ∑ d : Bool, defect (f k d) (g k d) (q k d) :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun d _ => defect_nonneg _ _ _))
      (Finset.mem_range.mpr hn)
  calc
    _ ≤ (∑ k ∈ Finset.range H, ∑ d : Bool, defect (f k d) (g k d) (q k d))+
        defect (s H) (t H) (r H) :=
      (h1.trans h2).trans (le_add_of_nonneg_right (defect_nonneg _ _ _))
    _ = _ := by
      simp only [defect, partitionNorm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring

private lemma limiting_coordinate_box (f g q : Nat → Bool → ℝ) (s t r : Nat → ℝ)
    (D : ℝ) (hf : ∀ H, partitionNorm f q s r H ≤ D)
    (hg : ∀ H, partitionNorm g q t r H ≤ D)
    (hlim : Filter.Tendsto (partitionNorm f g s t) Filter.atTop (nhds (2*D)))
    (n : Nat) (c : Bool) :
    min (f n c) (g n c) ≤ q n c ∧ q n c ≤ max (f n c) (g n c) := by
  have hindex : Filter.Tendsto (fun k : Nat => k+n+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (f := fun k : Nat => k) (fun k => by omega) Filter.tendsto_id
  have hl := (tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => 2*D)
    Filter.atTop (nhds (2*D))).sub (hlim.comp hindex)
  have hd : defect (f n c) (g n c) (q n c) ≤ 0 := by
    have hlim' : Filter.Tendsto (fun k : Nat => 2*D-partitionNorm f g s t (k+n+1))
        Filter.atTop (nhds 0) := by simpa using hl
    apply ge_of_tendsto hlim'
    apply Filter.Eventually.of_forall
    intro k
    have h := coordinate_defect_le f g q s t r (k+n+1) n (by omega) c
    linarith [hf (k+n+1), hg (k+n+1)]
  unfold defect at hd
  by_cases hfg : f n c ≤ g n c
  · rw [min_eq_left hfg, max_eq_right hfg]
    rw [abs_of_nonpos (sub_nonpos.mpr hfg)] at hd
    constructor
    · linarith [le_abs_self (f n c-q n c), le_abs_self (g n c-q n c)]
    · linarith [neg_le_abs (f n c-q n c), neg_le_abs (g n c-q n c)]
  · have hgf := le_of_not_ge hfg
    rw [min_eq_right hgf, max_eq_left hgf]
    rw [abs_of_nonneg (sub_nonneg.mpr hgf)] at hd
    constructor
    · linarith [le_abs_self (f n c-q n c), le_abs_self (g n c-q n c)]
    · linarith [neg_le_abs (f n c-q n c), neg_le_abs (g n c-q n c)]

private def geometricExit (u v D : ℝ) (n : Nat) (c : Bool) : ℝ :=
  if c then D*(1-u)*u^n else (1-D)*(1-v)*v^n

private def geometricSurvival (u v D : ℝ) (H : Nat) : ℝ :=
  (1-D)*v^H+D*u^H

private lemma geometric_partition_distance {u v D : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1) (hD : 0 ≤ D) (H : Nat) :
    partitionNorm (geometricExit u v 0) (geometricExit u v D)
      (geometricSurvival u v 0) (geometricSurvival u v D) H = 2*D*(1-u^H) := by
  have hv0 := hu.trans huv
  have hu1 := huv.trans hv
  have hv1 := sub_nonneg.mpr hv
  have hu1' := sub_nonneg.mpr hu1
  have hpow := pow_le_pow_left₀ hu huv H
  have he (n : Nat) : (∑ c : Bool, |geometricExit u v 0 n c-geometricExit u v D n c|) =
      D*(1-v)*v^n+D*(1-u)*u^n := by
    simp only [Fintype.sum_bool, geometricExit, Bool.false_eq_true, ite_true, ite_false, zero_mul, sub_zero,
      one_mul, zero_sub, abs_neg]
    have h1 : (1-v)*v^n-(1-D)*(1-v)*v^n = D*(1-v)*v^n := by ring
    rw [h1, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    ring
  have hs : |geometricSurvival u v 0 H-geometricSurvival u v D H| = D*(v^H-u^H) := by
    have h1 : geometricSurvival u v 0 H-geometricSurvival u v D H = D*(v^H-u^H) := by
      simp only [geometricSurvival]; ring
    rw [h1, abs_of_nonneg (mul_nonneg hD (sub_nonneg.mpr hpow))]
  have hsum (t : ℝ) : (∑ n ∈ Finset.range H, (1-t)*t^n) = 1-t^H := by
    rw [← Finset.mul_sum, mul_neg_geom_sum]
  unfold partitionNorm
  simp_rw [he]
  rw [hs, Finset.sum_add_distrib]
  have hsumD (t : ℝ) : (∑ n ∈ Finset.range H, D*(1-t)*t^n) = D*(1-t^H) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hsum]
  rw [hsumD, hsumD]
  ring

private lemma geometric_coordinate_box {u v D : ℝ} (hu : 0 < u) (huv : u < v)
    (hv : v < 1) (hD : 0 < D)
    (q : Nat → Bool → ℝ) (r : Nat → ℝ)
    (h0 : ∀ H, partitionNorm (geometricExit u v 0) q (geometricSurvival u v 0) r H ≤ D)
    (h1 : ∀ H, partitionNorm (geometricExit u v D) q (geometricSurvival u v D) r H ≤ D)
    (n : Nat) :
    (1-D)*(1-v)*v^n ≤ q n false ∧ q n false ≤ (1-v)*v^n ∧
    0 ≤ q n true ∧ q n true ≤ D*(1-u)*u^n := by
  have hlim : Filter.Tendsto
      (partitionNorm (geometricExit u v 0) (geometricExit u v D)
        (geometricSurvival u v 0) (geometricSurvival u v D)) Filter.atTop (nhds (2*D)) := by
    change Filter.Tendsto (fun H => partitionNorm (geometricExit u v 0) (geometricExit u v D)
      (geometricSurvival u v 0) (geometricSurvival u v D) H) _ _
    simp_rw [geometric_partition_distance hu.le huv.le hv.le hD.le]
    have hz := tendsto_pow_atTop_nhds_zero_of_lt_one hu.le (huv.trans hv)
    convert (tendsto_const_nhds.sub hz).const_mul (2*D) using 1 <;> simp
  have hd := limiting_coordinate_box _ _ _ _ _ _ D h0 h1 hlim n false
  have hf := limiting_coordinate_box _ _ _ _ _ _ D h0 h1 hlim n true
  have hv0 : 0 ≤ v := (hu.trans huv).le
  have hu1 := sub_nonneg.mpr (huv.trans hv).le
  have hv1 := sub_nonneg.mpr hv.le
  have hge : (1-D)*(1-v)*v^n ≤ (1-v)*v^n := by
    have hnon : 0 ≤ (1-v)*v^n := by positivity
    nlinarith
  have hnon : 0 ≤ D*(1-u)*u^n := by positivity
  simp only [geometricExit, Bool.false_eq_true, ite_false, ite_true, sub_zero, one_mul,
    zero_mul, min_eq_right hge, max_eq_left hge, min_eq_left hnon, max_eq_right hnon] at hd hf
  exact ⟨hd.1, hd.2, hf⟩


private lemma oriented_partition_bound {Z : Type*} (O : GeneratedObserver Z)
    {p q r : ℝ} (hp : admissible p q r) (z : Z) (x : ℝ) (H : Nat) :
    partitionNorm (geometricExit (min (a p q) (b r)) (max (a p q) (b r)) x)
      (fun n c => exitCoefficient O z n (if b r < a p q then c else !c))
      (geometricSurvival (min (a p q) (b r)) (max (a p q) (b r)) x)
      (survival O z) H ≤
      2*totalVariation (orientedMixture p q r x H) (generatedLaw O.update O.row z H) := by
  classical
  have ha : 1-a p q = p+q := by unfold a; ring
  have hb : 1-b r = r := by unfold b; ring
  by_cases hab : b r < a p q
  · have hc := generated_exit_coarsening O hp z (1-x) x 1 H
    have ht : 2*totalVariation (orientedMixture p q r x H) (generatedLaw O.update O.row z H) =
        ∑ w : Fin H → Visible,
          |(1-x)*pureLaw p q r 2 H w+x*pureLaw p q r 4 H w-
            1*generatedLaw O.update O.row z H w| := by
      unfold totalVariation
      have he (w : Fin H → Visible) : orientedMixture p q r x H w =
          (1-x)*pureLaw p q r 2 H w+x*pureLaw p q r 4 H w := by
        simp only [orientedMixture, if_pos hab, mixtureLaw]
        ring
      simp_rw [he]
      ring_nf
    rw [ht]
    convert hc using 1
    simp only [partitionNorm, Fintype.sum_bool, geometricExit, geometricSurvival,
      min_eq_right hab.le, max_eq_left hab.le, if_pos hab, Bool.false_eq_true,
      ite_true, ite_false, ha, hb, one_mul]
  · have hba := le_of_not_gt hab
    have hc := generated_exit_coarsening O hp z x (1-x) 1 H
    have ht : 2*totalVariation (orientedMixture p q r x H) (generatedLaw O.update O.row z H) =
        ∑ w : Fin H → Visible,
          |x*pureLaw p q r 2 H w+(1-x)*pureLaw p q r 4 H w-
            1*generatedLaw O.update O.row z H w| := by
      simp only [totalVariation, orientedMixture, if_neg hab, mixtureLaw]
      ring_nf
    rw [ht]
    convert hc using 1
    simp only [partitionNorm, Fintype.sum_bool, geometricExit, geometricSurvival,
      min_eq_left hba, max_eq_right hba, if_neg hab, Bool.false_eq_true,
      Bool.not_true, Bool.not_false, ite_true, ite_false, ha, hb, one_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro n _
      ring
    · congr 1
      ring

/-- The limiting diameter tie constrains the actual generated exit probabilities.
The all-B survivor is retained at every finite stage of the limiting argument. -/
private theorem generated_diameter_exit_box {Z : Type*} (O : GeneratedObserver Z)
    {p q r D : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (z : Z) (hD : 0 < D) (hD1 : D < 1)
    (h0 : profileDistance (dominantLaw p q r) (generatedLaw O.update O.row z) ≤ D/2)
    (h1 : profileDistance (orientedMixture p q r D) (generatedLaw O.update O.row z) ≤ D/2)
    (n : Nat) :
    (1-D)*(1-max (a p q) (b r))*(max (a p q) (b r))^n ≤
      exitCoefficient O z n (if b r < a p q then false else true) ∧
    exitCoefficient O z n (if b r < a p q then false else true) ≤
      (1-max (a p q) (b r))*(max (a p q) (b r))^n ∧
    0 ≤ exitCoefficient O z n (if b r < a p q then true else false) ∧
    exitCoefficient O z n (if b r < a p q then true else false) ≤
      D*(1-min (a p q) (b r))*(min (a p q) (b r))^n := by
  classical
  have hu : 0 < min (a p q) (b r) := lt_min (holding_bounds hp).1 (holding_bounds hp).2.2.1
  have hv : max (a p q) (b r) < 1 := max_lt (holding_bounds hp).2.1 (holding_bounds hp).2.2.2.1
  have huv : min (a p q) (b r) < max (a p q) (b r) := by
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [min_eq_left h.le, max_eq_right h.le] using h
    · simpa [min_eq_right h.le, max_eq_left h.le] using h
  have hprob : ProbabilityProfile (generatedLaw O.update O.row z) := (generated_coherent O z).1
  have hbound (x : ℝ) (hx : x ∈ Set.Icc 0 1)
      (hd : profileDistance (orientedMixture p q r x) (generatedLaw O.update O.row z) ≤ D/2) :
      ∀ H, partitionNorm (geometricExit (min (a p q) (b r)) (max (a p q) (b r)) x)
        (fun n c => exitCoefficient O z n (if b r < a p q then c else !c))
        (geometricSurvival (min (a p q) (b r)) (max (a p q) (b r)) x) (survival O z) H ≤ D := by
    intro H
    have hp' : ProbabilityProfile (orientedMixture p q r x) := by
      unfold orientedMixture
      split_ifs
      · exact mixture_probability hp ⟨by linarith [hx.2], by linarith [hx.1]⟩
      · exact mixture_probability hp hx
    have hh := (finite_le_profile hp' hprob H).trans hd
    have hc := oriented_partition_bound O hp z x H
    linarith
  have hd0 : profileDistance (orientedMixture p q r 0) (generatedLaw O.update O.row z) ≤ D/2 := by
    simpa only [← dominant_as_zero] using h0
  have hh := geometric_coordinate_box hu huv hv hD _ _
    (hbound 0 (by norm_num) hd0) (hbound D ⟨hD.le,hD1.le⟩ h1) n
  by_cases hab : b r < a p q <;> simpa [hab] using hh


private lemma generated_exitMass {Z : Type*} (O : GeneratedObserver Z) (z : Z)
    (H : Nat) (t : Bool) :
    exitMass (generatedLaw O.update O.row z) H t =
      ∑ n ∈ Finset.range H, exitCoefficient O z n t := by
  classical
  induction H generalizing z with
  | zero => simp [exitMass, FirstExit]
  | succ H ih =>
    have hr : exitMass (generatedLaw O.update O.row z) (H+1) t =
        exitCoefficient O z 0 t+O.row z B*exitMass (generatedLaw O.update O.row (O.update z B)) H t := by
      have hs (y : Visible) := generated_sum O.update O.row O.row_sum (O.update z y) H
      cases t <;>
        simp [exitMass, sum_words_succ, FirstExit, generated_cons, exitCoefficient,
          B, Fin.sum_univ_succ, ← Finset.mul_sum, hs, mul_ite, mul_zero,
          Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc] <;>
        simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [hr, ih, Finset.sum_range_succ']
    simp only [exitCoefficient, ← Finset.mul_sum]
    ring

private lemma mixture_exitMass (p q r x : ℝ) (H : Nat) (t : Bool) :
    exitMass (mixtureLaw p q r x) H t =
      x*exitMass (pureLaw p q r 2) H t+(1-x)*exitMass (pureLaw p q r 4) H t := by
  classical
  simp only [exitMass, mixtureLaw]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> ring

private lemma oriented_minority_exitMass {p q r : ℝ} (hp : admissible p q r)
    (x : ℝ) (H : Nat) :
    exitMass (orientedMixture p q r x) H (if b r < a p q then true else false) =
      x*(1-(min (a p q) (b r))^H) := by
  classical
  by_cases hab : b r < a p q
  · simp only [orientedMixture, if_pos hab, mixture_exitMass, min_eq_right hab.le,
      (branch_exit_masses hp H).1, (branch_exit_masses hp H).2.1]
    ring
  · simp only [orientedMixture, if_neg hab, mixture_exitMass, min_eq_left (le_of_not_gt hab),
      (branch_exit_masses hp H).2.2.1, (branch_exit_masses hp H).2.2.2]
    ring

private lemma minority_exit_positive {Z : Type*} (O : GeneratedObserver Z)
    {p q r D : ℝ} (hp : admissible p q r) (z : Z) (hD : 0 < D) (hD1 : D < 1)
    (h1 : profileDistance (orientedMixture p q r D) (generatedLaw O.update O.row z) ≤ D/2) :
    ∃ n, 0 < exitCoefficient O z n (if b r < a p q then true else false) := by
  classical
  by_contra hn
  have hz (n : Nat) : exitCoefficient O z n (if b r < a p q then true else false) = 0 :=
    le_antisymm (le_of_not_gt (fun h => hn ⟨n,h⟩)) (exit_nonneg O z n _)
  have hp' : ProbabilityProfile (orientedMixture p q r D) :=
    (oriented_geometry (w := 0) hp ⟨hD.le,hD1.le⟩ (by norm_num)).1.1
  have hu : 0 ≤ min (a p q) (b r) :=
    le_min (holding_bounds hp).1.le (holding_bounds hp).2.2.1.le
  have hu1 : min (a p q) (b r) < 1 :=
    (min_le_left _ _).trans_lt (holding_bounds hp).2.1
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hu hu1).const_sub (1 : ℝ)).const_mul D
  simp only [sub_zero, mul_one] at hlim
  have hbad : D ≤ D/2 := by
    apply le_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro H
    have he := finite_event_gap hp' (generated_coherent O z).1 H
      (FirstExit (if b r < a p q then true else false) H)
    change |exitMass (orientedMixture p q r D) H (if b r < a p q then true else false)-
      exitMass (generatedLaw O.update O.row z) H (if b r < a p q then true else false)| ≤ _ at he
    rw [oriented_minority_exitMass hp, generated_exitMass] at he
    simp only [hz, Finset.sum_const_zero, sub_zero] at he
    exact (le_abs_self _).trans (he.trans ((finite_le_profile hp' (generated_coherent O z).1 H).trans h1))
  linarith

private lemma exit_add {Z : Type*} (O : GeneratedObserver Z) (z : Z) (n m : Nat) (t : Bool) :
    exitCoefficient O z (n+m) t =
      survival O z n*exitCoefficient O ((fun z => O.update z B)^[n] z) m t := by
  induction n generalizing z with
  | zero => simp [survival]
  | succ n ih =>
    rw [Nat.succ_add, exitCoefficient, ih]
    simp only [survival, Function.iterate_succ_apply]
    ring

private lemma periodic_exit {Z : Type*} (O : GeneratedObserver Z) (z : Z) (L : Nat)
    (hper : (fun z => O.update z B)^[L] z = z) (m n : Nat) (t : Bool) :
    exitCoefficient O z (m*L+n) t = (survival O z L)^m*exitCoefficient O z n t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, show m*L+L+n = L+(m*L+n) by omega, exit_add, hper, ih, pow_succ]
    ring


/-- No normalized generator on a positive B period attains the diameter tie.
Only the B update is periodic; exits may lead anywhere in the full carrier. -/
theorem periodic_diameter_obstruction {Z : Type*} (O : GeneratedObserver Z)
    {p q r D : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (z : Z) (L : Nat) (hL : 0 < L)
    (hper : (fun z => O.update z B)^[L] z = z) (hD : 0 < D) (hD1 : D < 1)
    (h0 : profileDistance (dominantLaw p q r) (generatedLaw O.update O.row z) ≤ D/2)
    (h1 : profileDistance (orientedMixture p q r D) (generatedLaw O.update O.row z) ≤ D/2) : False := by
  classical
  let u := min (a p q) (b r)
  let v := max (a p q) (b r)
  let d : Bool := if b r < a p q then false else true
  let f : Bool := if b r < a p q then true else false
  let γ := survival O z L
  have hu : 0 < u := lt_min (holding_bounds hp).1 (holding_bounds hp).2.2.1
  have hv : v < 1 := max_lt (holding_bounds hp).2.1 (holding_bounds hp).2.2.2.1
  have huv : u < v := by
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [u,v,min_eq_left h.le,max_eq_right h.le] using h
    · simpa [u,v,min_eq_right h.le,max_eq_left h.le] using h
  have box (n : Nat) :
      (1-D)*(1-v)*v^n ≤ exitCoefficient O z n d ∧
      exitCoefficient O z n d ≤ (1-v)*v^n ∧
      0 ≤ exitCoefficient O z n f ∧ exitCoefficient O z n f ≤ D*(1-u)*u^n :=
    generated_diameter_exit_box O hp hne z hD hD1 h0 h1 n
  have hdom (n : Nat) : 0 < exitCoefficient O z n d := by
    have hpos : 0 < (1-D)*(1-v)*v^n :=
      mul_pos (mul_pos (sub_pos.mpr hD1) (sub_pos.mpr hv)) (pow_pos (hu.trans huv) n)
    exact hpos.trans_le (box n).1
  have hγ : 0 < γ := by
    have he := periodic_exit O z L hper 1 0 d
    simp only [one_mul, add_zero, pow_one] at he
    have hm : 0 < γ*exitCoefficient O z 0 d := by rw [← he]; exact hdom L
    exact pos_of_mul_pos_left hm (exit_nonneg O z 0 d)
  have hpow (t : ℝ) (m n : Nat) : t^(m*L+n) = (t^L)^m*t^n := by
    rw [pow_add, Nat.mul_comm m L, pow_mul]
  have hl : v^L ≤ γ := by
    apply D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.geometric_rate_bound
      (x := v^L) (y := γ) (A := (1-D)*(1-v)) (B := exitCoefficient O z 0 d)
      hγ (mul_pos (sub_pos.mpr hD1) (sub_pos.mpr hv))
    intro m
    have hb := (box (m*L+0)).1
    rw [periodic_exit O z L hper, hpow, pow_zero, mul_one] at hb
    simpa only [mul_comm] using hb
  obtain ⟨n,hn⟩ := minority_exit_positive O hp z hD hD1 h1
  change 0 < exitCoefficient O z n f at hn
  have hr : γ ≤ u^L := by
    apply D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.geometric_rate_bound
      (x := γ) (y := u^L) (A := exitCoefficient O z n f) (B := D*(1-u)*u^n)
      (pow_pos hu L) hn
    intro m
    have hb := (box (m*L+n)).2.2.2
    rw [periodic_exit O z L hper, hpow] at hb
    convert hb using 1 <;> ring
  exact (not_le_of_gt (pow_lt_pow_left₀ huv hu.le (ne_of_gt hL))) (hl.trans hr)

end
end D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter

/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive cylinder identities and raw prefix limits turn scalar waiting windows into distinct full histories at one cut. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.SlowSurvivalWindows
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Order.Filter.Finite
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SimpRw

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology BigOperators
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CylinderWaitingWindows

/-- The full future words with no marker `3` in their first `j` coordinates. -/
def survivalFutures (H j : ℕ) : Finset (Fin H → Fin 4) := by
  classical
  exact Finset.univ.filter fun v => ∀ k : Fin H, k.val < j → v k ≠ 3

/-- The first marker is after `L` and at or before `U`, counted in future reads. -/
def waitingFutures (H L U : ℕ) : Finset (Fin H → Fin 4) :=
  survivalFutures H L \ survivalFutures H U

/-- Embed a complete word over `0,1,B` into the four-label alphabet, with `B=2`. -/
def noMarkerWord {n : ℕ} (w : Fin n → Fin 3) : List (Fin 4) :=
  List.ofFn fun i => (w i).castSucc

/-- The prefix is part of the full history; no reset or forgotten prefix is used. -/
def prefixed (m : ℕ) (w : List (Fin 4)) : List (Fin 4) :=
  List.replicate m 2 ++ w

private theorem survival_subset (H : ℕ) {L U : ℕ} (h : L ≤ U) :
    survivalFutures H U ⊆ survivalFutures H L := by
  classical
  intro v hv
  simp only [survivalFutures, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  intro k hk
  exact hv k (lt_of_lt_of_le hk h)

private theorem waiting_disjoint {K : ℕ} (b : Fin (K + 1) → ℕ) (hb : StrictMono b)
    (H : ℕ) {i j : Fin K} (hij : i ≠ j) :
    Disjoint (waitingFutures H (b i.castSucc) (b i.succ))
      (waitingFutures H (b j.castSucc) (b j.succ)) := by
  classical
  have ordered (i j : Fin K) (hij : i < j) :
      Disjoint (waitingFutures H (b i.castSucc) (b i.succ))
        (waitingFutures H (b j.castSucc) (b j.succ)) := by
    apply Finset.disjoint_left.mpr
    intro v hi hj
    have hi' := Finset.mem_sdiff.mp hi
    have hj' := Finset.mem_sdiff.mp hj
    have hle : b i.succ ≤ b j.castSucc := hb.monotone (show i.succ ≤ j.castSucc from hij)
    exact hi'.2 (survival_subset H hle hj'.1)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ordered i j h
  · exact (ordered j i h).symm

private theorem prefix_event_limit (p q : List (Fin 4) → ℝ)
    (hlimit : ∀ w, Tendsto (fun m : ℕ => (4 : ℝ) ^ m * p (prefixed m w)) atTop (𝓝 (q w)))
    (w : List (Fin 4)) (hq : 0 < q w) (H : ℕ) (E : Finset (Fin H → Fin 4)) :
    Tendsto (fun m => (∑ v ∈ E, p (prefixed m w ++ List.ofFn v)) / p (prefixed m w))
      atTop (𝓝 ((∑ v ∈ E, q (w ++ List.ofFn v)) / q w)) := by
  have hn := tendsto_finsetSum E fun v _ => hlimit (w ++ List.ofFn v)
  have h := hn.div (hlimit w) hq.ne'
  apply h.congr'
  exact Eventually.of_forall fun m => by
    simp only [Pi.div_apply, prefixed, List.append_assoc]
    rw [← Finset.mul_sum, mul_div_mul_left _ _ (pow_ne_zero m (by norm_num : (4 : ℝ) ≠ 0))]

/-- An abstract finite-cylinder supplier for source equations 13.5--13.10.
`p` is an original full-word cylinder function and `q` a comparison cylinder
function. The assumptions concern nonnegative original masses, finite cylinder
partitions and rescaled raw `B`-prefix limits. No conditional-row convergence,
selected windows or row-packing conclusion is assumed. Instantiating these
primitive identities for the infinite diffusion remains a separate obligation. -/
theorem finite_full_word_common_cut
    (S : ℕ → ℝ) (hpos : ∀ n, 0 < S n)
    (hzero : Tendsto S atTop (𝓝 0))
    (hratio : Tendsto (fun n => S (n + 1) / S n) atTop (𝓝 1))
    (p q : List (Fin 4) → ℝ)
    (hp : ∀ u, 0 ≤ p u)
    (hpartition : ∀ (u : List (Fin 4)) (H : ℕ), ∑ v : Fin H → Fin 4, p (u ++ List.ofFn v) = p u)
    (hq : ∀ (n : ℕ) (w : Fin n → Fin 3), 0 < q (noMarkerWord w))
    (hsum : ∀ n, ∑ w : Fin n → Fin 3, q (noMarkerWord w) = S n)
    (hsurvival : ∀ (n H j : ℕ), j ≤ H →
      (∑ w : Fin n → Fin 3, ∑ v ∈ survivalFutures H j,
        q (noMarkerWord w ++ List.ofFn v)) = S (n + j))
    (hlimit : ∀ w, Tendsto (fun m : ℕ => (4 : ℝ) ^ m * p (prefixed m w)) atTop (𝓝 (q w)))
    (K : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1 / 16) :
    ∃ (H t : ℕ) (n : Fin K → ℕ) (b : Fin (K + 1) → ℕ)
      (w : ∀ i : Fin K, Fin (n i) → Fin 3),
      b 0 = 0 ∧ b (Fin.last K) = H ∧ (K = 0 ↔ H = 0) ∧
      StrictMono b ∧ StrictMono n ∧ 0 < t ∧
      (∀ i : Fin K, 0 < n i ∧ n i ≤ t ∧ b i.castSucc < b i.succ ∧ b i.succ ≤ H ∧
        (prefixed (t - n i) (noMarkerWord (w i))).length = t ∧
        1 - 2 * θ < (∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
          q (noMarkerWord (w i) ++ List.ofFn v)) / q (noMarkerWord (w i)) ∧
        0 < p (prefixed (t - n i) (noMarkerWord (w i))) ∧
        1 - 3 * θ < (∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
          p (prefixed (t - n i) (noMarkerWord (w i)) ++ List.ofFn v)) /
            p (prefixed (t - n i) (noMarkerWord (w i)))) ∧
      Function.Injective (fun i => prefixed (t - n i) (noMarkerWord (w i))) := by
  classical
  obtain ⟨H, n, b, hbzero, hblast, hH, hb, hn, hwin⟩ :=
    SlowSurvivalWindows.finite_waiting_windows S hpos hzero hratio K θ hθ
  have hevent (i : Fin K) :
      (∑ w : Fin (n i) → Fin 3, ∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
        q (noMarkerWord w ++ List.ofFn v)) =
          S (n i + b i.castSucc) - S (n i + b i.succ) := by
    simp_rw [waitingFutures, Finset.sum_sdiff_eq_sub (survival_subset H (hwin i).2.1.le)]
    rw [Finset.sum_sub_distrib,
      hsurvival (n i) H (b i.castSucc) ((hwin i).2.1.le.trans (hwin i).2.2.1),
      hsurvival (n i) H (b i.succ) (hwin i).2.2.1]
  have hword (i : Fin K) : ∃ w : Fin (n i) → Fin 3,
      1 - 2 * θ < (∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
        q (noMarkerWord w ++ List.ofFn v)) / q (noMarkerWord w) := by
    have htotal : (∑ w : Fin (n i) → Fin 3, (1 - 2 * θ) * q (noMarkerWord w)) <
        ∑ w : Fin (n i) → Fin 3, ∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
          q (noMarkerWord w ++ List.ofFn v) := by
      rw [← Finset.mul_sum, hsum, hevent]
      exact (lt_div_iff₀ (hpos (n i))).mp (hwin i).2.2.2
    obtain ⟨w, _, hw⟩ := Finset.exists_lt_of_sum_lt htotal
    exact ⟨w, (lt_div_iff₀ (hq (n i) w)).mpr hw⟩
  choose w hw using hword
  have hlarge (i : Fin K) : ∀ᶠ t : ℕ in atTop, n i ≤ t ∧
      0 < p (prefixed (t - n i) (noMarkerWord (w i))) ∧
      1 - 3 * θ < (∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
        p (prefixed (t - n i) (noMarkerWord (w i)) ++ List.ofFn v)) /
          p (prefixed (t - n i) (noMarkerWord (w i))) := by
    have hpositive : ∀ᶠ m : ℕ in atTop, 0 < p (prefixed m (noMarkerWord (w i))) := by
      filter_upwards [(hlimit (noMarkerWord (w i))).eventually
        (eventually_gt_nhds (hq (n i) (w i)))] with m hm
      exact (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0 : ℝ) < 4) m)).mp hm
    have hmass := (prefix_event_limit p q hlimit (noMarkerWord (w i)) (hq (n i) (w i)) H
      (waitingFutures H (b i.castSucc) (b i.succ))).eventually
        (eventually_gt_nhds (show 1 - 3 * θ <
          (∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
            q (noMarkerWord (w i) ++ List.ofFn v)) / q (noMarkerWord (w i)) by
          linarith [hw i]))
    exact (eventually_ge_atTop (n i)).and
      ((tendsto_sub_atTop_nat (n i)).eventually (hpositive.and hmass))
  obtain ⟨t, ht, hall⟩ := ((eventually_gt_atTop 0).and (eventually_all.mpr hlarge)).exists
  refine ⟨H, t, n, b, w, hbzero, hblast, hH, hb, hn, ht, ?_, ?_⟩
  · intro i
    refine ⟨(hwin i).1, (hall i).1, (hwin i).2.1, (hwin i).2.2.1, ?_, hw i,
      (hall i).2.1, (hall i).2.2⟩
    simp only [prefixed, noMarkerWord, List.length_append, List.length_replicate,
      List.length_ofFn, Nat.sub_add_cancel (hall i).1]
  · intro i j hij
    change prefixed (t - n i) (noMarkerWord (w i)) =
      prefixed (t - n j) (noMarkerWord (w j)) at hij
    by_contra hne
    have hd := waiting_disjoint b hb H hne
    have hbound : (∑ v ∈ waitingFutures H (b i.castSucc) (b i.succ),
        p (prefixed (t - n i) (noMarkerWord (w i)) ++ List.ofFn v)) +
        (∑ v ∈ waitingFutures H (b j.castSucc) (b j.succ),
        p (prefixed (t - n i) (noMarkerWord (w i)) ++ List.ofFn v)) ≤
          p (prefixed (t - n i) (noMarkerWord (w i))) := by
      rw [← Finset.sum_union hd]
      calc
        _ ≤ ∑ v : Fin H → Fin 4,
            p (prefixed (t - n i) (noMarkerWord (w i)) ++ List.ofFn v) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hp _)
        _ = _ := hpartition _ H
    have hi := (lt_div_iff₀ (hall i).2.1).mp (hall i).2.2
    have hj := (lt_div_iff₀ (hall j).2.1).mp (hall j).2.2
    rw [← hij] at hj
    have hhalf : (1 / 2 : ℝ) < 1 - 3 * θ := by linarith
    have hstrict := mul_lt_mul_of_pos_right hhalf (hall i).2.1
    linarith

#print axioms finite_full_word_common_cut

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CylinderWaitingWindows

/- GID: D5/S3/Entropy/CountableSpectralMoments
   generality: G
   mirror-B: D5/B/S3/Entropy/CountableSpectralMoments
   mirror-E: none(waiver:analytic-series-proof)
   anchors: []
   utility: none
   digest: Countable elementary symmetric moments and distinguished-coordinate identities. -/

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open Filter Topology

namespace D5.S3.Entropy.CountableSpectralMoments

def mass (p : ℕ → ℝ) : ℝ := ∑' i, p i
def purity (p : ℕ → ℝ) : ℝ := ∑' i, p i ^ 2
def cubicMoment (p : ℕ → ℝ) : ℝ := ∑' i, p i ^ 3

def pairPartial (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, p i * p j

def tripleLayer (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j, p i * p j * p k

/-- The increasing-triple convention, with no exterior factorial. -/
def third (p : ℕ → ℝ) : ℝ := ∑' k, tripleLayer p k

/-- Outer index k, then j, then i; the indicator retains exactly i < j < k. -/
def tripleTerm (p : ℕ → ℝ) (t : ℕ × (ℕ × ℕ)) : ℝ :=
  if t.2.2 < t.2.1 ∧ t.2.1 < t.1 then p t.2.2 * p t.2.1 * p t.1 else 0

/-- The increasing-triple definition is an absolutely convergent, unordered
countable sum. Its value agrees with the finite-layer convention above. -/
theorem absolute_triple_sum {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) :
    Summable (fun t => ‖tripleTerm p t‖) ∧ (∑' t, tripleTerm p t) = third p := by
  have hpair := hp.mul_of_nonneg hp hn hn
  have hprod := hp.mul_of_nonneg hpair hn (fun t => mul_nonneg (hn t.1) (hn t.2))
  have hnonneg (t : ℕ × (ℕ × ℕ)) : 0 ≤ tripleTerm p t := by
    unfold tripleTerm
    split_ifs
    · exact mul_nonneg (mul_nonneg (hn _) (hn _)) (hn _)
    · exact le_rfl
  have hsum : Summable (tripleTerm p) := by
    apply Summable.of_nonneg_of_le hnonneg _ hprod
    intro t
    unfold tripleTerm
    split_ifs
    · apply le_of_eq
      ring
    · exact mul_nonneg (hn t.1) (mul_nonneg (hn t.2.1) (hn t.2.2))
  refine ⟨hsum.congr (fun t => (Real.norm_of_nonneg (hnonneg t)).symm), ?_⟩
  rw [hsum.tsum_prod]
  unfold third
  apply tsum_congr
  intro k
  have hslice : Summable (fun t : ℕ × ℕ => tripleTerm p (k, t)) := by
    apply Summable.of_nonneg_of_le (fun t => hnonneg (k, t)) _ (hpair.mul_left (p k))
    intro t
    unfold tripleTerm
    split_ifs
    · apply le_of_eq
      ring
    · exact mul_nonneg (hn k) (mul_nonneg (hn t.1) (hn t.2))
  rw [hslice.tsum_prod]
  rw [tsum_eq_sum (s := Finset.range k) (fun j hj => by
    have hjk : ¬ j < k := by simpa using hj
    simp [tripleTerm, hjk])]
  unfold tripleLayer
  apply Finset.sum_congr rfl
  intro j hj
  rw [tsum_eq_sum (s := Finset.range j) (fun i hi => by
    have hij : ¬ i < j := by simpa using hi
    simp [tripleTerm, hij])]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [tripleTerm, Finset.mem_range.mp hi, Finset.mem_range.mp hj,
    and_self, ite_true]

private theorem pair_partial_newton (p : ℕ → ℝ) (n : ℕ) :
    2 * pairPartial p n =
      (∑ i ∈ Finset.range n, p i) ^ 2 - ∑ i ∈ Finset.range n, p i ^ 2 := by
  induction n with
  | zero => simp [pairPartial]
  | succ n ih =>
    simp only [pairPartial, Finset.sum_range_succ] at ih ⊢
    rw [← Finset.sum_mul]
    nlinarith

private theorem triple_partial_newton (p : ℕ → ℝ) (n : ℕ) :
    6 * (∑ k ∈ Finset.range n, tripleLayer p k) =
      (∑ i ∈ Finset.range n, p i) ^ 3 -
      3 * (∑ i ∈ Finset.range n, p i) * (∑ i ∈ Finset.range n, p i ^ 2) +
      2 * ∑ i ∈ Finset.range n, p i ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := pair_partial_newton p n
    have hl : tripleLayer p n = pairPartial p n * p n := by
      simp only [tripleLayer, pairPartial, Finset.sum_mul]
    simp only [Finset.sum_range_succ]
    rw [hl]
    nlinarith [congrArg (fun z : ℝ => 3 * p n * z) hp]

private theorem term_le_mass {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (i : ℕ) : p i ≤ mass p :=
  hp.le_tsum i (fun j _ => hn j)

private theorem summable_square {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p ≤ 1) : Summable (fun i => p i ^ 2) := by
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg (p i)) _ hp
  intro i
  have hi := (term_le_mass hp hn i).trans hm
  nlinarith [hn i]

private theorem summable_cube {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p ≤ 1) : Summable (fun i => p i ^ 3) := by
  apply Summable.of_nonneg_of_le (fun i => pow_nonneg (hn i) 3) _ hp
  intro i
  have hi := (term_le_mass hp hn i).trans hm
  have hi2 : p i ^ 2 ≤ 1 := by nlinarith [hn i]
  nlinarith [mul_nonneg (hn i) (sub_nonneg.mpr hi2)]

private theorem triple_layer_nonneg {p : ℕ → ℝ} (hn : ∀ i, 0 ≤ p i) (k : ℕ) :
    0 ≤ tripleLayer p k := by
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (hn i) (hn j)) (hn k)

private theorem triple_partial_bound {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p ≤ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, tripleLayer p k ≤ 1 / 6 := by
  let s := ∑ i ∈ Finset.range n, p i
  let q := ∑ i ∈ Finset.range n, p i ^ 2
  let r := ∑ i ∈ Finset.range n, p i ^ 3
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => hn i)
  have hs1 : s ≤ 1 := (hp.sum_le_tsum (Finset.range n) (fun i _ => hn i)).trans hm
  have hq0 : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hrq : r ≤ s * q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have his : p i ≤ s := Finset.single_le_sum (fun j _ => hn j) hi
    nlinarith [mul_nonneg (sub_nonneg.mpr his) (sq_nonneg (p i))]
  have hnew := triple_partial_newton p n
  change 6 * (∑ k ∈ Finset.range n, tripleLayer p k) = s ^ 3 - 3 * s * q + 2 * r at hnew
  have hs3 : s ^ 3 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1)
      (show 0 ≤ s ^ 2 + s + 1 by positivity)]
  nlinarith [mul_nonneg hs0 hq0]

private theorem summable_triple_layer {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p ≤ 1) : Summable (tripleLayer p) := by
  exact summable_of_sum_range_le (triple_layer_nonneg hn) (triple_partial_bound hp hn hm)

/-- Newton's identity for every nonnegative countable subprobability sequence. -/
theorem countable_newton {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p ≤ 1) :
    6 * third p = mass p ^ 3 - 3 * mass p * purity p + 2 * cubicMoment p := by
  have hs := hp.hasSum.tendsto_sum_nat
  have hq := (summable_square hp hn hm).hasSum.tendsto_sum_nat
  have hr := (summable_cube hp hn hm).hasSum.tendsto_sum_nat
  have he := (summable_triple_layer hp hn hm).hasSum.tendsto_sum_nat
  have ha : Tendsto (fun n => 6 * ∑ k ∈ Finset.range n, tripleLayer p k)
      atTop (𝓝 (6 * third p)) := tendsto_const_nhds.mul he
  have hb : Tendsto (fun n => (∑ i ∈ Finset.range n, p i) ^ 3 -
      3 * (∑ i ∈ Finset.range n, p i) * (∑ i ∈ Finset.range n, p i ^ 2) +
      2 * ∑ i ∈ Finset.range n, p i ^ 3)
      atTop (𝓝 (mass p ^ 3 - 3 * mass p * purity p + 2 * cubicMoment p)) :=
    ((hs.pow 3).sub ((tendsto_const_nhds.mul hs).mul hq)).add
      (tendsto_const_nhds.mul hr)
  have heq : (fun n => 6 * ∑ k ∈ Finset.range n, tripleLayer p k) =
      (fun n => (∑ i ∈ Finset.range n, p i) ^ 3 -
        3 * (∑ i ∈ Finset.range n, p i) * (∑ i ∈ Finset.range n, p i ^ 2) +
        2 * ∑ i ∈ Finset.range n, p i ^ 3) :=
    funext (triple_partial_newton p)
  rw [heq] at ha
  exact tendsto_nhds_unique ha hb

/-- Every summand in the elementary symmetric series is nonnegative. -/
theorem third_nonneg {p : ℕ → ℝ} (hn : ∀ i, 0 ≤ p i) : 0 ≤ third p :=
  tsum_nonneg (triple_layer_nonneg hn)

private theorem cubic_moment_lower {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p = 1) : purity p ^ 2 ≤ cubicMoment p := by
  have hq := summable_square hp hn hm.le
  have hr := summable_cube hp hn hm.le
  have hnonneg : 0 ≤ ∑' i, p i * (p i - purity p) ^ 2 :=
    tsum_nonneg (fun i => mul_nonneg (hn i) (sq_nonneg (p i - purity p)))
  have heq : (∑' i, p i * (p i - purity p) ^ 2) =
      cubicMoment p - 2 * purity p * purity p + purity p ^ 2 * mass p := by
    calc
      _ = ∑' i, (p i ^ 3 - 2 * purity p * p i ^ 2 + purity p ^ 2 * p i) := by
        apply tsum_congr
        intro i
        ring
      _ = _ := by
        rw [(hr.sub (hq.mul_left _)).tsum_add (hp.mul_left _),
          hr.tsum_sub (hq.mul_left _), tsum_mul_left, tsum_mul_left]
        rfl
  rw [heq, hm] at hnonneg
  nlinarith

/-- The lower-purity branch for countable probability spectra. -/
theorem third_lower_of_purity_le_third {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p = 1) (hq : purity p ≤ 1 / 3) :
    (1 - 3 * purity p + 2 * purity p ^ 2) / 6 ≤ third p ∧
    1 / 27 ≤ (1 - 3 * purity p + 2 * purity p ^ 2) / 6 := by
  have hnw := countable_newton hp hn hm.le
  have hcube := cubic_moment_lower hp hn hm
  have hq0 : 0 ≤ purity p := tsum_nonneg (fun i => sq_nonneg _)
  rw [hm] at hnw
  constructor
  · nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ 7 / 3 - 2 * purity p by linarith)]

/-- Removing a coordinate keeps a zero in its old slot, so no ordering or maximality
assumption is part of the distinguished-coordinate identity. -/
def erase (p : ℕ → ℝ) (i : ℕ) : ℕ → ℝ := fun j => if j = i then 0 else p j

private theorem erase_nonneg {p : ℕ → ℝ} (hn : ∀ j, 0 ≤ p j) (i j : ℕ) :
    0 ≤ erase p i j := by
  simp only [erase]
  split_ifs
  · exact le_rfl
  · exact hn j

private theorem erase_summable {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ j, 0 ≤ p j) (i : ℕ) : Summable (erase p i) := by
  apply Summable.of_nonneg_of_le (erase_nonneg hn i) _ hp
  intro j
  simp only [erase]
  split_ifs <;> simp_all

private theorem erase_moments {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ j, 0 ≤ p j) (hm : mass p ≤ 1) (i : ℕ) :
    mass (erase p i) = mass p - p i ∧
    purity (erase p i) = purity p - p i ^ 2 ∧
    cubicMoment (erase p i) = cubicMoment p - p i ^ 3 := by
  have h1 := hp.tsum_eq_add_tsum_ite i
  have h2 := (summable_square hp hn hm).tsum_eq_add_tsum_ite i
  have h3 := (summable_cube hp hn hm).tsum_eq_add_tsum_ite i
  have h2' : purity (erase p i) = ∑' j, if j = i then 0 else p j ^ 2 := by
    apply tsum_congr
    intro j
    simp only [erase]
    split_ifs <;> simp
  have h3' : cubicMoment (erase p i) = ∑' j, if j = i then 0 else p j ^ 3 := by
    apply tsum_congr
    intro j
    simp only [erase]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_⟩
  · change (∑' j, if j = i then 0 else p j) = (∑' j, p j) - p i
    linarith
  · rw [h2']
    change (∑' j, if j = i then 0 else p j ^ 2) = (∑' j, p j ^ 2) - p i ^ 2
    linarith
  · rw [h3']
    change (∑' j, if j = i then 0 else p j ^ 3) = (∑' j, p j ^ 3) - p i ^ 3
    linarith

/-- Exact D2 identity at an arbitrary distinguished coordinate of a countable
probability spectrum. Purity and sign restrictions belong only to its consequence. -/
theorem distinguished_identity {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ j, 0 ≤ p j) (hm : mass p = 1) (i : ℕ) :
    third p - 1 / 32 =
      (2 * p i - 1) * (4 * p i - 1) ^ 2 / 32 +
      (p i / 2) * (3 / 8 - purity p) + third (erase p i) := by
  have he := erase_moments hp hn hm.le i
  have hemi : mass (erase p i) ≤ 1 := by rw [he.1, hm]; linarith [hn i]
  have hfull := countable_newton hp hn hm.le
  have htail := countable_newton (erase_summable hp hn i) (erase_nonneg hn i) hemi
  rw [he.1, he.2.1, he.2.2, hm] at htail
  rw [hm] at hfull
  nlinarith

/-- Any distinguished eigenvalue at least one half suffices for the exclusion. -/
theorem third_lower_of_distinguished_ge_half {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ j, 0 ≤ p j) (hm : mass p = 1)
    (hq : purity p ≤ 3 / 8) (i : ℕ) (hi : 1 / 2 ≤ p i) :
    1 / 32 ≤ third p := by
  have hid := distinguished_identity hp hn hm i
  have ha : 0 ≤ (2 * p i - 1) * (4 * p i - 1) ^ 2 / 32 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hb : 0 ≤ (p i / 2) * (3 / 8 - purity p) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hq)
  have hc := third_nonneg (erase_nonneg hn i)
  linarith

#print axioms countable_newton
#print axioms absolute_triple_sum
#print axioms third_lower_of_purity_le_third
#print axioms distinguished_identity
#print axioms third_lower_of_distinguished_ge_half

end D5.S3.Entropy.CountableSpectralMoments

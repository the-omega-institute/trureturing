/- GID: D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangReciprocal/IntervalConvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Deriv]
   utility: none
   digest: Symmetric interval convolutions increase when positive parameters are balanced. -/

import D5.S3.Analytic.KarpZhangReciprocal.Coeff
import D5.S3.Analytic.KarpZhangReciprocal.BirthDeath
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Deriv

/-!
admission_basis: escape-witness
content theorem: symmetric_tail, through score_variance_bound.
escape_witness: Reversible rates on an arbitrary finite interval absorb the score variance
into expected coefficient curvature, including both endpoints. The resulting
logarithmic concavity on lines s+t=S and symmetry imply the tail comparison.
Only this direction of concavity is asserted. Projections of coefficient_calculus
that use only positivity, derivatives or ratio monotonicity do not inherit
the discarded curvature estimate as content.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* F: proof_shape: definition; escape_witness: none;
  consumers: shift_tail, symmetric, symmetric_tail, KarpZhangReciprocal.Result.abel_reduction, KarpZhangReciprocal.Result.reciprocal_half.
* weight: proof_shape: definition; escape_witness: none;
  consumers: balance, score_variance_bound, slice_concave, symmetric_tail, total_pos, weight_deriv, weight_pos.
* score: proof_shape: definition; escape_witness: none;
  consumers: score_deriv, score_variance_bound, slice_concave, weight_deriv.
* curvature: proof_shape: definition; escape_witness: none;
  consumers: score_deriv, score_variance_bound, slice_concave.
* birth: proof_shape: definition; escape_witness: none;
  consumers: balance, rate_curvature, score_variance_bound.
* death: proof_shape: definition; escape_witness: none;
  consumers: balance, rate_curvature, score_variance_bound.
* weight_pos: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound, total_pos.
* total_pos: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound, slice_concave, symmetric_tail.
* coefficient_step: proof_shape: bind-only; escape_witness: none;
  consumers: balance.
* balance: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound.
* rate_curvature: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound.
* square_split: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound.
* score_variance_bound: proof_shape: content; escape_witness: score_variance_bound;
  consumers: slice_concave.
* variance_expand: proof_shape: bind-only; escape_witness: none;
  consumers: slice_concave.
* weight_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: slice_concave.
* score_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: slice_concave.
* slice_concave: proof_shape: content; escape_witness: score_variance_bound;
  consumers: symmetric_tail.
* symmetric: proof_shape: bind-only; escape_witness: none;
  consumers: shift_tail, symmetric_tail.
* symmetric_tail: proof_shape: content; escape_witness: score_variance_bound;
  consumers: shift_tail.
* shift_tail: proof_shape: content; escape_witness: score_variance_bound;
  consumers: KarpZhangReciprocal.Result.reciprocal_half.

Direct frozen D5 dependencies: none; all KarpZhang dependencies are
same-delivery declarations. Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
-/

noncomputable section
open scoped BigOperators Topology
open Finset

namespace D5.S3.Analytic.KarpZhangReciprocal.IntervalConvolution

open Coeff

/-- For `L ≤ U ≤ m`, the convolution over all indices from `L` through `U`. -/
def F (m L U : ℕ) (s t : ℝ) : ℝ :=
  ∑ i ∈ range (U - L + 1), c (L + i) s * c (m - (L + i)) t

private def weight (m L i : ℕ) (s t : ℝ) : ℝ :=
  c (L + i) s * c (m - (L + i)) t

private def score (m L i : ℕ) (s t : ℝ) : ℝ :=
  psi (L + i) s - psi (m - (L + i)) t

private def curvature (m L i : ℕ) (s t : ℝ) : ℝ :=
  chi (L + i) s + chi (m - (L + i)) t

private def birth (m L n : ℕ) (s : ℝ) (i : ℕ) : ℝ :=
  if i < n then (m - (L + i) : ℕ) * lambda (L + i) s else 0

private def death (m L : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (L + i : ℕ) * lambda (m - (L + i)) t

private theorem weight_pos (m L i : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < weight m L i s t :=
  mul_pos (coefficient_calculus (L + i) hs).1
    (coefficient_calculus (m - (L + i)) ht).1

private theorem total_pos (m L n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < ∑ i ∈ range (n + 1), weight m L i s t := by
  apply sum_pos
  · intro i _
    exact weight_pos m L i hs ht
  · exact ⟨0, mem_range.mpr (Nat.succ_pos n)⟩

private theorem coefficient_step (k : ℕ) {s : ℝ} (hs : 0 < s) :
    c (k + 1) s * (k + 1 : ℕ) = c k s * lambda k s := by
  have h : c (k + 1) s / c k s = lambda k s / ((k + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (coefficient_calculus k hs).2.2.1
  have hc := ne_of_gt (coefficient_calculus k hs).1
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h' := (div_eq_div_iff hc hk).mp h
  simpa only [mul_comm] using h'

private theorem balance (m L n : ℕ) (hm : L + n ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (i : ℕ) (hi : i < n) :
    weight m L i s t * birth m L n s i =
      weight m L (i + 1) s t * death m L t (i + 1) := by
  have hi0 : i + 1 ≠ 0 := by omega
  have he : m - (L + i) = (m - (L + (i + 1))) + 1 := by omega
  have hleft := coefficient_step (L + i) hs
  have hright := coefficient_step (m - (L + (i + 1))) ht
  have hidx : L + (i + 1) = (L + i) + 1 := by omega
  simp only [birth, if_pos hi, death, if_neg hi0, weight]
  rw [← he] at hright
  rw [hidx]
  calc
    _ = (c (L + i) s * lambda (L + i) s) *
        (c (m - (L + i)) t * (m - (L + i) : ℕ)) := by ring
    _ = (c (L + i + 1) s * (L + i + 1 : ℕ)) *
        (c (m - (L + (i + 1))) t * lambda (m - (L + (i + 1))) t) := by
      rw [← hleft, hright]
    _ = _ := by rw [hidx]; ring

private theorem rate_curvature (m L n : ℕ) (hm : L + n ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (i : ℕ) (hi : i < n) :
    lambda (L + i) s + lambda (m - (L + (i + 1))) t ≤
      BirthDeath.kappa (birth m L n s) (death m L t) i := by
  have hi' : L + i < m := by omega
  have he : m - (L + i) = m - (L + (i + 1)) + 1 := by omega
  have hA := (coefficient_calculus (L + i) hs).2.1
  have hB := (coefficient_calculus (m - (L + (i + 1))) ht).2.1
  have hp : lambda (L + i) s ≤ birth m L n s i - birth m L n s (i + 1) := by
    simp only [birth, if_pos hi]
    split_ifs with hnext
    · have hmono := (coefficient_calculus 0 hs).2.2.2.2.2.2.2.2
      have hcmp := hmono (show L + i ≤ L + (i + 1) by omega)
      have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ)
        (m - (L + (i + 1)))) (sub_nonneg.mpr hcmp)
      have he' : ((m - (L + i) : ℕ) : ℝ) =
          (m - (L + (i + 1)) : ℕ) + 1 := by exact_mod_cast he
      nlinarith
    · have hdeg : (1 : ℝ) ≤ (m - (L + i) : ℕ) := by exact_mod_cast (show 1 ≤ m - (L + i) by omega)
      have hmul := mul_nonneg (sub_nonneg.mpr hdeg) hA.le
      nlinarith
  have hr : lambda (m - (L + (i + 1))) t ≤
      death m L t (i + 1) - death m L t i := by
    have hnext : i + 1 ≠ 0 := by omega
    simp only [death, if_neg hnext]
    split_ifs with hzero
    · subst i
      have hdeg : (1 : ℝ) ≤ (L + (0 + 1) : ℕ) := by exact_mod_cast (show 1 ≤ L + (0 + 1) by omega)
      have hmul := mul_nonneg (sub_nonneg.mpr hdeg) hB.le
      nlinarith
    · have hmono := (coefficient_calculus 0 ht).2.2.2.2.2.2.2.2
      have hcmp := hmono (show m - (L + (i + 1)) ≤ m - (L + i) by omega)
      have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) (L + i))
        (sub_nonneg.mpr hcmp)
      have he' : ((L + (i + 1) : ℕ) : ℝ) = (L + i : ℕ) + 1 := by push_cast; ring
      nlinarith
  unfold BirthDeath.kappa
  linarith

private theorem square_split {A B K X Y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hK : A + B ≤ K) : (X + Y) ^ 2 / K ≤ X ^ 2 / B + Y ^ 2 / A := by
  calc
    (X + Y) ^ 2 / K ≤ (X + Y) ^ 2 / (A + B) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (add_pos hA hB) hK
    _ ≤ X ^ 2 / B + Y ^ 2 / A := by
      apply (div_le_iff₀ (add_pos hA hB)).2
      have heq : (X ^ 2 / B + Y ^ 2 / A) * (A + B) =
          ((A * X ^ 2 + B * Y ^ 2) * (A + B)) / (A * B) := by
        field_simp [ne_of_gt hA, ne_of_gt hB]
        <;> ring
      rw [heq]
      apply (le_div_iff₀ (mul_pos hA hB)).2
      nlinarith [sq_nonneg (A * X - B * Y)]

/-- The variance absorption step for an arbitrary interval, including a singleton. -/
private theorem score_variance_bound (m L n : ℕ) (hm : L + n ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    let Z := ∑ i ∈ range (n + 1), weight m L i s t
    let π := fun i => weight m L i s t / Z
    BirthDeath.variance n π (fun i => score m L i s t) ≤
      ∑ i ∈ range (n + 1), π i * curvature m L i s t := by
  dsimp only
  let Z := ∑ i ∈ range (n + 1), weight m L i s t
  let π := fun i => weight m L i s t / Z
  let p := birth m L n s
  let r := death m L t
  let H := fun i => score m L i s t
  have hZ : 0 < Z := total_pos m L n hs ht
  have hπ (i : ℕ) (_ : i ≤ n) : 0 < π i := div_pos (weight_pos m L i hs ht) hZ
  have hprob : ∑ i ∈ range (n + 1), π i = 1 := by
    dsimp only [π]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hZ)
  have hp : p n = 0 := by simp [p, birth]
  have hr : r 0 = 0 := by simp [r, death]
  have hpp (i : ℕ) (hi : i < n) : 0 < p i := by
    dsimp only [p]
    rw [birth, if_pos hi]
    exact mul_pos (by exact_mod_cast (show 0 < m - (L + i) by omega))
      (coefficient_calculus (L + i) hs).2.1
  have hrr (i : ℕ) (hi : 0 < i) (_ : i ≤ n) : 0 < r i := by
    dsimp only [r]
    rw [death, if_neg (by omega : i ≠ 0)]
    exact mul_pos (by exact_mod_cast (show 0 < L + i by omega))
      (coefficient_calculus (m - (L + i)) ht).2.1
  have hb (i : ℕ) (hi : i < n) : π i * p i = π (i + 1) * r (i + 1) := by
    dsimp only [π, p, r]
    have h := balance m L n hm hs ht i hi
    exact (by simpa only [div_mul_eq_mul_div] using congrArg (fun x : ℝ => x / Z) h)
  have hk (i : ℕ) (hi : i < n) : 0 < BirthDeath.kappa p r i :=
    lt_of_lt_of_le (add_pos (coefficient_calculus (L + i) hs).2.1
      (coefficient_calculus (m - (L + (i + 1))) ht).2.1)
      (rate_curvature m L n hm hs ht i hi)
  have hv := BirthDeath.variance_bound n π p r H hπ hprob hp hr hpp hrr hb hk
  have hedge (i : ℕ) (hi : i < n) :
      π i * p i / BirthDeath.kappa p r i * (H (i + 1) - H i) ^ 2 ≤
        π (i + 1) * chi (L + (i + 1)) s + π i * chi (m - (L + i)) t := by
    let k := L + i
    let ell := m - (L + i)
    let A := lambda k s
    let B := lambda (ell - 1) t
    let X := eta k s
    let Y := eta (ell - 1) t
    have he : ell = m - (L + (i + 1)) + 1 := by dsimp [ell]; omega
    have he' : ell - 1 = m - (L + (i + 1)) := by omega
    have hk' : L + (i + 1) = k + 1 := by dsimp [k]; omega
    have hA : 0 < A := (coefficient_calculus k hs).2.1
    have hB : 0 < B := (coefficient_calculus (ell - 1) ht).2.1
    have hK : A + B ≤ BirthDeath.kappa p r i := by
      simpa only [A, B, k, he'] using rate_curvature m L n hm hs ht i hi
    have hdiff : H (i + 1) - H i = X + Y := by
      dsimp only [H, score, X, Y]
      have hpsi : psi ell t = psi (ell - 1) t + eta (ell - 1) t := by
        conv_lhs => rw [show ell = (ell - 1) + 1 by omega]
        exact sum_range_succ _ _
      rw [← he', hk']
      change psi (k + 1) s - psi (ell - 1) t - (psi k s - psi ell t) = _
      rw [hpsi, show psi (k + 1) s = psi k s + eta k s by
        exact sum_range_succ _ _]
      ring
    have hC : (k + 1 : ℕ) * X ^ 2 ≤ chi (k + 1) s := by
      simpa only [X, Nat.add_sub_cancel] using
        (coefficient_calculus (k + 1) hs).2.2.2.2.2.2.2.1
    have hD : (ell : ℝ) * Y ^ 2 ≤ chi ell t :=
      (coefficient_calculus ell ht).2.2.2.2.2.2.2.1
    have hpval : p i = (ell : ℝ) * A := by simp only [p, birth, if_pos hi, ell, A, k]
    have hrval : r (i + 1) = (k + 1 : ℕ) * B := by
      dsimp only [r]
      rw [death, if_neg (by omega : i + 1 ≠ 0), ← he', hk']
    have hC' : X ^ 2 / B ≤ chi (k + 1) s / r (i + 1) := by
      rw [hrval]
      apply (div_le_div_iff₀ hB (mul_pos (by positivity) hB)).2
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hC)]
    have hD' : Y ^ 2 / A ≤ chi ell t / p i := by
      rw [hpval]
      apply (div_le_div_iff₀ hA (mul_pos (by exact_mod_cast (show 0 < ell by omega)) hA)).2
      nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hD)]
    have hbase := (square_split hA hB hK).trans (add_le_add hC' hD')
    have hmul := mul_le_mul_of_nonneg_left hbase
      (mul_nonneg (hπ i (by omega)).le (hpp i hi).le)
    have hb' : π i * p i / r (i + 1) = π (i + 1) := by
      rw [hb i hi]
      exact mul_div_cancel_right₀ _ (ne_of_gt (hrr (i + 1) (by omega) (by omega)))
    rw [hdiff, hk']
    calc
      _ = π i * p i * ((X + Y) ^ 2 / BirthDeath.kappa p r i) := by ring
      _ ≤ π i * p i * (chi (k + 1) s / r (i + 1) + chi ell t / p i) := hmul
      _ = π (i + 1) * chi (k + 1) s + π i * chi ell t := by
        rw [mul_add]
        have hfirst : π i * p i * (chi (k + 1) s / r (i + 1)) =
            (π i * p i / r (i + 1)) * chi (k + 1) s := by ring
        rw [hfirst, hb']
        field_simp [ne_of_gt (hpp i hi)]
        <;> ring
  have hsum := sum_le_sum (fun i hi => hedge i (mem_range.mp hi))
  have hends : (∑ i ∈ range n,
        (π (i + 1) * chi (L + (i + 1)) s + π i * chi (m - (L + i)) t)) ≤
      ∑ i ∈ range (n + 1), π i * curvature m L i s t := by
    simp only [curvature, mul_add, sum_add_distrib]
    rw [sum_range_succ' (fun i => π i * chi (L + i) s),
      sum_range_succ (fun i => π i * chi (m - (L + i)) t)]
    have h0 := mul_nonneg (hπ 0 (by omega)).le
      (coefficient_calculus (L + 0) hs).2.2.2.2.2.2.1
    have hn := mul_nonneg (hπ n le_rfl).le
      (coefficient_calculus (m - (L + n)) ht).2.2.2.2.2.2.1
    linarith
  exact hv.trans (hsum.trans hends)

private theorem variance_expand (n : ℕ) (π H : ℕ → ℝ)
    (hprob : ∑ i ∈ range (n + 1), π i = 1) :
    BirthDeath.variance n π H = (∑ i ∈ range (n + 1), π i * H i ^ 2) -
      (∑ i ∈ range (n + 1), π i * H i) ^ 2 := by
  let a := ∑ i ∈ range (n + 1), π i * H i
  change (∑ i ∈ range (n + 1), π i * (H i - a) ^ 2) = _
  calc
    _ = ∑ i ∈ range (n + 1),
        (π i * H i ^ 2 - 2 * a * (π i * H i) + a ^ 2 * π i) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hprob]
      change _ - 2 * a * a + a ^ 2 * 1 = _ - a ^ 2
      ring

private theorem weight_deriv (m L i : ℕ) (S : ℝ) {s : ℝ}
    (hs : 0 < s) (ht : 0 < S - s) :
    HasDerivAt (fun u => weight m L i u (S - u))
      (weight m L i s (S - s) * score m L i s (S - s)) s := by
  have hd := (coefficient_calculus (L + i) hs).2.2.2.1
  have he := ((coefficient_calculus (m - (L + i)) ht).2.2.2.1).comp s
    ((hasDerivAt_id s).const_sub S)
  apply (hd.mul he).congr_deriv
  dsimp [weight, score]
  ring

private theorem score_deriv (m L i : ℕ) (S : ℝ) {s : ℝ}
    (hs : 0 < s) (ht : 0 < S - s) :
    HasDerivAt (fun u => score m L i u (S - u))
      (-curvature m L i s (S - s)) s := by
  have hd := (coefficient_calculus (L + i) hs).2.2.2.2.2.1
  have he := ((coefficient_calculus (m - (L + i)) ht).2.2.2.2.2.1).comp s
    ((hasDerivAt_id s).const_sub S)
  apply (hd.sub he).congr_deriv
  dsimp [curvature]
  ring

private theorem slice_concave (m L n : ℕ) (hm : L + n ≤ m) (S : ℝ) :
    ConcaveOn ℝ (Set.Ioo 0 S)
      (fun s => Real.log (∑ i ∈ range (n + 1), weight m L i s (S - s))) := by
  let Z := fun s => ∑ i ∈ range (n + 1), weight m L i s (S - s)
  let N := fun s => ∑ i ∈ range (n + 1),
    weight m L i s (S - s) * score m L i s (S - s)
  let Q := fun s => ∑ i ∈ range (n + 1),
    weight m L i s (S - s) *
      (score m L i s (S - s) ^ 2 - curvature m L i s (S - s))
  have hZ (s : ℝ) (hs : s ∈ Set.Ioo 0 S) : 0 < Z s :=
    total_pos m L n hs.1 (sub_pos.mpr hs.2)
  have dZ (s : ℝ) (hs : s ∈ Set.Ioo 0 S) : HasDerivAt Z (N s) s :=
    HasDerivAt.fun_sum (fun i _ => weight_deriv m L i S hs.1 (sub_pos.mpr hs.2))
  have dN (s : ℝ) (hs : s ∈ Set.Ioo 0 S) : HasDerivAt N (Q s) s := by
    apply HasDerivAt.fun_sum
    intro i _
    apply ((weight_deriv m L i S hs.1 (sub_pos.mpr hs.2)).mul
      (score_deriv m L i S hs.1 (sub_pos.mpr hs.2))).congr_deriv
    ring
  have dlog (s : ℝ) (hs : s ∈ Set.Ioo 0 S) :
      HasDerivAt (fun u => Real.log (Z u)) (N s / Z s) s :=
    (dZ s hs).log (ne_of_gt (hZ s hs))
  have dquot (s : ℝ) (hs : s ∈ Set.Ioo 0 S) :
      HasDerivAt (fun u => N u / Z u) ((Q s * Z s - N s ^ 2) / Z s ^ 2) s := by
    convert (dN s hs).div (dZ s hs) (ne_of_gt (hZ s hs)) using 1 <;> ring
  have hnonpos (s : ℝ) (hs : s ∈ Set.Ioo 0 S) :
      (Q s * Z s - N s ^ 2) / Z s ^ 2 ≤ 0 := by
    let π := fun i => weight m L i s (S - s) / Z s
    let H := fun i => score m L i s (S - s)
    let C := fun i => curvature m L i s (S - s)
    have hp : ∑ i ∈ range (n + 1), π i = 1 := by
      dsimp only [π]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (hZ s hs))
    have hv := score_variance_bound m L n hm hs.1 (sub_pos.mpr hs.2)
    change BirthDeath.variance n π H ≤ ∑ i ∈ range (n + 1), π i * C i at hv
    rw [variance_expand n π H hp] at hv
    have hmean : (∑ i ∈ range (n + 1), π i * H i) = N s / Z s := by
      dsimp only [π, H, N]
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div]
    have hQ : Q s / Z s = (∑ i ∈ range (n + 1), π i * H i ^ 2) -
        ∑ i ∈ range (n + 1), π i * C i := by
      dsimp only [Q, π, H, C]
      rw [Finset.sum_div, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [hmean] at hv
    have he : (Q s * Z s - N s ^ 2) / Z s ^ 2 = Q s / Z s - (N s / Z s) ^ 2 := by
      field_simp [ne_of_gt (hZ s hs)]
      <;> ring
    rw [he, hQ]
    linarith
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioo 0 S)
    (f' := fun s => N s / Z s)
    (f'' := fun s => (Q s * Z s - N s ^ 2) / Z s ^ 2)
  · intro s hs
    exact (dlog s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact (dlog s (interior_subset hs)).hasDerivWithinAt
  · intro s hs
    exact (dquot s (interior_subset hs)).hasDerivWithinAt
  · intro s hs
    exact hnonpos s (interior_subset hs)

private theorem symmetric (m q : ℕ) (hq : 2 * q ≤ m) (s t : ℝ) :
    F m q (m - q) s t = F m q (m - q) t s := by
  unfold F
  let n := m - q - q
  change (∑ i ∈ range (n + 1), _) = ∑ i ∈ range (n + 1), _
  apply sum_bij (fun i _ => n - i)
  · intro i hi
    apply mem_range.mpr
    have := mem_range.mp hi
    omega
  · intro i hi j hj hij
    have := mem_range.mp hi
    have := mem_range.mp hj
    omega
  · intro j hj
    have hj' := mem_range.mp hj
    refine ⟨n - j, mem_range.mpr (by omega), ?_⟩
    omega
  · intro i hi
    have hi' := mem_range.mp hi
    have h1 : q + (n - i) = m - (q + i) := by dsimp [n] at *; omega
    have h2 : m - (q + (n - i)) = q + i := by dsimp [n] at *; omega
    rw [h2, h1, mul_comm]

/-- A symmetric interval convolution increases under a balancing of its positive parameters.
The endpoint case `a = d` and all singleton index intervals are included. -/
theorem symmetric_tail (m q : ℕ) (hq : 2 * q ≤ m)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hsum : a + d = b + c) :
    F m q (m - q) a d ≤ F m q (m - q) b c := by
  let S := a + d
  have hd : 0 < d := lt_of_lt_of_le ha (hab.trans (hbc.trans hcd))
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hqa : q + (m - q - q) ≤ m := by omega
  have hconc := slice_concave m q (m - q - q) hqa S
  change ConcaveOn ℝ (Set.Ioo 0 S) (fun s => Real.log (F m q (m - q) s (S - s))) at hconc
  have hpa : a ∈ Set.Ioo 0 S := ⟨ha, by dsimp [S]; linarith⟩
  have hpd : d ∈ Set.Ioo 0 S := ⟨hd, by dsimp [S]; linarith⟩
  have hmin := hconc.min_le_of_mem_Icc hpa hpd ⟨hab, hbc.trans hcd⟩
  have hsa : S - a = d := by dsimp [S]; ring
  have hsd : S - d = a := by dsimp [S]; ring
  have hsb : S - b = c := by dsimp [S]; linarith
  rw [hsa, hsd, hsb, ← symmetric m q hq a d, min_self] at hmin
  exact (Real.log_le_log_iff (total_pos m q (m - q - q) ha hd)
    (total_pos m q (m - q - q) hb hc)).mp hmin

/-- The tail inequality with arbitrary nonnegative shifts; their order is immaterial. -/
theorem shift_tail (m q : ℕ) (hq : 2 * q ≤ m) {μ α β : ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    F m q (m - q) μ (μ + α + β) ≤ F m q (m - q) (μ + α) (μ + β) := by
  by_cases h : α ≤ β
  · exact symmetric_tail m q hq hμ (by linarith) (by linarith) (by linarith)
      (by ring)
  · have he := symmetric_tail m q hq hμ
      (b := μ + β) (c := μ + α) (d := μ + α + β)
      (by linarith) (by linarith) (by linarith) (by ring)
    rw [symmetric m q hq (μ + β) (μ + α)] at he
    exact he

end D5.S3.Analytic.KarpZhangReciprocal.IntervalConvolution

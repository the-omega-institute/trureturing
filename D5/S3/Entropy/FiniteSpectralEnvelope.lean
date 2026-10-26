/- GID: D5/S3/Entropy/FiniteSpectralEnvelope
   generality: G
   mirror-B: D5/B/S3/Entropy/FiniteSpectralEnvelope
   mirror-E: none(waiver:analytic-compact-extremum)
   anchors: []
   utility: none
   digest: Three-coordinate smoothing for the trace/purity spectral moment envelope. -/

import D5.S3.Entropy.SpectralEnvelopeParameters
import Mathlib.Analysis.Convex.StdSimplex
import Batteries.Tactic.OpenPrivate

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Entropy.FiniteSpectralEnvelope

open SpectralEnvelopeParameters
open private coordinate_value envelope_antitone from
  D5.S3.Entropy.SpectralEnvelopeParameters

/-- A strictly smaller positive triple preserves its first two moments whenever
the larger two original entries differ. No differentiability premise is used. -/
private theorem strict_triple_smoothing {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b < c) :
    ∃ a' b' c' : ℝ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧
      a' + b' + c' = a + b + c ∧
      a' ^ 2 + b' ^ 2 + c' ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      a' ^ 3 + b' ^ 3 + c' ^ 3 < a ^ 3 + b ^ 3 + c ^ 3 := by
  let u := c - b
  let v := b + c - 2 * a
  have hu : 0 < u := sub_pos.mpr hbc
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans hbc
  let t := min (a / 2) (min (1 / 2) (u ^ 2 / (4 * (v + 2))))
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htbudget : t * (4 * (v + 2)) ≤ u ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * (v + 2))).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  let D := u ^ 2 - 2 * t * v - 3 * t ^ 2
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg ht.le hv, mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  let d := Real.sqrt D
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = D := Real.sq_sqrt hD.le
  let b' := (b + c + t - d) / 2
  let c' := (b + c + t + d) / 2
  have hdp : d < b + c + t := by
    have hprod : 0 < b * c := mul_pos hb hc
    have htc : 0 ≤ t * (b + c - a) := mul_nonneg ht.le (by linarith)
    dsimp [D, u, v] at hd2
    nlinarith
  have hb' : 0 < b' := by dsimp [b']; linarith
  have hc' : 0 < c' := by dsimp [c']; linarith
  have hsum : (a - t) + b' + c' = a + b + c := by dsimp [b', c']; ring
  have hsq : (a - t) ^ 2 + b' ^ 2 + c' ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    dsimp [b', c']
    dsimp [D, u, v] at hd2
    nlinarith
  have hpair : (a - t) * b' + (a - t) * c' + b' * c' = a * b + a * c + b * c := by
    nlinarith [congrArg (fun z : ℝ => z ^ 2) hsum]
  have hbcp : b' * c' = b * c + t * (b + c - a) + t ^ 2 := by
    dsimp [b', c']
    dsimp [D, u, v] at hd2
    nlinarith
  have hprod : (a - t) * b' * c' - a * b * c =
      -t * (b - a) * (c - a) + t ^ 2 * (2 * a - b - c) - t ^ 3 := by
    nlinarith [congrArg (fun z : ℝ => (a - t) * z) hbcp]
  have hdecrease : (a - t) * b' * c' < a * b * c := by
    have h1 : 0 ≤ t * (b - a) * (c - a) :=
      mul_nonneg (mul_nonneg ht.le (sub_nonneg.mpr hab)) (by linarith)
    have h2 : t ^ 2 * (2 * a - b - c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    have h3 : 0 < t ^ 3 := pow_pos ht 3
    linarith
  have newton (r s z : ℝ) : r ^ 3 + s ^ 3 + z ^ 3 =
      (r + s + z) ^ 3 - 3 * (r + s + z) * (r * s + r * z + s * z) + 3 * r * s * z := by ring
  refine ⟨a - t, b', c', sub_pos.mpr hta, hb', hc', hsum, hsq, ?_⟩
  rw [newton, hsum, hpair, newton a b c]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finitePurity (p : ι → ℝ) : ℝ := ∑ i, p i ^ 2
def finiteThird (p : ι → ℝ) : ℝ :=
  ((∑ i, p i) ^ 3 - 3 * (∑ i, p i) * finitePurity p + 2 * ∑ i, p i ^ 3) / 6

private def feasible (q : ℝ) : Set (ι → ℝ) :=
  stdSimplex ℝ ι ∩ {p | finitePurity p ≤ q}

private theorem compact_feasible (q : ℝ) : IsCompact (feasible (ι := ι) q) := by
  apply (isCompact_stdSimplex ℝ ι).inter_right
  exact isClosed_le (by unfold finitePurity; fun_prop) continuous_const

private theorem exists_minimizer {q : ℝ} {p : ι → ℝ} (hp : p ∈ feasible q) :
    ∃ v ∈ feasible (ι := ι) q, IsMinOn finiteThird (feasible q) v := by
  apply (compact_feasible q).exists_isMinOn ⟨p, hp⟩
  unfold finiteThird finitePurity
  fun_prop

private def replace3 (p : ι → ℝ) (i j k : ι) (a b c : ℝ) : ι → ℝ :=
  Function.update (Function.update (Function.update p i a) j b) k c

private theorem sum_map_update (f : ℝ → ℝ) (p : ι → ℝ) (i : ι) (a : ℝ) :
    (∑ l, f (Function.update p i a l)) = (∑ l, f (p l)) - f (p i) + f a := by
  have heq : (fun l => f (Function.update p i a l)) =
      Function.update (fun l => f (p l)) i (f a) := by
    funext l
    by_cases h : l = i <;> simp [h]
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs := Finset.sum_erase_add univ (fun l => f (p l)) (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  linarith

private theorem sum_map_replace3 (f : ℝ → ℝ) (p : ι → ℝ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c : ℝ) :
    (∑ l, f (replace3 p i j k a b c l)) =
      (∑ l, f (p l)) - f (p i) - f (p j) - f (p k) + f a + f b + f c := by
  unfold replace3
  rw [sum_map_update, sum_map_update, sum_map_update]
  simp [Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  ring

private theorem minimizing_triple {q : ℝ} {p : ι → ℝ}
    (hp : p ∈ feasible q) (hmin : IsMinOn finiteThird (feasible q) p)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : 0 < p i) (hijv : p i ≤ p j) (hjkv : p j < p k) : False := by
  obtain ⟨a, b, c, ha, hb, hc, hsum, hsq, hcube⟩ :=
    strict_triple_smoothing hi hijv hjkv
  let v := replace3 p i j k a b c
  have hv0 : ∀ l, 0 ≤ v l := by
    intro l
    dsimp [v, replace3]
    by_cases hk : l = k
    · simp [hk, hc.le]
    by_cases hj : l = j
    · simp [hk, hj, hb.le]
    by_cases hi' : l = i
    · simp [hk, hj, hi', ha.le]
    simp [hk, hj, hi', hp.1.1 l]
  have hs := sum_map_replace3 id p i j k hij hik hjk a b c
  simp only [id_eq] at hs
  have hvsum : (∑ l, v l) = 1 := by
    change (∑ l, replace3 p i j k a b c l) = 1
    rw [hs, hp.1.2]
    linarith
  have hq := sum_map_replace3 (fun z => z ^ 2) p i j k hij hik hjk a b c
  have hvq : finitePurity v = finitePurity p := by
    unfold finitePurity
    change (∑ l, replace3 p i j k a b c l ^ 2) = ∑ l, p l ^ 2
    rw [hq]
    linarith
  have hr := sum_map_replace3 (fun z => z ^ 3) p i j k hij hik hjk a b c
  have hvr : (∑ l, v l ^ 3) < ∑ l, p l ^ 3 := by
    change (∑ l, replace3 p i j k a b c l ^ 3) < ∑ l, p l ^ 3
    rw [hr]
    linarith
  have hv : v ∈ feasible q := ⟨⟨hv0, hvsum⟩, hvq ▸ hp.2⟩
  have hle := hmin hv
  unfold finiteThird at hle
  rw [hvsum, hp.1.2, hvq] at hle
  linarith

private def positiveSupport (p : ι → ℝ) : Finset ι := univ.filter (fun i => 0 < p i)

private theorem sum_over_support (p : ι → ℝ) (hn : ∀ i, 0 ≤ p i)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i ∈ positiveSupport p, f (p i)) = ∑ i, f (p i) := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hz : p i = 0 := by
    have : ¬ 0 < p i := by simpa [positiveSupport] using hnot
    linarith [hn i]
  simp [hz, hf]

private theorem positive_support_nonempty {p : ι → ℝ} (hn : ∀ i, 0 ≤ p i)
    (hm : ∑ i, p i = 1) : (positiveSupport p).Nonempty := by
  by_contra h
  have hz : positiveSupport p = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hs := sum_over_support p hn id rfl
  simp only [hz, Finset.sum_empty, id_eq, hm] at hs
  norm_num at hs

/-- At a minimizer with four positive coordinates, all coordinates other than
a smallest one have one common value. This forces purity at most one third. -/
private theorem purity_le_third_of_four_positive {q : ℝ} {p : ι → ℝ}
    (hp : p ∈ feasible q) (hmin : IsMinOn finiteThird (feasible q) p)
    (hcard : 4 ≤ (positiveSupport p).card) : finitePurity p ≤ 1 / 3 := by
  let S := positiveSupport p
  obtain ⟨i, hi, hleast⟩ := S.exists_min_image p (positive_support_nonempty hp.1.1 hp.1.2)
  let R := S.erase i
  have hRcard : 3 ≤ R.card := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hi]
    dsimp [S] at *
    omega
  have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj⟩ := hRne
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
  have hpos (k : ι) (hk : k ∈ S) : 0 < p k := by
    simpa [S, positiveSupport] using hk
  have hall (k : ι) (hk : k ∈ R) : p k = p j := by
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    have hkS : k ∈ S := (Finset.mem_erase.mp hk).2
    rcases lt_trichotomy (p k) (p j) with hlt | heq | hgt
    · have hkj : k ≠ j := fun h => by simpa [h] using hlt
      exact False.elim (minimizing_triple hp hmin i k j hki.symm hji.symm hkj
        (hpos i hi) (hleast k hkS) hlt)
    · exact heq
    · have hjk : j ≠ k := fun h => by simpa [h] using hgt
      exact False.elim (minimizing_triple hp hmin i j k hji.symm hki.symm hjk
        (hpos i hi) (hleast j hjS) hgt)
  have ha : 0 < p i := hpos i hi
  have hx : 0 < p j := hpos j hjS
  have hax : p i ≤ p j := hleast j hjS
  have hsumR : (∑ k ∈ R, p k) = (R.card : ℝ) * p j := by
    rw [Finset.sum_congr rfl (fun k hk => hall k hk)]
    simp
  have hsqR : (∑ k ∈ R, p k ^ 2) = (R.card : ℝ) * p j ^ 2 := by
    rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℝ => z ^ 2) (hall k hk))]
    simp
  have hm : p i + (R.card : ℝ) * p j = 1 := by
    have hs := Finset.sum_erase_add S p hi
    rw [show S.erase i = R from rfl, hsumR, sum_over_support p hp.1.1 id rfl, hp.1.2] at hs
    linarith
  have hq : finitePurity p = p i ^ 2 + (R.card : ℝ) * p j ^ 2 := by
    have hs := Finset.sum_erase_add S (fun k => p k ^ 2) hi
    rw [show S.erase i = R from rfl, hsqR, sum_over_support p hp.1.1 (fun z => z ^ 2) (by norm_num)] at hs
    unfold finitePurity
    linarith
  have hR3 : (3 : ℝ) ≤ R.card := by exact_mod_cast hRcard
  have h3x : p i + 3 * p j ≤ 1 := by nlinarith
  have ha1 : p i ≤ 1 / 4 := by linarith
  have hq' : finitePurity p = p i ^ 2 + p j * (1 - p i) := by
    nlinarith [congrArg (fun z : ℝ => p j * z) hm]
  rw [hq']
  nlinarith [mul_nonneg (show 0 ≤ 1 - p i by linarith)
    (show 0 ≤ 1 - p i - 3 * p j by linarith),
    mul_nonneg ha.le (show 0 ≤ 1 - 2 * p i by linarith)]

private theorem finite_coarse {p : ι → ℝ} (hn : ∀ i, 0 ≤ p i)
    (hm : ∑ i, p i = 1) (hq : finitePurity p ≤ 1 / 3) : 1 / 27 ≤ finiteThird p := by
  have hvar : 0 ≤ ∑ i, p i * (p i - finitePurity p) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hn i) (sq_nonneg _))
  have heq : (∑ i, p i * (p i - finitePurity p) ^ 2) =
      (∑ i, p i ^ 3) - 2 * finitePurity p * finitePurity p + finitePurity p ^ 2 := by
    calc
      _ = ∑ i, (p i ^ 3 - 2 * finitePurity p * p i ^ 2 + finitePurity p ^ 2 * p i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hm]
        simp [finitePurity]
  rw [heq] at hvar
  have hq0 : 0 ≤ finitePurity p := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  unfold finiteThird
  rw [hm]
  nlinarith [mul_nonneg (sub_nonneg.mpr hq)
    (show 0 ≤ 7 / 3 - 2 * finitePurity p by linarith)]

private theorem minimizing_three_value {q : ℝ} {p : ι → ℝ}
    (hp : p ∈ feasible q) (hmin : IsMinOn finiteThird (feasible q) p)
    (hql : 1 / 3 < finitePurity p) (hqu : q ≤ 3 / 8) :
    finiteThird p = envelope (finitePurity p) := by
  let S := positiveSupport p
  have hcupper : S.card ≤ 3 := by
    by_contra h
    have hc : 4 ≤ (positiveSupport p).card := by dsimp [S] at *; omega
    exact (not_le_of_gt hql) (purity_le_third_of_four_positive hp hmin hc)
  have hq0 : 0 ≤ finitePurity p := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hclower : 3 ≤ S.card := by
    by_contra h
    have hc2 : (S.card : ℝ) ≤ 2 := by exact_mod_cast (show S.card ≤ 2 by omega)
    have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := p)
    rw [sum_over_support p hp.1.1 id rfl, hp.1.2,
      sum_over_support p hp.1.1 (fun z => z ^ 2) (by norm_num)] at hcs
    change 1 ^ 2 ≤ (S.card : ℝ) * finitePurity p at hcs
    have hbound := hp.2.trans hqu
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) hq0]
  have hc3 : S.card = 3 := by omega
  obtain ⟨i, hi, hleast⟩ := S.exists_min_image p (positive_support_nonempty hp.1.1 hp.1.2)
  have hRcard : (S.erase i).card = 2 := by rw [Finset.card_erase_of_mem hi, hc3]
  obtain ⟨j, k, hjk, hR⟩ := Finset.card_eq_two.mp hRcard
  have hjR : j ∈ S.erase i := by rw [hR]; simp
  have hkR : k ∈ S.erase i := by rw [hR]; simp
  have hji : j ≠ i := (Finset.mem_erase.mp hjR).1
  have hki : k ≠ i := (Finset.mem_erase.mp hkR).1
  have hjS := (Finset.mem_erase.mp hjR).2
  have hkS := (Finset.mem_erase.mp hkR).2
  have hi0 : 0 < p i := by simpa [S, positiveSupport] using hi
  have hx : p j = p k := by
    rcases lt_trichotomy (p j) (p k) with hlt | heq | hgt
    · exact False.elim (minimizing_triple hp hmin i j k hji.symm hki.symm hjk
        hi0 (hleast j hjS) hlt)
    · exact heq
    · exact False.elim (minimizing_triple hp hmin i k j hki.symm hji.symm hjk.symm
        hi0 (hleast k hkS) hgt)
  have hS : S = {i, j, k} := by rw [← Finset.insert_erase hi, hR]
  have sums (f : ℝ → ℝ) (hf : f 0 = 0) : (∑ l, f (p l)) = f (p i) + 2 * f (p j) := by
    rw [← sum_over_support p hp.1.1 f hf, hS]
    simp [hji.symm, hki.symm, hjk, ← hx]
    ring
  have hm : p i + 2 * p j = 1 := by simpa using (sums id rfl).symm.trans hp.1.2
  have hq : finitePurity p = p i ^ 2 + 2 * p j ^ 2 := sums (fun z => z ^ 2) (by norm_num)
  have hr : (∑ l, p l ^ 3) = p i ^ 3 + 2 * p j ^ 3 := sums (fun z => z ^ 3) (by norm_num)
  have ha : p i = 1 - 2 * p j := by linarith
  have hpoly : 6 * p j ^ 2 - 4 * p j + 1 = finitePurity p := by rw [hq, ha]; ring
  have hjthird : 1 / 3 ≤ p j := by linarith [hleast j hjS]
  have hsqrt : Real.sqrt (6 * finitePurity p - 2) = 6 * p j - 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)).mpr
    nlinarith
  have hcoord : upperCoordinate (finitePurity p) = p j := by
    unfold upperCoordinate
    rw [hsqrt]
    ring
  have hvalue := coordinate_value hql.le
  rw [hcoord] at hvalue
  rw [← hvalue]
  unfold finiteThird
  rw [hp.1.2, hr, ← hpoly, ha]
  ring

/-- The finite probability budget inequality, including the one-third endpoint.
The feasible set is the entire finite simplex; no support bound is assumed. -/
theorem finite_budget_envelope (p : ι → ℝ) (hn : ∀ i, 0 ≤ p i)
    (hm : ∑ i, p i = 1) {q : ℝ} (hq0 : 1 / 3 ≤ q) (hq1 : q ≤ 3 / 8)
    (hpq : finitePurity p ≤ q) : envelope q ≤ finiteThird p := by
  have hp : p ∈ feasible q := ⟨⟨hn, hm⟩, hpq⟩
  obtain ⟨v, hv, hmin⟩ := exists_minimizer hp
  have hminp := hmin hp
  suffices envelope q ≤ finiteThird v by linarith
  by_cases hqv : finitePurity v ≤ 1 / 3
  · have hcoarse := finite_coarse hv.1.1 hv.1.2 hqv
    have henv := envelope_antitone (a := 1 / 3) (b := q) le_rfl hq0
    norm_num [envelope] at henv
    linarith
  · rw [minimizing_three_value hv hmin (lt_of_not_ge hqv) hq1]
    exact envelope_antitone (lt_of_not_ge hqv).le hv.2

end D5.S3.Entropy.FiniteSpectralEnvelope

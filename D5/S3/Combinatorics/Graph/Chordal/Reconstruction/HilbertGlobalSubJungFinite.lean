/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJungFinite
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-global-sub-jung-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJungFinite.finite_mixture_neg; premises=D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJungFinite.certificate31,D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJungFinite.certificate51,D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJungFinite.certificate101
   digest: Finite retained-curl quadratic certificates and weighted Hilbert reduction. -/

import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.ChordalCliqueInvariant
import OmegaMath.Combinatorics.Graph.HilbertRetainedRows
import OmegaMath.Combinatorics.Graph.RetainedCliqueEnergy
import OmegaMath.Combinatorics.Graph.HilbertWeightedEnergy

/-! # Finite retained-curl certificates

This module proves the full scalar certificate for Section 3 of C39, independently
of its asymmetric triangle insertion. The three radii are `22302/10000`,
`22913/10000`, and `23434/10000`, with neighborhood caps 30, 50, and 100.

The certificate bounds expression (22) for every real probability vector,
including zero coordinates. A common affine majorant of its two quadratic
pieces replaces the enumeration of active-coordinate counts in (23).
All three envelopes are strictly below `-1/20000`. All comparisons are exact
kernel-checked arithmetic.

The weighted Hodge--Young estimate (19) and the pointwise retained-curl
inequality are also proved. The retained clique invariants and elementary-symmetric estimate close the
subset rows at every simplicial insertion.
-/

compile_only_with_mathlib

open scoped BigOperators

namespace SimpleGraph.HilbertGlobalSubJungFinite

noncomputable section

/-- Probability that `j` independent uniform draws from `n` labels are distinct.
The descending-factorial form includes `P(0,0)=1`. -/
def distinctUniform (n j : ℕ) : ℝ := (n.descFactorial j : ℝ) / (n : ℝ) ^ j

/-- The parameters of a finite retained-clique calculation. -/
structure Parameters where
  N : ℕ
  s : ℕ
  R : ℝ
  mu : ℝ
  sigma : ℝ

namespace Parameters

def r (t : Parameters) : ℝ := t.R ^ 2
def c (t : Parameters) : ℝ := 1 + 1 / t.mu
def beta (t : Parameters) : ℝ := t.c * t.sigma / t.N
def edgeFactor (t : Parameters) : ℝ := distinctUniform (t.N - 2) (t.s - 2)
def curlFactor (t : Parameters) : ℝ := distinctUniform (t.N - 3) (t.s - 3)
def credit (t : Parameters) : ℝ := (1 + t.mu) * t.beta * (t.s - 2) / (6 * t.edgeFactor)
def massCoeff (t : Parameters) : ℝ := (1 + t.mu) * t.r + t.c
def chooseTwo (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1) / 2
def Q (t : Parameters) : ℝ := t.massCoeff / 2 - t.credit * chooseTwo t.s * t.edgeFactor
def rankCoeff (t : Parameters) : ℝ := t.c * (t.s - 2) / 2
def constantTerm (t : Parameters) : ℝ :=
  t.massCoeff * chooseTwo t.N / (t.N : ℝ) ^ 2 - t.r -
    t.credit * distinctUniform t.N t.s
def uniform (t : Parameters) : ℝ := 1 / t.N
def threshold (t : Parameters) : ℝ := t.sigma / t.N

/-- The right side of (22), written on a padded simplex of size `N`.
For fewer than `N` coordinates, the omitted coordinates are exactly zero. -/
def envelope {ι : Type*} [Fintype ι] (t : Parameters) (p : ι → ℝ) : ℝ :=
  t.constantTerm - t.Q * ((∑ i, p i ^ 2) - t.uniform) +
    t.rankCoeff * ∑ i, p i * max (t.threshold - p i) 0

end Parameters

/-- Positivity of a quadratic from a strictly negative discriminant. -/
theorem quadratic_pos {a b c : ℝ} (ha : 0 < a) (hd : b ^ 2 < 4 * a * c)
    (x : ℝ) : 0 < c + b * x + a * x ^ 2 := by
  by_contra! h
  have hmul := mul_nonpos_of_nonneg_of_nonpos ha.le h
  nlinarith [sq_nonneg (2 * a * x + b)]

/-- A dual affine bound controls the positive-part penalty without sorting
coordinates or assuming they are strictly positive. -/
theorem penalty_affine_lt {q b u t H l : ℝ}
    (hq : 0 < q) (hqb : 0 < q + b)
    (h₀ : l ^ 2 < 4 * q * H)
    (h₁ : (l - b * (t - 2 * u)) ^ 2 < 4 * (q + b) * (H - b * u * (t - u)))
    (x : ℝ) :
    -q * (x - u) ^ 2 + b * x * max (t - x) 0 < H + l * (x - u) := by
  by_cases hx : t ≤ x
  · rw [max_eq_right (by linarith : t - x ≤ 0), mul_zero, add_zero]
    have hh := quadratic_pos hq h₀ (x - u)
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ t - x)]
    have hh := quadratic_pos hqb h₁ (x - u)
    nlinarith

/-- A reusable exact certificate for the complete finite scalar calculation.
The two strict discriminant tests are sufficient for every simplex point. -/
structure Certificate (t : Parameters) where
  N_pos : 0 < t.N
  size_bounds : 3 ≤ t.s ∧ t.s ≤ t.N
  R_pos : 0 < t.R
  mu_pos : 0 < t.mu
  sigma_bounds : 0 < t.sigma ∧ t.sigma ≤ 1
  edge_pos : 0 < t.edgeFactor
  curl_condition : t.beta * (t.s - 2) * t.curlFactor ≤ t.c * t.edgeFactor
  credit_pos : 0 < t.credit
  Q_pos : 0 < t.Q
  rank_nonneg : 0 ≤ t.rankCoeff
  constant_neg : t.constantTerm < 0
  margin : ℝ
  margin_pos : 0 < margin
  dual : ℝ
  inactive : dual ^ 2 < 4 * t.Q * ((-t.constantTerm - margin) / t.N)
  active : (dual - t.rankCoeff * (t.threshold - 2 * t.uniform)) ^ 2 <
    4 * (t.Q + t.rankCoeff) *
      ((-t.constantTerm - margin) / t.N - t.rankCoeff * t.uniform * (t.threshold - t.uniform))

namespace Certificate

/-- The scalar certificate closes (22) uniformly, also for simplices padded
by zero coordinates. Nonnegativity is unnecessary for this stronger bound. -/
theorem envelope_lt_margin {t : Parameters} (h : Certificate t)
    {ι : Type*} [Fintype ι] (hcard : Fintype.card ι ≤ t.N)
    (p : ι → ℝ) (hp : ∑ i, p i = 1) : t.envelope p < -h.margin := by
  classical
  have hN : (0 : ℝ) < t.N := by exact_mod_cast h.N_pos
  let u := t.uniform
  let H := (-t.constantTerm - h.margin) / t.N
  let f := fun x : ℝ => -t.Q * (x - u) ^ 2 + t.rankCoeff * x * max (t.threshold - x) 0
  have hpoint (x : ℝ) : f x < H + h.dual * (x - u) :=
    penalty_affine_lt h.Q_pos (by linarith [h.Q_pos, h.rank_nonneg]) h.inactive h.active x
  have hne : Nonempty ι := by
    by_contra hn
    have : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hp
  have := hne
  have hsum : (∑ i, f (p i)) < ∑ i, (H + h.dual * (p i - u)) := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hpoint (p i))
  have hpad : (0 : ℝ) ≤ t.N - Fintype.card ι := by
    exact sub_nonneg.mpr (by exact_mod_cast hcard)
  have hz := mul_le_mul_of_nonneg_left (hpoint 0).le hpad
  have hu : (t.N : ℝ) * u = 1 := by
    dsimp [u, Parameters.uniform]
    exact mul_one_div_cancel hN.ne'
  have hu₂ : (t.N : ℝ) * u ^ 2 = u := by
    calc
      _ = ((t.N : ℝ) * u) * u := by ring
      _ = u := by rw [hu, one_mul]
  have hd : (∑ i, (p i - u) ^ 2) =
      (∑ i, p i ^ 2) - 2 * u + (Fintype.card ι : ℝ) * u ^ 2 := by
    simp_rw [show ∀ i, (p i - u) ^ 2 = p i ^ 2 - (2 * u) * p i + u ^ 2 by
      intro i; ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hp, mul_one, Finset.card_univ]
  have hf : (∑ i, f (p i)) = -t.Q * (∑ i, (p i - u) ^ 2) +
      t.rankCoeff * ∑ i, p i * max (t.threshold - p i) 0 := by
    simp only [f, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  have he : t.envelope p = t.constantTerm + (∑ i, f (p i)) +
      ((t.N : ℝ) - Fintype.card ι) * f 0 := by
    rw [hf, hd]
    simp only [Parameters.envelope, f, zero_sub, neg_sq]
    change _ - _ * (_ - u) + _ = _
    nlinarith [congrArg (fun x : ℝ => t.Q * x) hu₂]
  have hH : (t.N : ℝ) * H = -t.constantTerm - h.margin := by
    dsimp [H]
    exact mul_div_cancel₀ _ hN.ne'
  have hr : t.constantTerm + (∑ i, (H + h.dual * (p i - u))) +
      ((t.N : ℝ) - Fintype.card ι) * (H + h.dual * (0 - u)) = -h.margin := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hp, Finset.card_univ]
    calc
      _ = t.constantTerm + (t.N : ℝ) * H + h.dual * (1 - (t.N : ℝ) * u) := by ring
      _ = -h.margin := by rw [hu, hH]; ring
  rw [he]
  linarith

/-- The certified margin is positive, so the envelope is strictly negative. -/
theorem envelope_neg {t : Parameters} (h : Certificate t)
    {ι : Type*} [Fintype ι] (hcard : Fintype.card ι ≤ t.N)
    (p : ι → ℝ) (hp : ∑ i, p i = 1) : t.envelope p < 0 :=
  (h.envelope_lt_margin hcard p hp).trans (neg_neg_of_pos h.margin_pos)

/-- Any normalized mixture estimate bounded by (22) is strictly negative. -/
theorem closes_mixture {t : Parameters} (h : Certificate t)
    {ι : Type*} [Fintype ι] (hcard : Fintype.card ι ≤ t.N)
    (p : ι → ℝ) (hp : ∑ i, p i = 1) {L : ℝ} (hL : L ≤ t.envelope p) : L < 0 :=
  hL.trans_lt (h.envelope_neg hcard p hp)

end Certificate

def cap31 : Parameters := ⟨30, 7, 22302 / 10000, 44 / 100, 86 / 100⟩
def cap51 : Parameters := ⟨50, 9, 22913 / 10000, 44 / 100, 82 / 100⟩
def cap101 : Parameters := ⟨100, 11, 23434 / 10000, 42 / 100, 84 / 100⟩

/-- Exact finite certificate at clique cutoff 31. -/
def certificate31 : Certificate cap31 where
  margin := 1 / 20000
  margin_pos := by norm_num
  dual := -52457 / 1000000
  N_pos := by norm_num [cap31]
  size_bounds := by norm_num [cap31]
  R_pos := by norm_num [cap31]
  mu_pos := by norm_num [cap31]
  sigma_bounds := by norm_num [cap31]
  edge_pos := by norm_num [Parameters.edgeFactor, distinctUniform, cap31, Nat.descFactorial]
  curl_condition := by norm_num [Parameters.beta, Parameters.c, Parameters.curlFactor,
    Parameters.edgeFactor, distinctUniform, cap31, Nat.descFactorial]
  credit_pos := by norm_num [Parameters.credit, Parameters.beta, Parameters.c,
    Parameters.edgeFactor, distinctUniform, cap31, Nat.descFactorial]
  Q_pos := by norm_num [Parameters.Q, Parameters.massCoeff, Parameters.r, Parameters.c,
    Parameters.credit, Parameters.beta, Parameters.edgeFactor, Parameters.chooseTwo,
    distinctUniform, cap31, Nat.descFactorial]
  rank_nonneg := by norm_num [Parameters.rankCoeff, Parameters.c, cap31]
  constant_neg := by norm_num [Parameters.constantTerm, Parameters.massCoeff, Parameters.r,
    Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, distinctUniform, cap31, Nat.descFactorial]
  inactive := by norm_num [Parameters.Q, Parameters.constantTerm, Parameters.massCoeff,
    Parameters.r, Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, distinctUniform, cap31, Nat.descFactorial]
  active := by norm_num [Parameters.Q, Parameters.constantTerm, Parameters.massCoeff,
    Parameters.r, Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, Parameters.rankCoeff, Parameters.threshold, Parameters.uniform,
    distinctUniform, cap31, Nat.descFactorial]

/-- Exact finite certificate at clique cutoff 51. -/
def certificate51 : Certificate cap51 where
  margin := 1 / 20000
  margin_pos := by norm_num
  dual := -37959 / 1000000
  N_pos := by norm_num [cap51]
  size_bounds := by norm_num [cap51]
  R_pos := by norm_num [cap51]
  mu_pos := by norm_num [cap51]
  sigma_bounds := by norm_num [cap51]
  edge_pos := by norm_num [Parameters.edgeFactor, distinctUniform, cap51, Nat.descFactorial]
  curl_condition := by norm_num [Parameters.beta, Parameters.c, Parameters.curlFactor,
    Parameters.edgeFactor, distinctUniform, cap51, Nat.descFactorial]
  credit_pos := by norm_num [Parameters.credit, Parameters.beta, Parameters.c,
    Parameters.edgeFactor, distinctUniform, cap51, Nat.descFactorial]
  Q_pos := by norm_num [Parameters.Q, Parameters.massCoeff, Parameters.r, Parameters.c,
    Parameters.credit, Parameters.beta, Parameters.edgeFactor, Parameters.chooseTwo,
    distinctUniform, cap51, Nat.descFactorial]
  rank_nonneg := by norm_num [Parameters.rankCoeff, Parameters.c, cap51]
  constant_neg := by norm_num [Parameters.constantTerm, Parameters.massCoeff, Parameters.r,
    Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, distinctUniform, cap51, Nat.descFactorial]
  inactive := by norm_num [Parameters.Q, Parameters.constantTerm, Parameters.massCoeff,
    Parameters.r, Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, distinctUniform, cap51, Nat.descFactorial]
  active := by norm_num [Parameters.Q, Parameters.constantTerm, Parameters.massCoeff,
    Parameters.r, Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, Parameters.rankCoeff, Parameters.threshold, Parameters.uniform,
    distinctUniform, cap51, Nat.descFactorial]

/-- Exact finite certificate at clique cutoff 101. -/
def certificate101 : Certificate cap101 where
  margin := 1 / 20000
  margin_pos := by norm_num
  dual := -6637 / 250000
  N_pos := by norm_num [cap101]
  size_bounds := by norm_num [cap101]
  R_pos := by norm_num [cap101]
  mu_pos := by norm_num [cap101]
  sigma_bounds := by norm_num [cap101]
  edge_pos := by norm_num [Parameters.edgeFactor, distinctUniform, cap101, Nat.descFactorial]
  curl_condition := by norm_num [Parameters.beta, Parameters.c, Parameters.curlFactor,
    Parameters.edgeFactor, distinctUniform, cap101, Nat.descFactorial]
  credit_pos := by norm_num [Parameters.credit, Parameters.beta, Parameters.c,
    Parameters.edgeFactor, distinctUniform, cap101, Nat.descFactorial]
  Q_pos := by norm_num [Parameters.Q, Parameters.massCoeff, Parameters.r, Parameters.c,
    Parameters.credit, Parameters.beta, Parameters.edgeFactor, Parameters.chooseTwo,
    distinctUniform, cap101, Nat.descFactorial]
  rank_nonneg := by norm_num [Parameters.rankCoeff, Parameters.c, cap101]
  constant_neg := by norm_num [Parameters.constantTerm, Parameters.massCoeff, Parameters.r,
    Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, distinctUniform, cap101, Nat.descFactorial]
  inactive := by norm_num [Parameters.Q, Parameters.constantTerm, Parameters.massCoeff,
    Parameters.r, Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, distinctUniform, cap101, Nat.descFactorial]
  active := by norm_num [Parameters.Q, Parameters.constantTerm, Parameters.massCoeff,
    Parameters.r, Parameters.c, Parameters.credit, Parameters.beta, Parameters.edgeFactor,
    Parameters.chooseTwo, Parameters.rankCoeff, Parameters.threshold, Parameters.uniform,
    distinctUniform, cap101, Nat.descFactorial]

/-- The three finite-clique rows of the C39 certificate. -/
inductive Cutoff
  | thirtyOne | fiftyOne | hundredOne

def Cutoff.parameters : Cutoff → Parameters
  | .thirtyOne => cap31
  | .fiftyOne => cap51
  | .hundredOne => cap101

def Cutoff.certificate : (k : Cutoff) → Certificate k.parameters
  | .thirtyOne => certificate31
  | .fiftyOne => certificate51
  | .hundredOne => certificate101

/-- All three C39 scalar bounds, uniform over arbitrary finite simplices. -/
theorem finite_envelope_neg (k : Cutoff) {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι ≤ k.parameters.N)
    (p : ι → ℝ) (hp : ∑ i, p i = 1) : k.parameters.envelope p < -(1 / 20000 : ℝ) := by
  have hm : k.certificate.margin = 1 / 20000 := by cases k <;> rfl
  simpa only [hm] using k.certificate.envelope_lt_margin hcard p hp

/-- Algebraic assembly of (19)--(22). Here `F` denotes `s! e_s(p)`;
the four hypotheses isolate the analytic and combinatorial inputs. -/
theorem mixture_le_envelope {ι : Type*} [Fintype ι] (t : Parameters) (hN : 0 < t.N) (p : ι → ℝ)
    (V D T H X F : ℝ) (hB : 0 ≤ t.credit)
    (hvariance : V ≤ (1 + t.mu) * (t.r * ((1 - ∑ i, p i ^ 2) / 2) - D - t.c * T) + t.c * H)
    (hcredit : t.credit * F ≤ (1 + t.mu) * (D + t.c * T))
    (hsymmetric : distinctUniform t.N t.s - Parameters.chooseTwo t.s * t.edgeFactor *
      ((∑ i, p i ^ 2) - t.uniform) ≤ F)
    (hpair : t.c * H + t.beta * X ≤ t.c * ((1 - ∑ i, p i ^ 2) / 2) +
      t.rankCoeff * ∑ i, p i * max (t.threshold - p i) 0) :
    V - t.r + t.beta * X ≤ t.envelope p := by
  have hc := (mul_le_mul_of_nonneg_left hsymmetric hB).trans hcredit
  unfold Parameters.envelope Parameters.constantTerm Parameters.Q Parameters.massCoeff
  have hn : Parameters.chooseTwo t.N / (t.N : ℝ) ^ 2 = (1 - t.uniform) / 2 := by
    unfold Parameters.chooseTwo Parameters.uniform
    have hN' : (t.N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  rw [show (((1 + t.mu) * t.r + t.c) * Parameters.chooseTwo t.N / (t.N : ℝ) ^ 2) =
    ((1 + t.mu) * t.r + t.c) * (1 - t.uniform) / 2 by rw [mul_div_assoc, hn]; ring]
  nlinarith only [hvariance, hc, hpair]

/-- The complete quantitative mixture certificate at each requested cutoff.
The symmetric-polynomial and retained-clique estimates remain explicit inputs. -/
theorem finite_mixture_neg (k : Cutoff) {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι ≤ k.parameters.N) (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (V D T H X F : ℝ)
    (hvariance : V ≤ (1 + k.parameters.mu) *
      (k.parameters.r * ((1 - ∑ i, p i ^ 2) / 2) - D - k.parameters.c * T) + k.parameters.c * H)
    (hcredit : k.parameters.credit * F ≤ (1 + k.parameters.mu) * (D + k.parameters.c * T))
    (hsymmetric : distinctUniform k.parameters.N k.parameters.s -
      Parameters.chooseTwo k.parameters.s * k.parameters.edgeFactor *
        ((∑ i, p i ^ 2) - k.parameters.uniform) ≤ F)
    (hpair : k.parameters.c * H + k.parameters.beta * X ≤
      k.parameters.c * ((1 - ∑ i, p i ^ 2) / 2) +
      k.parameters.rankCoeff * ∑ i, p i * max (k.parameters.threshold - p i) 0) :
    V - k.parameters.r + k.parameters.beta * X < -(1 / 20000 : ℝ) :=
  (mixture_le_envelope k.parameters k.certificate.N_pos p V D T H X F k.certificate.credit_pos.le
    hvariance hcredit hsymmetric hpair).trans_lt (finite_envelope_neg k hcard p hp)

end
end SimpleGraph.HilbertGlobalSubJungFinite

namespace SimpleGraph.HilbertGlobalSubJungFinite

open ChordalResidualExtension ChordalCliqueInvariant HilbertWeightedEnergy
open RetainedCliqueEnergy ElementarySymmetricAverage

noncomputable section

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem retained_edge_sum (p : ι → ℝ) (r : ℝ) (x : ι → ι → E) (hx : Skew x) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard 2, (∏ i ∈ A, p i) * edgeDeficit r x A) =
      HilbertRetainedRows.deficit p r x := by
  have hh := group_pairs p Finset.univ fun i j => r - ‖x i j‖ ^ 2
  simp only [edgeDeficit, ← mul_div_assoc, ← Finset.sum_div]
  rw [hh]
  have hf := ordered_pair_eq_two_sorted
    (fun i j => if i = j then 0 else p i * p j * (r - ‖x i j‖ ^ 2))
    (fun i j => by simp [eq_comm, hx i j, mul_comm (p i) (p j)]) (by simp)
  rw [hf]
  have hs : sortedPairSum (fun i j => if i = j then 0 else p i * p j * (r - ‖x i j‖ ^ 2)) =
      HilbertRetainedRows.deficit p r x := by
    unfold HilbertRetainedRows.deficit sortedPairSum
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      by_cases h : i < j <;> simp [h, ne_of_lt]
  rw [hs]
  ring

private theorem retained_curl_sum (p : ι → ℝ) (x : ι → ι → E) (hx : Skew x) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard 3, (∏ i ∈ A, p i) * curlSquare x A) =
      HilbertRetainedRows.triangleEnergy p x := by
  have hh := group_triples p Finset.univ fun i j k => ‖holonomy x i j k‖ ^ 2
  simp only [curlSquare, ← mul_div_assoc, ← Finset.sum_div]
  rw [hh]
  have hz (i j k : ι) (h : i = j ∨ j = k ∨ i = k) : holonomy x i j k = 0 := by
    rcases h with rfl | rfl | rfl
    · simp [holonomy, hx.diagonal]
    · simp [holonomy, hx.diagonal]
    · rw [← holonomy_rotate x hx i j i]
      simp [holonomy, hx.diagonal, hx i j]
  have he : (∑ i, ∑ j, ∑ k, if i = j ∨ j = k ∨ i = k then 0 else
      p i * p j * p k * ‖holonomy x i j k‖ ^ 2) = orderedCurlEnergy p x := by
    unfold orderedCurlEnergy
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by
        split_ifs with h
        · simp [show curl x i j k = 0 from hz i j k h]
        · rfl
  rw [he, ordered_curl_eq_six_sorted p x hx]
  change 6 * HilbertRetainedRows.triangleEnergy p x / 6 = _
  ring

private def Parameters.eCoeff (t : Parameters) : ℝ :=
  ((t.N - 2).choose (t.s - 2) : ℝ) * (1 / ((t.N - 2 : ℕ) : ℝ)) ^ (t.s - 2)

private def Parameters.tCoeff (t : Parameters) : ℝ :=
  ((t.N - 3).choose (t.s - 3) : ℝ) * (1 / ((t.N - 3 : ℕ) : ℝ)) ^ (t.s - 3)

private theorem Cutoff.arithmetic (k : Cutoff) :
    let t := k.parameters
    (0 ≤ t.beta) ∧ (0 < t.eCoeff) ∧ (0 ≤ t.credit) ∧
      t.beta * t.tCoeff ≤ t.c * t.eCoeff ∧
      t.eCoeff * (t.credit * (t.s.factorial : ℝ)) = (1 + t.mu) * (t.beta * (t.s.choose 3 : ℝ)) ∧
      factor t.N t.s = distinctUniform t.N t.s ∧
      (t.s.choose 2 : ℝ) * factor (t.N - 2) (t.s - 2) = Parameters.chooseTwo t.s * t.edgeFactor := by
  cases k <;>
    norm_num [Cutoff.parameters, cap31, cap51, cap101, Parameters.eCoeff, Parameters.tCoeff,
      Parameters.c, Parameters.beta, Parameters.credit, Parameters.edgeFactor, distinctUniform,
      factor, Parameters.chooseTwo, Nat.choose, Nat.factorial, Nat.descFactorial]

private theorem old_credit (k : Cutoff) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hm : ∑ i, p i = 1) (hcard : Fintype.card ι ≤ k.parameters.N)
    (x : ι → ι → E) (hx : Skew x)
    (hc : ∀ i j, i ≠ j → ‖x i j‖ ^ 2 ≤ k.parameters.r)
    (hi : ∀ W : Finset ι, W.card ≤ k.parameters.s →
      Retained k.parameters.beta (edgeDeficit k.parameters.r x) (curlSquare x) W) :
    let t := k.parameters
    t.credit * distinctUniform t.N t.s - (t.credit * Parameters.chooseTwo t.s * t.edgeFactor) *
      ((∑ i, p i ^ 2) - t.uniform) ≤
      (1 + t.mu) * (HilbertRetainedRows.deficit p t.r x + t.c * HilbertRetainedRows.triangleEnergy p x) := by
  classical
  let t := k.parameters
  let S : Finset ι := Finset.univ
  rcases k.arithmetic with ⟨hb, he, hB, hTc, hFac, hP, hS⟩
  have hs : 3 ≤ t.s := k.certificate.size_bounds.1
  have hn : 0 < t.N := k.certificate.N_pos
  have he₀ (A : Finset ι) (_ : A ∈ S.powersetCard 2) : 0 ≤ edgeDeficit t.r x A := by
    unfold edgeDeficit
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h
      · rfl
      · exact sub_nonneg.mpr (hc i j h)
  have ht₀ (A : Finset ι) (_ : A ∈ S.powersetCard 3) : 0 ≤ curlSquare x A := by
    unfold curlSquare
    exact div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => by split_ifs <;> positivity) (by norm_num)
  have complement (j : ℕ) (A : Finset ι) (hA : A ∈ S.powersetCard j) :
      (∑ T ∈ (S \ A).powersetCard (t.s - j), ∏ v ∈ T, p v) ≤
      ((t.N - j).choose (t.s - j) : ℝ) * (1 / ((t.N - j : ℕ) : ℝ)) ^ (t.s - j) := by
    obtain ⟨hsub, hlen⟩ := Finset.mem_powersetCard.mp hA
    apply complement_bound
    · rw [Finset.card_sdiff_of_subset hsub, hlen]
      exact Nat.sub_le_sub_right (by simpa [S] using hcard) _
    · exact fun i _ => hp i
    · rw [← hm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)
  have hA := RetainedCliqueEnergy.average p S t.s hs
      (edgeDeficit t.r x) (curlSquare x) t.beta t.eCoeff t.tCoeff
      (fun i _ => hp i) he₀ ht₀ hb (complement 2) (complement 3)
      (fun W hW => by
        have hh := (Finset.mem_powersetCard.mp hW).2
        simpa [Retained, cliqueSum, hh] using hi W hh.le)
  change _ ≤ _ at hA
  rw [retained_edge_sum p t.r x hx, retained_curl_sum p x hx] at hA
  have hLow := pad_lower S p t.N (t.s - 2) hn (by simpa [S] using hcard)
    (fun i _ => hp i) hm
  rw [show t.s - 2 + 2 = t.s by omega, hP, hS] at hLow
  have hT : 0 ≤ HilbertRetainedRows.triangleEnergy p x := by
    unfold HilbertRetainedRows.triangleEnergy sortedTripleSum
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => by
        split_ifs
        · exact mul_nonneg (mul_nonneg (mul_nonneg (hp i) (hp j)) (hp k)) (sq_nonneg _)
        · rfl
  have hM : 0 ≤ 1 + t.mu := by linarith [k.certificate.mu_pos]
  have hh := credit hB hM he hT hTc hFac hA hLow
  change _ ≤ _
  simpa only [Parameters.uniform, mul_sub, mul_assoc] using hh

end
end SimpleGraph.HilbertGlobalSubJungFinite

namespace SimpleGraph.HilbertGlobalSubJungFinite

open ChordalResidualExtension ChordalCliqueInvariant HilbertWeightedEnergy
open RetainedCliqueEnergy

noncomputable section

variable {V E : Type*} [LinearOrder V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem old_retained_subtype (K : Finset V) (g r : V → V → E)
    (a : V) (c : V → E) (hc : Compatible g a K r c)
    (s : ℕ) (cap beta : ℝ)
    (hi : ∀ W ⊆ K, W.card ≤ s → Retained beta (edgeDeficit cap r) (curlSquare g) W)
    (W : Finset K) (hs : W.card ≤ s) :
    Retained beta (edgeDeficit cap (fun i j : K => r i j)) (curlSquare (fun i j : K => r i j)) W := by
  classical
  let e : K ↪ V := Function.Embedding.subtype (· ∈ K)
  have hsub : W.map e ⊆ K := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have hh := hi (W.map e) hsub (by simpa using hs)
  simp only [Retained, cliqueSum, Finset.powersetCard_map, Finset.card_map, Finset.sum_map, Finset.mapEmbedding_apply] at hh ⊢
  have hE (A : Finset K) :
      edgeDeficit cap r (A.map e) = edgeDeficit cap (fun i j : K => r i j) A := by
    simp [edgeDeficit, Finset.sum_map, e]
  have hT (A : Finset K) :
      curlSquare g (A.map e) = curlSquare (fun i j : K => r i j) A := by
    unfold curlSquare
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    simp only [e, Function.Embedding.subtype_apply, Subtype.val_inj]
    change (if i = j ∨ j = k ∨ i = k then 0 else ‖holonomy g i.val j.val k.val‖ ^ 2) =
      (if i = j ∨ j = k ∨ i = k then 0 else ‖holonomy r i.val j.val k.val‖ ^ 2)
    rw [hc.curl _ i.property _ j.property _ k.property]
  have hmap (A : Finset K) : ((Finset.mapEmbedding e).toEmbedding A) = A.map e := rfl
  simpa only [hmap, hE, hT] using hh

private theorem new_retained_charge (K : Finset V) (g r : V → V → E) (hg : Skew g)
    (a : V) (ha : a ∉ K) (c : V → E) (hc : Compatible g a K r c)
    (y : K → K → E) (hy : Skew y)
    (hy_def : ∀ i j, y i j = r i j - (c i - c j)) (W : Finset K) :
    (∑ A ∈ (W.map (Function.Embedding.subtype (· ∈ K))).powersetCard 2,
      curlSquare g (insert a A)) =
        HilbertRetainedRows.subsetPairs W (fun i j => ‖y i j‖ ^ 2) := by
  classical
  let e : K ↪ V := Function.Embedding.subtype (· ∈ K)
  have hpair (A : Finset K) (hA : A ∈ W.powersetCard 2) :
      curlSquare g (insert a (A.map e)) =
        (∑ i ∈ A, ∑ j ∈ A, if i = j then 0 else ‖y i j‖ ^ 2) / 2 := by
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
    rw [Finset.map_insert, Finset.map_singleton]
    change curlSquare g (insert a {i.val, j.val}) = _
    rw [hc.curlSquare_pair hg ha i.property j.property (fun h => hij (Subtype.ext h))]
    rw [← hy_def i j]
    simp [hij, hij.symm, hy i j]
  simp only [Finset.powersetCard_map, Finset.sum_map, Finset.mapEmbedding_apply]
  change (∑ A ∈ W.powersetCard 2, curlSquare g (insert a (A.map e))) = _
  rw [Finset.sum_congr rfl hpair, ← Finset.sum_div]
  have hh := group_pairs (fun _ : K => (1 : ℝ)) W (fun i j => ‖y i j‖ ^ 2)
  simp only [Finset.prod_const_one, one_mul] at hh
  rw [hh]
  let f (i j : K) := if i ∈ W ∧ j ∈ W ∧ i ≠ j then ‖y i j‖ ^ 2 else 0
  have hsym (i j : K) : f j i = f i j := by
    simp [f, hy i j, and_comm, and_left_comm, ne_comm]
  have hs : (∑ i ∈ W, ∑ j ∈ W, if i = j then 0 else ‖y i j‖ ^ 2) =
      ∑ i, ∑ j, f i j := by
    have hW : (Finset.univ.filter (· ∈ W)) = W := by ext; simp
    conv_lhs => rw [← hW]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ W
    · simp only [hi, true_and, if_true]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ W <;> by_cases h : i = j <;> simp [f, hW, hi, hj, h]
    · simp [f, hi, hW]
  rw [hs, ordered_pair_eq_two_sorted f hsym (by simp [f])]
  have he : sortedPairSum f = HilbertRetainedRows.subsetPairs W (fun i j => ‖y i j‖ ^ 2) := by
    unfold sortedPairSum HilbertRetainedRows.subsetPairs
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      by_cases h : i < j <;> simp [h, ne_of_lt, f]
  rw [he]
  ring

private theorem chooseTwo_cast (n : ℕ) :
    (n.choose 2 : ℝ) = Parameters.chooseTwo n := by
  cases n with
  | zero => simp [Parameters.chooseTwo]
  | succ n =>
    have h : 2 * ((n + 1).choose 2) = (n + 1) * n := by
      rw [mul_comm 2, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (n + 1))]
      simp
    have hr : (2 : ℝ) * ((n + 1).choose 2 : ℝ) = ((n : ℝ) + 1) * (n : ℝ) := by exact_mod_cast h
    unfold Parameters.chooseTwo
    push_cast
    linarith

private theorem cutoff_scalar (k : Cutoff) (K : Finset V) (hK : K.card ≤ k.parameters.N)
    (p : K → ℝ) (hp : ∑ i, p i = 1) :
    let t := k.parameters
    HilbertRetainedRows.envelope t.s t.r t.mu t.threshold
      (t.credit * distinctUniform t.N t.s) (t.credit * Parameters.chooseTwo t.s * t.edgeFactor)
      t.uniform p ≤ 0 := by
  let t := k.parameters
  have hh := (k.certificate.envelope_neg (ι := K) (by simpa using hK) p hp).le
  have hN : (t.N : ℝ) ≠ 0 := by exact_mod_cast k.certificate.N_pos.ne'
  have he : Parameters.chooseTwo t.N / (t.N : ℝ) ^ 2 = (1 - t.uniform) / 2 := by
    unfold Parameters.chooseTwo Parameters.uniform
    field_simp
    <;> ring
  unfold HilbertRetainedRows.envelope
  unfold Parameters.envelope Parameters.constantTerm Parameters.Q Parameters.massCoeff Parameters.rankCoeff at hh
  rw [mul_div_assoc, he] at hh
  have hs : 2 ≤ t.s := (le_trans (by decide : 2 ≤ 3) k.certificate.size_bounds.1)
  dsimp only
  rw [Nat.cast_sub hs]
  unfold Parameters.c at hh
  convert hh using 1 <;> ring

set_option maxHeartbeats 4000000 in
private theorem place_retained {G : SimpleGraph V} (k : Cutoff)
    (a : V) (K : Finset V) (ha : a ∉ K) (hK : G.IsClique (K : Set V))
    (hN : K.card ≤ k.parameters.N)
    (g r : V → V → E) (hg : Skew g) (c : V → E) (hr : Skew r)
    (he : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖r i j‖ ^ 2 ≤ k.parameters.r)
    (hInv : ∀ W ⊆ K, W.card ≤ k.parameters.s →
      Retained k.parameters.beta (edgeDeficit k.parameters.r r) (curlSquare g) W)
    (hc : Compatible g a K r c)
    (hnew : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖holonomy g i j a‖ ≤ 1) :
    ∃ z, SubsetRows k.parameters.s k.parameters.r k.parameters.beta K c
      (fun A => curlSquare g (insert a A)) z := by
  classical
  let t := k.parameters
  let x (i j : K) := r i.val j.val
  let v (i : K) := c i.val
  let y (i j : K) := x i j - (v i - v j)
  have hx : Skew x := fun i j => hr i j
  have hy : Skew y := by
    intro i j
    dsimp [y]
    rw [hx i j]
    abel
  have hcap (i j : K) : ‖y i j‖ ^ 2 ≤ 1 := by
    by_cases hij : i = j
    · subst j; simp [hy.diagonal]
    · rw [show y i j = holonomy g i.val j.val a from hc.defect _ i.property _ j.property]
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hnew _ i.property _ j.property
        (fun eq => hij (Subtype.ext eq))) 2
  have hcOld (p : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hm : ∑ i, p i = 1) :
      t.credit * distinctUniform t.N t.s - t.credit * Parameters.chooseTwo t.s * t.edgeFactor *
        ((∑ i, p i ^ 2) - t.uniform) ≤
      (1 + t.mu) * (HilbertRetainedRows.deficit p t.r x +
        t.c * HilbertRetainedRows.triangleEnergy p x) :=
    old_credit k p hp hm (by simpa using hN) x hx
      (fun i j h => he _ i.property _ j.property (fun eq => h (Subtype.ext eq)))
      (old_retained_subtype K g r a c hc t.s t.r t.beta hInv)
  obtain ⟨z, hz⟩ := HilbertRetainedRows.exists_predecessor_centers K t.s v x y hx hy
    (fun i j => by dsimp [y]; abel) hcap t.r t.mu t.threshold
    (t.credit * distinctUniform t.N t.s) (t.credit * Parameters.chooseTwo t.s * t.edgeFactor)
    t.uniform k.certificate.mu_pos hcOld (fun p _ hp => cutoff_scalar k K hN p hp)
  refine ⟨z, fun W hWK hs => ?_⟩
  by_cases hW : W.Nonempty
  · let A : Finset K := W.subtype (· ∈ K)
    let e : K ↪ V := Function.Embedding.subtype (· ∈ K)
    have hA : A.map e = W := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact (Finset.mem_subtype.mp hj)
      · intro hi
        exact Finset.mem_map.mpr ⟨⟨i, hWK hi⟩, Finset.mem_subtype.mpr hi, rfl⟩
    have hcard : A.card = W.card := by simpa using congrArg Finset.card hA
    have hA' : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hW.card_pos)
    have hAs : A.card ≤ t.s - 1 := by
      have hWs : W.card < t.s := hs
      rw [hcard]
      omega
    have hZ := hz A hA' hAs
    have hsum : (∑ i ∈ W, ‖c i - z‖ ^ 2) = ∑ i ∈ A, ‖v i - z‖ ^ 2 := by
      rw [← hA, Finset.sum_map]
      rfl
    have hβ : (1 + 1 / t.mu) * t.threshold = t.beta := by
      unfold Parameters.beta Parameters.threshold Parameters.c
      ring
    change (∑ i ∈ A, ‖v i - z‖ ^ 2) ≤ A.card * t.r -
      ((1 + 1 / t.mu) * t.threshold) * Parameters.chooseTwo A.card +
      ((1 + 1 / t.mu) * t.threshold) * HilbertRetainedRows.subsetPairs A (fun i j => ‖y i j‖ ^ 2) at hZ
    rw [hβ, ← new_retained_charge K g r hg a ha c hc y hy (fun _ _ => rfl), hA,
      hcard, ← hsum, ← chooseTwo_cast] at hZ
    exact hZ
  · rw [Finset.not_nonempty_iff_eq_empty.mp hW]
    norm_num [Finset.powersetCard_eq_empty.mpr (by simp : (∅ : Finset V).card < 2)]

end
end SimpleGraph.HilbertGlobalSubJungFinite


namespace SimpleGraph.HilbertGlobalSubJungFinite

open ChordalResidualExtension ChordalCliqueInvariant

variable {V E : Type*} [Finite V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : SimpleGraph V}

/-- The retained-curl invariant gives all three certified clique-cutoff bounds
for a finite chordal graph with unit-bounded triangle defects. -/
theorem exists_retained_potential (hG : G.IsChordal) (k : Cutoff)
    (hclique : ∀ W : Finset V, G.IsClique (W : Set V) → W.card ≤ k.parameters.N + 1)
    (g : V → V → E) (hg : Skew g)
    (ht : ∀ i j l, Triangle G i j l → ‖holonomy g i j l‖ ≤ 1) :
    ∃ p : V → E, ∀ i j, G.Adj i j → ‖ChordalResidualExtension.residual g p i j‖ ≤ k.parameters.R := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let t := k.parameters
  have hs : 2 ≤ t.s := le_trans (by decide : 2 ≤ 3) k.certificate.size_bounds.1
  have hsize (W : Finset V) (hcl : G.IsClique (W : Set V)) (_ : W.Nonempty) :
      W.card - 1 ≤ t.N := by
    have hh : W.card ≤ t.N + 1 := hclique W hcl
    omega
  obtain ⟨p, hp, _⟩ := reconstruct_retained hG t.s hs t.r t.beta (· ≤ t.N) hsize g hg ht (by
    intro a K ha hK hN r c hr he hi hnew hc _
    exact place_retained k a K ha hK hN g r hg c hr he hi hc
      (fun i hi j hj hij => by rw [← hc.defect i hi j hj]; exact hnew i hi j hj hij))
  refine ⟨p, fun i j hij => ?_⟩
  have hR := k.certificate.R_pos
  have hsq := hp i j hij
  change ‖ChordalResidualExtension.residual g p i j‖ ^ 2 ≤ t.R ^ 2 at hsq
  exact le_of_pow_le_pow_left₀ (by norm_num) hR.le hsq

end SimpleGraph.HilbertGlobalSubJungFinite

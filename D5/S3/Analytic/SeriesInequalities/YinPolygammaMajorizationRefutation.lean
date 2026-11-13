/- GID: D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite polygamma majorization fails through a strict interior moment gap. -/

/-
admission_basis: open-problem-resolution (#24132; Refuted)
escape_witness: none; all proof declarations are bind-only compositions.
Direct frozen dependencies:
  D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity
    statement_id: sha256:82e7a2e4b177029c6eb3b146ff93acceb3a20f5fc6f490f44f8d60c6b556d7ef
  D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc
    statement_id: sha256:202c59b217e53e6c388923e06fa6acf48979f254a0e5c1bb35bd4e89c937db55
  D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed
    statement_id: sha256:565b9b70d03155f061b4fe949164aa173255e7ceac42365730d8420ff3c7616a
  D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.prefixSum
    statement_id: sha256:93ca1f1520e0d21d918273555bd2933d31f2a7bfe3a4b3c132e8c154b2ffdc8b
Escape audit unfinished: result is an audit target under utility: none;
https://github.com/the-omega-institute/trureturing/issues/29215
The source definitions are retained; sorting and weak majorization use their
existing owners directly. Implementation-only moment abbreviations are expanded.
All declarations describe arbitrary-parameter functions, limits or inequalities;
none is a bounded enumeration, checker, computed bound or certified instance.
proof_shape: psi: bind-only; consumer=polygamma_eq,polygamma; escape_witness: none
  Direct frozen dependencies: none
proof_shape: polygamma: bind-only;
  consumer=polygamma_ne_zero,polygamma_ratio,Q_family,Q,polygamma_eq; escape_witness: none
  Direct frozen dependencies: none
proof_shape: StrictlyMajorized: bind-only; consumer=family_majorization,result,claim,family_failure;
  escape_witness: none
  Direct frozen dependencies: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed
proof_shape: Q: bind-only; consumer=Q_family,result,claim,family_failure; escape_witness: none
  Direct frozen dependencies: none
proof_shape: claim: bind-only; consumer=result; escape_witness: none
  Direct frozen dependencies: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed
proof_shape: polygamma_eq: bind-only; consumer=polygamma_ne_zero,polygamma_ratio; escape_witness:
  none
  Direct frozen dependencies: none
proof_shape: ratio: bind-only;
  consumer=ratio_bounds,polygamma_ratio,Q_family,ratio_endpoints,family_failure,ratio_normalized,ratio_neither_monotone;
  escape_witness: none
  Direct frozen dependencies: none
proof_shape: moment_gap_identity: bind-only; consumer=strict_moment_gap; escape_witness: none
  Direct frozen dependencies: D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity
proof_shape: S_pos: bind-only; consumer=ratio_bounds,polygamma_ne_zero,polygamma_ratio;
  escape_witness: none
  Direct frozen dependencies: none
proof_shape: strict_moment_gap: bind-only; consumer=ratio_bounds; escape_witness: none
  Direct frozen dependencies: D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity
proof_shape: ratio_bounds: bind-only; consumer=ratio_neither_monotone; escape_witness: none
  Direct frozen dependencies: D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity
proof_shape: normalized_eq: bind-only; consumer=ratio_normalized; escape_witness: none
  Direct frozen dependencies: none
proof_shape: ratio_normalized: bind-only; consumer=ratio_endpoints; escape_witness: none
  Direct frozen dependencies: none
proof_shape: normalized_atTop: bind-only; consumer=ratio_endpoints; escape_witness: none
  Direct frozen dependencies: none
proof_shape: normalized_atZero: bind-only; consumer=ratio_endpoints; escape_witness: none
  Direct frozen dependencies: none
proof_shape: ratio_endpoints: bind-only; consumer=ratio_neither_monotone; escape_witness: none
  Direct frozen dependencies: none
proof_shape: ratio_neither_monotone: bind-only; consumer=family_failure; escape_witness: none
  Direct frozen dependencies: D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity
proof_shape: beta: bind-only;
  consumer=Q_family,desc_beta,family_majorization,beta_list,result,family_failure,orders_positive;
  escape_witness: none
  Direct frozen dependencies: none
proof_shape: desc_alpha: bind-only; consumer=family_majorization; escape_witness: none
  Direct frozen dependencies: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc
proof_shape: beta_list: bind-only; consumer=desc_beta; escape_witness: none
  Direct frozen dependencies: none
proof_shape: desc_beta: bind-only; consumer=family_majorization; escape_witness: none
  Direct frozen dependencies: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc
proof_shape: family_majorization: bind-only; consumer=family_failure; escape_witness: none
  Direct frozen dependencies: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.prefixSum
proof_shape: orders_positive: bind-only; consumer=result; escape_witness: none
  Direct frozen dependencies: none
proof_shape: polygamma_ne_zero: bind-only; consumer=Q_family; escape_witness: none
  Direct frozen dependencies: none
proof_shape: polygamma_ratio: bind-only; consumer=Q_family; escape_witness: none
  Direct frozen dependencies: none
proof_shape: Q_family: bind-only; consumer=family_failure; escape_witness: none
  Direct frozen dependencies: none
proof_shape: family_failure: bind-only; consumer=result; escape_witness: none
  Direct frozen dependencies: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.prefixSum,
    D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity
proof_shape: result: bind-only; consumer=settling result; escape_witness: none
  Direct frozen dependencies: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed,
    D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.prefixSum,
    D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity
-/

import D5.S3.QuantumBounds.LagrangeGramIdentity
import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing

/-! Binding definitions for Li Yin, JMI 16(3) (2022), Conjecture 4.1.
The truncation index p is a positive integer; k and x are positive reals.
Equation (1.5) and the preceding derivative definition bind psi and polygamma.
The inconsistent finite-sum sign printed in (1.6) is not a definition here.
-/

namespace D5.S3.Analytic.SeriesInequalities.YinPolygammaMajorizationRefutation

open scoped BigOperators
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing (moreMixed desc)

noncomputable section

/-- Source (1.5): psi_{p,k}(x) = log(pk)/k - sum_{j=0}^p 1/(jk+x). -/
def psi (p : ℕ) (k x : ℝ) : ℝ :=
  (1 / k) * Real.log ((p : ℝ) * k) -
    ∑ j ∈ Finset.range (p + 1), 1 / ((j : ℝ) * k + x)

/-- The source defines psi_{p,k}^{(m)} as the m-th derivative of psi_{p,k}. -/
def polygamma (p : ℕ) (k : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv m (psi p k) x

/-- Strict majorization: the existing weak-majorization owner and distinct rearrangements. -/
def StrictlyMajorized {n : ℕ} (a b : Fin n → ℕ) : Prop :=
  moreMixed (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) ∧
    desc (fun i => (a i : ℝ)) ≠ desc (fun i => (b i : ℝ))

/-- The product quotient in Conjecture 4.1, with the source's positive derivative orders. -/
def Q {n : ℕ} (p : ℕ) (k : ℝ) (a b : Fin n → ℕ) (x : ℝ) : ℝ :=
  (∏ i, polygamma p k (a i) x) / (∏ i, polygamma p k (b i) x)

/-- Conjecture 4.1 itself, including the asserted open image interval.
“Decreasing” means weak decrease; the proposed family refutes this as well. -/
def claim : Prop :=
  ∀ p : ℕ, 0 < p → ∀ k : ℝ, 0 < k → ∀ n : ℕ, 0 < n →
    ∀ a b : Fin n → ℕ, (∀ i, 0 < a i) → (∀ i, 0 < b i) →
      StrictlyMajorized a b →
        AntitoneOn (Q p k a b) (Set.Ioi 0) ∧
          (Q p k a b) '' (Set.Ioi 0) =
            Set.Ioo
              ((∏ i, (Nat.factorial (a i - 1) : ℝ)) /
                (∏ i, (Nat.factorial (b i - 1) : ℝ)))
              ((∏ i, (Nat.factorial (a i) : ℝ)) /
                (∏ i, (Nat.factorial (b i) : ℝ)))

open scoped Topology
open Filter

private lemma polygamma_eq (p r : ℕ) (k x : ℝ) (hk : 0 < k) (hx : 0 < x) (hr : 0 < r) :
    polygamma p k r x = (-1 : ℝ) ^ (r+1) * (r.factorial : ℝ) * (∑ j ∈ Finset.range (p + 1), (1 /
        ((j : ℝ) * k + x)) ^ (r+1)) := by
  have hd (j : ℕ) : (j : ℝ) * k + x ≠ 0 := by positivity
  have hc (j : ℕ) : ContDiffAt ℝ r (fun y : ℝ => 1 / ((j : ℝ) * k + y)) x := by
    exact contDiffAt_const.div (contDiffAt_const.add contDiffAt_id) (hd j)
  unfold polygamma psi
  rw [iteratedDeriv_const_sub hr, iteratedDeriv_neg, iteratedDeriv_fun_sum (fun j _ => hc j)]
  have hi (j : ℕ) : iteratedDeriv r (fun y : ℝ => 1 / ((j : ℝ) * k + y)) x =
      (-1 : ℝ)^r * (r.factorial : ℝ) * (1 / ((j : ℝ) * k + x))^(r+1) := by
    have hf : (fun y : ℝ => 1 / ((j : ℝ) * k + y)) =
        (fun y : ℝ => (1 * y + (j : ℝ) * k)⁻¹) := by ext y; simp [add_comm]
    rw [hf, iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
    simp only [one_mul, one_pow, mul_one]
    rw [show (-1 - (r : ℤ)) = -((r+1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    simp [one_div, inv_pow, add_comm]
  simp_rw [hi]
  simp only [Finset.mul_sum, pow_succ]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

open Filter
private def ratio (p : ℕ) (k : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ((m : ℝ) / (m+1)) * (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ (m+1)) ^ 2 / ((∑ j ∈
      Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ m) * (∑ j ∈ Finset.range (p + 1), (1 / ((j :
      ℝ) * k + x)) ^ (m+2)))

private lemma moment_gap_identity {ι : Type*} (s : Finset ι) (u : ι → ℝ) (m : ℕ)
    (hu : ∀ i ∈ s, 0 ≤ u i) :
    2 * ((∑ i ∈ s, u i ^ m) * (∑ i ∈ s, u i ^ (m+2)) -
      (∑ i ∈ s, u i ^ (m+1)) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, u i ^ m * u j ^ m * (u i - u j)^2 := by
  let a : ι → ℝ := fun i => Real.sqrt (u i ^ m)
  have ha (i : ι) (hi : i ∈ s) : a i ^ 2 = u i ^ m :=
    Real.sq_sqrt (pow_nonneg (hu i hi) m)
  have hA : (∑ i ∈ s, a i ^ 2) = ∑ i ∈ s, u i ^ m :=
    Finset.sum_congr rfl ha
  have hB : (∑ i ∈ s, (a i * u i)^2) = ∑ i ∈ s, u i ^ (m+2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, ha i hi, pow_add]
  have hC : (∑ i ∈ s, a i * (a i * u i)) = ∑ i ∈ s, u i ^ (m+1) := by
    apply Finset.sum_congr rfl
    intro i hi
    calc a i * (a i * u i) = a i ^ 2 * u i := by ring
         _ = u i ^ (m+1) := by rw [ha i hi, pow_succ]
  have hD : (∑ i ∈ s, ∑ j ∈ s, (a i * (a j*u j) - a j*(a i*u i))^2) =
      ∑ i ∈ s, ∑ j ∈ s, u i ^ m * u j ^ m * (u i-u j)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    calc (a i * (a j*u j) - a j*(a i*u i))^2 = a i^2 * a j^2 * (u i-u j)^2 := by ring
         _ = _ := by rw [ha i hi, ha j hj]
  have hg := D5.S3.QuantumBounds.LagrangeGramIdentity.lagrange_gram_identity
    s a (fun i => a i*u i)
  rw [hA, hB, hC, hD] at hg
  linarith

private lemma S_pos (p r : ℕ) (k x : ℝ) (hk : 0 < k) (hx : 0 < x) : 0 < (∑ j ∈ Finset.range (p +
    1), (1 / ((j : ℝ) * k + x)) ^ r) := by
  apply Finset.sum_pos
  · intro j hj
    exact pow_pos (by positivity) _
  · exact ⟨0, by simp⟩

private lemma strict_moment_gap (p m : ℕ) (k x : ℝ) (hp : 0 < p) (hk : 0 < k) (hx : 0 < x) :
    (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ (m+1)) ^ 2 < (∑ j ∈ Finset.range (p +
        1), (1 / ((j : ℝ) * k + x)) ^ m) * (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^
        (m+2)) := by
  let u : ℕ → ℝ := fun j => 1 / ((j : ℝ)*k+x)
  have hu (j : ℕ) : 0 < u j := by dsimp [u]; positivity
  have hn (i j : ℕ) : 0 ≤ u i ^ m * u j ^ m * (u i-u j)^2 := by positivity
  have h01 : u 0 ≠ u 1 := by
    have ht : 1 / (k+x) < 1/x := one_div_lt_one_div_of_lt hx (by linarith)
    simpa [u] using ne_of_gt ht
  have hs : 0 < ∑ i ∈ Finset.range (p+1), ∑ j ∈ Finset.range (p+1),
      u i ^ m * u j ^ m * (u i-u j)^2 := by
    apply Finset.sum_pos'
    · intro i hi; exact Finset.sum_nonneg (fun j hj => hn i j)
    · refine ⟨0, by simp, ?_⟩
      apply Finset.sum_pos'
      · intro j hj; exact hn 0 j
      · refine ⟨1, by simp; omega, ?_⟩
        exact mul_pos (mul_pos (pow_pos (hu 0) m) (pow_pos (hu 1) m))
          (sq_pos_of_ne_zero (sub_ne_zero.mpr h01))
  have he := moment_gap_identity (Finset.range (p+1)) u m (fun i _ => (hu i).le)
  change 2 * ((∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ m) * (∑ j ∈ Finset.range (p +
      1), (1 / ((j : ℝ) * k + x)) ^ (m+2)) - (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x))
      ^ (m+1)) ^ 2) = _ at he
  linarith

private lemma ratio_bounds (p m : ℕ) (k x : ℝ) (hp : 0 < p) (hm : 0 < m)
    (hk : 0 < k) (hx : 0 < x) : 0 < ratio p k m x ∧ ratio p k m x < (m : ℝ)/(m+1) := by
  have ha := S_pos p m k x hk hx
  have hb := S_pos p (m+1) k x hk hx
  have hc := S_pos p (m+2) k x hk hx
  have hd := strict_moment_gap p m k x hp hk hx
  have hm' : (0 : ℝ) < m := by exact Nat.cast_pos'.mpr hm
  have hconst : 0 < (m : ℝ)/(m+1) := by positivity
  constructor
  · exact div_pos (mul_pos hconst (sq_pos_of_pos hb)) (mul_pos ha hc)
  · unfold ratio
    apply (div_lt_iff₀ (mul_pos ha hc)).mpr
    exact mul_lt_mul_of_pos_left hd hconst

private lemma normalized_eq (p r : ℕ) (k x : ℝ) : (∑ j ∈ Finset.range (p + 1), (x / ((j : ℝ) * k +
    x)) ^ r) = x^r * (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ r) := by
  simp [div_eq_mul_inv, mul_pow, Finset.mul_sum]

private lemma ratio_normalized (p m : ℕ) (k x : ℝ) (hx : x ≠ 0) :
    ratio p k m x = ((m : ℝ)/(m+1)) * (∑ j ∈ Finset.range (p + 1), (x / ((j : ℝ) * k + x)) ^
        (m+1)) ^ 2 /
      ((∑ j ∈ Finset.range (p + 1), (x / ((j : ℝ) * k + x)) ^ m) * (∑ j ∈ Finset.range (p + 1), (x
          / ((j : ℝ) * k + x)) ^ (m+2))) := by
  have hz : (x^(m+1))^2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hx)
  calc ratio p k m x =
      ((x^(m+1))^2 * (((m : ℝ)/(m+1))*(∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^
          (m+1))^2)) /
        ((x^(m+1))^2 * ((∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ m)*(∑ j ∈
            Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ (m+2)))) := by
          exact (mul_div_mul_left _ _ hz).symm
       _ = _ := by
          simp only [normalized_eq]
          congr 1 <;> simp only [pow_succ] <;> ring

private lemma normalized_atTop (p r : ℕ) (k : ℝ) :
    Tendsto ((fun y : ℝ => (∑ j ∈ Finset.range (p + 1), (y / ((j : ℝ) * k + y)) ^ r))) atTop (𝓝
        (p+1 : ℝ)) := by
  have hj (j : ℕ) : Tendsto (fun x : ℝ => (x/((j : ℝ)*k+x))^r) atTop (𝓝 1) := by
    have ht : Tendsto (fun x : ℝ => 1 / ((j : ℝ)*k/x+1)) atTop (𝓝 1) := by
      have hd : Tendsto (fun x : ℝ => (j : ℝ)*k/x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have ha := hd.add_const (1 : ℝ)
      convert (tendsto_const_nhds (x := (1 : ℝ))).div ha
        (by norm_num : (0 : ℝ)+1 ≠ 0) using 1 <;> first | rfl | norm_num
    have he : (fun x : ℝ => x/((j : ℝ)*k+x)) =ᶠ[atTop]
        (fun x : ℝ => 1 / ((j : ℝ)*k/x+1)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [ne_of_gt hx]
    simpa using (ht.congr' he.symm).pow r
  change Tendsto (fun x : ℝ => ∑ j ∈ Finset.range (p+1),
    (x/((j : ℝ)*k+x))^r) atTop (𝓝 (p+1 : ℝ))
  simpa using tendsto_finsetSum (Finset.range (p+1)) (fun j hj' => hj j)

private lemma normalized_atZero (p r : ℕ) (k : ℝ) (hk : 0 < k) (hr : 0 < r) :
    Tendsto ((fun y : ℝ => (∑ j ∈ Finset.range (p + 1), (y / ((j : ℝ) * k + y)) ^ r))) (𝓝[>] 0) (𝓝
        1) := by
  have he : ((fun y : ℝ => (∑ j ∈ Finset.range (p + 1), (y / ((j : ℝ) * k + y)) ^ r))) =ᶠ[𝓝[>] 0]
      (fun x => 1 + ∑ j ∈ Finset.range p, (x/(((j+1 : ℕ) : ℝ)*k+x))^r) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Finset.sum_range_succ']
    have hx' : x ≠ 0 := ne_of_gt hx
    simp [hx', add_comm]
  have hj (j : ℕ) : Tendsto (fun x : ℝ => (x/(((j+1 : ℕ) : ℝ)*k+x))^r)
      (𝓝[>] 0) (𝓝 0) := by
    have hd : (((j+1 : ℕ) : ℝ)*k + 0) ≠ 0 := by positivity
    have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hden : Tendsto (fun x : ℝ => ((j+1 : ℕ) : ℝ)*k+x)
        (𝓝[>] 0) (𝓝 (((j+1 : ℕ) : ℝ)*k+0)) :=
      tendsto_const_nhds.add hid
    simpa [ne_of_gt hr] using (hid.div hden hd).pow r
  have hs := (tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_finsetSum (Finset.range p) (fun j hj' => hj j))
  simpa using hs.congr' he.symm

private lemma ratio_endpoints (p m : ℕ) (k : ℝ) (hk : 0 < k) (hm : 0 < m) :
    Tendsto (ratio p k m) atTop (𝓝 ((m : ℝ)/(m+1))) ∧
    Tendsto (ratio p k m) (𝓝[>] 0) (𝓝 ((m : ℝ)/(m+1))) := by
  constructor
  · have hlim := ((tendsto_const_nhds (x := ((m : ℝ)/(m+1)))).mul ((normalized_atTop p (m+1)
      k).pow 2)).div
      ((normalized_atTop p m k).mul (normalized_atTop p (m+2) k)) (by positivity)
    have he : ratio p k m =ᶠ[atTop] (fun x => ((m : ℝ)/(m+1)) *
        (∑ j ∈ Finset.range (p + 1), (x / ((j : ℝ) * k + x)) ^ (m+1)) ^ 2 / ((∑ j ∈ Finset.range
            (p + 1), (x / ((j : ℝ) * k + x)) ^ m) * (∑ j ∈ Finset.range (p + 1), (x / ((j : ℝ) * k
            + x)) ^ (m+2)))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact ratio_normalized p m k x (ne_of_gt hx)
    have hp' : (p : ℝ)+1 ≠ 0 := by exact Nat.cast_add_one_ne_zero p
    convert hlim.congr' he.symm using 1
    field_simp
  · have hlim := ((tendsto_const_nhds (x := ((m : ℝ)/(m+1)))).mul ((normalized_atZero p (m+1) k hk
      (by omega)).pow 2)).div
      ((normalized_atZero p m k hk hm).mul (normalized_atZero p (m+2) k hk (by omega)))
      (by norm_num : (1 : ℝ)*1 ≠ 0)
    have he : ratio p k m =ᶠ[𝓝[>] 0] (fun x => ((m : ℝ)/(m+1)) *
        (∑ j ∈ Finset.range (p + 1), (x / ((j : ℝ) * k + x)) ^ (m+1)) ^ 2 / ((∑ j ∈ Finset.range
            (p + 1), (x / ((j : ℝ) * k + x)) ^ m) * (∑ j ∈ Finset.range (p + 1), (x / ((j : ℝ) * k
            + x)) ^ (m+2)))) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact ratio_normalized p m k x (ne_of_gt hx)
    simpa using hlim.congr' he.symm

private lemma ratio_neither_monotone (p m : ℕ) (k : ℝ) (hp : 0 < p) (hm : 0 < m) (hk : 0 < k) :
    ¬ AntitoneOn (ratio p k m) (Set.Ioi 0) ∧ ¬ MonotoneOn (ratio p k m) (Set.Ioi 0) := by
  have hb := (ratio_bounds p m k 1 hp hm hk (by norm_num)).2
  have hl := ratio_endpoints p m k hk hm
  constructor
  · intro ha
    have hh : (m : ℝ)/(m+1) ≤ ratio p k m 1 := le_of_tendsto hl.1 (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact ha (by norm_num) (by change 0 < x; linarith) hx)
    have hu : ratio p k m 1 ≤ (m : ℝ)/(m+1) := ge_of_tendsto hl.2 (by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 :
          ℝ)<1 by norm_num))] with x hx hx'
      exact ha hx (by norm_num) (le_of_lt hx'))
    exact (ne_of_lt hb) (le_antisymm hu hh)
  · intro ha
    have hh : (m : ℝ)/(m+1) ≤ ratio p k m 1 := le_of_tendsto hl.2 (by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 :
          ℝ)<1 by norm_num))] with x hx hx'
      exact ha hx (by norm_num) (le_of_lt hx'))
    linarith

open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
private def beta (m l : ℕ) : Fin (l+2) → ℕ :=
  Fin.cons (m-1) (Fin.cons (m+1) (fun _ : Fin l => m))

private lemma desc_alpha (m l : ℕ) :
    desc (fun i => ((Function.const (Fin (l+2)) m) i : ℝ)) = List.replicate (l+2) (m : ℝ) := by
  unfold desc Function.const
  simp only [List.ofFn_const]
  apply List.mergeSort_eq_self
  exact List.pairwise_replicate.mpr (Or.inr le_rfl)

private lemma beta_list (m l : ℕ) :
    List.ofFn (fun i => (beta m l i : ℝ)) =
      ((m-1 : ℕ) : ℝ) :: (m+1 : ℝ) :: List.replicate l (m : ℝ) := by
  have he : (fun i => (beta m l i : ℝ)) =
      Fin.cons ((m-1 : ℕ) : ℝ) (Fin.cons (m+1 : ℝ) (fun _ : Fin l => (m : ℝ))) := by
    change ((fun r : ℕ => (r : ℝ)) ∘
      Fin.cons (m-1) (Fin.cons (m+1) (fun _ : Fin l => m))) = _
    rw [Fin.comp_cons, Fin.comp_cons]
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
  rw [he]
  simp

private lemma desc_beta (m l : ℕ) (hm : 1 ≤ m) :
    desc (fun i => (beta m l i : ℝ)) =
      (m+1 : ℝ) :: (List.replicate l (m : ℝ) ++ [((m-1 : ℕ) : ℝ)]) := by
  unfold desc
  rw [beta_list]
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℝ => b ≤ a)
  · exact List.pairwise_mergeSort' _ _
  · have hcast : ((m-1 : ℕ) : ℝ) = (m : ℝ)-1 := by
      rw [Nat.cast_sub hm]; norm_num
    simp only [List.pairwise_cons, List.mem_append, List.mem_replicate, List.mem_singleton,
      List.pairwise_append, List.pairwise_replicate, hcast]
    constructor
    · intro a ha
      rcases ha with ⟨_, rfl⟩ | rfl <;> linarith
    · refine ⟨Or.inr le_rfl, by simp, ?_⟩
      intro a ha b hb
      obtain ⟨_, rfl⟩ := ha
      subst b
      linarith
  · have he : ([((m-1 : ℕ) : ℝ)] ++ ((m+1 : ℝ)::List.replicate l (m : ℝ))).Perm
        (((m+1 : ℝ)::List.replicate l (m : ℝ)) ++ [((m-1 : ℕ) : ℝ)]) :=
      List.perm_append_comm
    exact (List.mergeSort_perm _ _).trans he

private lemma family_majorization (m l : ℕ) (hm : 2 ≤ m) :
    StrictlyMajorized ((Function.const (Fin (l+2)) m)) (beta m l) := by
  have hm1 : 1 ≤ m := by exact Nat.one_le_of_lt hm
  have hcast : ((m-1 : ℕ) : ℝ) = (m : ℝ)-1 := by
    exact Nat.cast_pred hm1
  unfold StrictlyMajorized moreMixed
  rw [desc_alpha, desc_beta m l hm1]
  constructor
  · constructor
    · intro t ht
      unfold prefixSum
      cases t
      · simp
      · rename_i t
        have ht' : t ≤ l := by omega
        simp only [List.take_replicate, List.sum_replicate, nsmul_eq_mul,
          min_eq_left (Nat.le_of_lt ht), List.take_succ_cons, List.sum_cons,
          List.take_append, List.length_replicate, List.take_replicate,
          min_eq_left ht', Nat.sub_eq_zero_of_le ht', List.take_zero,
          List.append_nil]
        push_cast
        linarith
    · unfold prefixSum
      simp only [List.take_replicate, min_self, List.sum_replicate, nsmul_eq_mul,
        List.take_succ_cons, List.take_append, List.length_replicate, List.take_replicate,
        Nat.min_eq_right (show l ≤ l+1 by omega), Nat.add_sub_cancel_left,
        List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_append,
        List.sum_replicate, List.sum_nil, hcast]
      push_cast
      ring
  · intro h
    have hh := congrArg (fun xs : List ℝ => xs.headD 0) h
    have hh' : (m : ℝ) = (m+1 : ℝ) := by simpa [List.replicate_succ] using hh
    linarith

private lemma orders_positive (m l : ℕ) (hm : 2 ≤ m) :
    (∀ i, 0 < (Function.const (Fin (l+2)) m) i) ∧ (∀ i, 0 < beta m l i) := by
  constructor
  · intro i; dsimp [Function.const]; omega
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [beta]; omega
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [beta] <;> omega


private lemma polygamma_ne_zero (p r : ℕ) (k x : ℝ) (hk : 0 < k) (hx : 0 < x) (hr : 0 < r) :
    polygamma p k r x ≠ 0 := by
  rw [polygamma_eq p r k x hk hx hr]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero r)) (ne_of_gt (S_pos p (r+1) k x hk hx))

private lemma polygamma_ratio (p m : ℕ) (k x : ℝ) (hm : 2 ≤ m) (hk : 0 < k) (hx : 0 < x) :
    polygamma p k m x ^ 2 /
      (polygamma p k (m-1) x * polygamma p k (m+1) x) = ratio p k m x := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t+2 := ⟨m-2, by omega⟩
  have ha := ne_of_gt (S_pos p (t+2) k x hk hx)
  have hc := ne_of_gt (S_pos p (t+4) k x hk hx)
  have hf : (t.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have ht : (t : ℝ)+1 ≠ 0 := by exact Nat.cast_add_one_ne_zero t
  have ht2 : (t : ℝ)+2 ≠ 0 := by positivity
  have ht3 : (t : ℝ)+3 ≠ 0 := by positivity
  rw [polygamma_eq p (t+2) k x hk hx (by omega),
    polygamma_eq p (t+2-1) k x hk hx (by omega),
    polygamma_eq p (t+2+1) k x hk hx (by omega)]
  simp only [show t+2-1=t+1 by omega, show t+2+1=t+3 by omega,
    show t+3+1=t+4 by omega, show t+1+1=t+2 by omega]
  unfold ratio
  generalize (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ (t+2)) = a at *
  generalize (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ (t+3)) = b at *
  generalize (∑ j ∈ Finset.range (p + 1), (1 / ((j : ℝ) * k + x)) ^ (t+4)) = c at *
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, pow_succ]
  field_simp [ha, hc, hf, ht, ht2, ht3]
  <;> ring

private lemma Q_family (p m l : ℕ) (k x : ℝ) (hm : 2 ≤ m) (hk : 0 < k) (hx : 0 < x) :
    Q p k ((Function.const (Fin (l+2)) m)) (beta m l) x = ratio p k m x := by
  have hn := polygamma_ne_zero p m k x hk hx (by omega)
  have hlow := polygamma_ne_zero p (m-1) k x hk hx (by omega)
  have hhigh := polygamma_ne_zero p (m+1) k x hk hx (by omega)
  rw [← polygamma_ratio p m k x hm hk hx]
  have hb : (fun i => polygamma p k (beta m l i) x) =
      Fin.cons (polygamma p k (m-1) x)
        (Fin.cons (polygamma p k (m+1) x) (fun _ : Fin l => polygamma p k m x)) := by
    change ((fun r : ℕ => polygamma p k r x) ∘
      Fin.cons (m-1) (Fin.cons (m+1) (fun _ : Fin l => m))) = _
    rw [Fin.comp_cons, Fin.comp_cons]
    rfl
  unfold Q
  rw [hb, Fin.prod_cons, Fin.prod_cons]
  simp only [Function.const, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_add]
  field_simp [hn, hlow, hhigh]

private lemma family_failure (p m l : ℕ) (k : ℝ) (hp : 0 < p) (hm : 2 ≤ m) (hk : 0 < k) :
    StrictlyMajorized ((Function.const (Fin (l+2)) m)) (beta m l) ∧
    ¬ AntitoneOn (Q p k ((Function.const (Fin (l+2)) m)) (beta m l)) (Set.Ioi 0) ∧
    ¬ MonotoneOn (Q p k ((Function.const (Fin (l+2)) m)) (beta m l)) (Set.Ioi 0) := by
  refine ⟨family_majorization m l hm, ?_, ?_⟩
  · intro ha
    apply (ratio_neither_monotone p m k hp (by omega) hk).1
    intro x hx y hy hxy
    rw [← Q_family p m l k x hm hk hx, ← Q_family p m l k y hm hk hy]
    exact ha hx hy hxy
  · intro ha
    apply (ratio_neither_monotone p m k hp (by omega) hk).2
    intro x hx y hy hxy
    rw [← Q_family p m l k x hm hk hx, ← Q_family p m l k y hm hk hy]
    exact ha hx hy hxy

theorem result : ¬ claim := by
  intro h
  have hp := orders_positive 2 1 (by omega)
  have hf := family_failure 1 2 1 1 (by omega) (by omega) (by norm_num)
  exact hf.2.1 ((h 1 (by omega) 1 (by norm_num) 3 (by omega)
    ((Function.const (Fin (1+2)) 2)) (beta 2 1) hp.1 hp.2 hf.1).1)

end
end D5.S3.Analytic.SeriesInequalities.YinPolygammaMajorizationRefutation

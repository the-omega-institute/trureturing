/- GID: D5/S3/Analytic/SparseEndpointTailModulus
   generality: G
   mirror-B: D5/B/S3/Analytic/SparseEndpointTailModulus
   mirror-E: none(waiver:unbounded-symbolic-endpoint-estimate)
   anchors: []
   digest: A selective sign annihilator bounds any visible exterior atom under sparse positive moments and an unmodelled positive tail. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

/-!
# Sparse endpoint resolution with model error

The moment observations are the repository's actual finite Prony sums.
A comparison spectrum may have arbitrarily many modes. Only the first
spectrum's retained part has a prescribed modal count; its remaining positive
mass is charged explicitly. No separation or distinct-node assumption occurs.

The proof constructs (t-b) times the squared factors of exactly those retained
nodes at or below b. It annihilates the adverse retained contributions without
annihilating near-colliding modes above b. A factor-by-factor induction pays
for raw-moment errors; the positive tail has a separate unit-norm charge.

Sparse moment stability is established background (Fan--Li, COLT 2023,
PMLR 195:3510-3565; Wu--Yang, Annals of Statistics 48(4), 2020).
The claim here is a one-sided, tail-aware endpoint estimate, not a new claim
to the classical sparse-moment exponent or to a physical mass-gap solution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.SparseEndpointTailModulus

open scoped BigOperators
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

/-- Propagate a finite raw-moment budget through a genuine product of linear
factors. This is an inductive estimate, not a supplied coefficient budget. -/
private theorem factor_budget
    (roots : List ℝ) (L : (ℝ → ℝ) →ₗ[ℝ] ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hr : ∀ a ∈ roots, |a| ≤ 1)
    (hm : ∀ k : ℕ, k ≤ roots.length → |L (fun t => t ^ k)| ≤ ε) :
    |L (fun t => (roots.map (fun a => t - a)).prod)| ≤
      (2 : ℝ) ^ roots.length * ε := by
  induction roots generalizing L ε with
  | nil =>
      simpa using hm 0 (by simp)
  | cons a roots ih =>
      let T : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
        { toFun := fun f t => (t - a) * f t
          map_add' := by intro f g; ext t; simp only [Pi.add_apply]; ring
          map_smul' := by intro c f; ext t; simp only [Pi.smul_apply, smul_eq_mul]; ring }
      let L' : (ℝ → ℝ) →ₗ[ℝ] ℝ := L.comp T
      have ha : |a| ≤ 1 := hr a (by simp)
      have hnext (k : ℕ) (hk : k ≤ roots.length) :
          |L' (fun t => t ^ k)| ≤ 2 * ε := by
        have heq : L' (fun t => t ^ k) =
            L (fun t => t ^ (k + 1)) - a * L (fun t => t ^ k) := by
          change L (fun t => (t - a) * t ^ k) = _
          have hf : (fun t : ℝ => (t - a) * t ^ k) =
              (fun t : ℝ => t ^ (k + 1)) - a • (fun t : ℝ => t ^ k) := by
            ext t
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
            ring
          simp only [hf, map_sub, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [heq]
        calc
          |L (fun t => t ^ (k + 1)) - a * L (fun t => t ^ k)| ≤
              |L (fun t => t ^ (k + 1))| + |a * L (fun t => t ^ k)| := abs_sub _ _
          _ ≤ ε + |a| * ε := by
            rw [abs_mul]
            exact add_le_add (hm (k + 1) (by simpa using Nat.succ_le_succ hk))
              (mul_le_mul_of_nonneg_left (hm k (by simp; omega)) (abs_nonneg a))
          _ ≤ 2 * ε := by nlinarith [mul_le_mul_of_nonneg_right ha hε]
      have h := ih L' (2 * ε) (by positivity)
        (fun z hz => hr z (by simp [hz])) hnext
      change |L (fun t => (t - a) * (roots.map (fun z => t - z)).prod)| ≤ _ at h
      simpa only [List.map_cons, List.prod_cons, List.length_cons, pow_succ,
        mul_assoc, mul_comm, mul_left_comm] using h

/-- A retained atom of weight at least eta cannot sit far above a competing
spectrum while the first 2*n raw moments agree. The retained part has n modes;
the positive residual tail and the competitor may have arbitrary finite size.
The endpoint penalty is separation-free and charges the tail mass explicitly.
No normalization, positive minimum spacing, or nonzero-weight promise is hidden.
For probability models those are special cases of these stated hypotheses. -/
theorem sparse_endpoint_tail_modulus
    {n m l : ℕ} (x u : Fin n → ℝ) (z a : Fin m → ℝ) (y v : Fin l → ℝ)
    (i₀ : Fin n) (b η ε τ : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hz : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (hy : ∀ j, y j ≤ b)
    (hu : ∀ i, 0 ≤ u i) (ha : ∀ j, 0 ≤ a j) (hv : ∀ j, 0 ≤ v j)
    (hb : 0 ≤ b) (hη : 0 < η) (hi : η ≤ u i₀) (hgap : b < x i₀)
    (hε : 0 ≤ ε) (htail : (∑ j, a j) ≤ τ)
    (hnoise : ∀ k : ℕ, k ≤ 2 * n - 1 →
      |pronyMoment x u k + pronyMoment z a k - pronyMoment y v k| ≤ ε) :
    η * (x i₀ - b) ^ (2 * n - 1) ≤ (2 : ℝ) ^ (2 * n - 1) * ε + τ := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i ≤ b)
  let nodes : List ℝ := s.toList.map x
  let roots : List ℝ := b :: nodes.flatMap (fun r => [r, r])
  let Q : ℝ → ℝ := fun t => (roots.map (fun r => t - r)).prod
  let δ : ℝ := x i₀ - b
  have hδ : 0 < δ := sub_pos.mpr hgap
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith [(hx i₀).2]
  have hb1 : b ≤ 1 := le_trans hgap.le (hx i₀).2
  have hnodes : ∀ r ∈ nodes, 0 ≤ r ∧ r ≤ b := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i, his, rfl⟩
    have hiS : i ∈ s := by simpa using his
    exact ⟨(hx i).1, (Finset.mem_filter.mp hiS).2⟩
  have hroots : ∀ r ∈ roots, 0 ≤ r ∧ r ≤ b := by
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact ⟨hb, le_rfl⟩
    · rcases List.mem_flatMap.mp hr with ⟨c, hc, hr⟩
      have heq : r = c := by simpa using hr
      subst r
      exact hnodes c hc
  have hpair (rs : List ℝ) (t : ℝ) :
      (((rs.flatMap (fun r => [r, r])).map (fun r => t - r)).prod) =
        (rs.map (fun r => (t - r) ^ 2)).prod := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
        simp only [List.flatMap_cons, List.map_append, List.prod_append,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        rw [ih]
        ring
  have hQ (t : ℝ) : Q t = (t - b) * (nodes.map (fun r => (t - r) ^ 2)).prod := by
    change (t - b) * _ = _
    rw [hpair]
  have hsq (rs : List ℝ) (t : ℝ) : 0 ≤ (rs.map (fun r => (t - r) ^ 2)).prod := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
        simpa only [List.map_cons, List.prod_cons] using mul_nonneg (sq_nonneg _) ih
  have hzero (i : Fin n) (hiS : i ∈ s) : Q (x i) = 0 := by
    have hmem : x i ∈ nodes := List.mem_map.mpr ⟨i, by simpa using hiS, rfl⟩
    have hp : (nodes.map (fun r => (x i - r) ^ 2)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨x i, hmem, by simp⟩)
    rw [hQ, hp, mul_zero]
  have hpositive (i : Fin n) : 0 ≤ Q (x i) := by
    by_cases hiS : i ∈ s
    · simpa only [hzero i hiS] using (le_refl (0 : ℝ))
    · have hxb : b < x i := by
        have : ¬ x i ≤ b := by simpa [s] using hiS
        exact lt_of_not_ge this
      rw [hQ]
      exact mul_nonneg (sub_nonneg.mpr hxb.le) (hsq nodes (x i))
  have hnegative (j : Fin l) : Q (y j) ≤ 0 := by
    rw [hQ]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hy j)) (hsq nodes (y j))
  have hnorm : ∀ (rs : List ℝ), (∀ r ∈ rs, 0 ≤ r ∧ r ≤ 1) →
      ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → |(rs.map (fun r => t - r)).prod| ≤ 1 := by
    intro rs
    induction rs with
    | nil => intro hr t ht0 ht1; simp
    | cons r rs ih =>
        intro hr t ht0 ht1
        have hr0 := (hr r (by simp)).1
        have hr1 := (hr r (by simp)).2
        have hfactor : |t - r| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hrest := ih (fun c hc => hr c (by simp [hc])) t ht0 ht1
        simp only [List.map_cons, List.prod_cons, abs_mul]
        exact (mul_le_mul hfactor hrest (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have htailnorm (j : Fin m) : -1 ≤ Q (z j) := by
    have h := hnorm roots (fun r hr => ⟨(hroots r hr).1, (hroots r hr).2.trans hb1⟩)
      (z j) (hz j).1 (hz j).2
    exact (abs_le.mp h).1
  have hground : ∀ (rs : List ℝ), (∀ r ∈ rs, r ≤ b) →
      δ ^ rs.length ≤ (rs.map (fun r => x i₀ - r)).prod := by
    intro rs
    induction rs with
    | nil => intro hr; simp
    | cons r rs ih =>
        intro hr
        have hrest := ih (fun c hc => hr c (by simp [hc]))
        have hf : δ ≤ x i₀ - r := sub_le_sub_left (hr r (by simp)) _
        have hprod0 := (pow_nonneg hδ.le rs.length).trans hrest
        simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
        calc
          δ ^ rs.length * δ ≤ (rs.map (fun c => x i₀ - c)).prod * (x i₀ - r) :=
            mul_le_mul hrest hf hδ.le hprod0
          _ = (x i₀ - r) * (rs.map (fun c => x i₀ - c)).prod := mul_comm _ _
  have hgroundQ : δ ^ roots.length ≤ Q (x i₀) :=
    hground roots (fun r hr => (hroots r hr).2)
  have hmu : η * δ ^ roots.length ≤ ∑ i, u i * Q (x i) := by
    calc
      η * δ ^ roots.length ≤ u i₀ * Q (x i₀) :=
        mul_le_mul hi hgroundQ (pow_nonneg hδ.le _) (hu i₀)
      _ ≤ ∑ i, u i * Q (x i) :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hu i) (hpositive i)) (Finset.mem_univ i₀)
  have hnu : (∑ j, v j * Q (y j)) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hv j) (hnegative j)
  have htailQ : -τ ≤ ∑ j, a j * Q (z j) := by
    calc
      -τ ≤ -(∑ j, a j) := neg_le_neg htail
      _ = ∑ j, a j * (-1) := by simp
      _ ≤ ∑ j, a j * Q (z j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (htailnorm j) (ha j)
  have hpairlen (rs : List ℝ) : (rs.flatMap (fun r => [r, r])).length = 2 * rs.length := by
    induction rs with
    | nil => simp
    | cons r rs ih => simp [ih]; omega
  have hcard : s.card ≤ n - 1 := by
    have hsub : s ⊆ Finset.univ.erase i₀ := by
      intro i hiS
      have hle := (Finset.mem_filter.mp hiS).2
      have hne : i ≠ i₀ := by intro heq; subst i; exact (not_le.mpr hgap) hle
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩
    simpa using Finset.card_le_card hsub
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt
  have hlen : roots.length = 2 * s.card + 1 := by
    simp [roots, hpairlen, nodes, Nat.add_comm]
  have hdegree : roots.length ≤ 2 * n - 1 := by omega
  let L : (ℝ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => (∑ i, u i * f (x i)) + (∑ j, a j * f (z j)) - ∑ j, v j * f (y j)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm _ c, ← Finset.mul_sum]
        ring }
  have herror : |L Q| ≤ (2 : ℝ) ^ roots.length * ε :=
    factor_budget roots L ε hε
      (fun r hr => by rw [abs_of_nonneg (hroots r hr).1]; exact (hroots r hr).2.trans hb1)
      (fun k hk => by simpa [L, pronyMoment] using hnoise k (hk.trans hdegree))
  have hraw : η * δ ^ roots.length ≤ (2 : ℝ) ^ roots.length * ε + τ := by
    have hLupper := (le_abs_self (L Q)).trans herror
    change (∑ i, u i * Q (x i)) + (∑ j, a j * Q (z j)) -
      (∑ j, v j * Q (y j)) ≤ _ at hLupper
    linarith
  have hpower : δ ^ (2 * n - 1) ≤ δ ^ roots.length := by
    have heq : 2 * n - 1 = roots.length + (2 * n - 1 - roots.length) := by omega
    rw [heq, pow_add]
    have hrem : δ ^ (2 * n - 1 - roots.length) ≤ 1 := pow_le_one₀ hδ.le hδ1
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hrem (pow_nonneg hδ.le _)
  have htwo : (2 : ℝ) ^ roots.length ≤ (2 : ℝ) ^ (2 * n - 1) :=
    pow_le_pow_right₀ (by norm_num) hdegree
  calc
    η * (x i₀ - b) ^ (2 * n - 1) ≤ η * δ ^ roots.length :=
      mul_le_mul_of_nonneg_left hpower hη.le
    _ ≤ (2 : ℝ) ^ roots.length * ε + τ := hraw
    _ ≤ (2 : ℝ) ^ (2 * n - 1) * ε + τ :=
      add_le_add_right (mul_le_mul_of_nonneg_right htwo hε) τ

#print axioms sparse_endpoint_tail_modulus

end D5.S3.Analytic.SparseEndpointTailModulus

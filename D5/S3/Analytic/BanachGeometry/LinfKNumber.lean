/- GID: D5/S3/Analytic/BanachGeometry/LinfKNumber
   generality: G
   mirror-B: D5/B/S3/Analytic/BanachGeometry/LinfKNumber
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Minimal K-sets among the vertices of the real sup-norm ball are bases; the K-number is the dimension. -/

/- Source: Sain–Manna–Paul, arXiv:2407.08900, end of §2.
   admission_basis: open-problem-resolution (#15605; Proved)
   Direct frozen dependencies: none (pinned Mathlib only).
   escape_witness: active_not_BJ, image_vertex, inverse_sign, spanning_KSet.
   Reuse: extremePoints_pi, Set.extremePoints_Icc, closedBall_pi,
     pi_norm_lt_iff, pi_norm_le_iff_of_nonneg, norm_le_pi_norm,
     LinearEquiv.ofInjectiveEndo, LinearMap.injective_iff_surjective,
     Submodule.exists_le_ker_of_lt_top, finrank_span_le_card,
     Module.finrank_fin_fun, pi_eq_sum_univ'.
   Definitions:
     BJOrth: proof_shape definition; consumers=PreservesBJAt, vertex_zero_BJ,
       not_BJ_self, active_not_BJ, image_vertex, inverse_sign
     PreservesBJAt: proof_shape definition; consumers=IsKSet,
       preserving_injective, image_vertex, inverse_sign, column_sparse,
       spanning_KSet, KSet_spans
     IsScalarMulIsometry: proof_shape definition; consumers=IsKSet,
       spanning_KSet, KSet_spans
     IsKSet: proof_shape definition; consumers=claim, spanning_KSet,
       KSet_spans, KSet_card, result
     claim: proof_shape definition; consumer=result
   Per-declaration proof_shape and live consumers:
     extreme_iff: bind-only; consumer=result
     vertex_norm: bind-only; consumers=vertex_zero_BJ, spanning_KSet
     vertex_zero_BJ: bind-only; consumers=preserving_injective, image_vertex,
       inverse_sign
     not_BJ_self: bind-only; consumer=preserving_injective
     active_not_BJ: content; consumers=image_vertex, inverse_sign,
       PolyhedralBJRefutation.product_of_bj
     preserving_injective: content; consumer=spanning_KSet
     image_vertex: content; consumers=column_sparse, spanning_KSet
     inverse_sign: content; consumer=column_sparse
     column_sparse: content; consumer=spanning_KSet
     inverse_monomial: content; consumer=spanning_KSet
     spanning_KSet: content; consumer=result
     KSet_spans: content; consumers=KSet_card, result
     KSet_card: content; consumer=result
     vertex_basis: content; consumer=result
     result: content; designated external open-problem resolution
   The inverse of a nonzero preserving operator has disjoint column supports.
   Its action on one vertex fixes the common modulus of its nonzero entries.
   A rank-one operator annihilating a proper span gives the necessary direction. -/

import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

noncomputable section
open scoped BigOperators
namespace D5.S3.Analytic.BanachGeometry.LinfKNumber

/-- Birkhoff–James orthogonality `x ⊥_B y`. -/
def BJOrth {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) : Prop :=
  ∀ t : ℝ, ‖x‖ ≤ ‖x + t • y‖

/-- `T` preserves Birkhoff–James orthogonality at `x`. -/
def PreservesBJAt {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ₗ[ℝ] E) (x : E) : Prop :=
  ∀ y : E, BJOrth x y → BJOrth (T x) (T y)

/-- `T` is a scalar multiple of an isometry. -/
def IsScalarMulIsometry {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ₗ[ℝ] E) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ y : E, ‖T y‖ = c * ‖y‖

/-- Koldobsky set (K-set). -/
def IsKSet {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (A : Set E) : Prop :=
  A ⊆ Metric.sphere (0 : E) 1 ∧
    ∀ T : E →ₗ[ℝ] E, (∀ x ∈ A, PreservesBJAt T x) → IsScalarMulIsometry T

def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ A : Set (Fin n → ℝ), A ⊆ (Metric.closedBall (0 : Fin n → ℝ) 1).extremePoints ℝ →
        (IsKSet A ↔ Submodule.span ℝ A = ⊤)) ∧
    (∃ A : Finset (Fin n → ℝ), A.card = n ∧ IsKSet (A : Set (Fin n → ℝ))) ∧
    (∀ A : Finset (Fin n → ℝ), IsKSet (A : Set (Fin n → ℝ)) → n ≤ A.card)

variable {n : ℕ}

private lemma extreme_iff (u : Fin n → ℝ) :
    u ∈ (Metric.closedBall (0 : Fin n → ℝ) 1).extremePoints ℝ ↔
      ∀ i, |u i| = 1 := by
  rw [closedBall_pi _ zero_le_one, extremePoints_pi]
  simp only [Set.mem_univ_pi, Pi.zero_apply, Real.closedBall_eq_Icc,
    sub_eq_add_neg, zero_add, Set.extremePoints_Icc (by norm_num : (-1 : ℝ) ≤ 1),
    Set.mem_insert_iff, Set.mem_singleton_iff]
  exact forall_congr' fun i => by
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    tauto

private lemma vertex_norm [Nonempty (Fin n)] {u : Fin n → ℝ}
    (hu : ∀ i, |u i| = 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp [Real.norm_eq_abs, hu i]
  · simpa [Real.norm_eq_abs, hu (Classical.arbitrary (Fin n))] using
      norm_le_pi_norm u (Classical.arbitrary (Fin n))

private lemma vertex_zero_BJ [Nonempty (Fin n)] {u y : Fin n → ℝ}
    (hu : ∀ i, |u i| = 1) (i : Fin n) (hy : y i = 0) : BJOrth u y := by
  intro t
  rw [vertex_norm hu]
  simpa [Real.norm_eq_abs, hy, hu i] using norm_le_pi_norm (u + t • y) i

private lemma not_BJ_self {w : Fin n → ℝ} (hw : w ≠ 0) : ¬ BJOrth w w := by
  intro h
  have := h (-1)
  simp only [neg_one_smul, add_neg_cancel, norm_zero] at this
  exact hw (norm_eq_zero.mp (le_antisymm this (norm_nonneg w)))

/-- Strictly positive slopes at every active coordinate rule out Birkhoff–James orthogonality. -/
lemma active_not_BJ {w z : Fin n → ℝ} (hw : w ≠ 0)
    (hz : ∀ i, |w i| = ‖w‖ → 0 < z i * w i) :
    ¬ ∀ t : ℝ, ‖w‖ ≤ ‖w + t • z‖ := by
  classical
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have local_bound (i : Fin n) : ∃ e : ℝ, 0 < e ∧
      ∀ d : ℝ, 0 < d → d < e → |w i - d * z i| < ‖w‖ := by
    by_cases hi : |w i| = ‖w‖
    · have hp := hz i hi
      have hw0 : w i ≠ 0 := by intro h; simp [h] at hp
      have hz0 : z i ≠ 0 := by intro h; simp [h] at hp
      refine ⟨|w i| / |z i|, div_pos (abs_pos.mpr hw0) (abs_pos.mpr hz0), ?_⟩
      intro d hd hde
      have hb : d * |z i| < |w i| := (lt_div_iff₀ (abs_pos.mpr hz0)).mp hde
      rcases lt_or_gt_of_ne hw0 with hneg | hpos
      · have hzneg : z i < 0 := by nlinarith
        rw [abs_of_neg hneg, abs_of_neg hzneg] at hb
        rw [abs_of_neg (by nlinarith : w i - d * z i < 0), ← hi, abs_of_neg hneg]
        nlinarith
      · have hzpos : 0 < z i := by nlinarith
        rw [abs_of_pos hpos, abs_of_pos hzpos] at hb
        rw [abs_of_pos (by nlinarith : 0 < w i - d * z i), ← hi, abs_of_pos hpos]
        nlinarith
    · have hg : 0 < ‖w‖ - |w i| := by
        have hle : |w i| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm w i
        exact sub_pos.mpr (lt_of_le_of_ne hle hi)
      refine ⟨(‖w‖ - |w i|) / (|z i| + 1), div_pos hg (by positivity), ?_⟩
      intro d hd hde
      have hb := (lt_div_iff₀ (by positivity : 0 < |z i| + 1)).mp hde
      calc
        |w i - d * z i| ≤ |w i| + |d * z i| := abs_sub _ _
        _ = |w i| + d * |z i| := by rw [abs_mul, abs_of_pos hd]
        _ < ‖w‖ := by nlinarith
  have hn : Nonempty (Fin n) := by
    by_contra h
    have : w = 0 := by ext i; exact (h ⟨i⟩).elim
    exact hw this
  have : Nonempty (Fin n) := hn
  choose e he hb using local_bound
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  have hd : 0 < e j / 2 := by linarith [he j]
  have hnorm : ‖w + (- (e j / 2)) • z‖ < ‖w‖ := by
    apply (pi_norm_lt_iff hr).mpr
    intro i
    simpa [Real.norm_eq_abs, sub_eq_add_neg] using hb i (e j / 2) hd
      (lt_of_lt_of_le (by linarith [he j]) (hj i (Finset.mem_univ i)))
  intro h
  exact (not_lt_of_ge (h (- (e j / 2)))) hnorm

private lemma preserving_injective [Nonempty (Fin n)]
    {T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} {u : Fin n → ℝ}
    (hu : ∀ i, |u i| = 1) (hp : PreservesBJAt T u) (htu : T u ≠ 0) :
    Function.Injective T := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro z hz
  have htz : T z = 0 := hz
  by_contra hn
  have hz0 : z ≠ 0 := by simpa using hn
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; exact hz0 (by ext i; simpa using not_exists.mp h i)
  let s := -u i / z i
  have hy : (u + s • z) i = 0 := by dsimp [s]; field_simp; ring
  have h := hp _ (vertex_zero_BJ hu i hy)
  rw [map_add, map_smul, htz, smul_zero, add_zero] at h
  exact not_BJ_self htu h

private lemma image_vertex [Nonempty (Fin n)]
    (E : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) {u : Fin n → ℝ}
    (hu : ∀ i, |u i| = 1) (hp : PreservesBJAt E.toLinearMap u) :
    ∀ k, |E u k| = ‖E u‖ := by
  classical
  have hu0 : u ≠ 0 := by
    intro h; have := hu (Classical.arbitrary (Fin n)); simp [h] at this
  have hw0 : E u ≠ 0 := by simpa using E.injective.ne hu0
  intro k
  by_contra hk
  have he0 : E.symm (Pi.single k 1) ≠ 0 := by
    intro h
    have hzero : Pi.single k (1 : ℝ) = 0 := E.symm.injective (by simpa using h)
    have := congrFun hzero k
    simpa using this
  obtain ⟨i, hi⟩ : ∃ i, E.symm (Pi.single k 1) i ≠ 0 := by
    by_contra h; exact he0 (by ext i; simpa using not_exists.mp h i)
  let s := -u i / E.symm (Pi.single k 1) i
  let z := E u + s • Pi.single k 1
  have hz : ¬ BJOrth (E u) z := by
    apply active_not_BJ hw0
    intro j hj
    have hjk : j ≠ k := by intro h; subst j; exact hk hj
    have hj0 : E u j ≠ 0 := by
      intro h; rw [h, abs_zero] at hj; exact hw0 (norm_eq_zero.mp hj.symm)
    simpa [z, Pi.single_eq_of_ne hjk] using mul_self_pos.mpr hj0
  have hy : E.symm z i = 0 := by
    simp only [z, map_add, map_smul, E.symm_apply_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    dsimp [s]
    field_simp
    ring
  have h := hp _ (vertex_zero_BJ hu i hy)
  exact hz (by simpa using h)

private lemma inverse_sign [Nonempty (Fin n)]
    (E : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) {u : Fin n → ℝ}
    (hu : ∀ i, |u i| = 1) (hp : PreservesBJAt E.toLinearMap u)
    (hw : ∀ j, |E u j| = ‖E u‖) :
    ∀ i j, 0 ≤ u i * E.symm (Pi.single j 1) i * E u j := by
  classical
  have hu0 : u ≠ 0 := by
    intro h; have := hu (Classical.arbitrary (Fin n)); simp [h] at this
  have hw0 : E u ≠ 0 := by simpa using E.injective.ne hu0
  have hwj (j) : E u j ≠ 0 := by
    intro h; have := hw j; rw [h, abs_zero] at this
    exact hw0 (norm_eq_zero.mp this.symm)
  have hui (i) : u i * u i = 1 := by
    nlinarith [sq_abs (u i), hu i]
  intro i j
  by_contra h
  have ha : u i * E.symm (Pi.single j 1) i * E u j < 0 := lt_of_not_ge h
  let t := -1 / (u i * E.symm (Pi.single j 1) i * E u j)
  have ht : 0 < t := div_pos_of_neg_of_neg (by norm_num) ha
  let z := E u + t • (E u j • Pi.single j 1)
  have hz : ¬ BJOrth (E u) z := by
    apply active_not_BJ hw0
    intro k _
    by_cases hkj : k = j
    · subst k
      simp only [z, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      nlinarith [mul_self_pos.mpr (hwj j)]
    · simpa [z, Pi.single_eq_of_ne hkj] using mul_self_pos.mpr (hwj k)
  have heq : t * (u i * E.symm (Pi.single j 1) i * E u j) = -1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_lt ha)
  have hy : E.symm z i = 0 := by
    simp only [z, map_add, map_smul, E.symm_apply_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    have hi0 : u i ≠ 0 := by intro h; have := hu i; simp [h] at this
    apply (mul_eq_zero.mp (show u i *
        (u i + t * (E u j * E.symm (Pi.single j 1) i)) = 0 by
      nlinarith [hui i])).resolve_left hi0
  exact hz (by simpa using hp _ (vertex_zero_BJ hu i hy))

private lemma column_sparse [Nonempty (Fin n)]
    (E : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) {A : Set (Fin n → ℝ)}
    (hu : ∀ u ∈ A, ∀ i, |u i| = 1) (hp : ∀ u ∈ A, PreservesBJAt E.toLinearMap u)
    (hs : Submodule.span ℝ A = ⊤) (j i k : Fin n)
    (hi : E.symm (Pi.single j 1) i ≠ 0) (hk : E.symm (Pi.single j 1) k ≠ 0) : i = k := by
  classical
  by_contra hik
  let a := E.symm (Pi.single j 1) i
  let b := E.symm (Pi.single j 1) k
  let q : ℝ := if 0 < a * b then 1 else -1
  have hrel : ∀ u ∈ A, u i = q * u k := by
    intro u hau
    have huv := hu u hau
    have hw := image_vertex E huv (hp u hau)
    have hsgn := inverse_sign E huv (hp u hau) hw
    have hu0 (l) : u l ≠ 0 := by intro h; simpa [h] using huv l
    have hw0 : E u j ≠ 0 := by
      intro h
      have hr := hw j
      rw [h, abs_zero] at hr
      have he : E u = 0 := norm_eq_zero.mp hr.symm
      have := congrFun (E.injective (by simpa using he)) i
      exact hu0 i (by simpa using this)
    have hai : 0 < u i * a * E u j :=
      lt_of_le_of_ne (hsgn i j) (Ne.symm (mul_ne_zero (mul_ne_zero (hu0 i) hi) hw0))
    have hbk : 0 < u k * b * E u j :=
      lt_of_le_of_ne (hsgn k j) (Ne.symm (mul_ne_zero (mul_ne_zero (hu0 k) hk) hw0))
    have hprod : 0 < ((u i * u k) * (a * b)) * (E u j * E u j) := by
      nlinarith [mul_pos hai hbk]
    have hpab : 0 < (u i * u k) * (a * b) :=
      pos_of_mul_pos_left hprod (mul_self_nonneg _)
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (huv i) with hui | hui <;>
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (huv k) with huk | huk <;>
      simp only [hui, huk] at hpab ⊢ <;>
      dsimp [q] <;> split_ifs <;> nlinarith
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i - q • LinearMap.proj k
  have hker : Submodule.span ℝ A ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    intro u hau
    change u i - q * u k = 0
    linarith [hrel u hau]
  have he : Pi.single i (1 : ℝ) ∈ Submodule.span ℝ A := by rw [hs]; trivial
  have hz := hker he
  change L (Pi.single i 1) = 0 at hz
  simpa [L, Pi.single_eq_of_ne (Ne.symm hik)] using hz

private lemma inverse_monomial [Nonempty (Fin n)]
    (E : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hsparse : ∀ j i k, E.symm (Pi.single j 1) i ≠ 0 →
      E.symm (Pi.single j 1) k ≠ 0 → i = k) :
    ∃ p : Equiv.Perm (Fin n), ∀ z j,
      E.symm z (p j) = z j * E.symm (Pi.single j 1) (p j) := by
  classical
  have hcol (j : Fin n) : ∃ i, E.symm (Pi.single j 1) i ≠ 0 := by
    by_contra h
    have he : E.symm (Pi.single j 1) = 0 := by ext i; simpa using not_exists.mp h i
    have he' : Pi.single j (1 : ℝ) = 0 := E.symm.injective (by simpa using he)
    have := congrFun he' j
    simpa using this
  choose p hp using hcol
  have hsingle (j) : E.symm (Pi.single j 1) = Pi.single (p j) (E.symm (Pi.single j 1) (p j)) := by
    ext i
    by_cases h : i = p j
    · subst i; simp
    · have hz : E.symm (Pi.single j 1) i = 0 := by
        by_contra hn; exact h (hsparse j i (p j) hn (hp j))
      simp [Pi.single_eq_of_ne h, hz]
  have hpinj : Function.Injective p := by
    intro j k hjk
    by_contra hne
    let a := E.symm (Pi.single j 1) (p j)
    let b := E.symm (Pi.single k 1) (p k)
    have hz : E.symm (b • Pi.single j 1 - a • Pi.single k 1) = 0 := by
      rw [map_sub, map_smul, map_smul, hsingle j, hsingle k, hjk]
      ext i
      by_cases h : i = p k <;> simp [a, b, h, hjk, Pi.single_eq_of_ne, mul_comm]
    have hz' : b • Pi.single j (1 : ℝ) - a • Pi.single k 1 = 0 :=
      E.symm.injective (by simpa using hz)
    have hb := congrFun hz' j
    have : b = 0 := by simpa [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne (Ne.symm hne)] using hb
    exact hp k this
  let P : Equiv.Perm (Fin n) := Equiv.ofBijective p
    ⟨hpinj, (Finite.injective_iff_surjective).mp hpinj⟩
  refine ⟨P, ?_⟩
  intro z j
  change E.symm z (p j) = z j * E.symm (Pi.single j 1) (p j)
  have hsum : E.symm z = ∑ k : Fin n, z k • E.symm (Pi.single k 1) := by
    conv_lhs => rw [pi_eq_sum_univ' z]
    rw [map_sum]
    simp only [map_smul]
  rw [hsum, Finset.sum_apply, Finset.sum_eq_single j]
  · rfl
  · intro k _ hkj
    have hpk : p j ≠ p k := fun h => hkj (hpinj h.symm)
    rw [hsingle k]
    simp [Pi.single_eq_of_ne hpk]
  · simp

private lemma spanning_KSet [Nonempty (Fin n)] {A : Set (Fin n → ℝ)}
    (hu : ∀ u ∈ A, ∀ i, |u i| = 1) (hs : Submodule.span ℝ A = ⊤) : IsKSet A := by
  classical
  refine ⟨?_, ?_⟩
  · intro u hau
    simpa [Metric.mem_sphere, dist_zero_right] using vertex_norm (hu u hau)
  · intro T hp
    by_cases hzero : ∀ u ∈ A, T u = 0
    · have hker : Submodule.span ℝ A ≤ LinearMap.ker T :=
        Submodule.span_le.mpr hzero
      have hT (y) : T y = 0 := hker (by rw [hs]; trivial)
      exact ⟨0, le_rfl, fun y => by simp [hT y]⟩
    · push Not at hzero
      obtain ⟨u, hau, htu⟩ := hzero
      have hinj := preserving_injective (hu u hau) (hp u hau) htu
      let E := LinearEquiv.ofInjectiveEndo T hinj
      have hep : ∀ v ∈ A, PreservesBJAt E.toLinearMap v := hp
      have hsp := column_sparse E hu hep hs
      obtain ⟨p, hmono⟩ := inverse_monomial E hsp
      let c := ‖E u‖
      have hc : 0 < c := norm_pos_iff.mpr htu
      have hw := image_vertex E (hu u hau) (hep u hau)
      have hscale (j) : c * |E.symm (Pi.single j 1) (p j)| = 1 := by
        have he := hmono (E u) j
        rw [E.symm_apply_apply] at he
        have ha := congrArg abs he
        rw [hu u hau (p j), abs_mul, hw j] at ha
        exact ha.symm
      have hcoord (z : Fin n → ℝ) (j) : |(c • E.symm z) (p j)| = |z j| := by
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, hmono z j]
        calc
          c * (|z j| * |E.symm (Pi.single j 1) (p j)|) =
              |z j| * (c * |E.symm (Pi.single j 1) (p j)|) := by ring
          _ = |z j| := by rw [hscale j, mul_one]
      have hnorm (z : Fin n → ℝ) : ‖c • E.symm z‖ = ‖z‖ := by
        apply le_antisymm
        · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
          intro i
          obtain ⟨j, rfl⟩ := p.surjective i
          rw [Real.norm_eq_abs, hcoord z j]
          exact norm_le_pi_norm z j
        · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (c • E.symm z))).mpr
          intro j
          rw [Real.norm_eq_abs, ← hcoord z j, ← Real.norm_eq_abs]
          exact norm_le_pi_norm (c • E.symm z) (p j)
      refine ⟨c, hc.le, fun y => ?_⟩
      change ‖E y‖ = c * ‖y‖
      have h := hnorm (E y)
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hc] using h.symm

private lemma KSet_spans (hn : 2 ≤ n) {A : Set (Fin n → ℝ)} (hA : IsKSet A) :
    Submodule.span ℝ A = ⊤ := by
  classical
  by_contra hs
  obtain ⟨f, hf, hker⟩ := (Submodule.span ℝ A).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hs)
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hji : j ≠ i := by simp [j, i, Fin.ext_iff]
  let T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun y => f y • Pi.single i 1
      map_add' := by intros; simp [map_add, add_smul]
      map_smul' := by intros; simp [map_smul, smul_smul] }
  have hpres : ∀ x ∈ A, PreservesBJAt T x := by
    intro x hx y _
    have hfx : f x = 0 := hker (Submodule.subset_span hx)
    intro t
    simp [T, hfx]
  obtain ⟨c, hc, hnorm⟩ := hA.2 T hpres
  have hc0 : c ≠ 0 := by
    intro he
    apply hf
    apply LinearMap.ext
    intro y
    have hTy : T y = 0 := norm_eq_zero.mp (by simpa [he] using hnorm y)
    have hfi := congrFun hTy i
    simpa [T] using hfi
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro y hy
    have hTy : T y = 0 := hy
    have hny : ‖y‖ = 0 := by
      have he := hnorm y
      rw [hTy, norm_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hc0
    exact norm_eq_zero.mp hny
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) (Pi.single j 1)
  have hz := congrFun hy j
  simpa [T, Pi.single_eq_of_ne hji] using hz

private lemma KSet_card (hn : 2 ≤ n) {A : Finset (Fin n → ℝ)}
    (hA : IsKSet (A : Set (Fin n → ℝ))) : n ≤ A.card := by
  have hs := KSet_spans hn hA
  have hb := finrank_span_le_card (R := ℝ) (A : Set (Fin n → ℝ))
  rw [hs] at hb
  simpa using hb

private lemma vertex_basis (hn : 2 ≤ n) :
    ∃ A : Finset (Fin n → ℝ), A.card = n ∧
      (∀ u ∈ (A : Set (Fin n → ℝ)), ∀ i, |u i| = 1) ∧ Submodule.span ℝ (A : Set (Fin n → ℝ)) = ⊤ := by
  classical
  let o : Fin n := ⟨0, by omega⟩
  let v : Fin n → (Fin n → ℝ) := fun k i => if k ≠ o ∧ i = k then -1 else 1
  have hv0 : v o = fun _ => 1 := by ext i; simp [v]
  have hinj : Function.Injective v := by
    intro j k he
    by_contra hne
    by_cases hk : k = o
    · have hj : j ≠ o := by intro h; exact hne (h.trans hk.symm)
      have := congrFun he j
      norm_num [v, hj, hk] at this
    · have := congrFun he k
      norm_num [v, hk, (Ne.symm hne)] at this
  let A := Finset.univ.image v
  have hv (k) : v k ∈ Submodule.span ℝ (A : Set (Fin n → ℝ)) :=
    Submodule.subset_span (by simp [A])
  have he (k : Fin n) (hk : k ≠ o) : Pi.single k (1 : ℝ) ∈ Submodule.span ℝ (A : Set (Fin n → ℝ)) := by
    have hid : Pi.single k (1 : ℝ) = (1 / 2 : ℝ) • (v o - v k) := by
      ext i
      by_cases hi : i = k <;> norm_num [v, hk, hi, Pi.single_eq_of_ne]
    rw [hid]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hv o) (hv k))
  have heo : Pi.single o (1 : ℝ) ∈ Submodule.span ℝ (A : Set (Fin n → ℝ)) := by
    have hid : Pi.single o (1 : ℝ) = v o - ∑ k ∈ Finset.univ.erase o, Pi.single k 1 := by
      have hid := pi_eq_sum_univ' (fun _ : Fin n => (1 : ℝ))
      simp only [one_smul] at hid
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o), ← hv0] at hid
      rw [hid]
      abel
    rw [hid]
    apply Submodule.sub_mem _ (hv o)
    exact Submodule.sum_mem _ fun k hk => he k (Finset.ne_of_mem_erase hk)
  refine ⟨A, ?_, ?_, ?_⟩
  · simpa [A] using Finset.card_image_of_injective Finset.univ hinj
  · intro u hu i
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    dsimp [v]
    split_ifs <;> norm_num
  · apply top_unique
    intro z _
    rw [pi_eq_sum_univ' z]
    apply Submodule.sum_mem
    intro k _
    apply Submodule.smul_mem
    by_cases hk : k = o
    · simpa [hk] using heo
    · exact he k hk

/-- The vertex K-set characterization and the K-number of real finite sup-norm spaces. -/
theorem result : claim := by
  intro n hn
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    exact ⟨KSet_spans hn, fun hs => spanning_KSet (fun u hu => (extreme_iff u).mp (hA hu)) hs⟩
  · obtain ⟨A, hc, hv, hs⟩ := vertex_basis hn
    exact ⟨A, hc, spanning_KSet hv hs⟩
  · intro A hA
    exact KSet_card hn hA

end D5.S3.Analytic.BanachGeometry.LinfKNumber

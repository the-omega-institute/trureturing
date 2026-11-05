/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Collision-free Cartesian vortex fields, positive-parameter similarity and polygon boundary. -/


import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! The collision-free Cartesian field, physical scaling and equilibrium boundary. -/


noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters

open AlternatingPolygonSpectrum

abbrev Configuration (N : ℕ) := Fin N ⊕ Fin N → ℝ

/-- The genuine domain of the Cartesian point-vortex equations. -/
def CollisionFree {N : ℕ} (z : Configuration N) : Prop :=
  ∀ j k : Fin N, j ≠ k →
    (z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2 ≠ 0

/-- Cartesian Eqs. (1)--(2), interpreted on `CollisionFree` configurations. -/
def field (N : ℕ) (b Ω : ℝ) (z : Configuration N) : Configuration N := fun p =>
  match p with
  | .inl j => -charge N j * Ω * z (.inr j) - (b / 2) *
      ∑ k : Fin N, if k = j then 0 else
        charge N k * (z (.inr j) - z (.inr k)) /
          ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)
  | .inr j => charge N j * Ω * z (.inl j) + (b / 2) *
      ∑ k : Fin N, if k = j then 0 else
        charge N k * (z (.inl j) - z (.inl k)) /
          ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)

/-- Partial derivatives of the actual field, at the specified configuration. -/
def jacobian (N : ℕ) (b Ω : ℝ) (z : Configuration N) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  fun p q => deriv (fun t : ℝ => field N b Ω (z + t • Pi.single q 1) p) 0

def radius (b Ω : ℝ) : ℝ := Real.sqrt (b / (4 * Ω))

theorem field_differentiable_at {N : ℕ} (b Ω : ℝ) {z : Configuration N}
    (hz : CollisionFree z) : DifferentiableAt ℝ (field N b Ω) z := by
  classical
  apply differentiableAt_pi.mpr
  intro p
  have hc (q : Fin N ⊕ Fin N) :
      DifferentiableAt ℝ (fun w : Configuration N => w q) z := differentiableAt_apply q z
  have hi (j : Fin N) (r : Fin N → Fin N ⊕ Fin N) :
      DifferentiableAt ℝ (fun z : Configuration N =>
        ∑ k : Fin N, if k = j then 0 else
          charge N k * (z (r j) - z (r k)) /
            ((z (.inl j) - z (.inl k)) ^ 2 +
              (z (.inr j) - z (.inr k)) ^ 2)) z := by
    apply DifferentiableAt.fun_sum
    intro k _
    by_cases hk : k = j
    · simp only [hk, ite_true]
      exact differentiableAt_const _
    · simp only [hk, ite_false]
      have hnum : DifferentiableAt ℝ (fun w : Configuration N =>
          charge N k * (w (r j) - w (r k))) z := by fun_prop
      have hden : DifferentiableAt ℝ (fun w : Configuration N =>
          (w (.inl j) - w (.inl k)) ^ 2 +
            (w (.inr j) - w (.inr k)) ^ 2) z := by fun_prop
      have hinv := (differentiableAt_inv (hz j k (Ne.symm hk))).comp z hden
      simpa only [Pi.mul_def, Function.comp_def, div_eq_mul_inv] using hnum.mul hinv
  cases p with
  | inl j =>
    exact ((hc (.inr j)).const_mul (-charge N j * Ω)).sub
      ((hi j Sum.inr).const_mul (b / 2))
  | inr j =>
    exact ((hc (.inl j)).const_mul (charge N j * Ω)).add
      ((hi j Sum.inl).const_mul (b / 2))

theorem collision_free_smul {N : ℕ} {z : Configuration N} {R : ℝ}
    (hR : R ≠ 0) : CollisionFree (R • z) ↔ CollisionFree z := by
  constructor
  · intro hz j k hjk hzero
    apply hz j k hjk
    change (R * z (.inl j) - R * z (.inl k)) ^ 2 +
      (R * z (.inr j) - R * z (.inr k)) ^ 2 = 0
    linear_combination R ^ 2 * hzero
  · intro hz j k hjk
    change (R * z (.inl j) - R * z (.inl k)) ^ 2 +
      (R * z (.inr j) - R * z (.inr k)) ^ 2 ≠ 0
    rw [show (R * z (.inl j) - R * z (.inl k)) ^ 2 +
        (R * z (.inr j) - R * z (.inr k)) ^ 2 =
        R ^ 2 * ((z (.inl j) - z (.inl k)) ^ 2 +
          (z (.inr j) - z (.inr k)) ^ 2) by ring]
    exact mul_ne_zero (pow_ne_zero _ hR) (hz j k hjk)

theorem radius_pos {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) : 0 < radius b Ω :=
  Real.sqrt_pos.mpr (div_pos hb (mul_pos (by norm_num) hΩ))

theorem radius_sq {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    (radius b Ω) ^ 2 = b / (4 * Ω) :=
  Real.sq_sqrt (le_of_lt (div_pos hb (mul_pos (by norm_num) hΩ)))

/-- Scaling is derived from the Cartesian field, on its genuine domain. -/
private theorem field_scaling_algebraic (N : ℕ) {b Ω R : ℝ} (hR : R ≠ 0)
    (hb : b = 4 * Ω * R ^ 2) (w : Configuration N) :
    field N b Ω (R • w) = (2 * Ω * R) • AlternatingPolygonSpectrum.field N w := by
  classical
  have hi (j : Fin N) (r : Fin N → Fin N ⊕ Fin N) :
      (∑ k : Fin N, if k = j then 0 else
        charge N k * ((R • w) (r j) - (R • w) (r k)) /
          (((R • w) (.inl j) - (R • w) (.inl k)) ^ 2 +
            ((R • w) (.inr j) - (R • w) (.inr k)) ^ 2)) =
      R⁻¹ * ∑ k : Fin N, if k = j then 0 else
        charge N k * (w (r j) - w (r k)) /
          ((w (.inl j) - w (.inl k)) ^ 2 +
            (w (.inr j) - w (.inr k)) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · simp [hk]
    · simp only [hk, ite_false, Pi.smul_apply, smul_eq_mul]
      rw [show (R * w (.inl j) - R * w (.inl k)) ^ 2 +
          (R * w (.inr j) - R * w (.inr k)) ^ 2 =
          R * (R * ((w (.inl j) - w (.inl k)) ^ 2 +
            (w (.inr j) - w (.inr k)) ^ 2)) by ring]
      rw [show charge N k * (R * w (r j) - R * w (r k)) =
          R * (charge N k * (w (r j) - w (r k))) by ring]
      rw [mul_div_mul_left _ _ hR, div_mul_eq_div_div]
      ring
  ext p
  cases p with
  | inl j =>
    change -charge N j * Ω * (R * w (.inr j)) - (b / 2) * _ = _
    rw [hi j Sum.inr, hb]
    simp only [Pi.smul_apply, smul_eq_mul, AlternatingPolygonSpectrum.field]
    field_simp [hR]
    <;> ring
  | inr j =>
    change charge N j * Ω * (R * w (.inl j)) + (b / 2) * _ = _
    rw [hi j Sum.inl, hb]
    simp only [Pi.smul_apply, smul_eq_mul, AlternatingPolygonSpectrum.field]
    field_simp [hR]
    <;> ring

/-- The normalized and parameterized definitions agree at `b = 2`, `Ω = 1/2`. -/
theorem normalized_field (N : ℕ) :
    field N 2 (1 / 2) = AlternatingPolygonSpectrum.field N := by
  funext z p
  cases p <;> simp [field, AlternatingPolygonSpectrum.field]

/-- Physical scaling is asserted on the collision-free domain. The algebraic
identity used to differentiate it does not assert a derivative at a collision. -/
theorem field_scaling (N : ℕ) {b Ω R : ℝ} (hR : R ≠ 0)
    (hb : b = 4 * Ω * R ^ 2) (w : Configuration N) (_hw : CollisionFree w) :
    field N b Ω (R • w) = (2 * Ω * R) • AlternatingPolygonSpectrum.field N w :=
  field_scaling_algebraic N hR hb w

/-- The canonical polygon belongs to the genuine domain of the field. -/
theorem polygon_collision_free (N : ℕ) : CollisionFree (polygon N) :=
  fun j k hjk => chord_sq_ne_zero N j k hjk

/-- Existence of the actual multivariable derivative at every normalized polygon. -/
theorem normalized_differentiable (N : ℕ) :
    DifferentiableAt ℝ (AlternatingPolygonSpectrum.field N) (polygon N) := by
  rw [← normalized_field]
  exact field_differentiable_at 2 (1 / 2) (polygon_collision_free N)

/-- The positive-parameter Jacobian scaling is differentiated from the field
identity at a collision-free polygon. It is not a presumed spectral scaling. -/
theorem jacobian_scaling (N : ℕ) {b Ω R : ℝ} (hR : R ≠ 0)
    (hb : b = 4 * Ω * R ^ 2) :
    jacobian N b Ω (R • polygon N) = (2 * Ω) • AlternatingPolygonSpectrum.jacobian N := by
  classical
  ext p q
  let v : Configuration N := Pi.single q 1
  let g : ℝ → ℝ := fun t => AlternatingPolygonSpectrum.field N (polygon N + t • v) p
  have hp : DifferentiableAt ℝ (fun t : ℝ => polygon N + t • v) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (polygon N)
    exact h.differentiableAt
  have houter : DifferentiableAt ℝ (AlternatingPolygonSpectrum.field N)
      (polygon N + (0 : ℝ) • v) := by simpa using normalized_differentiable N
  have hnorm := houter.comp (0 : ℝ) hp
  have heval : DifferentiableAt ℝ (fun w : Configuration N => w p)
      (AlternatingPolygonSpectrum.field N (polygon N + (0 : ℝ) • v)) :=
    differentiableAt_apply p _
  have hg : DifferentiableAt ℝ g 0 := by
    simpa only [g, Function.comp_def] using heval.comp (0 : ℝ) hnorm
  have hg' : HasDerivAt g (AlternatingPolygonSpectrum.jacobian N p q) 0 :=
    hg.hasDerivAt
  have ht : HasDerivAt (fun t : ℝ => t / R) (1 / R) 0 :=
    (hasDerivAt_id 0).div_const R
  have hder := (hg'.comp_of_eq (0 : ℝ) ht (by simp)).const_mul (2 * Ω * R)
  have heq : (fun t : ℝ => field N b Ω (R • polygon N + t • v) p) =
      fun t : ℝ => (2 * Ω * R) * g (t / R) := by
    funext t
    have hz : R • polygon N + t • v = R • (polygon N + (t / R) • v) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ hR]
    rw [hz, field_scaling_algebraic N hR hb]
    rfl
  change deriv (fun t : ℝ => field N b Ω (R • polygon N + t • v) p) 0 = _
  rw [heq]
  simp only [Function.comp_def] at hder
  rw [hder.deriv]
  change (2 * Ω * R) * (AlternatingPolygonSpectrum.jacobian N p q * (1 / R)) =
    (2 * Ω) * AlternatingPolygonSpectrum.jacobian N p q
  field_simp [hR]

/-- Positive physical parameters select a strictly positive equilibrium radius. -/
theorem scaled_equilibrium (m : ℕ) (hm : 1 ≤ m) {b Ω : ℝ}
    (hb : 0 < b) (hΩ : 0 < Ω) :
    CollisionFree ((radius b Ω) • polygon (2 * m)) ∧
      field (2 * m) b Ω ((radius b Ω) • polygon (2 * m)) = 0 := by
  have hR := ne_of_gt (radius_pos hb hΩ)
  have hscale : b = 4 * Ω * radius b Ω ^ 2 := by
    rw [radius_sq hb hΩ]
    field_simp
  constructor
  · exact (collision_free_smul hR).mpr (polygon_collision_free _)
  · rw [field_scaling _ hR hscale _ (polygon_collision_free _), equilibrium_all m hm,
      smul_zero]

/-- A simultaneous physical rotation of all vortex positions. -/
def rotate {N : ℕ} (θ : ℝ) (z : Configuration N) : Configuration N := fun p =>
  match p with
  | .inl j => Real.cos θ * z (.inl j) - Real.sin θ * z (.inr j)
  | .inr j => Real.sin θ * z (.inl j) + Real.cos θ * z (.inr j)

/-- The trap-centered polygon, with arbitrary radius and orientation. -/
def regular (N : ℕ) (ρ θ : ℝ) : Configuration N := ρ • rotate θ (polygon N)

private theorem rotate_norm {N : ℕ} (θ : ℝ) (z : Configuration N) (j : Fin N) :
    rotate θ z (.inl j) ^ 2 + rotate θ z (.inr j) ^ 2 =
      z (.inl j) ^ 2 + z (.inr j) ^ 2 := by
  dsimp [rotate]
  linear_combination (z (.inl j) ^ 2 + z (.inr j) ^ 2) *
    (Real.sin_sq_add_cos_sq θ)

private theorem rotate_distance {N : ℕ} (θ : ℝ) (z : Configuration N) (j k : Fin N) :
    (rotate θ z (.inl j) - rotate θ z (.inl k)) ^ 2 +
      (rotate θ z (.inr j) - rotate θ z (.inr k)) ^ 2 =
    (z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2 := by
  dsimp [rotate]
  linear_combination ((z (.inl j) - z (.inl k)) ^ 2 +
    (z (.inr j) - z (.inr k)) ^ 2) * (Real.sin_sq_add_cos_sq θ)

private theorem rotate_smul {N : ℕ} (θ a : ℝ) (z : Configuration N) :
    rotate θ (a • z) = a • rotate θ z := by
  ext p
  cases p <;> simp [rotate, mul_sub, mul_add] <;> ring

/-- Collision freedom is invariant under a common physical rotation. -/
theorem collision_free_rotate {N : ℕ} {z : Configuration N} (θ : ℝ) :
    CollisionFree (rotate θ z) ↔ CollisionFree z := by
  unfold CollisionFree
  simp only [rotate_distance]

/-- Rotational covariance follows from the Cartesian equations and distances. -/
theorem field_rotation {N : ℕ} (b Ω θ : ℝ) (z : Configuration N) :
    field N b Ω (rotate θ z) = rotate θ (field N b Ω z) := by
  classical
  have hi (j : Fin N) :
      (∑ k : Fin N, if k = j then 0 else charge N k *
        (rotate θ z (.inl j) - rotate θ z (.inl k)) /
        ((rotate θ z (.inl j) - rotate θ z (.inl k)) ^ 2 +
          (rotate θ z (.inr j) - rotate θ z (.inr k)) ^ 2)) =
      Real.cos θ * (∑ k : Fin N, if k = j then 0 else charge N k *
        (z (.inl j) - z (.inl k)) /
        ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) -
      Real.sin θ * (∑ k : Fin N, if k = j then 0 else charge N k *
        (z (.inr j) - z (.inr k)) /
        ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · simp [hk]
    · simp only [hk, ite_false]
      rw [rotate_distance]
      dsimp only [rotate]
      ring
  have hj (j : Fin N) :
      (∑ k : Fin N, if k = j then 0 else charge N k *
        (rotate θ z (.inr j) - rotate θ z (.inr k)) /
        ((rotate θ z (.inl j) - rotate θ z (.inl k)) ^ 2 +
          (rotate θ z (.inr j) - rotate θ z (.inr k)) ^ 2)) =
      Real.sin θ * (∑ k : Fin N, if k = j then 0 else charge N k *
        (z (.inl j) - z (.inl k)) /
        ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) +
      Real.cos θ * (∑ k : Fin N, if k = j then 0 else charge N k *
        (z (.inr j) - z (.inr k)) /
        ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · simp [hk]
    · simp only [hk, ite_false]
      rw [rotate_distance]
      dsimp only [rotate]
      ring
  ext p
  cases p with
  | inl j =>
    change -charge N j * Ω * rotate θ z (.inr j) - (b / 2) * _ = _
    rw [hj]
    dsimp [rotate, field]
    ring
  | inr j =>
    change charge N j * Ω * rotate θ z (.inl j) + (b / 2) * _ = _
    rw [hi]
    dsimp [rotate, field]
    ring

private theorem regular_norm (N : ℕ) (ρ θ : ℝ) (j : Fin N) :
    regular N ρ θ (.inl j) ^ 2 + regular N ρ θ (.inr j) ^ 2 = ρ ^ 2 := by
  change (ρ * rotate θ (polygon N) (.inl j)) ^ 2 +
    (ρ * rotate θ (polygon N) (.inr j)) ^ 2 = _
  rw [show (ρ * rotate θ (polygon N) (.inl j)) ^ 2 +
      (ρ * rotate θ (polygon N) (.inr j)) ^ 2 = ρ ^ 2 *
      (rotate θ (polygon N) (.inl j) ^ 2 + rotate θ (polygon N) (.inr j) ^ 2) by ring,
    rotate_norm]
  simp only [polygon]
  rw [add_comm, Real.sin_sq_add_cos_sq, mul_one]

/-- Every positive-radius regular polygon is collision-free, including odd N. -/
theorem regular_collision_free (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    CollisionFree (regular N ρ θ) :=
  (collision_free_smul (ne_of_gt hρ)).mpr
    ((collision_free_rotate θ).mpr (polygon_collision_free N))

/-- Tangential readout of the actual field at any equal-radius configuration.
It uses no cancellation between reflected charges. -/
theorem angular_readout {N : ℕ} (b Ω ρ : ℝ) {z : Configuration N}
    (hz : CollisionFree z)
    (hn : ∀ j : Fin N, z (.inl j) ^ 2 + z (.inr j) ^ 2 = ρ ^ 2)
    (j : Fin N) :
    z (.inl j) * field N b Ω z (.inr j) -
      z (.inr j) * field N b Ω z (.inl j) =
      charge N j * Ω * ρ ^ 2 + (b / 4) *
        ((∑ k : Fin N, charge N k) - charge N j) := by
  classical
  have hterm (k : Fin N) (hk : k ≠ j) :
      z (.inl j) * (charge N k * (z (.inl j) - z (.inl k)) /
          ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) +
      z (.inr j) * (charge N k * (z (.inr j) - z (.inr k)) /
          ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) =
      charge N k / 2 := by
    have hd := hz j k hk.symm
    field_simp
    linear_combination charge N k * (hn j - hn k)
  have hsum :
      z (.inl j) * (∑ k : Fin N, if k = j then 0 else
        charge N k * (z (.inl j) - z (.inl k)) /
          ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) +
      z (.inr j) * (∑ k : Fin N, if k = j then 0 else
        charge N k * (z (.inr j) - z (.inr k)) /
          ((z (.inl j) - z (.inl k)) ^ 2 + (z (.inr j) - z (.inr k)) ^ 2)) =
      ((∑ k : Fin N, charge N k) - charge N j) / 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    have he : (∑ k : Fin N, if k = j then 0 else charge N k) =
        (∑ k : Fin N, charge N k) - charge N j := by
      rw [← Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      have hset : Finset.univ.erase j = Finset.univ.filter (fun k : Fin N => k ≠ j) := by
        ext k
        simp [ne_comm]
      rw [hset, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = j <;> simp [hk]
    rw [← he, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · simp [hk]
    · simp only [hk, ite_false]
      exact hterm k hk
  dsimp only [field]
  linear_combination (b / 2) * hsum + charge N j * Ω * hn j

theorem total_charge (N : ℕ) :
    (∑ j : Fin N, charge N j) = if Even N then 0 else 1 := by
  simp only [charge, pow_add, neg_one_sq, mul_one]
  exact Fin.sum_neg_one_pow ℝ N

/-- An odd cyclic charge pattern still defines the Cartesian field. Its
positive vortex has nonzero tangential velocity at every positive radius. -/
theorem odd_nonstationary {N : ℕ} (hN : 0 < N) (hodd : ¬ Even N)
    (b : ℝ) {Ω ρ : ℝ} (hΩ : 0 < Ω) (hρ : 0 < ρ) {z : Configuration N}
    (hz : CollisionFree z)
    (hn : ∀ j : Fin N, z (.inl j) ^ 2 + z (.inr j) ^ 2 = ρ ^ 2) :
    field N b Ω z ≠ 0 := by
  intro hf
  let j : Fin N := ⟨0, hN⟩
  have h := angular_readout b Ω ρ hz hn j
  rw [hf, total_charge, ite_eq_right hodd] at h
  simp [charge, j] at h
  exact h.elim (ne_of_gt hΩ) (ne_of_gt hρ)

/-- Sharp actual-field boundary for the specified cyclic charge pattern. -/
theorem regular_equilibrium_iff {N : ℕ} (hN : 3 ≤ N) {b Ω ρ : ℝ}
    (hb : 0 < b) (hΩ : 0 < Ω) (hρ : 0 < ρ) (θ : ℝ) :
    field N b Ω (regular N ρ θ) = 0 ↔ Even N ∧ ρ ^ 2 = b / (4 * Ω) := by
  constructor
  · intro hf
    have heven : Even N := by
      by_contra ho
      exact odd_nonstationary (by omega) ho b hΩ hρ
        (regular_collision_free N hρ θ) (regular_norm N ρ θ) hf
    refine ⟨heven, ?_⟩
    let j : Fin N := ⟨0, by omega⟩
    have ha := angular_readout b Ω ρ (regular_collision_free N hρ θ)
      (regular_norm N ρ θ) j
    rw [hf, total_charge, ite_eq_left heven] at ha
    simp [charge, j] at ha
    apply (eq_div_iff (by positivity : 4 * Ω ≠ 0)).mpr
    nlinarith
  · rintro ⟨heven, hrad⟩
    obtain ⟨m, hm⟩ := heven
    have hNm : N = 2 * m := by omega
    rw [hNm]
    have hscale : b = 4 * Ω * ρ ^ 2 := by
      rw [hrad]
      field_simp
    rw [regular, ← rotate_smul, field_rotation, field_scaling _ (ne_of_gt hρ)
      hscale _ (polygon_collision_free _), equilibrium_all m (by omega)]
    ext p
    cases p <;> simp [rotate]

/-- Positive radii identify the square-root radius without a sign ambiguity. -/
theorem regular_equilibrium_iff_radius {N : ℕ} (hN : 3 ≤ N) {b Ω ρ : ℝ}
    (hb : 0 < b) (hΩ : 0 < Ω) (hρ : 0 < ρ) (θ : ℝ) :
    field N b Ω (regular N ρ θ) = 0 ↔ Even N ∧ ρ = radius b Ω := by
  rw [regular_equilibrium_iff hN hb hΩ hρ θ]
  constructor
  · rintro ⟨hN, hr⟩
    refine ⟨hN, ?_⟩
    have := radius_sq hb hΩ
    have := radius_pos hb hΩ
    nlinarith
  · rintro ⟨hN, rfl⟩
    exact ⟨hN, radius_sq hb hΩ⟩

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters

/- GID: D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bounded even class function with affine two-readout data reduces to d'Alembert. -/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Affine two-readout equations on an abstract group. -/

namespace D5.S3.Quantum.Algebra.Comparison.TwoReadoutNormalization

private theorem nonpos_of_bounded_squaring {G : Type*} [Mul G] (f : G → ℝ) {B : ℝ}
    (hbound : ∀ g, f g ≤ B) (hgrowth : ∀ g, 2 * f g ≤ f (g * g)) (g : G) :
    f g ≤ 0 := by
  have hiter (n : ℕ) : ∀ x, (2 : ℝ) ^ n * f x ≤ B := by
    induction n with
    | zero => simpa using hbound
    | succ n ih =>
      intro x
      rw [pow_succ, mul_assoc]
      exact (mul_le_mul_of_nonneg_left (hgrowth x) (by positivity)).trans (ih (x * x))
  by_contra! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / f g) (by norm_num : (1 : ℝ) < 2)
  exact (not_lt_of_ge (hiter n g)) ((div_lt_iff₀ h).mp hn)

/-- Faithfulness forces the coefficient of the forward readout at a non-involutive step. -/
theorem coefficient_eq_neg_one {G : Type*} [Group G] (ψ : G → ℝ)
    (heven : ∀ g, ψ g⁻¹ = ψ g) (_hcentral : ∀ g h, ψ (h * g * h⁻¹) = ψ g)
    (hfaithful : ∀ g, ψ g = 1 ↔ g = 1) (a b d : ℝ) (u : G)
    (hlaw : ∀ z, ψ (z * u⁻¹) = a * ψ z + b * ψ (z * u) + d)
    (hu : u * u ≠ 1) :
    b = -1 := by
  have hone : ψ 1 = 1 := (hfaithful 1).mpr rfl
  have hsquare : ψ (u⁻¹ * u⁻¹) = ψ (u * u) := by rw [← mul_inv_rev, heven]
  have hf := hlaw u
  have hr := hlaw u⁻¹
  rw [mul_inv_cancel, hone] at hf
  rw [hsquare, heven, inv_mul_cancel, hone] at hr
  have hprod : (1 + b) * (ψ (u * u) - 1) = 0 := by nlinarith
  have hn : ψ (u * u) - 1 ≠ 0 := sub_ne_zero.mpr (mt (hfaithful _).mp hu)
  linarith [(mul_eq_zero.mp hprod).resolve_right hn]

/-- Subtracting one common offset turns the symmetric affine law into d'Alembert's equation. -/
theorem bounded_dalembert_of_affine_law {G : Type*} [Group G] (ψ : G → ℝ)
    (hone : ψ 1 = 1) (heven : ∀ g, ψ g⁻¹ = ψ g)
    (hcentral : ∀ g h, ψ (h * g * h⁻¹) = ψ g) (hbound : ∀ g, |ψ g| ≤ 1)
    (hnonconst : ∃ g, ψ g ≠ 1) (a d : G → ℝ)
    (hlaw : ∀ z u, ψ (z * u) + ψ (z * u⁻¹) = a u * ψ z + d u) :
    ∃ m : ℝ, m < 1 ∧
      let q := fun g => (ψ g - m) / (1 - m)
      (∀ g, |q g| ≤ 1) ∧ (∀ z u, q (z * u) + q (z * u⁻¹) = 2 * q z * q u) := by
  have hswap (x y : G) : ψ (x * y) = ψ (y * x) := by
    have h := hcentral (y * x) x
    rwa [show x * (y * x) * x⁻¹ = x * y by group] at h
  have hstep (u : G) : 2 * ψ u = a u + d u := by
    simpa [hone, heven, two_mul] using hlaw 1 u
  have hcross (u v : G) : d u * (2 - a v) = d v * (2 - a u) := by
    have hinverse : ψ (u * v⁻¹) = ψ (v * u⁻¹) := by
      rw [← heven (u * v⁻¹), mul_inv_rev, inv_inv]
    have hu := hlaw u v
    have hv := hlaw v u
    rw [hswap u v, hinverse, hv] at hu
    nlinarith [congrArg (fun x => a v * x) (hstep u),
      congrArg (fun x => a u * x) (hstep v)]
  have hnonlinear : ∃ v, a v ≠ 2 := by
    by_contra! h
    have hzero (u : G) : 1 - ψ u ≤ 0 := by
      apply nonpos_of_bounded_squaring (fun g => 1 - ψ g) (B := 2)
      · intro g
        linarith [(abs_le.mp (hbound g)).1]
      · intro g
        have hgg := hlaw g g
        rw [mul_inv_cancel, hone, h g] at hgg
        have ha := hstep g
        rw [h g] at ha
        linarith [(abs_le.mp (hbound g)).2]
    obtain ⟨g, hg⟩ := hnonconst
    exact hg (le_antisymm (abs_le.mp (hbound g)).2 (by linarith [hzero g]))
  obtain ⟨v, hv⟩ := hnonlinear
  have hv' : 2 - a v ≠ 0 := sub_ne_zero.mpr hv.symm
  let m := d v / (2 - a v)
  have hmv : m * (2 - a v) = d v := div_mul_cancel₀ _ hv'
  have hoffset (u : G) : d u = m * (2 - a u) := by
    apply mul_right_cancel₀ hv'
    calc
      d u * (2 - a v) = d v * (2 - a u) := hcross u v
      _ = (m * (2 - a u)) * (2 - a v) := by rw [← hmv]; ring
  have hshift (u : G) : 2 * (ψ u - m) = a u * (1 - m) := by
    linarith [hstep u, hoffset u]
  have hmne : m ≠ 1 := by
    intro hm
    obtain ⟨u, hu⟩ := hnonconst
    have h := hshift u
    rw [hm] at h
    exact hu (by linarith)
  have hd : 1 - m ≠ 0 := sub_ne_zero.mpr hmne.symm
  let q (g : G) := (ψ g - m) / (1 - m)
  have hqmul (g : G) : q g * (1 - m) = ψ g - m := div_mul_cancel₀ _ hd
  have hcoefficient (u : G) : 2 * q u = a u := by
    apply mul_right_cancel₀ hd
    rw [mul_assoc, hqmul, hshift]
  have hnormalized (z u : G) : q (z * u) + q (z * u⁻¹) = 2 * q z * q u := by
    calc
      q (z * u) + q (z * u⁻¹) = a u * q z := by
        apply mul_right_cancel₀ hd
        rw [add_mul, hqmul, hqmul, mul_assoc, hqmul]
        linarith [hlaw z u, hoffset u]
      _ = 2 * q z * q u := by rw [← hcoefficient u]; ring
  have hqone : q 1 = 1 := by simp [q, hone, hd]
  have hdup (u : G) : q (u * u) = 2 * q u ^ 2 - 1 := by
    have hu := hnormalized u u
    rw [mul_inv_cancel, hqone] at hu
    linarith
  have hmlt : m < 1 := by
    by_contra! h
    have hmpos : 0 < m - 1 := sub_pos.mpr (lt_of_le_of_ne h hmne.symm)
    have hdefect (g : G) : q g - 1 = (1 - ψ g) / (m - 1) := by
      dsimp [q]
      field_simp [hd, hmpos.ne']
      ring
    have hnonneg (g : G) : 0 ≤ q g - 1 := by
      rw [hdefect]
      exact div_nonneg (sub_nonneg.mpr (abs_le.mp (hbound g)).2) hmpos.le
    have hnonpos (g : G) : q g - 1 ≤ 0 := by
      apply nonpos_of_bounded_squaring (fun x => q x - 1) (B := 2 / (m - 1))
      · intro x
        rw [hdefect]
        exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp (hbound x)).1]) hmpos.le
      · intro x
        rw [hdup]
        nlinarith [hnonneg x, sq_nonneg (q x - 1)]
    obtain ⟨u, hu⟩ := hnonconst
    have hzero := le_antisymm (hnonpos u) (hnonneg u)
    rw [hdefect, div_eq_zero_iff] at hzero
    exact hu (by linarith [hzero.resolve_right hmpos.ne'])
  have hupper (g : G) : q g ≤ 1 := by
    exact (div_le_iff₀ (sub_pos.mpr hmlt)).mpr (by linarith [(abs_le.mp (hbound g)).2])
  have hlower (g : G) : -1 ≤ q g := by
    by_contra! h
    have hu := hupper (g * g)
    rw [hdup] at hu
    nlinarith [sq_nonneg (q g + 1)]
  exact ⟨m, hmlt, fun g => abs_le.mpr ⟨hlower g, hupper g⟩, hnormalized⟩

/-- On a group with no nonidentity involutions, one-sided affine laws suffice to produce
the bounded d'Alembert solution. -/
theorem bounded_dalembert_of_one_sided_law {G : Type*} [Group G] (ψ : G → ℝ)
    (heven : ∀ g, ψ g⁻¹ = ψ g) (hcentral : ∀ g h, ψ (h * g * h⁻¹) = ψ g)
    (hfaithful : ∀ g, ψ g = 1 ↔ g = 1) (hbound : ∀ g, |ψ g| ≤ 1)
    (hnonconst : ∃ g, ψ g ≠ 1) (hinvolutions : ∀ u : G, u * u = 1 → u = 1)
    (hlaw : ∀ u : G, u ≠ 1 → ∃ a b d : ℝ, ∀ z,
      ψ (z * u⁻¹) = a * ψ z + b * ψ (z * u) + d) :
    ∃ m : ℝ, m < 1 ∧
      let q := fun g => (ψ g - m) / (1 - m)
      (∀ g, |q g| ≤ 1) ∧ (∀ z u, q (z * u) + q (z * u⁻¹) = 2 * q z * q u) := by
  classical
  have hsym (u : G) : ∃ a d : ℝ, ∀ z, ψ (z * u) + ψ (z * u⁻¹) = a * ψ z + d := by
    by_cases hu : u = 1
    · subst u
      exact ⟨2, 0, fun z => by simp [two_mul]⟩
    · obtain ⟨a, b, d, hb⟩ := hlaw u hu
      have hb' := coefficient_eq_neg_one ψ heven hcentral hfaithful a b d u hb
        (mt (hinvolutions u) hu)
      refine ⟨a, d, fun z => ?_⟩
      rw [hb, hb']
      ring
  choose a d ha using hsym
  exact bounded_dalembert_of_affine_law ψ ((hfaithful 1).mpr rfl) heven hcentral hbound
    hnonconst a d (fun z u => ha u z)

end D5.S3.Quantum.Algebra.Comparison.TwoReadoutNormalization

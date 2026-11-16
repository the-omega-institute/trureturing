/- GID: D5/S3/StatisticalMechanics/InversePowerLineNetwork
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/InversePowerLineNetwork
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Induced capacity and positive harmonic rigidity. -/

/-
admission_basis: escape-witness
question_answered: https://github.com/the-omega-institute/trureturing/issues/27202
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27401
energy:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.energy_bound_by_supported_moments,
    InversePowerLineEquilibria.capacity_zero_of_second_moment_mass_bound, ground_state_identity,
    energy_nonneg, subharmonic_energy_obstruction, no_strict_subharmonic_at_capacity_zero,
    harmonic_constant_of_sublevel_capacity_zero.
laplacian:
  proof_shape: bind-only; escape_witness: none.
  consumers: ground_state_identity, subharmonic_energy_obstruction,
    no_strict_subharmonic_at_capacity_zero, harmonic_constant_of_sublevel_capacity_zero.
summable_finite_rows:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.energy_bound_by_supported_moments, summable_left_weight,
    ground_state_identity.
summable_left_weight:
  proof_shape: bind-only; escape_witness: none.
  consumers: energy_summable.
energy_summable:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.energy_bound_by_supported_moments, ground_state_identity,
    subharmonic_energy_obstruction.
weighted_row_summable:
  proof_shape: bind-only; escape_witness: none.
  consumers: ground_state_identity, subharmonic_energy_obstruction.
ground_state_identity:
  proof_shape: bind-only; escape_witness: none.
  consumers: subharmonic_energy_obstruction.
energy_nonneg:
  proof_shape: bind-only; escape_witness: none.
  consumers: subharmonic_energy_obstruction, no_strict_subharmonic_at_capacity_zero.
subharmonic_energy_obstruction:
  proof_shape: content; escape_witness: subharmonic_energy_obstruction.
  consumers: no_strict_subharmonic_at_capacity_zero.
no_strict_subharmonic_at_capacity_zero:
  proof_shape: content; escape_witness: subharmonic_energy_obstruction.
  consumers: harmonic_constant_of_sublevel_capacity_zero.
harmonic_constant_of_sublevel_capacity_zero:
  proof_shape: content; escape_witness: harmonic_constant_of_sublevel_capacity_zero.
  consumers: InversePowerLineEquilibria.reciprocal_constant_of_power_bound.
-/

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Induced capacity and positive harmonic rigidity
-/

namespace D5.S3.StatisticalMechanics.InversePowerLineNetwork



noncomputable def energy {V : Type*} (C : V → V → ℝ) (f : V → ℝ) : ℝ :=
  (1 / 2) * ∑' p : V × V, C p.1 p.2 * (f p.1 - f p.2) ^ 2

private noncomputable def laplacian {V : Type*} (C : V → V → ℝ) (w : V → ℝ) (x : V) : ℝ :=
  ∑' y, C x y * (w x - w y)

theorem summable_finite_rows {V W : Type*} (S : Finset V) (F : V × W → ℝ)
    (hrow : ∀ x, Summable (fun y => F (x, y)))
    (hzero : ∀ x, x ∉ S → ∀ y, F (x, y) = 0) : Summable F := by
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun p => norm_nonneg (F p))).mpr
  constructor
  · intro x
    simpa only [Real.norm_eq_abs] using (hrow x).abs
  · apply summable_of_ne_finset_zero (s := S)
    intro x hx
    simp [hzero x hx]

private theorem summable_left_weight {V : Type*} (C : V → V → ℝ)
    (hrow : ∀ x, Summable (C x)) (u : V → ℝ) (S : Finset V)
    (hu : ∀ x, x ∉ S → u x = 0) :
    Summable (fun p : V × V => C p.1 p.2 * u p.1) := by
  apply summable_finite_rows S
  · intro x
    exact (hrow x).mul_right (u x)
  · intro x hx y
    simp [hu x hx]

theorem energy_summable {V : Type*} (C : V → V → ℝ)
    (hsymm : ∀ x y, C x y = C y x) (hnonneg : ∀ x y, 0 ≤ C x y)
    (hrow : ∀ x, Summable (C x)) (f : V → ℝ) (S : Finset V)
    (hf : ∀ x, x ∉ S → f x = 0) :
    Summable (fun p : V × V => C p.1 p.2 * (f p.1 - f p.2) ^ 2) := by
  have hleft := summable_left_weight C hrow (fun x => (f x) ^ 2) S (by
    intro x hx; simp [hf x hx])
  have hright : Summable (fun p : V × V => C p.1 p.2 * (f p.2) ^ 2) := by
    convert hleft.prod_symm using 1
    ext p
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hsymm]
  apply ((hleft.add hright).mul_left 2).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg _ _) (sq_nonneg _))]
  have hsq : (f p.1 - f p.2)^2 ≤ 2 * ((f p.1)^2 + (f p.2)^2) := by
    simpa only [sub_eq_add_neg, neg_sq] using (add_sq_le (a := f p.1) (b := -f p.2))
  nlinarith [mul_le_mul_of_nonneg_left hsq (hnonneg p.1 p.2)]

private theorem weighted_row_summable {V : Type*} (C : V → V → ℝ)
    (hnonneg : ∀ x y, 0 ≤ C x y) (hrow : ∀ x, Summable (C x))
    (w : V → ℝ) (M : ℝ) (hw : ∀ x, |w x| ≤ M) (x : V) :
    Summable (fun y => C x y * w y) := by
  apply ((hrow x).mul_right M).of_norm_bounded
  intro y
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnonneg x y)]
  exact mul_le_mul_of_nonneg_left (hw y) (hnonneg x y)

private theorem ground_state_identity {V : Type*} (C : V → V → ℝ)
    (hsymm : ∀ x y, C x y = C y x) (hnonneg : ∀ x y, 0 ≤ C x y)
    (hrow : ∀ x, Summable (C x)) (f w : V → ℝ) (S : Finset V)
    (hf : ∀ x, x ∉ S → f x = 0) (M : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hwM : ∀ x, w x ≤ M) :
    energy C (fun x => f x * w x) =
      (∑' x, (f x)^2 * w x * laplacian C w x) +
      energy (fun x y => C x y * w x * w y) f := by
  have hw : ∀ x, |w x| ≤ M := fun x => by rw [abs_of_nonneg (hw0 x)]; exact hwM x
  have hwr := weighted_row_summable C hnonneg hrow w M hw
  let A : V × V → ℝ := fun p => C p.1 p.2 * (f p.1)^2 * w p.1 * (w p.1 - w p.2)
  have hArow (x : V) : Summable (fun y => A (x, y)) := by
    convert (((hrow x).mul_right (w x)).sub (hwr x)).mul_left ((f x)^2 * w x) using 1
    ext y
    dsimp [A]
    ring
  have hA : Summable A := summable_finite_rows S A hArow (by
    intro x hx y
    dsimp [A]
    rw [hf x hx]
    ring)
  let B : V × V → ℝ := fun p => C p.1 p.2 * w p.1 * w p.2 * (f p.1 - f p.2)^2
  have hB : Summable B := by
    apply energy_summable (fun x y => C x y * w x * w y)
      (fun x y => by rw [hsymm x y]; ring)
      (fun x y => mul_nonneg (mul_nonneg (hnonneg x y) (hw0 x)) (hw0 y))
      (fun x => by
        convert (hwr x).mul_left (w x) using 1
        ext y; ring) f S hf
  have hAswap : Summable (fun p : V × V => A p.swap) := hA.prod_symm
  have hAid : (∑' p, A p) = ∑' x, (f x)^2 * w x * laplacian C w x := by
    rw [hA.tsum_prod]
    apply tsum_congr
    intro x
    unfold laplacian
    rw [← tsum_mul_left]
    apply tsum_congr
    intro y
    dsimp [A]
    ring
  have halgebra (p : V × V) :
      C p.1 p.2 * (f p.1 * w p.1 - f p.2 * w p.2)^2 = A p + A p.swap + B p := by
    dsimp [A, B]
    rw [hsymm p.2 p.1]
    ring
  have hswap : (∑' p : V × V, A p.swap) = ∑' p, A p := by
    simpa only [Equiv.prodComm_apply] using (Equiv.prodComm V V).tsum_eq A
  unfold energy
  simp_rw [halgebra]
  rw [(hA.add hAswap).tsum_add hB, hA.tsum_add hAswap,
    hswap, hAid]
  change (1 / 2 : ℝ) * (_ + _ + _) = _ + (1 / 2 : ℝ) * _
  ring

private theorem energy_nonneg {V : Type*} (C : V → V → ℝ)
    (hnonneg : ∀ x y, 0 ≤ C x y) (f : V → ℝ) : 0 ≤ energy C f := by
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun p =>
    mul_nonneg (hnonneg p.1 p.2) (sq_nonneg _)))

private theorem subharmonic_energy_obstruction {V : Type*} (C : V → V → ℝ)
    (hsymm : ∀ x y, C x y = C y x) (hnonneg : ∀ x y, 0 ≤ C x y)
    (hrow : ∀ x, Summable (C x)) (f w : V → ℝ) (S : Finset V)
    (hf : ∀ x, x ∉ S → f x = 0) (M : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hwM : ∀ x, w x ≤ M)
    (hsub : ∀ x, laplacian C w x ≤ 0) (x0 : V) (hf0 : f x0 = 1) :
    -(w x0 * laplacian C w x0) ≤ M^2 * energy C f := by
  classical
  have hw : ∀ x, |w x| ≤ M := fun x => by rw [abs_of_nonneg (hw0 x)]; exact hwM x
  have hwr := weighted_row_summable C hnonneg hrow w M hw
  have hW : ∀ x, Summable (fun y => C x y * w x * w y) := by
    intro x
    convert (hwr x).mul_left (w x) using 1
    ext y; ring
  have hEs := energy_summable C hsymm hnonneg hrow f S hf
  have hBs := energy_summable (fun x y => C x y * w x * w y)
    (fun x y => by rw [hsymm x y]; ring)
    (fun x y => mul_nonneg (mul_nonneg (hnonneg x y) (hw0 x)) (hw0 y)) hW f S hf
  have hEB : energy (fun x y => C x y * w x * w y) f ≤ M^2 * energy C f := by
    have hpoint (p : V × V) : C p.1 p.2 * w p.1 * w p.2 * (f p.1 - f p.2)^2 ≤
        M^2 * (C p.1 p.2 * (f p.1 - f p.2)^2) := by
      have hprod : w p.1 * w p.2 ≤ M^2 := by
        have hm : 0 ≤ M := (hw0 p.1).trans (hwM p.1)
        calc
          w p.1 * w p.2 ≤ M * M := mul_le_mul (hwM p.1) (hwM p.2) (hw0 p.2) hm
          _ = M^2 := by exact Eq.symm (pow_two M)
      nlinarith [mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (hnonneg p.1 p.2) (sq_nonneg (f p.1 - f p.2)))]
    have ht := hBs.tsum_le_tsum hpoint (hEs.mul_left (M^2))
    rw [tsum_mul_left] at ht
    dsimp [energy]
    nlinarith
  let P : V → ℝ := fun x => (f x)^2 * w x * laplacian C w x
  have hP : Summable P := summable_of_ne_finset_zero (s := S) (by
    intro x hx
    simp [P, hf x hx])
  have hPneg (x : V) : P x ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (hw0 x)) (hsub x)
  have hPbound : (∑' x, P x) ≤ w x0 * laplacian C w x0 := by
    have hnegP : Summable (fun x => -P x) := hP.neg
    have h := hnegP.le_tsum x0 (fun x _ => neg_nonneg.mpr (hPneg x))
    rw [tsum_neg] at h
    dsimp [P] at h
    rw [hf0] at h
    norm_num at h
    linarith
  have hid := ground_state_identity C hsymm hnonneg hrow f w S hf M hw0 hwM
  have hpos := energy_nonneg C hnonneg (fun x => f x * w x)
  change energy C (fun x => f x * w x) = (∑' x, P x) + _ at hid
  linarith

private theorem no_strict_subharmonic_at_capacity_zero {V : Type*} (C : V → V → ℝ)
    (hsymm : ∀ x y, C x y = C y x) (hnonneg : ∀ x y, 0 ≤ C x y)
    (hrow : ∀ x, Summable (C x)) (w : V → ℝ) (M : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hwM : ∀ x, w x ≤ M)
    (hsub : ∀ x, laplacian C w x ≤ 0) (x0 : V)
    (hcap : ∀ ε : ℝ, 0 < ε → ∃ (S : Finset V) (f : V → ℝ),
      (∀ x, x ∉ S → f x = 0) ∧ f x0 = 1 ∧ energy C f < ε) :
    ¬ (0 < w x0 ∧ laplacian C w x0 < 0) := by
  rintro ⟨hwpos, hLneg⟩
  let δ := -(w x0 * laplacian C w x0)
  have hδ : 0 < δ := neg_pos.mpr (mul_neg_of_pos_of_neg hwpos hLneg)
  have hden : 0 < M^2 + 1 := by positivity
  obtain ⟨S, f, hf, hf0, hE⟩ := hcap (δ / (M^2 + 1)) (div_pos hδ hden)
  have hbound := subharmonic_energy_obstruction C hsymm hnonneg hrow f w S hf M hw0 hwM hsub x0 hf0
  change δ ≤ M^2 * energy C f at hbound
  have hsmall := (lt_div_iff₀ hden).mp hE
  have hEnonneg := energy_nonneg C hnonneg f
  nlinarith

theorem harmonic_constant_of_sublevel_capacity_zero {V : Type*}
    (C : V → V → ℝ) (hsymm : ∀ x y, C x y = C y x)
    (hnonneg : ∀ x y, 0 ≤ C x y) (hpositive : ∀ x y, x ≠ y → 0 < C x y)
    (hrow : ∀ x, Summable (C x)) (h : V → ℝ) (hhpos : ∀ x, 0 < h x)
    (hweighted : ∀ x, Summable (fun y => C x y * h y))
    (hharm : ∀ x, (∑' y, C x y * h y) = (∑' y, C x y) * h x)
    (hcap : ∀ M : ℝ, 0 < M → (∃ y : V, M < h y) →
      ∀ x0 : {x : V // h x ≤ M},
      ∀ ε : ℝ, 0 < ε → ∃ (S : Finset {x : V // h x ≤ M})
        (f : {x : V // h x ≤ M} → ℝ),
        (∀ x, x ∉ S → f x = 0) ∧ f x0 = 1 ∧
          energy (fun x y => C x.val y.val) f < ε) :
    ∀ x y, h x = h y := by
  classical
  have hnotlt (x0 y0 : V) : ¬ h x0 < h y0 := by
    intro hxy
    let M : ℝ := (h x0 + h y0) / 2
    have hM : 0 < M := by dsimp [M]; linarith [hhpos x0, hhpos y0]
    have hxM : h x0 < M  := by exact left_lt_add_div_two.mpr hxy

    have hMy : M < h y0  := by exact add_div_two_lt_right.mpr hxy

    let A : Set V := {x | h x ≤ M}
    let w : A → ℝ := fun x => M - h x.val
    let D : A → A → ℝ := fun x y => C x.val y.val
    have hDrow (x : A) : Summable (D x) := (hrow x.val).subtype A
    have hdiff (x : V) : Summable (fun y => C x y * (h y - h x)) := by
      convert (hweighted x).sub ((hrow x).mul_right (h x)) using 1
      ext y; ring
    have hzero (x : V) : (∑' y, C x y * (h y - h x)) = 0 := by
      simp_rw [mul_sub]
      rw [(hweighted x).tsum_sub ((hrow x).mul_right (h x)), tsum_mul_right, hharm x]
      ring
    have hLneg (x : A) : laplacian D w x < 0 := by
      have hyout : y0 ∈ Aᶜ := by
        change ¬ h y0 ≤ M
        exact not_le.mpr hMy
      have hsumpos : 0 < ∑' y : ↑(Aᶜ), C x.val y.val * (h y.val - h x.val) := by
        refine ((hdiff x.val).subtype (Aᶜ)).tsum_pos ?_ ⟨y0, hyout⟩ ?_
        · intro y
          have hy : M < h y.val := lt_of_not_ge y.property
          have hx : h x.val ≤ M := x.property
          exact mul_nonneg (hnonneg x.val y.val) (by linarith)
        · have hne : x.val ≠ y0 := by
            intro heq
            have hx := x.property
            change h x.val ≤ M at hx
            rw [heq] at hx
            linarith
          have hx : h x.val ≤ M := x.property
          exact mul_pos (hpositive x.val y0 hne) (by linarith)
      have hsplit := (hdiff x.val).tsum_subtype_add_tsum_subtype_compl A
      rw [hzero] at hsplit
      have heq : laplacian D w x = ∑' y : A, C x.val y.val * (h y.val - h x.val) := by
        apply tsum_congr
        intro y
        dsimp [D, w]
        ring
      rw [heq]
      linarith
    have hw0 (x : A) : 0 ≤ w x := sub_nonneg.mpr x.property
    have hwM (x : A) : w x ≤ M := by
      dsimp [w]
      linarith [hhpos x.val]
    let z : A := ⟨x0, hxM.le⟩
    have hz : 0 < w z  := by exact sub_pos.mpr hxM

    exact (no_strict_subharmonic_at_capacity_zero D
      (fun x y => hsymm x.val y.val) (fun x y => hnonneg x.val y.val)
      hDrow w M hw0 hwM (fun x => (hLneg x).le) z (hcap M hM ⟨y0, hMy⟩ z)) ⟨hz, hLneg z⟩
  intro x y
  exact le_antisymm (le_of_not_gt (hnotlt y x)) (le_of_not_gt (hnotlt x y))


end D5.S3.StatisticalMechanics.InversePowerLineNetwork

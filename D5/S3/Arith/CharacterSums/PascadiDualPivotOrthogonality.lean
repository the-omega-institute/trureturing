/- GID: D5/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality
   mirror-E: none(waiver:open-short-frequency-concentration)
   anchors: []
   utility: none
   digest: The fixed-sum cubic separates pivot spectra and gives exact complete dual energy. -/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Tactic

/-! The whole unprojected dual kernel is retained. Complete frequency
orthogonality does not assert a bound in a short frequency window. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexConjugate
open Finset Complex

namespace D5.S3.Arith.CharacterSums.PascadiDualPivotOrthogonality

/-- The physical pivot reconstructed from its reduced resonance coordinates. -/
def physicalPivot {R : Type*} [CommRing R] (r s ρ σ : R) (u : R × R) : R × R :=
  (r * u.1 + σ * u.2, s * u.1 - ρ * u.2)

/-- The actual fixed-sum cubic, with third coordinate h-x-y. -/
def fixedSumCubic {R : Type*} [CommRing R] (h : R) (z : R × R) : R :=
  z.1 * z.2 * (h - z.1 - z.2)

/-- The four simultaneous spectral readings against the two complete
two-dimensional frequencies. -/
def spectralReading {R : Type*} [CommRing R] (u z : R × R) :
    (R × R) × (R × R) :=
  ((u.1 * z.1, u.1 * z.2), (u.2 * z.1, u.2 * z.2))

/-- All coordinate and pair-sum units of the fixed-sum word, and its exact
cubic equation. No frequency or critical-point projection is imposed. -/
def AdmissiblePoint {R : Type*} [CommRing R] (r s ρ σ g h : R)
    (u z : R × R) : Prop :=
  IsUnit (physicalPivot r s ρ σ u).1 ∧
  IsUnit (physicalPivot r s ρ σ u).2 ∧
  IsUnit z.1 ∧ IsUnit z.2 ∧ IsUnit (h - z.1 - z.2) ∧
  IsUnit (z.1 + z.2) ∧ IsUnit (h - z.1) ∧ IsUnit (h - z.2) ∧
  g * (physicalPivot r s ρ σ u).1 * (physicalPivot r s ρ σ u).2 *
    fixedSumCubic h z = h

private theorem spectral_reading_eq_forces_equal {R : Type*} [CommRing R]
    (r s ρ σ g h : R) (hg : IsUnit g) (u v z w : R × R)
    (hu : AdmissiblePoint r s ρ σ g h u z)
    (hv : AdmissiblePoint r s ρ σ g h v w)
    (heq : spectralReading u z = spectralReading v w) :
    u = v ∧ z = w := by
  rcases hu with ⟨ha, hb, hx, hy, hz, hxy, hxz, hyz, hcurve⟩
  rcases hv with ⟨ha', hb', hx', hy', hz', hxy', hxz', hyz', hcurve'⟩
  let t : Rˣ := hx.unit * hx'.unit⁻¹
  have hxscale : z.1 = (t : R) * w.1 := by
    calc
      z.1 = (hx.unit : R) := hx.unit_spec.symm
      _ = (((hx.unit * hx'.unit⁻¹) * hx'.unit : Rˣ) : R) := by simp
      _ = _ := by rw [Units.val_mul, hx'.unit_spec]
  have h11 : u.1 * z.1 = v.1 * w.1 := congrArg (fun x ↦ x.1.1) heq
  have h12 : u.1 * z.2 = v.1 * w.2 := congrArg (fun x ↦ x.1.2) heq
  have h21 : u.2 * z.1 = v.2 * w.1 := congrArg (fun x ↦ x.2.1) heq
  have h22 : u.2 * z.2 = v.2 * w.2 := congrArg (fun x ↦ x.2.2) heq
  have hα : v.1 = (t : R) * u.1 := by
    apply hx'.mul_right_cancel
    rw [← h11, hxscale]
    ring
  have hβ : v.2 = (t : R) * u.2 := by
    apply hx'.mul_right_cancel
    rw [← h21, hxscale]
    ring
  have hascale : (physicalPivot r s ρ σ v).1 =
      (t : R) * (physicalPivot r s ρ σ u).1 := by
    simp only [physicalPivot, hα, hβ]
    ring
  have hbscale : (physicalPivot r s ρ σ v).2 =
      (t : R) * (physicalPivot r s ρ σ u).2 := by
    simp only [physicalPivot, hα, hβ]
    ring
  have hyscale : z.2 = (t : R) * w.2 := by
    apply ha.mul_left_cancel
    calc
      _ = r * (u.1 * z.2) + σ * (u.2 * z.2) := by
        dsimp [physicalPivot]
        ring
      _ = r * (v.1 * w.2) + σ * (v.2 * w.2) := by rw [h12, h22]
      _ = _ := by
        simp only [physicalPivot, hα, hβ]
        ring
  have hcubic : fixedSumCubic h z = (t : R) ^ 2 * fixedSumCubic h w := by
    apply ((hg.mul ha).mul hb).mul_left_cancel
    calc
      _ = h := hcurve
      _ = g * (physicalPivot r s ρ σ v).1 * (physicalPivot r s ρ σ v).2 *
          fixedSumCubic h w := hcurve'.symm
      _ = _ := by rw [hascale, hbscale]; ring
  have hfactor : ((t : R) ^ 2 * w.1 * w.2 * (w.1 + w.2)) * ((t : R) - 1) = 0 := by
    have he := sub_eq_zero.mpr hcubic
    rw [fixedSumCubic, fixedSumCubic, hxscale, hyscale] at he
    linear_combination -he
  have hunit : IsUnit ((t : R) ^ 2 * w.1 * w.2 * (w.1 + w.2)) :=
    (((t.isUnit.pow 2).mul hx').mul hy').mul hxy'
  have ht : (t : R) = 1 := sub_eq_zero.mp
    (hunit.mul_left_cancel (by simpa only [mul_zero] using hfactor))
  constructor
  · exact Prod.ext (by simpa [ht] using hα.symm) (by simpa [ht] using hβ.symm)
  · exact Prod.ext (by simpa [ht] using hxscale) (by simpa [ht] using hyscale)

/-- On the actual unit cubic, spectral coincidence identifies both the pivot
and the cubic point. The conclusion holds over any commutative ring. -/
theorem spectral_reading_injective {R : Type*} [CommRing R]
    (r s ρ σ g h : R) (hg : IsUnit g) :
    Set.InjOn (fun x : (R × R) × (R × R) ↦ spectralReading x.1 x.2)
      {x | AdmissiblePoint r s ρ σ g h x.1 x.2} := by
  intro x hx y hy hxy
  obtain ⟨hu, hz⟩ := spectral_reading_eq_forces_equal r s ρ σ g h hg x.1 y.1 x.2 y.2
    hx hy hxy
  exact Prod.ext hu hz

/-- The unprojected pair of two-dimensional frequency variables. -/
abbrev DualFrequency (q : ℕ) :=
  (ZMod q × ZMod q) × (ZMod q × ZMod q)

private def frequencyPairing {q : ℕ} (f v : DualFrequency q) : ZMod q :=
  f.1.1 * v.1.1 + f.1.2 * v.1.2 + f.2.1 * v.2.1 + f.2.2 * v.2.2

private def dualCharacter {q : ℕ} [NeZero q] (v : DualFrequency q) :
    AddChar (DualFrequency q) ℂ where
  toFun f := ZMod.stdAddChar (frequencyPairing f v)
  map_zero_eq_one' := by simp [frequencyPairing]
  map_add_eq_mul' f k := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [frequencyPairing, Prod.fst_add, Prod.snd_add]
    ring

private theorem dualCharacter_injective {q : ℕ} [NeZero q] :
    Function.Injective (dualCharacter : DualFrequency q → AddChar (DualFrequency q) ℂ) := by
  intro v w heq
  have h1 := congrArg (fun χ : AddChar (DualFrequency q) ℂ ↦ χ ((1, 0), (0, 0))) heq
  have h2 := congrArg (fun χ : AddChar (DualFrequency q) ℂ ↦ χ ((0, 1), (0, 0))) heq
  have h3 := congrArg (fun χ : AddChar (DualFrequency q) ℂ ↦ χ ((0, 0), (1, 0))) heq
  have h4 := congrArg (fun χ : AddChar (DualFrequency q) ℂ ↦ χ ((0, 0), (0, 1))) heq
  simp only [dualCharacter, AddChar.coe_mk, frequencyPairing, one_mul, zero_mul,
    add_zero, zero_add] at h1 h2 h3 h4
  exact Prod.ext (Prod.ext (ZMod.injective_stdAddChar h1) (ZMod.injective_stdAddChar h2))
    (Prod.ext (ZMod.injective_stdAddChar h3) (ZMod.injective_stdAddChar h4))

private theorem complete_character_gram {q : ℕ} [NeZero q]
    (v w : DualFrequency q) :
    (∑ f : DualFrequency q, dualCharacter v f * conj (dualCharacter w f)) =
      if v = w then (q : ℂ) ^ 4 else 0 := by
  have hcard : Fintype.card (DualFrequency q) = q ^ 4 := by
    simp only [DualFrequency, Fintype.card_prod, ZMod.card]
    ring
  have hs := AddChar.wInner_cWeight_eq_boole (dualCharacter w) (dualCharacter v)
  have hn : ((q : ℂ) ^ 4) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne q))
  have he :
      (∑ f : DualFrequency q, dualCharacter v f * conj (dualCharacter w f)) /
        (q : ℂ) ^ 4 = if v = w then 1 else 0 := by
    simpa only [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
      RCLike.inner_apply, hcard, Nat.cast_pow, dualCharacter_injective.eq_iff,
      eq_comm, mul_comm] using hs
  have H := (div_eq_iff hn).mp he
  simpa only [ite_mul, one_mul, zero_mul] using H

private theorem injective_character_energy {q : ℕ} [NeZero q]
    {ι : Type*} (S : Finset ι) (v : ι → DualFrequency q) (c : ι → ℂ)
    (hv : Set.InjOn v S) :
    (∑ f : DualFrequency q, ‖∑ i ∈ S, c i * dualCharacter (v i) f‖ ^ 2) =
      (q : ℝ) ^ 4 * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  classical
  have he :
      (∑ f : DualFrequency q, (∑ i ∈ S, c i * dualCharacter (v i) f) *
        conj (∑ i ∈ S, c i * dualCharacter (v i) f)) =
      (q : ℂ) ^ 4 * ∑ i ∈ S, c i * conj (c i) := by
    calc
      _ = ∑ f : DualFrequency q, ∑ i ∈ S, ∑ j ∈ S,
          (c i * dualCharacter (v i) f) *
            (conj (c j) * conj (dualCharacter (v j) f)) := by
        simp only [map_sum, map_mul, sum_mul, mul_sum]
        apply sum_congr rfl
        intro f hf
        rw [sum_comm]
      _ = ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
          (∑ f : DualFrequency q, dualCharacter (v i) f * conj (dualCharacter (v j) f)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i hi
        rw [sum_comm]
        apply sum_congr rfl
        intro j hj
        rw [mul_sum]
        apply sum_congr rfl
        intro f hf
        ring
      _ = ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
          (if i = j then (q : ℂ) ^ 4 else 0) := by
        apply sum_congr rfl
        intro i hi
        apply sum_congr rfl
        intro j hj
        have hij : v i = v j ↔ i = j := ⟨fun H ↦ hv hi hj H, congrArg v⟩
        rw [complete_character_gram]
        simp only [hij]
      _ = _ := by
        simp only [mul_ite, mul_zero]
        have hsum (i : ι) (hi : i ∈ S) :
            (∑ j ∈ S, if i = j then c i * conj (c j) * (q : ℂ) ^ 4 else 0) =
              c i * conj (c i) * (q : ℂ) ^ 4 := by simp [hi]
        rw [sum_congr rfl hsum, ← sum_mul]
        ring
  simp_rw [Complex.mul_conj'] at he
  exact_mod_cast he

/-- The whole two-frequency kernel for the actual retained cubic fibres.
The scalar mask may be any complex function of the pivot. -/
def dualKernel {q : ℕ} [NeZero q]
    (Z : (ZMod q × ZMod q) → Finset (ZMod q × ZMod q))
    (χ : (ZMod q × ZMod q) → ℂ) (u : ZMod q × ZMod q)
    (f : DualFrequency q) : ℂ :=
  χ u * ∑ z ∈ Z u, ZMod.stdAddChar
    ((u.1 * f.1.1 + u.2 * f.2.1) * z.1 +
      (u.1 * f.1.2 + u.2 * f.2.2) * z.2)

/-- Exact complete dual-frequency energy, with arbitrary pivot coefficients
and masks. The input fibres are required to satisfy the actual cubic and
unit conditions, rather than an assumed spectral separation property.
This applies in particular with q=p². -/
theorem complete_dual_energy {q : ℕ} [NeZero q]
    (r s ρ σ g h : ZMod q) (hg : IsUnit g)
    (S : Finset (ZMod q × ZMod q))
    (Z : (ZMod q × ZMod q) → Finset (ZMod q × ZMod q))
    (hZ : ∀ u ∈ S, ∀ z ∈ Z u, AdmissiblePoint r s ρ σ g h u z)
    (c χ : (ZMod q × ZMod q) → ℂ) :
    (∑ f : DualFrequency q, ‖∑ u ∈ S, c u * dualKernel Z χ u f‖ ^ 2) /
        (q : ℝ) ^ 4 =
      ∑ u ∈ S, ‖c u * χ u‖ ^ 2 * ((Z u).card : ℝ) := by
  classical
  let T := S.sigma Z
  let v : (Σ _u : ZMod q × ZMod q, ZMod q × ZMod q) → DualFrequency q :=
    fun x ↦ spectralReading x.1 x.2
  let d : (Σ _u : ZMod q × ZMod q, ZMod q × ZMod q) → ℂ :=
    fun x ↦ c x.1 * χ x.1
  have hinj : Set.InjOn v T := by
    intro x hx y hy hxy
    obtain ⟨hxS, hxZ⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hyS, hyZ⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hpivot, hpoint⟩ := spectral_reading_eq_forces_equal r s ρ σ g h hg
      x.1 y.1 x.2 y.2 (hZ x.1 hxS x.2 hxZ) (hZ y.1 hyS y.2 hyZ) hxy
    exact Sigma.ext hpivot (heq_of_eq hpoint)
  have he := injective_character_energy T v d hinj
  have hsum (f : DualFrequency q) :
      (∑ x ∈ T, d x * dualCharacter (v x) f) =
        ∑ u ∈ S, c u * dualKernel Z χ u f := by
    dsimp [T, d, v]
    rw [Finset.sum_sigma]
    apply sum_congr rfl
    intro u hu
    rw [dualKernel, ← mul_assoc, mul_sum]
    apply sum_congr rfl
    intro z hz
    apply congrArg (fun x : ℂ ↦ (c u * χ u) * x)
    change ZMod.stdAddChar (frequencyPairing f (spectralReading u z)) = _
    apply congrArg (ZMod.stdAddChar (N := q))
    dsimp [frequencyPairing, spectralReading]
    ring
  have hdiag : (∑ x ∈ T, ‖d x‖ ^ 2) =
      ∑ u ∈ S, ‖c u * χ u‖ ^ 2 * ((Z u).card : ℝ) := by
    dsimp [T, d]
    rw [Finset.sum_sigma]
    simp only [sum_const, nsmul_eq_mul]
    apply sum_congr rfl
    intro u hu
    ring
  simp_rw [hsum] at he
  rw [hdiag] at he
  rw [he]
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hq)

end D5.S3.Arith.CharacterSums.PascadiDualPivotOrthogonality

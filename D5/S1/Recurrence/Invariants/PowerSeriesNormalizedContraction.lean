/- GID: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficientwise iteration constructs a unique normalized fixed point. -/

/-
proof_shape: exists_unique_fixed: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralT, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralT_spec, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integralT, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integralT_spec, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.normalized_unique.
proof_shape: geometric_zero: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_mod_three.
proof_shape: geometric_one: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_mod_three.
proof_shape: geometric_coeff: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.result, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.result.
proof_shape: geometric_mul: bind-only; consumers: D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.geometric_subst_mul, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.geometric_equation, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.geometric_equation.
proof_shape: map_subst_pow: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.residual_even, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.map_equation.
proof_shape: geometric_subst_mul: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.geometric_equation.
escape_witness: exists_unique_fixed
admission_basis: escape-witness: exists_unique_fixed
Direct frozen dependencies: existing power-series suppliers at their original declaration addresses;
declaration identities and the elaborated dependency closure are reported in the handover.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19089.
Unbounded existence, uniqueness, and coefficient identities; no finite-instance computation.
Both Hanna mod-three modules use exists_unique_fixed.
-/

import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Invariants.ScaledReversionCongruence
import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence

set_option autoImplicit false
open PowerSeries
namespace D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Invariants.ScaledReversionCongruence

variable {R : Type*} [CommRing R]

/-- A strict coefficient contraction on normalized series has a unique fixed point. -/
theorem exists_unique_fixed
    (step : PowerSeries R → PowerSeries R)
    (h0 : ∀ f, constantCoeff f = 1 → constantCoeff (step f) = 1)
    (hc : ∀ {d : ℕ} {f g : PowerSeries R}, 1 ≤ d →
      constantCoeff f = 1 → constantCoeff g = 1 → Agree d f g →
      Agree (d + 1) (step f) (step g)) :
    ∃ f : PowerSeries R, constantCoeff f = 1 ∧ f = step f ∧
      ∀ g, constantCoeff g = 1 → g = step g → g = f := by
  let a : ℕ → PowerSeries R := Nat.rec (1 : PowerSeries R) (fun _ prev => step prev)
  have a0 (n : ℕ) : constantCoeff (a n) = 1 := by
    induction n with
    | zero => simp [a]
    | succ n ih => exact h0 _ ih
  have astable {d k : ℕ} (h : d ≤ k) : Agree (d + 1) (a d) (a k) := by
    induction d generalizing k with
    | zero =>
      intro n hn
      have : n = 0 := Nat.lt_one_iff.mp hn
      subst n
      simpa only [coeff_zero_eq_constantCoeff] using (a0 0).trans (a0 k).symm
    | succ d ih =>
      cases k with
      | zero => omega
      | succ k => exact hc (by omega) (a0 d) (a0 k) (ih (by omega))
  let f : PowerSeries R := mk fun n => coeff n (a n)
  have fa (d : ℕ) : Agree (d + 1) f (a d) := by
    intro n hn
    simpa only [f, coeff_mk] using astable (by omega : n ≤ d) n (by omega)
  have f0 : constantCoeff f = 1 := by
    have hh := fa 0 0 (by omega)
    simpa only [coeff_zero_eq_constantCoeff] using hh.trans (show coeff 0 (a 0) = 1 by simpa only [coeff_zero_eq_constantCoeff] using a0 0)
  have ff : f = step f := by
    ext n
    exact (fa (n + 1) n (by omega)).trans
      (hc (by omega : 1 ≤ n + 1) f0 (a0 n) (fa n) n (by omega)).symm
  refine ⟨f, f0, ff, ?_⟩
  intro g g0 gg
  have all (d : ℕ) : Agree (d + 1) g f := by
    induction d with
    | zero =>
      intro n hn
      have : n = 0 := Nat.lt_one_iff.mp hn
      subst n
      simpa only [coeff_zero_eq_constantCoeff] using g0.trans f0.symm
    | succ d ih => simpa only [← gg, ← ff] using hc (by omega : 1 ≤ d + 1) g0 f0 ih
  ext n
  exact all n n (by omega)


theorem geometric_zero : constantCoeff (geometric : PowerSeries R) = 0 := by
  simpa only [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius,
    rescale_one, RingHom.id_apply, geometric] using
    D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius_zero (1 : R)
theorem geometric_coeff (n : ℕ) (hn : 1 ≤ n) : coeff n (geometric : PowerSeries R) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change coeff (k + 1) ((X : PowerSeries R) * mk 1) = 1
  simp
theorem geometric_one : coeff 1 (geometric : PowerSeries R) = 1 := by
  exact geometric_coeff 1 (by decide)
theorem geometric_mul : (geometric : PowerSeries R) * (1 - X) = X := by
  have h :=
    D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius_denominator (1 : R)
  change D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius (1 : R) *
    (1 - C (1 : R) * X) = X at h
  simpa [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius,
    geometric, rescale_one] using h

theorem map_subst_pow {S : Type*} [CommRing S] (hom : R →+* S)
    (f : PowerSeries R) (k : ℕ) (hk : k ≠ 0) :
    PowerSeries.map hom (f.subst ((X : PowerSeries R) ^ k)) =
      (PowerSeries.map hom f).subst ((X : PowerSeries S) ^ k) := by
  have h := PowerSeries.map_subst (h := hom) (PowerSeries.HasSubst.X_pow hk) f
  change PowerSeries.map hom (f.subst ((X : PowerSeries R) ^ k)) =
    (PowerSeries.map hom f).subst (PowerSeries.map hom ((X : PowerSeries R) ^ k)) at h
  simpa only [map_pow, PowerSeries.map_X] using h

theorem geometric_subst_mul (k : ℕ) (hk : k ≠ 0) :
    (geometric : PowerSeries R).subst ((X : PowerSeries R) ^ k) *
      (1 - (X : PowerSeries R) ^ k) = (X : PowerSeries R) ^ k := by
  have hs : HasSubst ((X : PowerSeries R) ^ k) := .X_pow hk
  have hone : (1 : PowerSeries R).subst ((X : PowerSeries R) ^ k) = 1 := by
    simpa only [map_one] using (subst_C (a := (X : PowerSeries R) ^ k) (1 : R))
  have he := congrArg (subst ((X : PowerSeries R) ^ k)) (geometric_mul (R := R))
  rw [subst_mul hs, subst_sub hs, subst_X hs, hone] at he
  exact he


end D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

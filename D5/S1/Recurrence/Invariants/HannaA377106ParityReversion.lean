/- GID: D5/S1/Recurrence/Invariants/HannaA377106ParityReversion
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA377106ParityReversion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Normalized cubic substitution determines integer coefficients and dyadic parity. -/

/-
admission_basis: open-problem-resolution (#18788; Proved)
escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19794.
Published-owner audit targets: D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_mul; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_iff; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_pow; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_subst_order; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.power_two_one; https://github.com/the-omega-institute/trureturing/issues/19794.
The source predicates retain the recorded coefficient rings and normalizations.
The proof uses coefficient agreement and formal substitution over the displayed rings.
utility: none; no finite-instance refutation, enumeration, checker or numeric reduction.
Dependency identities are declaration statement_id values from the compiled Lean report.

F1: D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
  declaration: D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.Agree
  statement_id: sha256:18e60d106d70a7c2b4a1f20df01a2a3b5de4f15b8b0e181c4e59849d2e97d39e
F2: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: _private.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.0.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.Agree
  statement_id: sha256:e3cd9c09ab9c066077e3362c2145b9293441e263c1e4e0df7614ff40a3b1cb53
F3: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_iff
  statement_id: sha256:340430849ca0ad913c0aa0863bcccb92d33bd21aa50c3b412a8b3cef397f35ad
F4: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_subst_order
  statement_id: sha256:ead6f2eaafaae036370ac4584734f53ff96d7447845331c6fff0a1d1fe01facd
F5: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.powerTwoSeries
  statement_id: sha256:b8d06ca726de7b75ba200f87da476e9506036c6dab9e63f4421f4681357c960a
F6: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.power_two_one
  statement_id: sha256:931917eb317d34ddd1d65b2a394909dddf8191a1b7ed611ee52abeb23229117c
F7: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.power_two_zero
  statement_id: sha256:1294c542989f805f468158e6cbdaf12b7c07cbe1a88d0868854d1717c72163c4
F8: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst
  statement_id: sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795
F9: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.thue_series_equation
  statement_id: sha256:fc3ac63dd05e27bfd84403674dfaa5f427c0b485f4d8a16e79f6e39110349fe2

proof_shape: IsGF: bind-only
  consumers: claim, result
  direct_frozen_dependencies: none
proof_shape: claim: bind-only
  consumers: result
  direct_frozen_dependencies: none
proof_shape: map_solution: bind-only
  consumers: result
  direct_frozen_dependencies: none
proof_shape: result: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique
  consumers: settling conclusion
  direct_frozen_dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9
-/

import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality

/-! Integer lifting and reduction modulo two for the normalized cubic series. -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaA377106ParityReversion

open PowerSeries

/-- OEIS A377106: "G.f. A(x) satisfies A(x)^3 = A( x^3 + 9*x*A(x)^3 ), with A(0)=0, A'(0)=1." -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ A ^ 3 = PowerSeries.subst (X ^ 3 + 9 * X * A ^ 3) A

/-- OEIS A377106 (P. D. Hanna), conjecture: "a(n) is odd iff n = 2^k for some k >= 0", where
a(n) = [x^n] A(x), n ≥ 1 (offset 1). The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, coeff n A = m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k)

end D5.S1.Recurrence.Invariants.HannaA377106ParityReversion


open PowerSeries
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

namespace D5.S1.Recurrence.Invariants.HannaA377106ParityReversion
open D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General
private theorem map_solution {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) (hp : 0 < p) (c : R) (hom : R →+* S) (f : PowerSeries R)
    (he : f ^ p = f.subst (inner p c f)) :
    (f.map hom) ^ p = (f.map hom).subst (inner p (hom c) (f.map hom)) := by
  have h := congrArg (PowerSeries.map hom) he
  rw [map_pow, show PowerSeries.map hom (f.subst (inner p c f)) =
      (f.map hom).subst ((inner p c f).map hom) from
    map_subst (.of_constantCoeff_zero (inner_zero p hp c f)) f] at h
  simpa only [inner, map_add, map_mul, map_pow, map_X, map_C] using h
end D5.S1.Recurrence.Invariants.HannaA377106ParityReversion

namespace D5.S1.Recurrence.Invariants.HannaA377106ParityReversion
open D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

theorem result : claim := by
  classical
  obtain ⟨G, hG0, hG1, hG⟩ := exists_integral 3 (by decide) 9 (by norm_num)
  let hom := Int.castRingHom ℚ
  let A := G.map hom
  have hA0 : constantCoeff A = 0 := by
    exact Eq.symm (Rat.ext (id (Eq.symm hG0)) rfl)
  have hA1 : coeff 1 A = 1 := by
    exact Eq.symm (Rat.ext (id (Eq.symm hG1)) rfl)
  have hAe : A ^ 3 = A.subst (inner 3 (9 : ℚ) A) := by
    simpa [hom] using map_solution 3 (by decide) 9 hom G hG
  have hA : IsGF A := by simpa [IsGF, inner, map_ofNat] using And.intro hA0 (And.intro hA1 hAe)
  have hmod : G.map (Int.castRingHom (ZMod 2)) = powerTwoSeries := by
    let hom2 := Int.castRingHom (ZMod 2)
    have hz : constantCoeff (G.map hom2) = 0 := by
      change hom2 (constantCoeff G) = 0
      rw [hG0, map_zero]
    have h1 : coeff 1 (G.map hom2) = 1 := by simp [hG1]
    have he : (G.map hom2) ^ 3 = (G.map hom2).subst (inner 3 (1 : ZMod 2) (G.map hom2)) := by
      have h9 : hom2 (9 : ℤ) = 1 := by decide
      simpa only [h9] using map_solution 3 (by decide) 9 hom2 G hG
    have ht : powerTwoSeries ^ 3 = powerTwoSeries.subst (inner 3 (1 : ZMod 2) powerTwoSeries) := by
      simpa [inner] using thue_series_equation.2
    exact solution_unique (by decide : 2 ≤ 3) 1 (by decide : (3 : ZMod 2) ≠ 0)
      hz power_two_zero h1 power_two_one he ht
  refine ⟨⟨A, hA⟩, ?_⟩
  intro B hB n hn
  have hBA : B = A := by
    exact solution_unique (by decide : 2 ≤ 3) 9 (by norm_num : (3 : ℚ) ≠ 0)
      hB.1 hA0 hB.2.1 hA1 (by simpa [inner, map_ofNat] using hB.2.2) hAe
  rw [hBA]
  refine ⟨coeff n G, ?_, ?_⟩
  · rfl
  · have hc := congrArg (coeff n) hmod
    change ((coeff n G : ℤ) : ZMod 2) = coeff n powerTwoSeries at hc
    rw [← ZMod.intCast_eq_one_iff_odd, hc]
    simp only [powerTwoSeries, coeff_mk]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · exact ⟨fun he => (zero_ne_one he).elim, fun he => (h he).elim⟩
end D5.S1.Recurrence.Invariants.HannaA377106ParityReversion

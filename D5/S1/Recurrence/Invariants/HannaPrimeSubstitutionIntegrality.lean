/- GID: D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime Frobenius congruence gives integral normalized substitution solutions. -/

/-
admission_basis: open-problem-resolution (#18792; Proved)
escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_spec; D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_stable; D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted; D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limit_agree; D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique
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
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst
  statement_id: sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795

proof_shape: claim: bind-only
  consumers: result
  direct_frozen_dependencies: none
proof_shape: General.power_factor: bind-only
  consumers: General.agree_power_order, General.power_top
  direct_frozen_dependencies: F1, F2, F3
proof_shape: General.agree_power_order: bind-only
  consumers: General.inner_agree, General.residual_agree
  direct_frozen_dependencies: F1, F2, F3
proof_shape: General.power_top: bind-only
  consumers: General.residual_top
  direct_frozen_dependencies: F1, F2, F3
proof_shape: General.inner: bind-only
  consumers: General.inner_zero, General.inner_order, General.inner_agree, General.rhs_agree,
  General.residual, General.residual_agree, General.residual_top, General.residual_divisible,
  General.residual_base, General.solution_unique,
  D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.map_solution,
  D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result
  direct_frozen_dependencies: none
proof_shape: General.inner_zero: bind-only
  consumers: General.rhs_agree, General.residual_divisible, General.residual_base,
  D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.map_solution
  direct_frozen_dependencies: none
proof_shape: General.inner_order: bind-only
  consumers: General.rhs_agree
  direct_frozen_dependencies: none
proof_shape: General.inner_agree: bind-only
  consumers: General.rhs_agree
  direct_frozen_dependencies: F1, F2, F3
proof_shape: General.rhs_agree: bind-only
  consumers: General.residual_agree, General.residual_top
  direct_frozen_dependencies: F1, F2, F3, F4
proof_shape: General.residual: bind-only
  consumers: General.residual_agree, General.residual_top, General.residual_divisible,
  General.residual_base, General.exists_solution_of_correction, General.solution_unique,
  General.exists_integral
  direct_frozen_dependencies: none
proof_shape: General.residual_agree: bind-only
  consumers: General.exists_solution_of_correction
  direct_frozen_dependencies: F1, F2, F3, F4
proof_shape: General.residual_top: bind-only
  consumers: General.exists_solution_of_correction, General.solution_unique
  direct_frozen_dependencies: F1, F2, F3, F4
proof_shape: General.residual_divisible: bind-only
  consumers: General.exists_integral
  direct_frozen_dependencies: F5
proof_shape: General.Lifting.extend: bind-only
  consumers: General.Lifting.extend_agree, General.Lifting.approximation,
  General.Lifting.extend_spec, General.Lifting.approximation_spec,
  General.Lifting.approximation_stable
  direct_frozen_dependencies: none
proof_shape: General.Lifting.extend_agree: bind-only
  consumers: General.Lifting.extend_spec, General.Lifting.approximation_stable
  direct_frozen_dependencies: F1
proof_shape: General.Lifting.approximation: bind-only
  consumers: General.Lifting.approximation_spec, General.Lifting.approximation_stable,
  General.Lifting.limitSeries, General.Lifting.limit_agree, General.Lifting.exists_lifted
  direct_frozen_dependencies: none
proof_shape: General.Lifting.extend_spec: bind-only
  consumers: General.Lifting.approximation_spec
  direct_frozen_dependencies: F1
proof_shape: General.Lifting.approximation_spec: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_spec
  consumers: General.Lifting.exists_lifted
  direct_frozen_dependencies: F1
proof_shape: General.Lifting.approximation_stable: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_stable
  consumers: General.Lifting.limit_agree
  direct_frozen_dependencies: F1
proof_shape: General.Lifting.limitSeries: bind-only
  consumers: General.Lifting.limit_agree, General.Lifting.exists_lifted
  direct_frozen_dependencies: none
proof_shape: General.Lifting.limit_agree: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limit_agree
  consumers: General.Lifting.exists_lifted
  direct_frozen_dependencies: F1
proof_shape: General.Lifting.exists_lifted: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
  consumers: General.exists_solution_of_correction,
  D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_solution_of_correction
  direct_frozen_dependencies: F1
proof_shape: General.normal_of_agree: bind-only
  consumers: General.exists_solution_of_correction
  direct_frozen_dependencies: F1
proof_shape: General.residual_base: bind-only
  consumers: General.exists_solution_of_correction
  direct_frozen_dependencies: F1
proof_shape: General.exists_solution_of_correction: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
  consumers: General.exists_integral
  direct_frozen_dependencies: F1, F2, F3, F4
proof_shape: General.solution_unique: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique
  consumers: D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result
  direct_frozen_dependencies: F1, F2, F3, F4
proof_shape: General.exists_integral: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
  consumers: result, D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result
  direct_frozen_dependencies: F1, F2, F3, F4, F5
proof_shape: result: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
  consumers: settling conclusion
  direct_frozen_dependencies: F1, F2, F3, F4, F5
-/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

/-! Prime-exponent integral lifting and normalized formal-series uniqueness. -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality

open PowerSeries

/-- OEIS A271931, A271932, A271933 (P. D. Hanna), conjecture: "for prime p there exists an integer series
G(x) that satisfies: G(x) = G( x^p + p*x*G(x)^p )^(1/p) with G(0)=0, G'(0)=1". The p-th root is the one
with leading coefficient 1, so the equation is G(x)^p = G( x^p + p*x*G(x)^p ). -/
def claim : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ G : PowerSeries ℤ, constantCoeff G = 0 ∧ coeff 1 G = 1 ∧
      G ^ p = PowerSeries.subst (X ^ p + (p : PowerSeries ℤ) * X * G ^ p) G

end D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality


open PowerSeries
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (Agree)

namespace D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General
section Ring
variable {R : Type*} [CommRing R]

private theorem power_factor {n p : ℕ} (hp : 0 < p) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree n f g) :
    ∃ u v w : PowerSeries R, f = X * u ∧ g = X * v ∧
      f - g = X ^ n * w ∧
      f ^ p - g ^ p = X ^ (n + p - 1) *
        (w * ∑ i ∈ Finset.range p, u ^ i * v ^ (p - 1 - i)) := by
  classical
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr hf
  obtain ⟨v, hv⟩ := X_dvd_iff.mpr hg
  obtain ⟨w, hw⟩ := (agree_iff _ _ _).mp h
  refine ⟨u, v, w, hu, hv, hw, ?_⟩
  have hs : (∑ i ∈ Finset.range p, f ^ i * g ^ (p - 1 - i)) =
      X ^ (p - 1) * ∑ i ∈ Finset.range p, u ^ i * v ^ (p - 1 - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ p - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hi)
    rw [hu, hv, mul_pow, mul_pow]
    calc
      _ = (X ^ i * X ^ (p - 1 - i)) * (u ^ i * v ^ (p - 1 - i)) := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hi']
  rw [← geom_sum₂_mul, hs, hw]
  have hn : n + p - 1 = n + (p - 1) := Nat.add_sub_assoc hp n
  rw [hn, pow_add]
  ring

private theorem agree_power_order {n p : ℕ} (hp : 0 < p) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree n f g) : Agree (n + p - 1) (f ^ p) (g ^ p) := by
  obtain ⟨u, v, w, _, _, _, he⟩ := power_factor hp hf hg h
  exact (agree_iff _ _ _).mpr ⟨_, he⟩

private theorem power_top {n p : ℕ} (hp : 0 < p) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    coeff (n + p - 1) (f ^ p) - coeff (n + p - 1) (g ^ p) =
      (p : R) * (coeff n f - coeff n g) := by
  classical
  obtain ⟨u, v, w, hu, hv, hw, he⟩ := power_factor hp hf hg h
  have hu0 : constantCoeff u = 1 := by simpa [hu] using hf1
  have hv0 : constantCoeff v = 1 := by simpa [hv] using hg1
  have hc := congrArg (coeff (n + p - 1)) he
  have hd := congrArg (coeff n) hw
  simp only [map_sub, coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self,
    coeff_zero_eq_constantCoeff, map_mul, map_sum, map_pow, hu0, hv0,
    one_pow, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hc hd
  rw [hd]
  simpa [mul_comm] using hc
end Ring
end D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General

namespace D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General
section Ring
variable {R : Type*} [CommRing R]

noncomputable def inner (p : ℕ) (c : R) (f : PowerSeries R) : PowerSeries R :=
  X ^ p + C c * X * f ^ p

theorem inner_zero (p : ℕ) (hp : 0 < p) (c : R) (f : PowerSeries R) :
    constantCoeff (inner p c f) = 0 := by
  simp [inner, hp.ne']

private theorem inner_order {p : ℕ} (c : R) {f : PowerSeries R} (hf : constantCoeff f = 0) :
    (X : PowerSeries R) ^ p ∣ inner p c f := by
  apply dvd_add (dvd_refl _)
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) p) _

private theorem inner_agree {n p : ℕ} (hp : 0 < p) (c : R) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + p) (inner p c f) (inner p c g) := by
  apply (agree_iff _ _ _).mpr
  obtain ⟨w, hw⟩ := (agree_iff _ _ _).mp (agree_power_order hp hf hg h)
  refine ⟨C c * w, ?_⟩
  have he : inner p c f - inner p c g = C c * X * (f ^ p - g ^ p) := by dsimp [inner]; ring
  rw [he, hw]
  calc
    _ = X ^ ((n + p - 1) + 1) * (C c * w) := by rw [pow_succ]; ring
    _ = _ := by congr 2; omega

private theorem rhs_agree {n p : ℕ} (hp : 2 ≤ p) (c : R) {f g : PowerSeries R} (hn : 1 < n)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + p) (f.subst (inner p c f)) (g.subst (inner p c g)) := by
  exact agree_subst_order (inner_zero p (by omega) c f) (inner_zero p (by omega) c g)
    (inner_order c hf) (inner_order c hg) (by nlinarith) h (inner_agree (by omega) c hf hg h)

private noncomputable def residual (p : ℕ) (c : R) (f : PowerSeries R) : PowerSeries R :=
  f ^ p - f.subst (inner p c f)

private theorem residual_agree {n p : ℕ} (hp : 2 ≤ p) (c : R) {f g : PowerSeries R} (hn : 1 < n)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + p - 1) (residual p c f) (residual p c g) := by
  intro k hk
  simp only [residual, map_sub]
  rw [agree_power_order (by omega) hf hg h k hk,
    rhs_agree hp c hn hf hg h k (by omega)]

private theorem residual_top {n p : ℕ} (hp : 2 ≤ p) (c : R) {f g : PowerSeries R} (hn : 1 < n)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    coeff (n + p - 1) (residual p c f) - coeff (n + p - 1) (residual p c g) =
      (p : R) * (coeff n f - coeff n g) := by
  have hc := power_top (by omega : 0 < p) hf hg hf1 hg1 h
  have hr := rhs_agree hp c hn hf hg h (n + p - 1) (by omega)
  simp only [residual, map_sub]
  linear_combination hc - hr

end Ring

private theorem residual_divisible (p : ℕ) (hp : p.Prime) (c : ℤ) (hc : (p : ℤ) ∣ c)
    (f : PowerSeries ℤ) (n : ℕ) : (p : ℤ) ∣ coeff n (residual p c f) := by
  let : Fact p.Prime := ⟨hp⟩
  let hom := Int.castRingHom (ZMod p)
  have hc0 : hom c = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr hc
  have hi : (inner p c f).map hom = X ^ p := by
    simp only [inner, map_add, map_mul, map_pow, map_X, map_C, hc0, map_zero, zero_mul, add_zero]
  have he : (residual p c f).map hom = 0 := by
    simp only [residual, map_sub, map_pow]
    rw [show PowerSeries.map hom (f.subst (inner p c f)) =
        (f.map hom).subst ((inner p c f).map hom) from
      map_subst (.of_constantCoeff_zero (inner_zero p hp.pos c f)) _, hi,
      prime_power_subst, sub_self]
  have h := congrArg (coeff n) he
  simp only [coeff_map, map_zero, hom, Int.coe_castRingHom] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
end D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General

namespace D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General
namespace Lifting
variable {R : Type*} [CommRing R]
variable (F : PowerSeries R → PowerSeries R) (base : PowerSeries R) (n0 s : ℕ) (a : R) (q : R → R)

private noncomputable def extend (n : ℕ) (f : PowerSeries R) : PowerSeries R :=
  f + C (q (coeff (n + s) (F f))) * X ^ n

private theorem extend_agree (n : ℕ) (f : PowerSeries R) : Agree n (extend F s q n f) f := by
  intro k hk
  simp only [extend, map_add, coeff_C_mul_X_pow, ite_eq_right (show k ≠ n by omega), add_zero]

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => base
  | j + 1 => extend F s q (j + n0) (approximation j)

variable
  (hag : ∀ n, n0 ≤ n → ∀ f g, Agree n0 f base → Agree n0 g base →
    Agree n f g → Agree (n + s) (F f) (F g))
  (htop : ∀ n, n0 ≤ n → ∀ f g, Agree n0 f base → Agree n0 g base →
    Agree n f g → coeff (n + s) (F f) - coeff (n + s) (F g) =
      a * (coeff n f - coeff n g))
  (hdiv : ∀ f, Agree n0 f base → ∀ n, a * q (coeff n (F f)) = -coeff n (F f))
  (hbase : Agree (n0 + s) (F base) 0)

include hag htop hdiv in
private theorem extend_spec {n : ℕ} (hn : n0 ≤ n) {f : PowerSeries R}
    (hf : Agree n0 f base) (he : Agree (n + s) (F f) 0) :
    Agree n0 (extend F s q n f) base ∧ Agree (n + 1 + s) (F (extend F s q n f)) 0 := by
  have hz : Agree n0 (extend F s q n f) base :=
    fun k hk => (extend_agree F s q n f k (by omega)).trans (hf k hk)
  refine ⟨hz, ?_⟩
  have ht := htop n hn _ _ hz hf (extend_agree F s q n f)
  have hc : a * q (coeff (n + s) (F f)) = -coeff (n + s) (F f) := hdiv f hf (n + s)
  have hd : coeff n (extend F s q n f) - coeff n f = q (coeff (n + s) (F f)) := by
    simp only [extend, map_add, coeff_C_mul_X_pow, ↓reduceIte]
    ring
  rw [hd, hc] at ht
  intro k hk
  by_cases hkn : k < n + s
  · exact (hag n hn _ _ hz hf (extend_agree F s q n f) k hkn).trans (he k hkn)
  · have hk' : k = n + s :=
      Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt hkn)
        (by simpa only [Nat.add_right_comm n 1 s] using hk)
    subst k
    simp only [map_zero]
    linear_combination ht

include hag htop hdiv hbase in
private theorem approximation_spec (j : ℕ) :
    Agree n0 (approximation F base n0 s q j) base ∧
    Agree (j + n0 + s) (F (approximation F base n0 s q j)) 0 := by
  induction j with
  | zero =>
    constructor
    · intro k hk; rfl
    · simpa [approximation] using hbase
  | succ j ih =>
    simpa only [approximation, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      extend_spec F base n0 s a q hag htop hdiv (by omega : n0 ≤ j + n0) ih.1 ih.2

private theorem approximation_stable {j k : ℕ} (hjk : j ≤ k) :
    Agree (j + n0) (approximation F base n0 s q k) (approximation F base n0 s q j) := by
  induction k, hjk using Nat.le_induction with
  | base => intro i hi; rfl
  | succ k hk ih =>
    intro i hi
    exact (extend_agree F s q (k + n0) _ i (by omega)).trans (ih i hi)

private noncomputable def limitSeries : PowerSeries R :=
  mk fun n => coeff n (approximation F base n0 s q (n + 1))

private theorem limit_agree (j : ℕ) :
    Agree (j + n0) (limitSeries F base n0 s q) (approximation F base n0 s q j) := by
  intro n hn
  simp only [limitSeries, coeff_mk]
  by_cases hnj : n + 1 ≤ j
  · exact (approximation_stable F base n0 s q hnj n (by omega)).symm
  · exact approximation_stable F base n0 s q (by omega : j ≤ n + 1) n hn

include hag htop hdiv hbase in
theorem exists_lifted : ∃ f, Agree n0 f base ∧ F f = 0 := by
  have hz : Agree n0 (limitSeries F base n0 s q) base := by
    simpa [approximation] using limit_agree F base n0 s q 0
  refine ⟨limitSeries F base n0 s q, hz, ?_⟩
  ext n
  exact (hag (n + 1 + n0) (by omega) _ _ hz
      (approximation_spec F base n0 s a q hag htop hdiv hbase (n + 1)).1
      (limit_agree F base n0 s q (n + 1)) n (by omega)).trans
    ((approximation_spec F base n0 s a q hag htop hdiv hbase (n + 1)).2 n (by omega))

end Lifting
end D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General

namespace D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General
section Ring
variable {R : Type*} [CommRing R]

private theorem normal_of_agree {f : PowerSeries R} (h : Agree 2 f X) :
    constantCoeff f = 0 ∧ coeff 1 f = 1 := by
  constructor
  · simpa using h 0 (by decide)
  · simpa using h 1 (by decide)

private theorem residual_base (p : ℕ) (hp : 2 ≤ p) (c : R) :
    Agree (2 + (p - 1)) (residual p c X) 0 := by
  intro k hk
  simp only [map_zero]
  have hd : (X : PowerSeries R) ^ (p + 1) ∣ residual p c X := by
    refine ⟨-C c, ?_⟩
    simp only [residual]
    rw [subst_X (.of_constantCoeff_zero (inner_zero p (by omega) c X))]
    dsimp [inner]
    rw [pow_succ]
    ring
  exact X_pow_dvd_iff.mp hd k (by omega)

private theorem exists_solution_of_correction (p : ℕ) (hp : 2 ≤ p) (c : R) (q : R → R)
    (hq : ∀ f : PowerSeries R, Agree 2 f X → ∀ n,
      (p : R) * q (coeff n (residual p c f)) = -coeff n (residual p c f)) :
    ∃ f : PowerSeries R, constantCoeff f = 0 ∧ coeff 1 f = 1 ∧
      f ^ p = f.subst (X ^ p + C c * X * f ^ p) := by
  obtain ⟨f, hf, he⟩ := Lifting.exists_lifted (residual p c) X 2 (p - 1) (p : R) q
    (by
      intro n hn f g hf hg h
      have hf' := normal_of_agree hf
      have hg' := normal_of_agree hg
      simpa only [Nat.add_sub_assoc (by omega : 1 ≤ p)] using
        residual_agree hp c (by omega : 1 < n) hf'.1 hg'.1 h)
    (by
      intro n hn f g hf hg h
      have hf' := normal_of_agree hf
      have hg' := normal_of_agree hg
      simpa only [Nat.add_sub_assoc (by omega : 1 ≤ p)] using
        residual_top hp c (by omega : 1 < n) hf'.1 hg'.1 hf'.2 hg'.2 h)
    hq (residual_base p hp c)
  exact ⟨f, (normal_of_agree hf).1, (normal_of_agree hf).2, sub_eq_zero.mp he⟩

theorem solution_unique {p : ℕ} (hp : 2 ≤ p) (c : R) [NoZeroDivisors R]
    (hp0 : (p : R) ≠ 0) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : f ^ p = f.subst (inner p c f)) (he' : g ^ p = g.subst (inner p c g)) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff, hf] using hg.symm
    by_cases hn1 : n = 1
    · subst n
      exact hf1.trans hg1.symm
    have ht := residual_top hp c (by omega : 1 < n) hf hg hf1 hg1 ih
    have hr : residual p c f = 0 := sub_eq_zero.mpr he
    have hr' : residual p c g = 0 := sub_eq_zero.mpr he'
    rw [hr, hr', map_zero, sub_self] at ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht.symm).resolve_left hp0)
end Ring

theorem exists_integral (p : ℕ) (hp : p.Prime) (c : ℤ) (hc : (p : ℤ) ∣ c) :
    ∃ G : PowerSeries ℤ, constantCoeff G = 0 ∧ coeff 1 G = 1 ∧
      G ^ p = G.subst (X ^ p + C c * X * G ^ p) := by
  apply exists_solution_of_correction p hp.two_le c (fun t => -(t / (p : ℤ)))
  intro f hf n
  rw [mul_neg, Int.mul_ediv_cancel' (residual_divisible p hp c hc f n)]

end D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General

namespace D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality
theorem result : claim := by
  intro p hp
  simpa using D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_integral p hp p (dvd_refl _)
end D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality

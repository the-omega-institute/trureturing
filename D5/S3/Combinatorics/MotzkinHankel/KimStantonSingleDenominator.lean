/- GID: D5/S3/Combinatorics/MotzkinHankel/KimStantonSingleDenominator
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/KimStantonSingleDenominator
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer polynomial denominators of contiguous basic hypergeometric coefficients. -/

/-
proof_shape: per-declaration classifications below.
Classification: bind-only helpers are inlined in the compiled proof-term classification;
source helpers have actual consumers on the settling proof path.
escape_witness: KimStantonDenominatorCore.inverse_floor_bound
admission_basis: open-problem-resolution (#21469; Proved)
Protected-baseline frozen dependencies: none. The Core module is a same-delivery prerequisite;
its declaration identities are supplied by the scoped Lean report.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21724
Declarations: name | proof_shape | escape_witness | consumer(s).
gamma | bind-only | none | claim
claim | bind-only | none | result
parameters | bind-only | none | beta, beta_mem, parameters_mem, parameters_nonzero, parameters_succ, ratio_mem, u_recurrence
parameters_succ | bind-only | none | u_recurrence
beta | bind-only | none | beta_mem, ratio_mem, u_recurrence
parameters_mem | bind-only | none | beta_mem
parameters_nonzero | bind-only | none | u_recurrence
F_swap | bind-only | none | ratio_mem, u_recurrence
u_recurrence | bind-only | none | ratio_mem
beta_mem | bind-only | none | ratio_mem
ratio_mem | content | KimStantonDenominatorCore.recurrence_coefficients_mem | result
result | content | KimStantonDenominatorCore.inverse_floor_bound | settling result
-/

import D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonSingleDenominator
open D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

/-- The coefficient of the contiguous formal quotient. -/
def gamma (n : ℕ) : FractionRing (MvPolynomial (Fin 4) ℤ) :=
  PowerSeries.coeff n (F (a * q) b (c * q) q * (F a b c q)⁻¹)

/-- Kim–Stanton Conjecture 8.4. -/
def claim : Prop :=
  ∀ n : ℕ, ∃ P : MvPolynomial (Fin 4) ℤ,
    gamma n / (1 - c) = algebraMap (MvPolynomial (Fin 4) ℤ)
      (FractionRing (MvPolynomial (Fin 4) ℤ)) P / D n

open PowerSeries


private def parameters (m : ℕ) : (FractionRing (MvPolynomial (Fin 4) ℤ)) × (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  ((fun pair : (FractionRing (MvPolynomial (Fin 4) ℤ)) × (FractionRing (MvPolynomial (Fin 4) ℤ)) => (pair.2, pair.1 * q))^[m]) (a, b)

private theorem parameters_succ (m : ℕ) :
    parameters (m + 1) = ((parameters m).2, (parameters m).1 * q) := by
  simp only [parameters, Function.iterate_succ_apply']

private def beta (m : ℕ) : (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  (1 - (parameters m).2) * ((parameters m).1 - c * q ^ m) /
    ((1 - c * q ^ m) * (1 - c * q ^ (m + 1)))

private theorem parameters_mem (m : ℕ) : (parameters m).1 ∈ S ∧ (parameters m).2 ∈ S := by
  let E : Set ((FractionRing (MvPolynomial (Fin 4) ℤ)) × (FractionRing (MvPolynomial (Fin 4) ℤ))) :=
    {pair | pair.1 ∈ S ∧ pair.2 ∈ S}
  have step : Set.MapsTo (fun pair => (pair.2, pair.1 * q)) E E := by
    intro pair hpair
    exact ⟨hpair.2, S.mul_mem hpair.1 (S.algebraMap_mem _)⟩
  exact step.iterate m (show (a, b) ∈ E from ⟨S.algebraMap_mem _, S.algebraMap_mem _⟩)

private theorem parameters_nonzero (m : ℕ) :
    (∀ j : ℕ, 1 - (parameters m).1 * q ^ j ≠ 0) ∧
      (∀ j : ℕ, 1 - (parameters m).2 * q ^ j ≠ 0) := by
  let E : Set ((FractionRing (MvPolynomial (Fin 4) ℤ)) × (FractionRing (MvPolynomial (Fin 4) ℤ))) :=
    {pair | (∀ j : ℕ, 1 - pair.1 * q ^ j ≠ 0) ∧ (∀ j : ℕ, 1 - pair.2 * q ^ j ≠ 0)}
  have step : Set.MapsTo (fun pair => (pair.2, pair.1 * q)) E E := by
    intro pair hpair
    refine ⟨hpair.2, ?_⟩
    intro j
    simpa only [mul_assoc, ← pow_succ'] using hpair.1 (j + 1)
  exact step.iterate m (show (a, b) ∈ E from
    ⟨fun j => variable_factor_ne_zero 0 3 j, fun j => variable_factor_ne_zero 1 3 j⟩)

private theorem F_swap (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) : F A B C Q = F B A C Q := by
  ext n; simp only [F, coeff_mk, mul_comm]

private theorem u_recurrence (m : ℕ) :
    (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) m = (1 - PowerSeries.C (0 : (FractionRing (MvPolynomial (Fin 4) ℤ))) * X) * (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) (m + 1) -
      (PowerSeries.C (beta m) * X + PowerSeries.C (0 : (FractionRing (MvPolynomial (Fin 4) ℤ))) * X ^ 2) * (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) (m + 2) := by
  have ha : 1 - (parameters m).1 ≠ 0 := by simpa using (parameters_nonzero m).1 0
  have hb : 1 - (parameters m).2 ≠ 0 := by simpa using (parameters_nonzero m).2 0
  have hc : ∀ j : ℕ, 1 - (c * q ^ m) * q ^ j ≠ 0 := by
    intro j
    simpa only [c, q, mul_assoc, ← pow_add] using variable_factor_ne_zero 2 3 (m + j)
  have hq : ∀ j : ℕ, 1 - q ^ (j + 1) ≠ 0 :=
    fun j => one_sub_q_pow_ne_zero (j + 1) (by omega)
  have h := heine_contiguous (parameters m).1 (parameters m).2 (c * q ^ m) q ha hb hc hq
  have hshift : (c * q ^ m) * q = c * q ^ (m + 1) := by rw [pow_succ, mul_assoc]
  have hshift2 : (c * q ^ m) * q ^ 2 = c * q ^ (m + 2) := by rw [pow_add, mul_assoc]
  have hu1 : F ((parameters m).1 * q) (parameters m).2 ((c * q ^ m) * q) q = (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) (m + 1) := by
    dsimp only
    rw [F_swap, hshift, parameters_succ]
  have hu2 : F ((parameters m).1 * q) ((parameters m).2 * q) ((c * q ^ m) * q ^ 2) q = (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) (m + 2) := by
    dsimp only
    rw [hshift2, parameters_succ, parameters_succ]
  rw [hu1, hu2, hshift] at h
  change (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) (m + 1) - (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) m = PowerSeries.C (beta m) * X * (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) (m + 2) at h
  simp only [map_zero, zero_mul, sub_zero, one_mul, add_zero]
  linear_combination -h

private theorem beta_mem (m : ℕ) : beta m ∈ S := by
  have hc : c * q ^ m ∈ S :=
    S.mul_mem (S.algebraMap_mem _) (S.pow_mem (S.algebraMap_mem _) m)
  have hnum := S.mul_mem (S.sub_mem S.one_mem (parameters_mem m).2)
    (S.sub_mem (parameters_mem m).1 hc)
  have hd := S.mul_mem (S_inv_p m) (S_inv_p (m + 1))
  simpa only [beta, div_eq_mul_inv, mul_inv_rev, mul_comm] using S.mul_mem hnum hd

private theorem ratio_mem (n : ℕ) :
    coeff n (ratio (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 0 * MvPolynomial.X 3) (MvPolynomial.X 1)) ∈ S := by
  have h := D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore.quotient_coefficients_mem S.toSubring
    (fun m : ℕ => F (parameters m).1 (parameters m).2 (c * q ^ m) q) (fun _ => 0) beta (fun _ => 0)
    (fun m => F_constant _ _ _ _) (fun _ => S.zero_mem)
    beta_mem (fun _ => S.zero_mem) u_recurrence n 0
  simp only [parameters, Function.iterate_zero, Function.iterate_one, id_eq,
    Nat.zero_add, pow_zero, pow_one, mul_one] at h
  rw [F_swap b (a * q)] at h
  simpa only [ratio, map_mul, a, b, c, q, Subalgebra.mem_toSubring] using h

theorem result : claim := by
  simpa only [claim, gamma, ratio, map_mul, a, b, c, q] using
    denominator_from_localization (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 0 * MvPolynomial.X 3) (MvPolynomial.X 1) ratio_mem

end D5.S3.Combinatorics.MotzkinHankel.KimStantonSingleDenominator

end

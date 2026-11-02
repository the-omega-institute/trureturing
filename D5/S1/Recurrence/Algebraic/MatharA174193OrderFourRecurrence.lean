/- GID: D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Mathar's order-four recurrence for the algebraic series A174193. -/

/-
admission_basis: open-problem-resolution (#24106; Proved)
The public definitions retain the source polynomials and source-series equation.
The Euler operator is written as X * derivative, without a duplicate definition.
The proof uses Catalan, derivation and coefficient identities and polynomial normalization.
p: proof_shape: bind-only; escape_witness: none;
  consumers: D, IsSourceSeries, source_exists, p_ne, root_derivatives, certificate_P,
    certificate_B, root_certificate, inhomogeneous.
  Direct frozen dependencies: none.
P: proof_shape: bind-only; escape_witness: none;
  consumers: IsSourceSeries, source_exists, certificate_P, inhomogeneous.
  Direct frozen dependencies: none.
B: proof_shape: bind-only; escape_witness: none;
  consumers: IsSourceSeries, source_exists, certificate_B, root_certificate, inhomogeneous.
  Direct frozen dependencies: none.
D: proof_shape: bind-only; escape_witness: none;
  consumers: IsSourceSeries, source_exists, d_ne, certificate_P, certificate_B, root_certificate,
    inhomogeneous.
  Direct frozen dependencies: none.
IsSourceSeries: proof_shape: bind-only; escape_witness: none;
  consumers: claim, source_exists, inhomogeneous.
  Direct frozen dependencies: none.
claim: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies: none.
U: proof_shape: bind-only; escape_witness: none;
  consumers: certificate_P, certificate_B, root_certificate, inhomogeneous,
    recurrence_from_operator.
  Direct frozen dependencies: none.
V: proof_shape: bind-only; escape_witness: none;
  consumers: certificate_P, certificate_B, root_certificate, inhomogeneous,
    recurrence_from_operator.
  Direct frozen dependencies: none.
W: proof_shape: bind-only; escape_witness: none;
  consumers: certificate_P, certificate_B, root_certificate, inhomogeneous,
    recurrence_from_operator.
  Direct frozen dependencies: none.
H: proof_shape: bind-only; escape_witness: none;
  consumers: certificate_P, inhomogeneous, recurrence_from_operator.
  Direct frozen dependencies: none.
E: proof_shape: bind-only; escape_witness: none;
  consumers: K, quotient_euler, certificate_P, certificate_B, root_certificate, inhomogeneous.
  Direct frozen dependencies: none.
K: proof_shape: bind-only; escape_witness: none;
  consumers: quotient_euler, certificate_P, certificate_B, root_certificate, inhomogeneous.
  Direct frozen dependencies: none.
derivative_number: proof_shape: bind-only; escape_witness: none;
  consumers: root_derivatives, certificate_P, certificate_B.
  Direct frozen dependencies: none.
two_ne: proof_shape: bind-only; escape_witness: none;
  consumers: d_ne, root_derivatives.
  Direct frozen dependencies: none.
source_exists: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies: none.
p_ne: proof_shape: bind-only; escape_witness: none;
  consumers: d_ne, inhomogeneous.
  Direct frozen dependencies: none.
d_ne: proof_shape: bind-only; escape_witness: none;
  consumers: inhomogeneous.
  Direct frozen dependencies: none.
root_derivatives: proof_shape: bind-only; escape_witness: none;
  consumers: inhomogeneous.
  Direct frozen dependencies: none.
quotient_euler: proof_shape: bind-only; escape_witness: none;
  consumers: inhomogeneous.
  Direct frozen dependencies: none.
certificate_P: proof_shape: bind-only; escape_witness: none;
  consumers: inhomogeneous.
  Direct frozen dependencies: none.
certificate_B: proof_shape: bind-only; escape_witness: none;
  consumers: root_certificate.
  Direct frozen dependencies: none.
root_certificate: proof_shape: bind-only; escape_witness: none;
  consumers: inhomogeneous.
  Direct frozen dependencies: none.
inhomogeneous: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies: none.
recurrence_from_operator: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies: none.
result: proof_shape: bind-only; escape_witness: none;
  consumers: external problem settlement.
  Direct frozen dependencies:
    D5/S1/Recurrence/A308815DFiniteRecurrence.euler_coeff;
    declaration statement_id at the merged dev base (private owner before publication):
    sha256:43175d82732112d51569e1200b3589952abe53f0386a80441dbe65b5aded325e.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25507
-/

import D5.S1.Recurrence.A308815DFiniteRecurrence
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The specified algebraic series exists and satisfies Mathar's order-four recurrence. -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.MatharA174193OrderFourRecurrence

open PowerSeries

/-- The radicand in OEIS A174193. -/
noncomputable def p : PowerSeries ℚ := 1 - 4 * X

/-- The rational part of the displayed numerator. -/
noncomputable def P : PowerSeries ℚ :=
  1 - 8 * X + 13 * X ^ 2 + 24 * X ^ 3 - 48 * X ^ 4

/-- The polynomial multiplying the square root in the displayed numerator. -/
noncomputable def B : PowerSeries ℚ :=
  1 - 6 * X + X ^ 2 + 34 * X ^ 3 - 26 * X ^ 4 - 4 * X ^ 5

/-- The displayed denominator, before cancellation of X squared. -/
noncomputable def D : PowerSeries ℚ := 2 * X ^ 2 * (1 - X) * p ^ 2

/-- The formal branch with constant coefficient one, and the exact generating - function equation.
The multiplication equation avoids assigning a totalized inverse to the nonunit denominator. -/
def IsSourceSeries (A : PowerSeries ℚ) : Prop :=
  ∃ s : PowerSeries ℚ,
    constantCoeff s = 1 ∧ s ^ 2 = p ∧ D * A = P - B * s

/-- Existence is part of the claim. The recurrence ranges over every defined index n at least four. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsSourceSeries A) ∧
  ∀ A : PowerSeries ℚ, IsSourceSeries A → ∀ n : ℕ, 4 ≤ n →
    -((n : ℚ) + 2) * (404489 * (n : ℚ) - 1866368) * coeff n A
 + (3147815 * (n : ℚ) ^ 2 - 8680082 * (n : ℚ) - 14098754) * coeff (n - 1) A
 + 2 * (-2336439 * (n : ℚ) ^ 2 + 652022 * (n : ℚ) + 14514849) * coeff (n - 2) A
 + 8 * (-1044770 * (n : ℚ) ^ 2 + 10585023 * (n : ℚ) - 20370553) * coeff (n - 3) A
 + 8 * (642982 * (n : ℚ) - 2004177) * (2 * (n : ℚ) - 9) * coeff (n - 4) A = 0



set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

private noncomputable def U : PowerSeries ℚ :=
  (X - 1) * (4 * X - 1) * (2571928 * X ^ 2 + 1125370 * X - 404489)
private noncomputable def V : PowerSeries ℚ :=
  2 * (1970080 * X ^ 4 + 17265612 * X ^ 3 - 8693734 * X ^ 2 - 1192226 * X + 528695)
private noncomputable def W : PowerSeries ℚ :=
  -4542008 * X ^ 4 + 15852688 * X ^ 3 + 12946274 * X ^ 2 - 19631021 * X + 3732736
private noncomputable def H : PowerSeries ℚ :=
  4 * (677079 * X ^ 3 + 634434 * X ^ 2 - 3811346 * X + 933184)
private noncomputable def E (f d : PowerSeries ℚ) : PowerSeries ℚ := derivative f * d - f * derivative d
private noncomputable def K (f d : PowerSeries ℚ) : PowerSeries ℚ :=
  X * E f d * d + X ^ 2 * (derivative (E f d) * d - 2 * E f d * derivative d)

private theorem derivative_number (n : ℕ) [Nat.AtLeastTwo n] :
    derivative (ofNat(n) : PowerSeries ℚ) = 0 := by
  exact Derivation.map_natCast _ n

attribute [local simp] derivative_number

private theorem two_ne : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have hc := congrArg constantCoeff h
  norm_num only [map_ofNat, map_zero] at hc

private theorem source_exists : ∃ A : PowerSeries ℚ, IsSourceSeries A := by
  let c : PowerSeries ℚ := catalanSeries.map (Nat.castRingHom ℚ)
  have hc : c ^ 2 * X + 1 = c := by
    simpa [c] using congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      catalanSeries_sq_mul_X_add_one
  let s : PowerSeries ℚ := 1 - 2 * X * c
  have hs : s ^ 2 = p := by
    dsimp [s, p]
    linear_combination 4 * X * hc
  let q : PowerSeries ℚ := 2 * c ^ 2 + 12 - 10 * X - 22 * X ^ 2 + 4 * X ^ 3 +
    2 * (-6 + X + 34 * X ^ 2 - 26 * X ^ 3 - 4 * X ^ 4) * c
  have hn : P - B * s = X ^ 2 * q := by
    dsimp [P, B, s, q]
    linear_combination -2 * X * hc
  let d : PowerSeries ℚ := 2 * (1 - X) * p ^ 2
  have hd : d * d⁻¹ = 1 := PowerSeries.mul_inv_cancel d (by norm_num [d, p, map_ofNat])
  refine ⟨q * d⁻¹, s, by simp [s], hs, ?_⟩
  rw [hn]
  change (2 * X ^ 2 * (1 - X) * p ^ 2) * (q * d⁻¹) = X ^ 2 * q
  calc
    _ = X ^ 2 * q * (d * d⁻¹) := by dsimp [d]; ring
    _ = X ^ 2 * q := by rw [hd, mul_one]

private theorem p_ne : p ≠ 0 := by
  intro h
  have hc := congrArg constantCoeff h
  norm_num [p] at hc

private theorem d_ne : D ≠ 0 := by
  dsimp [D]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero two_ne
      exact pow_ne_zero _ X_ne_zero
    · intro h
      have hc := congrArg constantCoeff h
      norm_num at hc
  · exact pow_ne_zero _ p_ne

private theorem root_derivatives (s : PowerSeries ℚ) (hs : s ^ 2 = p) :
    p * derivative s = -2 * s ∧ p ^ 2 * derivative (derivative s) = -4 * s := by
  have h1 := congrArg (derivative (R := ℚ)) hs
  simp only [p, map_sub, Derivation.leibniz, derivative_pow, derivative_X,
    derivative_one, derivative_number, smul_eq_mul] at h1
  have hfirst : p * derivative s = -2 * s := by
    apply (mul_left_inj' two_ne).mp
    linear_combination s * h1 - 2 * derivative s * hs
  have h2 := congrArg (derivative (R := ℚ)) hfirst
  simp only [p, map_sub, map_neg, Derivation.leibniz, derivative_X,
    derivative_one, derivative_number, smul_eq_mul] at h2
  refine ⟨hfirst, ?_⟩
  dsimp only [p] at hfirst ⊢
  linear_combination (1 - 4 * X) * h2 + 2 * hfirst

private theorem quotient_euler (a f d : PowerSeries ℚ) (h : d * a = f) :
    d ^ 2 * (X * derivative a) = X * E f d ∧ d ^ 3 * (X * derivative (X * derivative a)) = K f d := by
  have h1 := congrArg (derivative (R := ℚ)) h
  simp only [Derivation.leibniz, smul_eq_mul] at h1
  have hfirst : d ^ 2 * (X * derivative a) = X * E f d := by
    dsimp [E]
    linear_combination X * d * h1 - X * derivative d * h
  have h2 := congrArg (derivative (R := ℚ)) hfirst
  simp only [Derivation.leibniz, derivative_pow, derivative_X, smul_eq_mul] at h2
  refine ⟨hfirst, ?_⟩
  dsimp only [K]
  simp only [Derivation.leibniz, derivative_X, smul_eq_mul]
  linear_combination X * d * h2 - 2 * X * derivative d * hfirst

private theorem certificate_P :
    U * K P D + V * X * E P D * D + W * P * D ^ 2 - H * D ^ 3 = 0 := by
  simp [K, E, P, D, p, U, V, W, H, Derivation.leibniz, smul_eq_mul]
  ring

private theorem certificate_B :
    U * p ^ 2 * K B D + (V * p ^ 2 - 4 * X * p * U) * X * E B D * D +
      (W * p ^ 2 - 2 * X * p * V - 2 * X * (1 - 2 * X) * U) * B * D ^ 2 = 0 := by
  simp [K, E, B, D, p, U, V, W, Derivation.leibniz, smul_eq_mul]
  ring

private theorem root_certificate (s : PowerSeries ℚ)
    (h1 : p * derivative s = -2 * s)
    (h2 : p ^ 2 * derivative (derivative s) = -4 * s) :
    p ^ 2 * (U * K (B * s) D + V * X * E (B * s) D * D + W * (B * s) * D ^ 2) = 0 := by
  have hb := certificate_B
  have ht :
      p ^ 2 * (U * K (B * s) D + V * X * E (B * s) D * D + W * (B * s) * D ^ 2) =
      s * (U * p ^ 2 * K B D + (V * p ^ 2 - 4 * X * p * U) * X * E B D * D +
        (W * p ^ 2 - 2 * X * p * V - 2 * X * (1 - 2 * X) * U) * B * D ^ 2) := by
    dsimp only [K, E]
    simp only [map_sub, map_add, Derivation.leibniz, smul_eq_mul]
    dsimp only [p] at h1 h2 ⊢
    linear_combination
      ((1 - 4 * X) * (2 * U * X ^ 2 * (derivative B * D - B * derivative D) * D +
        (U + V) * X * B * D ^ 2)) * h1 + (U * X ^ 2 * B * D ^ 2) * h2
  rw [ht, hb, mul_zero]

private theorem inhomogeneous (a : PowerSeries ℚ) (ha : IsSourceSeries a) :
    U * (X * derivative (X * derivative a)) + V * (X * derivative a) + W * a = H := by
  obtain ⟨s, hs0, hs, ha⟩ := ha
  obtain ⟨h1, h2⟩ := root_derivatives s hs
  obtain ⟨hq1, hq2⟩ := quotient_euler a (P - B * s) D ha
  have hr := root_certificate s h1 h2
  have hp := certificate_P
  have hc : p ^ 2 * D ^ 3 * (U * (X * derivative (X * derivative a)) + V * (X * derivative a) + W * a - H) = 0 := by
    have he : E (P - B * s) D = E P D - E (B * s) D := by
      simp only [E, map_sub]; ring
    have hk : K (P - B * s) D = K P D - K (B * s) D := by
      simp only [K, he, map_sub]; ring
    rw [he] at hq1
    rw [hk] at hq2
    linear_combination
      p ^ 2 * U * hq2 + p ^ 2 * V * D * hq1 + p ^ 2 * W * D ^ 2 * ha + p ^ 2 * hp - hr
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left
    (mul_ne_zero (pow_ne_zero _ p_ne) (pow_ne_zero _ d_ne)))

private theorem recurrence_from_operator (a : PowerSeries ℚ)
    (hop : U * (X * derivative (X * derivative a)) + V * (X * derivative a) + W * a = H)
    (ec : ∀ (f : PowerSeries ℚ) (k : ℕ), coeff k (X * derivative f) = (k : ℚ) * coeff k f)
    (n : ℕ) (hn : 4 ≤ n) :
    -((n : ℚ) + 2) * (404489 * (n : ℚ) - 1866368) * coeff n a
 + (3147815 * (n : ℚ) ^ 2 - 8680082 * (n : ℚ) - 14098754) * coeff (n - 1) a
 + 2 * (-2336439 * (n : ℚ) ^ 2 + 652022 * (n : ℚ) + 14514849) * coeff (n - 2) a
 + 8 * (-1044770 * (n : ℚ) ^ 2 + 10585023 * (n : ℚ) - 20370553) * coeff (n - 3) a
 + 8 * (642982 * (n : ℚ) - 2004177) * (2 * (n : ℚ) - 9) * coeff (n - 4) a = 0 := by
  have hexp : U * (X * derivative (X * derivative a)) + V * (X * derivative a) + W * a =
      (-404489 * (X * derivative (X * derivative a)) + 1057390 * (X * derivative a) + 3732736 * a) +
      X ^ 1 * (3147815 * (X * derivative (X * derivative a)) - 2384452 * (X * derivative a) - 19631021 * a) +
      X ^ 2 * (-4672878 * (X * derivative (X * derivative a)) - 17387468 * (X * derivative a) + 12946274 * a) +
      X ^ 3 * (-8358160 * (X * derivative (X * derivative a)) + 34531224 * (X * derivative a) + 15852688 * a) +
      X ^ 4 * (10287712 * (X * derivative (X * derivative a)) + 3940160 * (X * derivative a) - 4542008 * a) := by
    dsimp only [U, V, W]
    ring
  have hh : coeff n H = 0 := by
    have h0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
    have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by exact Ne.symm (Nat.ne_of_lt hn)
    simp [H, mul_add, mul_sub, coeff_X_pow, coeff_X, ← map_ofNat C 4,
      ← map_ofNat C 933184, coeff_C, h0, h1, h2, h3]
  rw [hexp] at hop
  have h := congrArg (coeff n) hop
  rw [hh] at h
  simp (disch := omega) only [map_add, map_sub, map_neg, neg_mul, coeff_ofNat_mul,
    coeff_X_pow_mul', ite_eq_left, ec] at h
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n)] at h
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h
  linear_combination h

theorem result : claim := by
  refine ⟨source_exists, ?_⟩
  intro a ha n hn
  refine recurrence_from_operator a (inhomogeneous a ha) ?_ n hn
  exact D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff

end D5.S1.Recurrence.Algebraic.MatharA174193OrderFourRecurrence

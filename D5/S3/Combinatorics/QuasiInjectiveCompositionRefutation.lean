/- GID: D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/QuasiInjectiveCompositionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.claim; result=D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.result; claim=D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.claim
   digest: Squaring followed by collapsing the squares is a quasi-injective pair whose composite is not. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QuasiInjectiveCompositionRefutation

/-
proof_shape: result: content
escape_witness: `sq_not_square`, that a positive multiple of a prime not dividing it is never a
  perfect square, together with `collapse_quasi`, that collapsing the squares leaves a
  quasi-injective function; neither is an instantiation, projection or normalisation of a
  pinned upstream statement, and the refutation rests on both.
admission_basis: open-problem-resolution (issue #9295)
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- `f` is quasi-injective: agreeing on the multiples of `a` and on the multiples of `b`
forces `a = b`. -/
def QuasiInjective (f : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → (∀ n : ℕ, 1 ≤ n → f (a * n) = f (b * n)) → a = b

/-- Squaring. -/
def square (n : ℕ) : ℕ := n * n

/-- Collapsing the perfect squares to one and fixing everything else. -/
def collapse (n : ℕ) : ℕ := if Nat.sqrt n * Nat.sqrt n = n then 1 else n

/-! ### A positive multiple of a large prime is not a square -/

private lemma not_square_prime_mul {a p : ℕ} (_ha : 1 ≤ a) (hp : p.Prime) (hpa : ¬ p ∣ a) :
    ∀ k : ℕ, k * k ≠ a * p := by
  intro k hk
  have hdvd : p ∣ k * k := ⟨a, by rw [hk]; ring⟩
  have hpk : p ∣ k := (Nat.Prime.dvd_mul hp).1 hdvd |>.elim id id
  obtain ⟨c, rfl⟩ := hpk
  have hp0 : 0 < p := hp.pos
  have h2 : p * (p * (c * c)) = p * a := by
    calc p * (p * (c * c)) = p * c * (p * c) := by ring
      _ = a * p := hk
      _ = p * a := by ring
  have ha' : p * (c * c) = a := Nat.eq_of_mul_eq_mul_left hp0 h2
  exact hpa ⟨c * c, ha'.symm⟩

private lemma collapse_of_not_square {n : ℕ} (h : ∀ k : ℕ, k * k ≠ n) : collapse n = n := by
  unfold collapse
  rw [if_neg]
  exact fun hc => h (Nat.sqrt n) hc

private lemma collapse_square (n : ℕ) : collapse (n * n) = 1 := by
  have hs : Nat.sqrt (n * n) = n := by
    rw [show n * n = n ^ 2 from by ring]
    exact Nat.sqrt_eq' n
  unfold collapse
  rw [if_pos (by rw [hs])]

/-! ### Both factors are quasi-injective -/

private lemma square_quasi : QuasiInjective square := by
  intro a b ha hb h
  have h1 := h 1 le_rfl
  simp only [square, Nat.mul_one] at h1
  exact Nat.mul_self_inj.mp h1

private lemma collapse_quasi : QuasiInjective collapse := by
  intro a b ha hb h
  by_contra hab
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (a * b + 1)
  have hab1 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpa : ¬ p ∣ a := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    have : a * 1 ≤ a * b := Nat.mul_le_mul_left a hb
    omega
  have hpb : ¬ p ∣ b := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    have : 1 * b ≤ a * b := Nat.mul_le_mul_right b ha
    omega
  have hna := collapse_of_not_square (not_square_prime_mul ha hp hpa)
  have hnb := collapse_of_not_square (not_square_prime_mul hb hp hpb)
  have hkey := h p (by omega)
  rw [hna, hnb] at hkey
  have : a = b := Nat.eq_of_mul_eq_mul_right (by omega) hkey
  exact hab this

/-! ### The composite is not quasi-injective -/

private lemma composite_const (n : ℕ) : (collapse ∘ square) n = 1 := by
  simp only [Function.comp_apply, square]
  exact collapse_square n

private lemma not_quasi_composite : ¬ QuasiInjective (collapse ∘ square) := by
  intro h
  have := h 1 2 (by omega) (by omega) (fun n _ => by rw [composite_const, composite_const])
  omega

/-! ### Question 19 -/

/-- The first question of Question 19 of Pongsriiam: is the composite of two quasi-injective
functions quasi-injective? -/
def claim : Prop :=
  ∀ f g : ℕ → ℕ, QuasiInjective f → QuasiInjective g → QuasiInjective (f ∘ g)

theorem result : ¬ claim := by
  intro h
  exact not_quasi_composite (h collapse square collapse_quasi square_quasi)

end D5.S3.Combinatorics.QuasiInjectiveCompositionRefutation

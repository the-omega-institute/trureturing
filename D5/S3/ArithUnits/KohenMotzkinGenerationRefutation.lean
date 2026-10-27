/- GID: D5/S3/ArithUnits/KohenMotzkinGenerationRefutation
   generality: I
   mirror-B: D5/B/S3/ArithUnits/KohenMotzkinGenerationRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithUnits/KohenMotzkinGenerationRefutation.claim; result=D5/S3/ArithUnits/KohenMotzkinGenerationRefutation.result; claim=D5/S3/ArithUnits/KohenMotzkinGenerationRefutation.claim
   digest: The unrestricted generalized trinomial residue generation conjecture is false. -/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.KohenMotzkinGenerationRefutation

/-- The integer Laurent polynomial whose powers define the source sequence. -/
noncomputable def step (a b : ℤ) : LaurentPolynomial ℤ :=
  LaurentPolynomial.C a * LaurentPolynomial.T (-1) + LaurentPolynomial.C b +
    LaurentPolynomial.C a * LaurentPolynomial.T 1

/-- The coefficient of exponent zero, taken over the integers before reduction. -/
noncomputable def central (a b : ℤ) (n : ℕ) : ℤ :=
  ((step a b) ^ n).coeff 0

/-- The first p residues, regarded as elements of the multiplicative unit group. -/
def generators (p : ℕ) (a b : ℤ) : Set (ZMod p)ˣ :=
  {u | ∃ n : ℕ, n < p ∧ (u : ZMod p) = (central a b n : ZMod p)}

/-- Conjecture 1 with all integer parameters and the full generated subgroup. -/
def claim : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∀ a b : ℤ,
    (∀ n : ℕ, n < p → ¬ (p : ℤ) ∣ central a b n) →
      Subgroup.closure (generators p a b) = ⊤

/-- At p = 3, a = 3 and b = 1 the residues generate only the identity subgroup. -/
theorem result : ¬ claim := by
  intro h
  have values : ∀ n : ℕ, n < 3 → central 3 1 n = if n = 2 then 19 else 1 := by
    intro n hn
    interval_cases n <;>
      norm_num [central, step, pow_two, add_mul, mul_add, LaurentPolynomial.C,
        LaurentPolynomial.T, AddMonoidAlgebra.single_mul_single,
        -LaurentPolynomial.single_eq_C_mul_T]
  have hnotdiv : ∀ n : ℕ, n < 3 → ¬ (3 : ℤ) ∣ central 3 1 n := by
    intro n hn
    rw [values n hn]
    split_ifs <;> norm_num
  have hgen := h 3 (by norm_num) 3 1 hnotdiv
  have hle : Subgroup.closure (generators 3 3 1) ≤ ⊥ := by
    apply (Subgroup.closure_le _).2
    rintro u ⟨n, hn, hu⟩
    apply Subgroup.mem_bot.mpr
    apply Units.ext
    change (u : ZMod 3) = 1
    rw [hu, values n hn]
    split_ifs <;> norm_num
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let u : (ZMod 3)ˣ := Units.mk0 2 (by norm_num)
  have hu : u ∈ Subgroup.closure (generators 3 3 1) := by
    rw [hgen]
    exact Subgroup.mem_top u
  have heq : u = 1 := Subgroup.mem_bot.mp (hle hu)
  have htwo := congrArg (fun v : (ZMod 3)ˣ => (v : ZMod 3)) heq
  norm_num [u] at htwo

end D5.S3.ArithUnits.KohenMotzkinGenerationRefutation

/- GID: D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeightedPolynomialSubstitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed cover-degree and coefficient-weight conservation for arbitrary polynomial substitution. -/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution

variable {σ τ R : Type*} [CommSemiring R]

/-- Every nonzero scalar coefficient has coefficient weight plus cover
degree equal to `N`. This also records that coefficients above `N` vanish. -/
def HasTotalWeight (w : τ → ℕ) (P : Polynomial (MvPolynomial τ R)) (N : ℕ) : Prop :=
  ∀ (r : ℕ) (d : τ →₀ ℕ), (P.coeff r).coeff d ≠ 0 →
    Finsupp.weight w d + r = N

namespace HasTotalWeight

variable {w : τ → ℕ} {P Q : Polynomial (MvPolynomial τ R)} {N M : ℕ}

private theorem zero (w : τ → ℕ) (N : ℕ) :
    HasTotalWeight w (0 : Polynomial (MvPolynomial τ R)) N := by
  intro r d hd
  exact (hd (by simp)).elim

private theorem add (hP : HasTotalWeight w P N) (hQ : HasTotalWeight w Q N) :
    HasTotalWeight w (P + Q) N := by
  intro r d hd
  by_cases h : (P.coeff r).coeff d = 0
  · apply hQ r d
    simpa only [Polynomial.coeff_add, MvPolynomial.coeff_add, h, zero_add] using hd
  · exact hP r d h

theorem C {p : MvPolynomial τ R}
    (hp : MvPolynomial.IsWeightedHomogeneous w p N) :
    HasTotalWeight w (Polynomial.C p) N := by
  intro r d hd
  by_cases hr : r = 0
  · subst r
    have hw := hp (by simpa only [Polynomial.coeff_C_zero] using hd)
    simpa only [Nat.add_zero] using hw
  · exact (hd (by simp [Polynomial.coeff_C, hr, Ne.symm hr])).elim

private theorem one (w : τ → ℕ) :
    HasTotalWeight w (1 : Polynomial (MvPolynomial τ R)) 0 := by
  simpa only [Polynomial.C_1] using
    (C (MvPolynomial.isWeightedHomogeneous_one R w))

theorem X_pow (w : τ → ℕ) (k : ℕ) :
    HasTotalWeight w (Polynomial.X ^ k : Polynomial (MvPolynomial τ R)) k := by
  intro r d hd
  by_cases hr : r = k
  · subst r
    have hz : (1 : MvPolynomial τ R).coeff d ≠ 0 := by
      simpa only [Polynomial.coeff_X_pow_self] using hd
    have hw := MvPolynomial.isWeightedHomogeneous_one R w hz
    simpa only [hw, Nat.zero_add]
  · exact (hd (by simp [Polynomial.coeff_X_pow, hr])).elim

theorem mul (hP : HasTotalWeight w P N) (hQ : HasTotalWeight w Q M) :
    HasTotalWeight w (P * Q) (N + M) := by
  classical
  intro r d hd
  rw [Polynomial.coeff_mul, MvPolynomial.coeff_sum] at hd
  obtain ⟨⟨i, j⟩, hij, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [MvPolynomial.coeff_mul] at hterm
  obtain ⟨⟨u, v⟩, huv, huvterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hterm
  have hP' := hP i u (left_ne_zero_of_mul huvterm)
  have hQ' := hQ j v (right_ne_zero_of_mul huvterm)
  have hij' : i + j = r := Finset.mem_antidiagonal.mp hij
  have huv' : u + v = d := Finset.mem_antidiagonal.mp huv
  rw [← huv', map_add]
  omega

private theorem pow (hP : HasTotalWeight w P N) (k : ℕ) :
    HasTotalWeight w (P ^ k) (k * N) := by
  induction k with
  | zero => simpa only [pow_zero, Nat.zero_mul] using one (R := R) w
  | succ k ih =>
    simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

private theorem sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial τ R))
    (N : ℕ) (hf : ∀ i ∈ s, HasTotalWeight w (f i) N) :
    HasTotalWeight w (∑ i ∈ s, f i) N := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa only [Finset.sum_empty] using zero (R := R) w N
  · intro i s hi ih hf
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial τ R))
    (n : ι → ℕ) (hf : ∀ i ∈ s, HasTotalWeight w (f i) (n i)) :
    HasTotalWeight w (∏ i ∈ s, f i) (∑ i ∈ s, n i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa only [Finset.prod_empty, Finset.sum_empty] using one (R := R) w
  · intro i s hi ih hf
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))



end HasTotalWeight

section Ring
variable {R : Type*} [CommRing R] {w : τ → ℕ}
  {P Q : Polynomial (MvPolynomial τ R)} {N : ℕ}

private theorem HasTotalWeight.neg (hP : HasTotalWeight w P N) :
    HasTotalWeight w (-P) N := by
  intro r d hd
  apply hP r d
  simpa only [Polynomial.coeff_neg, MvPolynomial.coeff_neg, ne_eq, neg_eq_zero] using hd

theorem HasTotalWeight.sub (hP : HasTotalWeight w P N) (hQ : HasTotalWeight w Q N) :
    HasTotalWeight w (P - Q) N := by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg

end Ring

/-- Natural-to-integer conversion preserves the exact monomial weight. -/
theorem weight_intCast (w : τ → ℕ) (d : τ →₀ ℕ) :
    Finsupp.weight (fun x => (w x : ℤ)) d = (Finsupp.weight w d : ℤ) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id,
    Nat.cast_sum, Nat.cast_mul]

theorem homogeneous_intCast {w : τ → ℕ} {p : MvPolynomial τ R} {N : ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous w p N) :
    MvPolynomial.IsWeightedHomogeneous (fun x => (w x : ℤ)) p (N : ℤ) := by
  intro d hd
  rw [weight_intCast, hp hd]

/-- Signed lowering has no truncated subtraction in its conclusion. If
`r > N`, the coefficient vanishes, rather than acquiring weight zero. -/
theorem HasTotalWeight.coeff_homogeneous_int {w : τ → ℕ}
    {P : Polynomial (MvPolynomial τ R)} {N : ℕ}
    (hP : HasTotalWeight w P N) (r : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun x => (w x : ℤ))
      (P.coeff r) ((N : ℤ) - r) := by
  intro d hd
  have h := hP r d hd
  have hc : (Finsupp.weight w d : ℤ) + (r : ℤ) = (N : ℤ) := by
    exact_mod_cast h
  rw [weight_intCast]
  omega

/-- Weighted substitution into a polynomial-valued algebra. Source and
coefficient variable types and weights may be different. -/
theorem eval2_totalWeight (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → Polynomial (MvPolynomial τ R))
    (hf : ∀ i, HasTotalWeight w (f i) (v i))
    (p : MvPolynomial σ R) (N : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous v p N) :
    HasTotalWeight w
      (MvPolynomial.eval₂ (algebraMap R (Polynomial (MvPolynomial τ R))) f p) N := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply HasTotalWeight.sum
  intro d hd
  have hw : Finsupp.weight v d = N := hp (MvPolynomial.mem_support_iff.mp hd)
  have hprod := HasTotalWeight.prod d.support (fun i => f i ^ d i)
    (fun i => d i * v i) (fun i _ => (hf i).pow (d i))
  have hprod' : HasTotalWeight w (∏ i ∈ d.support, f i ^ d i) N := by
    have hsum : (∑ i ∈ d.support, d i * v i) = N := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id] using hw
    simpa only [hsum] using hprod
  have hconstant : HasTotalWeight w
      ((algebraMap R (Polynomial (MvPolynomial τ R))) (p.coeff d)) 0 := by
    change HasTotalWeight w (Polynomial.C (MvPolynomial.C (p.coeff d))) 0
    exact HasTotalWeight.C (MvPolynomial.isWeightedHomogeneous_C w _)
  simpa only [Nat.zero_add] using hconstant.mul hprod'

end D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution

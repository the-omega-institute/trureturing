/- GID: D5/S1/Recurrence/PrimeSquareThickFactorObstruction
   generality: G
   mirror-B: none(waiver:all-coefficient-lift-obstruction)
   mirror-E: none(waiver:universal-intermediate-degree-range)
   anchors: []
   digest: No factor reducing to an intermediate power of X-1 divides X^p-1 modulo p squared. -/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.PrimeSquareThickFactorObstruction

open Polynomial

/-- Actual reduction of the prime-square coefficient ring. -/
def reduction (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)

/-- Two elements in the reduction kernel multiply to zero, including composite moduli. -/
private lemma kernel_mul_zero (p : ℕ) (x y : ZMod (p ^ 2))
    (hx : reduction p x = 0) (hy : reduction p y = 0) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  have ha0 : (a : ZMod p) = 0 := by simpa using hx
  have hb0 : (b : ZMod p) = 0 := by simpa using hy
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha0 hb0
  obtain ⟨u, hu⟩ := ha0
  obtain ⟨v, hv⟩ := hb0
  have hz : ((a * b : ℤ) : ZMod (p ^ 2)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨u * v, ?_⟩
    rw [hu, hv]
    push_cast
    ring
  simpa only [Int.cast_mul] using hz

private lemma repeated_root_jet {R : Type*} [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    eval (1 : R) ((X - 1 : R[X]) ^ n) = 0 ∧
      eval (1 : R) (derivative ((X - 1 : R[X]) ^ n)) = 0 := by
  have he : (X - 1 : R[X]) ^ n =
      (X - 1) ^ (n - 2) * ((X - 1) * (X - 1)) := by
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  constructor
  · rw [he]
    simp
  · rw [he]
    simp [derivative_mul]

private lemma reduced_jet (p n : ℕ) (f : (ZMod (p ^ 2))[X]) (hn : 2 ≤ n)
    (hf : f.map (reduction p) = (X - 1) ^ n) :
    reduction p (eval 1 f) = 0 ∧ reduction p (eval 1 (derivative f)) = 0 := by
  have hv := repeated_root_jet (R := ZMod p) n hn
  have h0 : eval 1 (f.map (reduction p)) = reduction p (eval 1 f) := by
    simpa using (Polynomial.eval_map_apply (p := f) (reduction p) (1 : ZMod (p ^ 2)))
  have h1 : eval 1 (derivative (f.map (reduction p))) =
      reduction p (eval 1 (derivative f)) := by
    rw [derivative_map]
    simpa using (Polynomial.eval_map_apply (p := derivative f)
      (reduction p) (1 : ZMod (p ^ 2)))
  rw [hf] at h0 h1
  exact ⟨h0.symm.trans hv.1, h1.symm.trans hv.2⟩

/-- No product with both reduced factors double at one can equal the p-th cyclotomic return.
The proof uses the square-zero kernel and the nonzero first derivative p modulo p squared. -/
theorem no_thick_product (p d e : ℕ) (hp : p.Prime)
    (hd : 2 ≤ d) (he : 2 ≤ e) (f g : (ZMod (p ^ 2))[X])
    (hf : f.map (reduction p) = (X - 1) ^ d)
    (hg : g.map (reduction p) = (X - 1) ^ e) :
    f * g ≠ X ^ p - 1 := by
  obtain ⟨hf0, hf1⟩ := reduced_jet p d f hd hf
  obtain ⟨hg0, hg1⟩ := reduced_jet p e g he hg
  have hj : eval 1 (derivative (f * g)) = 0 := by
    rw [derivative_mul, eval_add, eval_mul, eval_mul,
      kernel_mul_zero p _ _ hf1 hg0, kernel_mul_zero p _ _ hf0 hg1, add_zero]
  intro hfg
  rw [hfg] at hj
  have hpzero : (p : ZMod (p ^ 2)) = 0 := by
    simpa [derivative_sub, derivative_X_pow] using hj
  have hdiv : p ^ 2 ∣ p := (ZMod.natCast_eq_zero_iff p (p ^ 2)).mp hpzero
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdiv
  have hpge := hp.two_le
  nlinarith

/-- Complete obstruction for every lifted coefficient choice; no monicity assumption is needed. -/
theorem intermediate_factor_not_dvd (p d : ℕ) (hp : p.Prime)
    (hd : 2 ≤ d) (hdegree : d + 2 ≤ p) (f : (ZMod (p ^ 2))[X])
    (hf : f.map (reduction p) = (X - 1) ^ d) :
    ¬ f ∣ X ^ p - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hdiv
  obtain ⟨g, hfg⟩ := hdiv
  have hfrob : ((X - 1 : (ZMod p)[X]) ^ p) = X ^ p - 1 := by
    simpa only [frobenius_def, one_pow] using
      (map_sub (frobenius ((ZMod p)[X]) p) (X : (ZMod p)[X]) 1)
  have hnonzero : (X - 1 : (ZMod p)[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 1) h
    simpa using hc
  have hg : g.map (reduction p) = (X - 1) ^ (p - d) := by
    apply mul_left_cancel₀ (pow_ne_zero d hnonzero)
    calc
      (X - 1) ^ d * g.map (reduction p) = X ^ p - 1 := by
        simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_one, hf] using
            congrArg (fun P => P.map (reduction p)) hfg.symm
      _ = (X - 1) ^ p := hfrob.symm
      _ = (X - 1) ^ d * (X - 1) ^ (p - d) := by
        rw [← pow_add, Nat.add_sub_of_le (show d ≤ p by omega)]
  exact no_thick_product p d (p - d) hp hd (by omega) f g hf hg hfg.symm

/-- The quadratic branch of the 2026 multiple-root proposal fails for every p at least five. -/
theorem quadratic_lift_not_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (f : (ZMod (p ^ 2))[X]) (hf : f.map (reduction p) = (X - 1) ^ 2) :
    ¬ f ∣ X ^ p - 1 :=
  intermediate_factor_not_dvd p 2 hp (by omega) (by omega) f hf

/-- A sharp boundary witness: the complementary exponent is only one at p=3. -/
theorem cubic_boundary_lift :
    (X ^ 2 + X + 1 : (ZMod 9)[X]) ∣ X ^ 3 - 1 := by
  refine ⟨X - 1, ?_⟩
  ring

end D5.S1.Recurrence.PrimeSquareThickFactorObstruction

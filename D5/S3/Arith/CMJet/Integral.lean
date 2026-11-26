/- GID: D5/S3/Arith/CMJet/Integral
   generality: G
   mirror-B: none(waiver:cm-jet-native-arithmetic)
   mirror-E: none(waiver:cm-jet-native-arithmetic)
   anchors: []
   utility: none
   digest: Reduction modulo p lifts inert divisibility to an actual integral endomorphism and repeated jet divisibility. -/

import D5.S3.Arith.CMJet.Prime
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.GCD.BigOperators

/-! Coefficient reduction, the integral prime operator, and the complete row. -/

noncomputable section

namespace D5.S3.Arith.CMJet

open Polynomial Finset Function
open scoped Polynomial BigOperators

def reduce (p : ℕ) (z : Curve ℤ) : Curve (ZMod p) :=
  ⟨z.re.map (Int.castRingHom (ZMod p)), z.im.map (Int.castRingHom (ZMod p))⟩

lemma reduce_D (p : ℕ) (z : Curve ℤ) :
    reduce p (D ℤ z) = D (ZMod p) (reduce p z) := by
  apply QuadraticAlgebra.ext
  · change (W ℤ * z.im.derivative - 2 * X ^ 3 * z.im).map _ =
      W (ZMod p) * (z.im.map _).derivative - 2 * X ^ 3 * z.im.map _
    simp [W, Polynomial.derivative_map]
  · change z.re.derivative.map _ = (z.re.map _).derivative
    exact (Polynomial.derivative_map _ _).symm

lemma reduce_iter (p n : ℕ) (z : Curve ℤ) :
    reduce p (iter n z) = iter n (reduce p z) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iter_succ, iter_succ, reduce_D, ih]

lemma reduce_poly_X_pow (p r : ℕ) :
    reduce p (poly (X ^ r : ℤ[X])) = poly (X ^ r : (ZMod p)[X]) := by
  apply QuadraticAlgebra.ext
  · change (X ^ r : ℤ[X]).map (Int.castRingHom (ZMod p)) = X ^ r
    simp
  · dsimp [reduce, poly]
    simp

lemma reduce_atO (p : ℕ) (z : Curve ℤ) : (↑(atO z) : ZMod p) = atO (reduce p z) := by
  simp [reduce, Polynomial.coeff_map]

lemma reduce_eq_zero_iff (p : ℕ) (z : Curve ℤ) :
    reduce p z = 0 ↔ ∃ w : Curve ℤ, z = (p : ℤ) • w := by
  constructor
  · intro h
    have hcoeff (f : ℤ[X]) (hf : f.map (Int.castRingHom (ZMod p)) = 0) :
        C (p : ℤ) ∣ f := by
      apply (C_dvd_iff_dvd_coeff _ _).mpr
      intro k
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa [Polynomial.coeff_map] using congrArg (fun g : (ZMod p)[X] => g.coeff k) hf
    obtain ⟨f, hf⟩ := hcoeff z.re (by simpa [reduce] using congrArg QuadraticAlgebra.re h)
    obtain ⟨g, hg⟩ := hcoeff z.im (by simpa [reduce] using congrArg QuadraticAlgebra.im h)
    refine ⟨⟨f, g⟩, QuadraticAlgebra.ext ?_ ?_⟩
    · simpa [Polynomial.smul_eq_C_mul] using hf
    · simpa [Polynomial.smul_eq_C_mul] using hg
  · rintro ⟨w, rfl⟩
    have hp : (↑(p : ℤ) : ZMod p) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_refl _)
    apply QuadraticAlgebra.ext <;>
      simp [reduce, Polynomial.smul_eq_C_mul, hp, ZMod.natCast_self]

lemma int_smul_injective {d : ℤ} (hd : d ≠ 0) :
    Injective (fun z : Curve ℤ => d • z) := by
  have hC : (C d : ℤ[X]) ≠ 0 := by simpa using hd
  intro u v h
  apply QuadraticAlgebra.ext
  · apply mul_left_cancel₀ hC
    simpa [Polynomial.smul_eq_C_mul] using congrArg QuadraticAlgebra.re h
  · apply mul_left_cancel₀ hC
    simpa [Polynomial.smul_eq_C_mul] using congrArg QuadraticAlgebra.im h

variable {p : ℕ} [Fact p.Prime]

private lemma inert_has_quotient (hp : p % 4 = 3) (z : Curve ℤ) :
    ∃ w : Curve ℤ, iter p z = (p : ℤ) • w := by
  apply (reduce_eq_zero_iff p _).mp
  rw [reduce_iter, inert_iter_zero hp]

theorem inert_quotient_unique (hp : p % 4 = 3) (z : Curve ℤ) :
    ∃! w : Curve ℤ, iter p z = (p : ℤ) • w := by
  obtain ⟨w, hw⟩ := inert_has_quotient hp z
  refine ⟨w, hw, fun v hv => ?_⟩
  exact int_smul_injective (by omega : (p : ℤ) ≠ 0) (hv.symm.trans hw)

/-- The integral endomorphism obtained by dividing \(D^p\) by \(p\). -/
noncomputable def inertLift (hp : p % 4 = 3) : Module.End ℤ (Curve ℤ) where
  toFun z := Classical.choose (inert_has_quotient hp z)
  map_add' u v := by
    apply int_smul_injective (by omega : (p : ℤ) ≠ 0)
    change (p : ℤ) • Classical.choose (inert_has_quotient hp (u + v)) =
      (p : ℤ) • (Classical.choose (inert_has_quotient hp u) +
        Classical.choose (inert_has_quotient hp v))
    rw [← Classical.choose_spec (inert_has_quotient hp (u + v)), smul_add,
      ← Classical.choose_spec (inert_has_quotient hp u),
      ← Classical.choose_spec (inert_has_quotient hp v), map_add]
  map_smul' a z := by
    change Classical.choose (inert_has_quotient hp (a • z)) =
      a • Classical.choose (inert_has_quotient hp z)
    apply int_smul_injective (by omega : (p : ℤ) ≠ 0)
    change (p : ℤ) • Classical.choose (inert_has_quotient hp (a • z)) =
      (p : ℤ) • (a • Classical.choose (inert_has_quotient hp z))
    rw [← Classical.choose_spec (inert_has_quotient hp (a • z)), smul_comm (p : ℤ) a,
      ← Classical.choose_spec (inert_has_quotient hp z), map_smul]

lemma inertLift_spec (hp : p % 4 = 3) (z : Curve ℤ) :
    iter p z = (p : ℤ) • inertLift hp z :=
  Classical.choose_spec (inert_has_quotient hp z)

/-- The operator identity on every integral polynomial pair for any derivative order. -/
theorem iter_eq_inertLift (hp : p % 4 = 3) (N : ℕ) (z : Curve ℤ) :
    iter N z = (p : ℤ) ^ (N / p) • (inertLift hp)^[N / p] (iter (N % p) z) := by
  have hblock (k : ℕ) (w : Curve ℤ) : iter (p * k) w =
      (p : ℤ) ^ k • (inertLift hp)^[k] w := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show p * (k + 1) = p + p * k by ring, iter_add, ih, map_smul, inertLift_spec hp,
          Function.iterate_succ_apply', pow_succ, mul_smul]
  calc
    iter N z = iter (p * (N / p) + N % p) z := by
      have hdecomp : p * (N / p) + N % p = N := by
        exact Nat.div_add_mod N p
      rw [hdecomp]
    _ = _ := by rw [iter_add, hblock]

theorem inert_dvd_jet (hp : p % 4 = 3) (N : ℕ) (z : Curve ℤ) :
    (p : ℤ) ^ (N / p) ∣ atO (iter N z) := by
  rw [iter_eq_inertLift hp, map_smul]
  exact dvd_mul_right _ _

def order (m : ℕ) : ℕ := 4 * m + 1

def row (m : ℕ) (j : Fin (m + 1)) : ℤ :=
  atO (iter (order m) (poly (X ^ (4 * (j : ℕ) + 1) : ℤ[X])))

def content (m : ℕ) : ℕ := univ.gcd (fun j : Fin (m + 1) => (row m j).natAbs)

lemma row_coeff (m : ℕ) (j : Fin (m + 1)) :
    row m j = (Q^[2 * m] (X ^ (4 * (j : ℕ) + 1) : ℤ[X])).coeff 1 := by
  unfold row order
  have he : 4 * m + 1 = 2 * (2 * m) + 1 := by omega
  exact (congrArg (fun n => atO (iter n (poly (X ^ (4 * (j : ℕ) + 1) : ℤ[X])))) he).trans
    (odd_jet _ _)

/-- The complete row accounts for every monomial that can contribute to this jet. -/
theorem jet_monomial_outside_row (m r : ℕ) (h : order m < r ∨ r % 4 ≠ 1) :
    atO (iter (order m) (poly (X ^ r : ℤ[X]))) = 0 := by
  rw [order, show 4*m + 1 = 2*(2*m) + 1 by omega, odd_jet]
  rcases h with h | h
  · exact Q_iter_low _ _ _ (by unfold order at h; omega)
  · exact Q_iter_monomial_support _ _ _ (by omega)

/-- The last column is \(N!\). -/
theorem row_last (m : ℕ) : row m (Fin.last m) = ↑(order m).factorial := by
  simpa [row, order, show 2 * (2 * m) + 1 = 4 * m + 1 by omega] using (odd_top_jet (A := ℤ) (2 * m))

theorem dvd_content_iff (m d : ℕ) :
    d ∣ content m ↔ ∀ j : Fin (m + 1), (d : ℤ) ∣ row m j := by
  simp only [content, Finset.dvd_gcd_iff, mem_univ, true_implies]
  constructor <;> intro h j
  · exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (h j))
  · exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (h j))

theorem content_dvd_factorial (m : ℕ) : content m ∣ (order m).factorial := by
  have h := Finset.gcd_dvd (f := fun j : Fin (m + 1) => (row m j).natAbs)
    (Finset.mem_univ (Fin.last m))
  simpa [content, row_last] using h

theorem content_pos (m : ℕ) : 0 < content m :=
  Nat.pos_of_dvd_of_pos (content_dvd_factorial m) (Nat.factorial_pos _)

theorem inert_dvd_content (hp : p % 4 = 3) (m : ℕ) :
    p ^ (order m / p) ∣ content m := by
  apply (dvd_content_iff _ _).mpr
  intro j
  simpa [row] using inert_dvd_jet hp (order m) (poly (X ^ (4 * (j : ℕ) + 1) : ℤ[X]))

end D5.S3.Arith.CMJet

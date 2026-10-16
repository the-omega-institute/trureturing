/- GID: D5/S3/ConceptDynamics/Coding/LocalizedCocycle
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/LocalizedCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clearing denominators transfers integer polynomial values modulo three. -/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic

noncomputable section
namespace SourceOnlyLocalizedCocycle

open MvPolynomial

/- Integer evaluations are hypotheses at BOTH tuples. No reduction of the
   rational coefficients into ZMod is attempted. -/
theorem integerValues_mod_three {σ : Type*}
    (P : MvPolynomial σ ℚ) (Q : MvPolynomial σ ℤ)
    (D : ℤ) (hD : D ≠ 0) (e : ℕ) (he : padicValInt 3 D ≤ e)
    (hclear : Q.map (Int.castRingHom ℚ) = C (D : ℚ) * P)
    (x y : σ → ℤ) (a b : ℤ)
    (ha : eval (fun i => (x i : ℚ)) P = (a : ℚ))
    (hb : eval (fun i => (y i : ℚ)) P = (b : ℚ))
    (hxy : ∀ i, (x i : ZMod (3 ^ (e + 1))) = (y i : ZMod (3 ^ (e + 1)))) :
    (a : ZMod 3) = (b : ZMod 3) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hscaled (z : σ → ℤ) (c : ℤ)
      (hc : eval (fun i => (z i : ℚ)) P = (c : ℚ)) : eval z Q = D * c := by
    have hq : (eval z Q : ℚ) = (D : ℚ) * (c : ℚ) := by
      calc
        (eval z Q : ℚ) =
            eval (fun i => (z i : ℚ)) (Q.map (Int.castRingHom ℚ)) := by
          rw [MvPolynomial.eval_map]
          exact MvPolynomial.eval₂_comp (Int.castRingHom ℚ) z Q
        _ = (D : ℚ) * (c : ℚ) := by
          rw [hclear, map_mul, MvPolynomial.eval_C, hc]
    exact_mod_cast hq
  have hfun : (fun i => (x i : ZMod (3 ^ (e + 1)))) =
      (fun i => (y i : ZMod (3 ^ (e + 1)))) := funext hxy
  have hcast : (eval x Q : ZMod (3 ^ (e + 1))) =
      (eval y Q : ZMod (3 ^ (e + 1))) := by
    change (Int.castRingHom (ZMod (3 ^ (e + 1)))) (eval x Q) =
      (Int.castRingHom (ZMod (3 ^ (e + 1)))) (eval y Q)
    rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
    exact congrArg
      (fun z => eval z (Q.map (Int.castRingHom (ZMod (3 ^ (e + 1)))))) hfun
  have hmod := (ZMod.intCast_eq_intCast_iff (eval x Q) (eval y Q)
    (3 ^ (e + 1))).mp hcast
  have hdiv : (3 : ℤ) ^ (e + 1) ∣ D * (b - a) := by
    have hd := hmod.dvd
    rw [hscaled x a ha, hscaled y b hb] at hd
    simpa only [← mul_sub, Nat.cast_pow, Nat.cast_ofNat] using hd
  apply (ZMod.intCast_eq_intCast_iff a b 3).mpr
  apply Int.modEq_iff_dvd.mpr
  by_cases hz : b - a = 0
  · rw [hz]
    exact dvd_zero _
  · have hp : D * (b - a) ≠ 0 := mul_ne_zero hD hz
    have hv := ((padicValInt_dvd_iff (p := 3) (e + 1) (D * (b - a))).mp
      hdiv).resolve_left hp
    rw [padicValInt.mul hD hz] at hv
    have hone : 1 ≤ padicValInt 3 (b - a) := by omega
    simpa only [pow_one] using
      (padicValInt_dvd_iff (p := 3) 1 (b - a)).mpr (Or.inr hone)

/- Dyadic reduction via the universal property of localization, consumed by
   the canonical rectangular cochain.
-/
theorem dyadicReduction (e : ℕ) :
    ∃ rho : Localization.Away (2 : ℤ) →+* ZMod (3 ^ (e + 1)),
      ∀ z : ℤ, rho (algebraMap ℤ (Localization.Away (2 : ℤ)) z) =
        (z : ZMod (3 ^ (e + 1))) := by
  have htwo : IsUnit (2 : ZMod (3 ^ (e + 1))) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow
      (by decide : Nat.Prime 3) (Nat.succ_pos e)).mpr (by norm_num)
  let rho : Localization.Away (2 : ℤ) →+* ZMod (3 ^ (e + 1)) :=
    Localization.awayLift (Int.castRingHom (ZMod (3 ^ (e + 1)))) (2 : ℤ)
      (by simpa using htwo)
  refine ⟨rho, ?_⟩
  intro z
  exact IsLocalization.Away.lift_eq (2 : ℤ) (by simpa using htwo) z

end SourceOnlyLocalizedCocycle

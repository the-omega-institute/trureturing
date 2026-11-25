/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Specialization of the monic literal jet. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformHermiteLiteralJet
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformCollisionTaylor
import Mathlib.Tactic.LinearCombination

/-! Monic literal power remainders across split and colliding transfer weights. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.HorizontalNativeU

open Polynomial
open scoped Polynomial Matrix

noncomputable section

/-- The literal frozen jet is formed by monic division, so every coefficient
specializes at coinciding nodes. -/
def literalJetRemainder {R : Type*} [CommRing R] (v : Fin 4 → R) (m : ℕ) : R[X] :=
  X ^ m %ₘ ((∏ i, (X - C (v i))) ^ 2)

theorem literalJetRemainder_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Fin 4 → R) (m : ℕ) :
    (literalJetRemainder v m).map f = literalJetRemainder (f ∘ v) m := by
  unfold literalJetRemainder
  rw [map_modByMonic]
  · simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_C, Function.comp_apply]
  · exact (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (v i)).pow 2

theorem literalJetRemainder_eq_hermite {F : Type*} [Field F]
    (v : Fin 4 → F) (hv : Function.Injective v) (m : ℕ) :
    literalJetRemainder v m =
      PeriodicMPSUniformHermiteLiteralJet.hermite Finset.univ v (fun i => v i ^ m)
        (fun i => (m : F) * v i ^ (m - 1)) := by
  symm
  simpa only [literalJetRemainder, Lagrange.nodal_eq, eval_pow, eval_X, derivative_X_pow,
    eval_mul, eval_C] using
    PeriodicMPSUniformHermiteLiteralJet.hermite_eq_modByMonic (s := Finset.univ)
      (fun i _ j _ hij => hv hij) (X ^ m : F[X])

def collisionJet {F : Type*} [CommRing F] (m : ℕ) : F[X] :=
  ∑ s ∈ Finset.range 8, C (m.choose s : F) * (C 4 * X - 1) ^ s

theorem collisionJet_eq_scaled_remainder {F : Type*} [Field F] [CharZero F] (m : ℕ) :
    collisionJet m = C ((4 : F)^m) * literalJetRemainder (fun _ => (1/4 : F)) m := by
  let V : F[X] := X - C (1 / 4)
  have hχ : ((∏ _ : Fin 4, V) ^ 2) = V ^ 8 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hmonic : (V ^ 8).Monic := (monic_X_sub_C _).pow _
  have hfour : C (4 : F) = (4 : F[X]) := map_ofNat (C : F →+* F[X]) 4
  have hdvd : V ^ 8 ∣ C ((4 : F)^m) * X^m - collisionJet m := by
    have h := HorizontalKCollision.charpoly_sq_dvd_taylor_sub (F := F) m
    rw [← pow_mul, ← hfour,
      mul_pow, ← C_pow] at h
    simpa only [V, collisionJet, HorizontalKCollision.taylor, hfour] using h
  have hdegree : (collisionJet (F := F) m).natDegree ≤ 7 := by
    simpa only [collisionJet, HorizontalKCollision.taylor, hfour] using
      HorizontalKCollision.taylor_degree (R := F) m
  have hdeg : (collisionJet (F := F) m).degree < (V^8).degree := by
    rw [degree_eq_natDegree hmonic.ne_zero, natDegree_pow, show V.natDegree = 1 from
      natDegree_X_sub_C _]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr
      (hdegree.trans_lt (by decide)))
  obtain ⟨q, hq⟩ := hdvd
  have he := (div_modByMonic_unique q (collisionJet m) hmonic
    ⟨by rw [← hq, add_sub_cancel], hdeg⟩).2
  rw [div_modByMonic_unique (C ((4 : F)^m) * (X^m /ₘ V^8))
    (C ((4 : F)^m) * (X^m %ₘ V^8)) hmonic
      ⟨?_, by
        rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (pow_ne_zero m (by norm_num : (4 : F) ≠ 0)))]
        exact degree_modByMonic_lt _ hmonic⟩ |>.2] at he
  · simpa only [literalJetRemainder, ← hχ, V] using he.symm
  · rw [mul_left_comm, ← mul_add, modByMonic_add_div]

/-- The collision polynomial evaluates to the normalized literal power even
on the matrix with an arbitrary first-order perturbation. -/
theorem collisionJet_at_perturbation {F : Type*} [Field F] [CharZero F]
    (T J : Matrix (Fin 4) (Fin 4) F) (m : ℕ)
    (hχ : T.charpoly = (X - C (1/4 : F))^4) :
    aeval (PeriodicMPSUniformHermiteLiteralJet.perturbation T J) (collisionJet (F := F) m) =
      algebraMap F (Matrix (Fin 4) (Fin 4) (DualNumber F)) ((4 : F)^m) * (PeriodicMPSUniformHermiteLiteralJet.perturbation T J)^m := by
  let H := PeriodicMPSUniformHermiteLiteralJet.perturbation T J
  have h : aeval H (((∏ _ : Fin 4, (X - C (1/4 : F)))^2)) = 0 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hχ]
    exact PeriodicMPSUniformHermiteLiteralJet.aeval_charpoly_sq_perturbation T J
  rw [collisionJet_eq_scaled_remainder, map_mul, aeval_C]
  congr 1
  have he := congrArg (aeval H) (modByMonic_add_div (X^m : F[X])
    (((∏ _ : Fin 4, (X - C (1/4 : F)))^2)))
  simpa only [literalJetRemainder, map_add, map_mul, h, zero_mul, add_zero, aeval_X_pow, H]
    using he

/-- The literal jet over the original invariant ring requires only monic
division by the squared transfer characteristic polynomial. -/
def invariantCharacteristic {R : Type*} [CommRing R] (a b c : R) : R[X] :=
  X^4 - X^3 + C a * X^2 - C b * X + C c

private theorem invariantCharacteristic_monic {R : Type*} [CommRing R] (a b c : R) :
    (invariantCharacteristic a b c).Monic := by
  by_cases h : Nontrivial R
  · let _ := h
    have htail : (-X^3 + C a * X^2 - C b * X + C c : R[X]).natDegree ≤ 3 := by
      apply natDegree_add_le_of_le (m := 3) (n := 3)
      · apply natDegree_sub_le_of_le (m := 3) (n := 3)
        · apply natDegree_add_le_of_le (m := 3) (n := 3)
          · simp
          · exact (natDegree_C_mul_le a _).trans (by simp)
        · exact (natDegree_C_mul_le b X).trans (by simp)
      · simp
    unfold invariantCharacteristic
    rw [sub_eq_add_neg (X^4 : R[X])]
    have hh : (X^4 + -X^3 + C a * X^2 - C b * X + C c : R[X]) =
        X^4 + (-X^3 + C a * X^2 - C b * X + C c) := by ring
    rw [hh]
    apply (monic_X_pow (R := R) 4).add_of_left
    rw [degree_X_pow]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (htail.trans_lt (by decide)))
  · let _ : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    rw [Subsingleton.elim (invariantCharacteristic a b c) 1]
    exact monic_one

def invariantLiteralJet {R : Type*} [CommRing R] (a b c : R) (m : ℕ) : R[X] :=
  X^m %ₘ (invariantCharacteristic a b c)^2

theorem invariantLiteralJet_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c : R) (m : ℕ) :
    (invariantLiteralJet a b c m).map f = invariantLiteralJet (f a) (f b) (f c) m := by
  unfold invariantLiteralJet
  rw [map_modByMonic f ((invariantCharacteristic_monic a b c).pow 2)]
  simp only [invariantCharacteristic, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C]

theorem invariantLiteralJet_collision {F : Type*} [Field F] [CharZero F] (m : ℕ) :
    C ((4 : F)^m) * invariantLiteralJet (3/8 : F) (1/16) (1/256) m = collisionJet m := by
  have hχ : invariantCharacteristic (3/8 : F) (1/16) (1/256) =
      (X - C (1/4 : F))^4 := by
    unfold invariantCharacteristic
    have h₁ : (4 : F[X]) * C (1/4 : F) = 1 := by
      rw [← map_ofNat (C : F →+* F[X]) 4, ← map_mul]
      norm_num
    have h₂ : (6 : F[X]) * C (1/4 : F)^2 = C (3/8 : F) := by
      rw [← map_ofNat (C : F →+* F[X]) 6, ← map_pow, ← map_mul]
      norm_num
    have h₃ : (4 : F[X]) * C (1/4 : F)^3 = C (1/16 : F) := by
      rw [← map_ofNat (C : F →+* F[X]) 4, ← map_pow, ← map_mul]
      norm_num
    have h₄ : C (1/4 : F)^4 = C (1/256 : F) := by rw [← map_pow]; norm_num
    linear_combination X^3*h₁ - X^2*h₂ + X*h₃ - h₄
  rw [collisionJet_eq_scaled_remainder, invariantLiteralJet, literalJetRemainder, hχ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end
end D5.S3.Quantum.TensorNetworks.HorizontalNativeU

/-
Uncompiled source candidate, all original states and rational modes.
This module derives the two triple-channel factors and their actual finite
coefficient reconstructions. Scalar pentagon is imported separately; the
three-variable common witness and FIVE four-input channel identifications
are not asserted here. Arbitrary-weak-input extension remains conditional
on the pending actual sector-pair representing equivalence.
The weak-associativity import is exact pinned source, not fresh native acceptance.
Bakalov--Kac math/0602072 Theorem 3.5/Corollary 3.5(23) and section 3.6(27);
all supplier Carnahan/Kytölä attributions and truth boundaries are retained.
-/
import D5.S3.VertexAlgebra.Sectors.LatticeChargedQuotientScalar
import D5.S3.VertexAlgebra.Sectors.LatticeCosetWeakAssociativity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeChargedQuotientAssociator
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeSugawaraCurrents
open LatticeChargedTransport LatticeChargedQuotientScalar LatticeDualCosetTransport
open LatticeCosetCanonicalIntertwiner (zeroSymm zeroEven)
open scoped BigOperators VertexOperator Matrix
noncomputable section

/-- Actual quotient Hahn field: postcompose the prescribed canonical field by
T_carry. This is a field on the original full carrier, not a neutral model. -/
def quotientField (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) : LatticeDualCosetIntertwiner.Fields D :=
  Modules.ActualWeakModuleFullIntertwiner.rawMap LinearMap.id LinearMap.id
    (transport D (representative D (c+d)) (carry D hD c d))
    (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ)
      (representative D c) (representative D d))

/-- Every raw rational coefficient, including off-coset zero coefficients. -/
theorem quotientField_coeff (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) (u v : Carrier D) (q : ℚ) :
    (quotientField D hD c d u).coeff q v =
      transport D (representative D (c+d)) (carry D hD c d)
        ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ)
          (representative D c) (representative D d) u).coeff q v) :=
  Modules.ActualWeakModuleFullIntertwiner.rawMap_coeff _ _ _ _ u v q

/-- The prescribed quotient field is lawful for the LITERAL quotient target.
The transportHom proof is reused after the actual carry equation, not assumed. -/
theorem quotientField_lawful (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Modules.ActualWeakModuleFullIntertwiner.Lawful
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (representative D c))
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (representative D d))
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (representative D (c+d)))
      H (quotientField D hD c d) := by
  let k : Modules.FullJacobiIntertwiner.ModuleHom
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D
        (representative D c + representative D d))
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (representative D (c+d))) :=
    { linearMap := transport D (representative D (c+d)) (carry D hD c d)
      intertwines := by
        intro x j v
        have hp : shiftedCharge D (representative D (c+d)) (carry D hD c d) =
            representative D c + representative D d := (carry_equation D hD c d).symm
        change transport D (representative D (c+d)) (carry D hD c d)
            (((LatticeDualCosetModule.action D (representative D c + representative D d) x)[[j]]) v) =
          ((LatticeDualCosetModule.action D (representative D (c+d)) x)[[j]])
            (transport D (representative D (c+d)) (carry D hD c d) v)
        simpa only [hp] using transport_all_modes D (representative D (c+d))
          (carry D hD c d) x v j }
  let J := (Modules.ActualWeakModuleFullIntertwiner.sectorReadback
    (representative D c) (representative D d) H
    (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D
      (representative D c + representative D d))).symm
    ((Sectors.ActualWeakTargetFullIntertwiner.scalarReadback D
      (representative D c) (representative D d) H).symm
      (LatticeDualCosetFusion.canonicalOperator D hD
        (representative D c) (representative D d) H hHG hGH))
  exact Modules.ActualWeakModuleFullIntertwiner.lawful_map H
    (Modules.FullJacobiIntertwiner.ModuleHom.id _) (Modules.FullJacobiIntertwiner.ModuleHom.id _)
    k J.val J.property

/-- The full original off-coset support statement is retained under transport. -/
theorem quotientField_coeff_off (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) (u v : Carrier D) (q : ℚ)
    (hq : q ∉ Set.range (LatticeCosetCanonicalIntertwiner.exponentEmbedding
      (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
        (representative D c) (representative D d)))) :
    (quotientField D hD c d u).coeff q v = 0 := by
  rw [quotientField_coeff]
  have hz := LatticeCosetCanonicalIntertwiner.field_coeff_off D (1 : Matrix _ _ ℤ)
    (representative D c) (representative D d) u v q hq
  change (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ)
    (representative D c) (representative D d) u).coeff q v = 0 at hz
  rw [hz, map_zero]

/-- Rational mode tau has the original raw exponent -tau-1. -/
def quotientMode (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) (u : Carrier D) (τ : ℚ) :
    Carrier D →ₗ[ℂ] Carrier D := (quotientField D hD c d u).coeff (-τ-1)

theorem quotientMode_eq (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) (u v : Carrier D) (τ : ℚ) :
    quotientMode D hD c d u τ v =
      transport D (representative D (c+d)) (carry D hD c d)
        (LatticeCosetCanonicalIntertwiner.mode D (1 : Matrix _ _ ℤ)
          (representative D c) (representative D d) u τ v) :=
  quotientField_coeff D hD c d u v (-τ-1)

theorem quotientMode_off (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) (u v : Carrier D) (τ : ℚ)
    (hτ : -τ-1 ∉ Set.range (LatticeCosetCanonicalIntertwiner.exponentEmbedding
      (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
        (representative D c) (representative D d)))) :
    quotientMode D hD c d u τ v = 0 :=
  quotientField_coeff_off D hD c d u v (-τ-1) hτ

/-- Literal ground normalization is e_carry, not an imposed e_0. -/
theorem quotientField_ground (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) :
    (quotientField D hD c d (LatticeAllStateField.vacuum D)).coeff
      (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
        (representative D c) (representative D d)) (LatticeAllStateField.vacuum D) =
      Finsupp.single (carry D hD c d) 1 := by
  rw [quotientField_coeff, LatticeCosetCanonicalIntertwiner.ground_coefficient]
  change transport D (representative D (c+d)) (carry D hD c d) (Finsupp.single 0 1) = _
  exact transport_vacuum D (representative D (c+d)) (carry D hD c d)

section Triple
variable (D : LatticeData) (hD : (gramReal D).PosDef)
variable (c d e : Discriminant D)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
local notation "a" => representative D c
local notation "b" => representative D d
local notation "h" => representative D e
local notation "p" => carry D hD c d
local notation "r" => carry D hD (c+d) e
local notation "q" => carry D hD d e
local notation "s" => carry D hD c (d+e)
local notation "C₀" => LatticeCosetCanonicalIntertwiner.mode D (1 : Matrix _ _ ℤ)
local notation "Q₀" => LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
local notation "I₀" => LatticeCosetCompression.compressed D (1 : Matrix _ _ ℤ)
  0 zeroSymm zeroEven
local notation "P₀" => LatticeCosetWeakAssociativity.productCoefficient D
  (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a b h
local notation "A₀" => LatticeCosetWeakAssociativity.iterateCoefficient D
  (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a b h
local notation "Ψ₀" => LatticeCosetWeakAssociativity.sharedNumerator D
  (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a b h

include hHG hGH in
/-- Exact all-state iterate channel, with epsilon(p,r), at unchanged rational modes. -/
theorem quotient_iterate_modes (u v w : Carrier D) (τ σ : ℚ) :
    quotientMode D hD (c+d) e (quotientMode D hD c d u τ v) σ w =
      epsilon D p r • transport D 0 (p+r) (C₀ (a+b) h (C₀ a b u τ v) σ w) := by
  rw [quotientMode_eq, quotientMode_eq]
  have ht := two_leg_mode D hD (representative D (c+d)) h p 0 H hHG hGH
    (C₀ a b u τ v) w σ
  have hp : shiftedCharge D (representative D (c+d)) p = a+b :=
    (carry_equation D hD c d).symm
  simp only [shiftedCharge_zero, transport_zero, LinearMap.id_apply,
    epsilon_zero_right, mul_one, add_zero] at ht
  have hz : chi D (representative D (c+d)) 0 = 1 := by simp [chi, dotProduct, paritySign]
  rw [hz, one_smul, hp] at ht
  rw [ht]
  exact congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D =>
    f (C₀ (a+b) h (C₀ a b u τ v) σ w)) (transport_comp D 0 0 p r)

include hHG hGH in
/-- Exact all-state product channel. The carry cocycle identifies its total T. -/
theorem quotient_product_modes (u v w : Carrier D) (τ σ : ℚ) :
    quotientMode D hD c (d+e) u τ (quotientMode D hD d e v σ w) =
      (chi D a q * epsilon D q s) •
        transport D 0 (p+r) (C₀ a (b+h) u τ (C₀ b h v σ w)) := by
  rw [quotientMode_eq, quotientMode_eq]
  have ht := two_leg_mode D hD a (representative D (d+e)) 0 q H hHG hGH
    u (C₀ b h v σ w) τ
  have hq : shiftedCharge D (representative D (d+e)) q = b+h :=
    (carry_equation D hD d e).symm
  simp only [shiftedCharge_zero, transport_zero, LinearMap.id_apply,
    epsilon_zero_left, mul_one, zero_add] at ht
  rw [hq] at ht
  rw [ht, map_smul]
  have hc := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D =>
    f (C₀ a (b+h) u τ (C₀ b h v σ w))) (transport_comp D 0 0 q s)
  change transport D 0 s (transport D 0 q (C₀ a (b+h) u τ (C₀ b h v σ w))) =
    epsilon D q s • transport D 0 (q+s) (C₀ a (b+h) u τ (C₀ b h v σ w)) at hc
  change chi D a q • transport D 0 s
    (transport D 0 q (C₀ a (b+h) u τ (C₀ b h v σ w))) = _
  rw [hc, smul_smul, carry_cocycle D hD c d e]

/-- The literal scalar is exactly the ratio of the two proved channel factors. -/
theorem channel_factor_ratio :
    associator D hD c d e * epsilon D p r = chi D a q * epsilon D q s := by
  exact div_mul_cancel₀ _ (epsilon_nonzero D _ _)

private theorem shift_product : Q₀ a (b+h) = Q₀ a (representative D (d+e)) +
    ((a ⬝ᵥ q : ℤ) : ℚ) := by
  have ht := shift_gram D hD a (representative D (d+e)) 0 q
  have hq : shiftedCharge D (representative D (d+e)) q = b+h :=
    (carry_equation D hD d e).symm
  simpa [hq, shiftedCharge_zero, bilinear, dotProduct] using ht

private theorem shift_iterate : Q₀ (a+b) h = Q₀ (representative D (c+d)) h +
    ((p ⬝ᵥ h : ℤ) : ℚ) := by
  have ht := shift_gram D hD (representative D (c+d)) h p 0
  have hp : shiftedCharge D (representative D (c+d)) p = a+b :=
    (carry_equation D hD c d).symm
  simpa [hp, shiftedCharge_zero, bilinear, dotProduct] using ht

include hHG hGH in
/-- Pro (21): the product's OUTER integer index is m+a.dot.q, with its sign. -/
theorem quotient_product_integer (u v w : Carrier D) (m n : ℤ) :
    quotientMode D hD c (d+e) u ((m : ℚ)-Q₀ a (representative D (d+e)))
      (quotientMode D hD d e v ((n : ℚ)-Q₀ b h) w) =
      (chi D a q * epsilon D q s) • transport D 0 (p+r)
        (P₀ u v w (m+a ⬝ᵥ q) n) := by
  rw [quotient_product_modes D hD c d e H hHG hGH]
  have hm : (m : ℚ)-Q₀ a (representative D (d+e)) =
      ((m+a ⬝ᵥ q : ℤ) : ℚ)-Q₀ a (b+h) := by rw [shift_product D hD c d e]; push_cast; ring
  rw [hm, LatticeCosetCanonicalIntertwiner.mode_integer,
    LatticeCosetCanonicalIntertwiner.mode_integer]
  rfl

include hHG hGH in
/-- Pro (22): the iterate's OUTER index is n+p.dot.beta(e); inner m is unchanged. -/
theorem quotient_iterate_integer (u v w : Carrier D) (m n : ℤ) :
    quotientMode D hD (c+d) e
      (quotientMode D hD c d u ((m : ℚ)-Q₀ a b) v)
      ((n : ℚ)-Q₀ (representative D (c+d)) h) w =
      epsilon D p r • transport D 0 (p+r)
        (A₀ u v w m (n+p ⬝ᵥ h)) := by
  rw [quotient_iterate_modes D hD c d e H hHG hGH]
  have hn : (n : ℚ)-Q₀ (representative D (c+d)) h =
      ((n+p ⬝ᵥ h : ℤ) : ℚ)-Q₀ (a+b) h := by rw [shift_iterate D hD c d e]; push_cast; ring
  rw [hn, LatticeCosetCanonicalIntertwiner.mode_integer,
    LatticeCosetCanonicalIntertwiner.mode_integer]
  rfl

private theorem schur_shift (x y : Charge D) :
    LatticeCosetCompression.schur D (1 : Matrix _ _ ℤ) 0 x y = -Q₀ x y := by
  simp [LatticeCosetCompression.schur, LatticeCosetCanonicalIntertwiner.shift,
    mul_neg, neg_mul]

include hHG hGH in
/-- Each requested product coefficient has THIS finite range. R,M,N remain
arbitrary signed original cutoffs. No supremum over intermediate states occurs. -/
theorem quotient_product_reconstruction (u v w : Carrier D) (R M N : ℤ)
    (hR : ∀ k : ℤ, R ≤ k → I₀ a b u k v = 0)
    (hM : ∀ k : ℤ, M ≤ k → I₀ b h v k w = 0)
    (hN : ∀ k : ℤ, N ≤ k → I₀ a h u k w = 0) (m n : ℤ) :
    quotientMode D hD c (d+e) u ((m : ℚ)-Q₀ a (representative D (d+e)))
      (quotientMode D hD d e v ((n : ℚ)-Q₀ b h) w) =
      (chi D a q * epsilon D q s) • transport D 0 (p+r)
        (∑ j ∈ Finset.range (M-n).toNat,
          ((-1 : ℂ)^j * ((Ring.choose (Q₀ a b-(R : ℚ)) j : ℚ) : ℂ)) •
            LatticeCosetWeakAssociativity.extend (Ψ₀ u v w R M N)
              (N+R-1-(m+a ⬝ᵥ q)+j) (M-1-n-j)) := by
  rw [quotient_product_integer D hD c d e H hHG hGH]
  have hp := (LatticeCosetWeakAssociativity.actual_shared_numerator D
    (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a b h u v w hD R M N hR hM hN).2.2.1
      (m+a ⬝ᵥ q) n
  simp only [schur_shift D, neg_neg] at hp
  rw [hp]

include hHG hGH in
/-- Each requested iterate coefficient has range (R-m)_+ and the ORIGINAL
second numerator coordinate N+M-1-(n+p.dot.h)+j, with PLUS j. -/
theorem quotient_iterate_reconstruction (u v w : Carrier D) (R M N : ℤ)
    (hR : ∀ k : ℤ, R ≤ k → I₀ a b u k v = 0)
    (hM : ∀ k : ℤ, M ≤ k → I₀ b h v k w = 0)
    (hN : ∀ k : ℤ, N ≤ k → I₀ a h u k w = 0) (m n : ℤ) :
    quotientMode D hD (c+d) e
      (quotientMode D hD c d u ((m : ℚ)-Q₀ a b) v)
      ((n : ℚ)-Q₀ (representative D (c+d)) h) w =
      epsilon D p r • transport D 0 (p+r)
        (∑ j ∈ Finset.range (R-m).toNat,
          ((Ring.choose (Q₀ a h-(N : ℚ)) j : ℚ) : ℂ) •
            LatticeCosetWeakAssociativity.extend
              (LatticeCosetWeakAssociativity.coordinateChange 1 (Ψ₀ u v w R M N))
              (R-1-m-j) (N+M-1-(n+p ⬝ᵥ h)+j)) := by
  rw [quotient_iterate_integer D hD c d e H hHG hGH]
  have ha := (LatticeCosetWeakAssociativity.actual_shared_numerator D
    (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a b h u v w hD R M N hR hM hN).2.2.2.1
      m (n+p ⬝ᵥ h)
  simp only [schur_shift D, neg_neg] at ha
  rw [ha]

/-- A single ACTUAL ordinary numerator is used by both preceding channels.
This coefficient statement is the supplier's shear, transported by the actual
iterate factor. The finite range e'+1 predates all linear-map operations. -/
theorem transported_numerator_shear (u v w : Carrier D) (R M N : ℤ)
    (hR : ∀ k : ℤ, R ≤ k → I₀ a b u k v = 0)
    (hM : ∀ k : ℤ, M ≤ k → I₀ b h v k w = 0)
    (hN : ∀ k : ℤ, N ≤ k → I₀ a h u k w = 0) (d' e' : ℕ) :
    epsilon D p r • transport D 0 (p+r)
      (LatticeCosetWeakAssociativity.numerator D (1 : Matrix _ _ ℤ)
        0 zeroSymm zeroEven a b h u v w R M N d' e') =
      ∑ j ∈ Finset.range (e'+1), ((d'+j).choose j : ℂ) •
        (epsilon D p r • transport D 0 (p+r)
          (Ψ₀ u v w R M N (d'+j) (e'-j))) := by
  have hs := (LatticeCosetWeakAssociativity.actual_shared_numerator D
    (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a b h u v w hD R M N hR hM hN).2.1 d' e'
  rw [hs, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, smul_comm]

end Triple
end
end D5.S3.VertexAlgebra.LatticeChargedQuotientAssociator

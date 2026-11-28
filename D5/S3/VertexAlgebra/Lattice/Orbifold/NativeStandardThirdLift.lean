/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeStandardThirdLift
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The standard lift of an even lattice isometry of period three on its native carrier. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeAction
import D5.S3.VertexAlgebra.Lattice.Automorphisms.InvariantQuadraticConformalState
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy

/-!
The actual standard lift of a period-three even lattice isometry on the
untwisted lattice carrier. The correction is the canonical orbit character
itself, whose sign is the phase on the orbit norm since the norm pairing is
even. This identifies the charged ground coefficients with the phase already
used in the order-three twisted charge action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeStandardThirdLift

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeActualProductKernel
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open ThirdTwistedChargeAction (N N_apply nativeStandardEta nativeStandardEta_fixed)
open CyclicIsometryLift (orbitCharacter canonical_power corrected diagonal)
open scoped BigOperators VertexOperator

open private corrected_compatible corrected_pow_single oscillator_pow_fixed
  diagonal_single charge_detects_power from
  D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open private inverse_gram_covariance from
  D5.S3.VertexAlgebra.Lattice.Automorphisms.InvariantQuadraticConformalState

noncomputable section

variable (D : LatticeData) (g : Charge D ≃+ Charge D)
variable (h3 : ∀ a, g (g (g a)) = a)
variable (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)

include h3 in
private theorem iterate_cube (a : Charge D) : g^[3] a = a := by
  change g (g (g a)) = a
  exact h3 a

include h3 hg in
/-- For a period-three isometry the integral pairing of a charge with its
orbit norm is even. -/
theorem norm_pairing_even (a : Charge D) : Even (bilinear D a (N D g a)) := by
  have hPair : bilinear D a (g (g a)) = bilinear D a (g a) := by
    calc
      _ = bilinear D (g a) a := by
        simpa only [h3 a] using (hg a (g (g a))).symm
      _ = _ := bilinear_symmetric D (g a) a
  have hEven : Even (bilinear D a a) := LatticeHalfFockChargedMonodromy.norm_even D a
  obtain ⟨k, hk⟩ := hEven
  rw [N_apply, bilinear_add_right, bilinear_add_right, hPair, hk]
  refine ⟨k + bilinear D a (g a), ?_⟩
  ring

/-- In period three the orbit character itself supplies the correction. -/
abbrev standardCharacter : Charge D →+ F₂ :=
  orbitCharacter D g hg 3 (iterate_cube D g h3)

/-- The correcting character has the literal inverse norm phase of the native
standard twisted lift. -/
theorem standardCharacter_sign (a : Charge D) :
    complexSign (standardCharacter D g h3 hg a) =
      (↑((IsometryLift.phase D g (N D g a))⁻¹) : ℂ) := by
  have h := (canonical_power D g hg 3 (iterate_cube D g h3)).2.2.2 a
  change complexSign (standardCharacter D g h3 hg a) =
    (IsometryLift.phase D g (N D g a) : ℂ) * paritySign (bilinear D a (N D g a)) at h
  rw [paritySign, ite_eq_left (norm_pairing_even D g h3 hg a), mul_one] at h
  have hInv : (IsometryLift.phase D g (N D g a))⁻¹ =
      IsometryLift.phase D g (N D g a) :=
    inv_eq_of_mul_eq_one_right (CyclicIsometryLift.phase_square D g hg (N D g a))
  rw [hInv]
  exact h

/-- The additive orbit character takes the same value on the norm as on the
original charge, by cyclic invariance and characteristic two. -/
theorem standardCharacter_norm (a : Charge D) :
    standardCharacter D g h3 hg (N D g a) = standardCharacter D g h3 hg a := by
  have hInv (b : Charge D) :
      standardCharacter D g h3 hg (g b) = standardCharacter D g h3 hg b :=
    (canonical_power D g hg 3 (iterate_cube D g h3)).2.1 b
  simp only [N_apply, map_add, hInv, CharTwo.add_self_eq_zero, zero_add]

/-- The standard lift on the actual untwisted lattice carrier. -/
def standardLift : Carrier D ≃ₗ[ℂ] Carrier D :=
  corrected D g (standardCharacter D g h3 hg)

/-- The standard lift transforms the oscillator and charge simultaneously,
with precisely the native standard phase on the entire charge sector. -/
theorem standardLift_single (a : Charge D) (p : Oscillator D) :
    standardLift D g h3 hg (Finsupp.single a p) =
      (nativeStandardEta D g a : ℂ) •
        Finsupp.single (g a) (IsometryLift.oscillator D g p) := by
  change IsometryLift.lift D g
    (diagonal D (standardCharacter D g h3 hg) (Finsupp.single a p)) = _
  rw [diagonal_single, map_smul, IsometryLift.lift_single, smul_smul,
    standardCharacter_sign D g h3 hg]
  simp only [nativeStandardEta, Units.val_mul, mul_comm]

/-- Identification of the actual charged ground coefficient with the phase
used in the twisted charge field. -/
theorem standardLift_ground_single (a : Charge D) :
    standardLift D g h3 hg (Finsupp.single a (1 : Oscillator D)) =
      (nativeStandardEta D g a : ℂ) • Finsupp.single (g a) (1 : Oscillator D) := by
  simpa only [map_one] using standardLift_single D g h3 hg a 1

/-- The standard lift is normalized on the fixed charged ground states. -/
theorem standardLift_fixed_ground (a : Charge D) (ha : g a = a) :
    standardLift D g h3 hg (Finsupp.single a (1 : Oscillator D)) =
      Finsupp.single a (1 : Oscillator D) := by
  rw [standardLift_ground_single, nativeStandardEta_fixed D g hg a ha, ha,
    Units.val_one, one_smul]

/-- The actual vacuum, integer-mode state-field correspondence and translation
are preserved on arbitrary states. -/
theorem standardLift_compatible :
    standardLift D g h3 hg (vacuum D) = vacuum D ∧
    (∀ (u : Carrier D) (n : ℤ) (v : Carrier D),
      standardLift D g h3 hg (((Y D u)[[n]]) v) =
        ((Y D (standardLift D g h3 hg u))[[n]]) (standardLift D g h3 hg v)) ∧
    (∀ v : Carrier D, standardLift D g h3 hg (translation D v) =
      translation D (standardLift D g h3 hg v)) :=
  corrected_compatible D g hg (standardCharacter D g h3 hg)

/-- In particular the actual charged-field coefficients intertwine with the
native phase, for every mode and every input state. -/
theorem standardLift_ground_mode (a : Charge D) (n : ℤ) (v : Carrier D) :
    standardLift D g h3 hg (((Y D (Finsupp.single a (1 : Oscillator D)))[[n]]) v) =
      (nativeStandardEta D g a : ℂ) •
        (((Y D (Finsupp.single (g a) (1 : Oscillator D)))[[n]])
          (standardLift D g h3 hg v)) := by
  rw [(standardLift_compatible D g h3 hg).2.1, standardLift_ground_single]
  simp only [map_smul, VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply]

/-- The same intertwining law in the Laurent-coefficient indexing. -/
theorem standardLift_rawCoeff (a : Charge D) (k : ℤ) (v : Carrier D) :
    standardLift D g h3 hg (rawCoeff D a k v) =
      (nativeStandardEta D g a : ℂ) • rawCoeff D (g a) k (standardLift D g h3 hg v) := by
  have hk : -(-k - 1) - 1 = k := by ring
  have hCoeff (b : Charge D) :
      (Y D (Finsupp.single b (1 : Oscillator D)))[[-k - 1]] = rawCoeff D b k := by
    rw [stateField_ground D b, LatticeActualGeneratorLocality.actual_modes D b (-k - 1), hk]
  have h := standardLift_ground_mode D g h3 hg a (-k - 1) v
  rw [hCoeff a, hCoeff (g a)] at h
  exact h

/-- The third power is the identity on the entire untwisted carrier. -/
theorem standardLift_cube : standardLift D g h3 hg ^ 3 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  change (corrected D g (standardCharacter D g h3 hg) ^ 3) (Finsupp.single a p) =
    Finsupp.single a p
  rw [corrected_pow_single D g hg]
  change complexSign (standardCharacter D g h3 hg a +
    standardCharacter D g h3 hg (N D g a)) •
      Finsupp.single (g^[3] a) ((IsometryLift.oscillator D g ^ 3) p) = Finsupp.single a p
  rw [standardCharacter_norm D g h3 hg, CharTwo.add_self_eq_zero, sign_zero,
    one_smul, iterate_cube D g h3, oscillator_pow_fixed D g 3 (iterate_cube D g h3)]

/-- If the charge isometry acts nontrivially, the standard lift has exact
order three. -/
theorem standardLift_orderOf (hne : ∃ a, g a ≠ a) :
    orderOf (standardLift D g h3 hg) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime_iff.mpr
  refine ⟨standardLift_cube D g h3 hg, ?_⟩
  intro h
  have hpow : corrected D g (standardCharacter D g h3 hg) ^ 1 = 1 := by
    simpa only [pow_one, standardLift] using h
  have he := charge_detects_power D g hg (standardCharacter D g h3 hg) 1 hpow
  rw [pow_one] at he
  obtain ⟨a, ha⟩ := hne
  apply ha
  exact congrArg (fun e : Charge D ≃ Charge D => e a) he

/-- Every inverse-Gram conformal state is fixed by the standard lift. The
character correction is trivial in the neutral sector and the underlying
oscillator action transports the inverse Gram matrix by congruence. -/
theorem standardLift_omega (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1) :
    standardLift D g h3 hg (LatticeActualConformalState.omega D H) =
      LatticeActualConformalState.omega D H := by
  change IsometryLift.lift D g
    (diagonal D (standardCharacter D g h3 hg) (LatticeActualConformalState.omega D H)) = _
  have hd : diagonal D (standardCharacter D g h3 hg) (LatticeActualConformalState.omega D H) =
      LatticeActualConformalState.omega D H := by
    rw [LatticeActualConformalState.omega, diagonal_single, map_zero, sign_zero, one_smul]
  rw [hd, InvariantQuadraticConformalState.lift_omega, inverse_gram_covariance D H hHG g hg]

#print axioms standardLift_orderOf
#print axioms standardLift_omega

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeStandardThirdLift

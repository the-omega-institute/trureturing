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
import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter

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

section TwiningTrace

open LatticeThetaCharacter LatticePositiveEnergy
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open private chargeSupported_mem_iff cutoffCoeffEquiv_apply cutoffBasis_carrierCoeff from
  D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter

private theorem standardLift_charge (a : Charge D) (v : Carrier D) :
    (standardLift D g h3 hg v) (g a) =
      (nativeStandardEta D g a : ℂ) • IsometryLift.oscillator D g (v a) := by
  classical
  let L : Carrier D →ₗ[ℂ] Oscillator D :=
    (Finsupp.lapply (g a)).comp (standardLift D g h3 hg).toLinearMap
  let R : Carrier D →ₗ[ℂ] Oscillator D :=
    (nativeStandardEta D g a : ℂ) •
      ((IsometryLift.oscillator D g).toLinearMap.comp (Finsupp.lapply a))
  suffices L = R from LinearMap.congr_fun this v
  apply Finsupp.lhom_ext
  intro b p
  change (standardLift D g h3 hg (Finsupp.single b p)) (g a) =
    (nativeStandardEta D g a : ℂ) • IsometryLift.oscillator D g (Finsupp.single b p a)
  rw [standardLift_single, Finsupp.smul_apply]
  by_cases hb : b = a
  · subst b
    simp
  · have hgb : g b ≠ g a := fun h => hb (g.injective h)
    simp [Finsupp.single_eq_of_ne (Ne.symm hb), Finsupp.single_eq_of_ne hgb.symm]

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

private theorem standardLift_mem_cutoff (hHG : H * gramComplex D = 1)
    (C : Finset (Charge D)) (n : ℤ) (hC : ∀ a ∈ C, g a ∈ C)
    (v : cutoffActualGrade D H C n) :
    standardLift D g h3 hg v.1 ∈ cutoffActualGrade D H C n := by
  refine ⟨?_, ?_⟩
  · apply (chargeSupported_mem_iff D C _).mpr
    have hv := (chargeSupported_mem_iff D C v.1).mp v.2.1
    intro a ha
    have hpre : g.symm a.1 ∉ C := fun hc => ha (by simpa using hC _ hc)
    have hz : v.1 (g.symm a.1) = 0 := by
      ext d
      exact hv (g.symm a.1, d) hpre
    change ((standardLift D g h3 hg v.1) a.1).coeff a.2 = 0
    rw [← g.apply_symm_apply a.1, standardLift_charge D g h3 hg, hz, map_zero, smul_zero]
    rfl
  · have hv := (Module.End.mem_eigenspace_iff.mp v.2.2)
    apply Module.End.mem_eigenspace_iff.mpr
    have hmode : ((Y D (LatticeActualConformalState.omega D H))[[1]]) =
        sugawaraMode D H 0 := LatticeActualConformalState.omega_modes D H 0
    have h := (standardLift_compatible D g h3 hg).2.1
      (LatticeActualConformalState.omega D H) 1 v.1
    rw [standardLift_omega D g h3 hg H hHG, hmode, hv, map_smul] at h
    exact h.symm

/-- The native lift restricted to the actual Sugawara grade with charges in `C`. -/
def cutoffStandardLift (hHG : H * gramComplex D = 1)
    (C : Finset (Charge D)) (n : ℤ) (hC : ∀ a ∈ C, g a ∈ C) :
    Module.End ℂ (cutoffActualGrade D H C n) :=
  (standardLift D g h3 hg).toLinearMap.restrict
    (fun v hv => standardLift_mem_cutoff D g h3 hg H hHG C n hC ⟨v, hv⟩)

/-- The finite grade trace of the restricted native lift. -/
def cutoffStandardLiftTrace (hHG : H * gramComplex D = 1)
    (C : Finset (Charge D)) (n : ℤ) (hC : ∀ a ∈ C, g a ∈ C) : ℂ := by
  letI : Finite (CutoffIndex D C n) := cutoffIndex_finite D C n
  letI : Fintype (CutoffIndex D C n) := Fintype.ofFinite _
  exact LinearMap.trace ℂ _ (cutoffStandardLift D g h3 hg H hHG C n hC)

/-- The oscillator trace at integral energy `n`, realized on the actual neutral
charge sector. The native phase on that sector is one. -/
def standardOscillatorTrace (hHG : H * gramComplex D = 1) (n : ℤ) : ℂ :=
  cutoffStandardLiftTrace D g h3 hg H hHG {0} n (by simp)

private theorem cutoffStandardLiftTrace_diagonal (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ) (hC : ∀ a ∈ C, g a ∈ C)
    [Fintype (CutoffIndex D C n)] :
    cutoffStandardLiftTrace D g h3 hg H hHG C n hC =
      ∑ i : CutoffIndex D C n, if g i.1.1 = i.1.1 then
        (IsometryLift.oscillator D g (MvPolynomial.monomial i.1.2 1)).coeff i.1.2 else 0 := by
  classical
  unfold cutoffStandardLiftTrace
  rw [LinearMap.trace_eq_matrix_trace ℂ (cutoffBasis D H hHG hGH C n)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  change cutoffCoeffEquiv D H hHG hGH C n
    (cutoffStandardLift D g h3 hg H hHG C n hC (cutoffBasis D H hHG hGH C n i)) i = _
  rw [cutoffCoeffEquiv_apply]
  have hb : (cutoffBasis D H hHG hGH C n i).1 = carrierBasis D i.1 := by
    apply (carrierCoeffEquiv D).injective
    rw [carrierCoeffEquiv_basis, cutoffBasis_carrierCoeff]
  change ((standardLift D g h3 hg (cutoffBasis D H hHG hGH C n i).1) i.1.1).coeff i.1.2 = _
  rw [hb, carrierBasis_apply, standardLift_single, Finsupp.smul_apply]
  by_cases hi : g i.1.1 = i.1.1
  · rw [ite_eq_left hi, nativeStandardEta_fixed D g hg _ hi, Units.val_one, one_smul, hi,
      Finsupp.single_eq_same]
  · rw [ite_eq_right hi, Finsupp.single_eq_of_ne (Ne.symm hi), smul_zero]
    rfl

/-- Each energy-`n` cutoff label splits into its charge and a neutral label at
the remaining oscillator energy. -/
private def cutoffNeutralEquiv (C : Finset (Charge D)) (n : ℤ) :
    CutoffIndex D C n ≃ Σ a : C, CutoffIndex D {0} (n - chargeEnergy D a.1) where
  toFun i := ⟨⟨i.1.1, i.2.1⟩, ⟨(0, i.1.2), by simp, by
    have he := i.2.2
    simp only [energy, chargeEnergy_zero, zero_add] at he ⊢
    omega⟩⟩
  invFun i := ⟨(i.1.1, i.2.1.2), i.1.2, by
    have hzero : i.2.1.1 = 0 := Finset.mem_singleton.mp i.2.2.1
    have he := i.2.2.2
    simp only [energy, hzero, chargeEnergy_zero, zero_add] at he ⊢
    omega⟩
  left_inv i := Subtype.ext (Prod.eta _)
  right_inv := by
    rintro ⟨a, ⟨⟨b, d⟩, hb, _⟩⟩
    have hzero : b = 0 := Finset.mem_singleton.mp hb
    subst b
    rfl

/-- On each finite actual Sugawara grade, only fixed charges contribute to
the native cubic twining trace. Their contributions are neutral oscillator
traces shifted by their charge energies. -/
theorem cutoff_standardLift_trace_fixed_charges (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ) (hC : ∀ a ∈ C, g a ∈ C) :
    cutoffStandardLiftTrace D g h3 hg H hHG C n hC =
      ∑ a ∈ C.filter (fun a => g a = a),
        standardOscillatorTrace D g h3 hg H hHG (n - chargeEnergy D a) := by
  classical
  let : Finite (CutoffIndex D C n) := cutoffIndex_finite D C n
  let (a : C) : Finite (CutoffIndex D {0} (n - chargeEnergy D a.1)) :=
    cutoffIndex_finite D {0} _
  let : Fintype (CutoffIndex D C n) := Fintype.ofFinite _
  let (a : C) : Fintype (CutoffIndex D {0} (n - chargeEnergy D a.1)) := Fintype.ofFinite _
  rw [cutoffStandardLiftTrace_diagonal D g h3 hg H hHG hGH C n hC,
    Finset.sum_filter, ← Finset.sum_attach C]
  refine (Fintype.sum_equiv (cutoffNeutralEquiv D C n) _
    (fun i => if g i.1.1 = i.1.1 then
      (IsometryLift.oscillator D g (MvPolynomial.monomial i.2.1.2 1)).coeff i.2.1.2 else 0)
    (fun _ => rfl)).trans ?_
  rw [Fintype.sum_sigma]
  change (∑ a : C, ∑ i : CutoffIndex D {0} (n - chargeEnergy D a.1), _) = _
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : g a.1 = a.1
  · simp only [ite_eq_left ha, standardOscillatorTrace]
    rw [cutoffStandardLiftTrace_diagonal D g h3 hg H hHG hGH]
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.1.1 = 0 := Finset.mem_singleton.mp i.2.1
    simp [hi]
  · simp [ha]

#print axioms cutoff_standardLift_trace_fixed_charges

end TwiningTrace

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeStandardThirdLift

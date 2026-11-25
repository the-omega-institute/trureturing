/- GID: D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual rootless lattice VOA conformal automorphisms recover integral charge isometries and ground-line phases. -/

import D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
import D5.S3.VertexAlgebra.LatticeActualConformalState

/-!
For an actual even integral lattice carrier, positive definiteness and rootlessness
make the grade-one states exactly the canonical currents. A mode-preserving
complex-linear automorphism fixing the inverse-Gram Sugawara vector therefore
recovers the charge action from the joint current zero-mode spectrum and sends
each charge ground line to a scalar multiple of the recovered charge line.
The hypotheses are explicit in the public theorems: hPos is real positive
definiteness, hRoot excludes norm-two charges, hHG identifies H with the inverse
Gram matrix via H * gramComplex D = 1, hMode preserves every integer state mode,
and hOmega fixes the actual conformal vector omega D H. The group projection additionally
assumes an injective additive identification mu whose range contains every
integral bilinear isometry.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeSugawaraVirasoro MvPolynomial
open scoped BigOperators Matrix VertexOperator

noncomputable section

private abbrev Coordinates (D : LatticeData) := Fin D.rank → ℂ

private def chargeVector (D : LatticeData) (a : Charge D) : Coordinates D :=
  fun i => (a i : ℂ)

private theorem chargeVector_injective (D : LatticeData) :
    Function.Injective (chargeVector D) := by
  intro a b h
  funext i
  have hi : (a i : ℂ) = (b i : ℂ) := congrFun h i
  exact_mod_cast hi

private abbrev gram (D : LatticeData) := Matrix.toBilin' (gramComplex D)

private theorem gram_charges (D : LatticeData) (a b : Charge D) :
    gram D (chargeVector D a) (chargeVector D b) = (bilinear D a b : ℂ) := by
  rw [Matrix.toBilin'_apply]
  simp only [chargeVector, bilinear, Matrix.map_apply, Int.cast_sum, Int.cast_mul]

private theorem chargeVector_unit (D : LatticeData) (i : Fin D.rank) :
    chargeVector D (unitCharge D i) = Pi.single i 1 := by
  classical
  funext j
  by_cases h : j = i <;> simp [chargeVector, unitCharge, h]

/-- The state of a complex linear combination of the canonical currents. -/
def current (D : LatticeData) (x : Fin D.rank → ℂ) : Carrier D :=
  ∑ i, x i • currentState D i

/-- Actual mode one of two basis currents is their Gram entry times the vacuum. -/
theorem current_one_current (D : LatticeData) (i j : Fin D.rank) :
    ((Y D (currentState D i))[[1]]) (currentState D j) =
      (D.G i j : ℂ) • vacuum D := by
  classical
  rw [current_state_field, neutralField_ncoeff, currentState, neutralMode_single,
    show (1 : ℤ) = (0 : ℕ) + 1 by simp, neutralPolynomialMode_positive]
  simp [weightedPartial, LinearMap.sum_apply, Derivation.coeFn_coe,
    pderiv_X, Pi.single_apply, Prod.mk.injEq, vacuum, Finsupp.smul_single]

private theorem current_mode_apply (D : LatticeData) (x : Coordinates D)
    (n : ℤ) (v : Carrier D) :
    ((Y D (current D x))[[n]]) v =
      ∑ i, x i • neutralMode D i n v := by
  simp only [current, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    current_state_field, neutralField_ncoeff]

private theorem current_one (D : LatticeData) (x y : Coordinates D) :
    ((Y D (current D x))[[1]]) (current D y) = gram D x y • vacuum D := by
  have h (i j : Fin D.rank) :
      neutralMode D i 1 (currentState D j) = (D.G i j : ℂ) • vacuum D := by
    simpa only [current_state_field, neutralField_ncoeff] using current_one_current D i j
  rw [current_mode_apply, Matrix.toBilin'_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [current, map_sum, map_smul, h, Finset.smul_sum, Finset.sum_smul,
    smul_smul, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

private theorem basis_zero_coeff (D : LatticeData) (i : Fin D.rank)
    (v : Carrier D) (q : Label D) :
    carrierCoeffEquiv D (neutralMode D i 0 v) q =
      (bilinear D (unitCharge D i) q.1 : ℂ) * carrierCoeffEquiv D v q := by
  classical
  let f : Carrier D →ₗ[ℂ] ℂ :=
    (Finsupp.lapply q).comp (carrierCoeffEquiv D).toLinearMap
  have h : f.comp (neutralMode D i 0) =
      (bilinear D (unitCharge D i) q.1 : ℂ) • f := by
    apply Finsupp.lhom_ext
    intro a p
    change f (neutralMode D i 0 (Finsupp.single a p)) =
      (bilinear D (unitCharge D i) q.1 : ℂ) • f (Finsupp.single a p)
    rw [neutralMode_zero_single, map_smul]
    change (bilinear D (unitCharge D i) a : ℂ) • f (Finsupp.single a p) = _
    by_cases ha : a = q.1
    · rw [ha]
    · have hz : f (Finsupp.single a p) = 0 := by
        change ((Finsupp.single a p) q.1).coeff q.2 = 0
        simp [ha]
      rw [hz, smul_zero, smul_zero]
  exact LinearMap.congr_fun h v

/-- Each actual mode-zero coefficient reads the Gram pairing with its own charge. -/
theorem current_zero_coeff (D : LatticeData) (x : Fin D.rank → ℂ)
    (v : Carrier D) (q : Label D) :
    carrierCoeffEquiv D (((Y D (current D x))[[0]]) v) q =
      Matrix.toBilin' (gramComplex D) x (fun i => (q.1 i : ℂ)) *
        carrierCoeffEquiv D v q := by
  rw [current_mode_apply]
  change _ = gram D x (chargeVector D q.1) * _
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, basis_zero_coeff]
  rw [Matrix.toBilin'_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← gram_charges, chargeVector_unit, Matrix.toBilin'_apply',
    single_dotProduct, one_mul, Matrix.mulVec, dotProduct]
  rw [← mul_assoc, Finset.mul_sum]
  simp only [mul_assoc]

private theorem current_zero_single (D : LatticeData) (x : Coordinates D)
    (a : Charge D) (p : Oscillator D) :
    ((Y D (current D x))[[0]]) (Finsupp.single a p) =
      gram D x (chargeVector D a) • Finsupp.single a p := by
  apply (carrierCoeffEquiv D).injective
  ext q
  rw [current_zero_coeff]
  change gram D x (chargeVector D q.1) * carrierCoeffEquiv D (Finsupp.single a p) q = _
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases ha : a = q.1
  · rw [ha]
  · have hz : carrierCoeffEquiv D (Finsupp.single a p) q = 0 := by
      change ((Finsupp.single a p) q.1).coeff q.2 = 0
      simp [ha]
    simp [hz]

private abbrev PreservesModes (D : LatticeData) (U : Carrier D ≃ₗ[ℂ] Carrier D) : Prop :=
  ∀ (u : Carrier D) (n : ℤ) (v : Carrier D),
    U (((Y D u)[[n]]) v) = ((Y D (U u))[[n]]) (U v)

private theorem preservesModes_symm (D : LatticeData)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hMode : PreservesModes D U) :
    PreservesModes D U.symm := by
  intro u n v
  apply U.injective
  rw [U.apply_symm_apply, hMode, U.apply_symm_apply, U.apply_symm_apply]

private theorem vacuum_fixed (D : LatticeData)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hMode : PreservesModes D U) :
    U (vacuum D) = vacuum D := by
  have h := hMode (vacuum D) (-1) (U.symm (vacuum D))
  rw [stateField_vacuum, identity_modes, ite_eq_left rfl, LinearMap.id_apply,
    U.apply_symm_apply, stateField_creation] at h
  exact h.symm

private theorem grade_preserved (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hMode : PreservesModes D U)
    (hOmega : U (omega D H) = omega D H)
    (n : ℤ) (v : Carrier D) (hv : v ∈ grade D n) : U v ∈ grade D n := by
  have hGH : gramComplex D * H = 1 := mul_eq_one_comm.mp hHG
  have hL0 : ((Y D (omega D H))[[1]]) = sugawaraMode D H 0 := by
    simpa using omega_modes D H 0
  have h := hMode (omega D H) 1 v
  rw [hOmega, hL0, (actualL0_eigen_iff_grade D H hHG hGH n v).mpr hv, map_smul] at h
  exact (actualL0_eigen_iff_grade D H hHG hGH n (U v)).mp h.symm

private def currentBasis (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.Basis (Fin D.rank) ℂ (grade D 1) :=
  (gradeBasis D 1).reindex (Lattice.RootlessLowGrades.energyOneEquiv D hPos hRoot)

private theorem currentBasis_coe (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2) (i : Fin D.rank) :
    (currentBasis D hPos hRoot i : Carrier D) = currentState D i := by
  classical
  rw [currentBasis, Module.Basis.reindex_apply]
  let a := (Lattice.RootlessLowGrades.energyOneEquiv D hPos hRoot).symm i
  change (carrierCoeffEquiv D).symm
    (((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ)
      {b : Label D | energy D b = 1}).symm (Finsupp.single a 1)) : Label D →₀ ℂ) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  change carrierBasis D a.1 = _
  rw [carrierBasis_apply]
  change Finsupp.single 0 (monomial (Finsupp.single (i, 0) 1) 1) = currentState D i
  simp [currentState, MvPolynomial.X]

private theorem currentBasis_equivFun_symm_coe (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2) (x : Coordinates D) :
    ((currentBasis D hPos hRoot).equivFun.symm x : Carrier D) = current D x := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, currentBasis_coe, current]

#print axioms current_zero_coeff
#print axioms current_one_current

private theorem grade_one_map (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hMode : PreservesModes D U)
    (hOmega : U (omega D H) = omega D H) :
    (grade D 1).map U.toLinearMap = grade D 1 := by
  apply le_antisymm
  · rintro v ⟨u, hu, rfl⟩
    exact grade_preserved D H hHG U hMode hOmega 1 u hu
  · intro v hv
    have hOmegaInv : U.symm (omega D H) = omega D H := by
      apply U.injective
      rw [U.apply_symm_apply, hOmega]
    exact ⟨U.symm v, grade_preserved D H hHG U.symm
      (preservesModes_symm D U hMode) hOmegaInv 1 v hv, U.apply_symm_apply v⟩

private theorem current_transport (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hMode : PreservesModes D U)
    (hOmega : U (omega D H) = omega D H) :
    ∃ T : Coordinates D ≃ₗ[ℂ] Coordinates D,
      (∀ x, U (current D x) = current D (T x)) ∧
      ∀ x y, gram D (T x) (T y) = gram D x y := by
  let B := (currentBasis D hPos hRoot).equivFun
  let V := U.ofSubmodules (grade D 1) (grade D 1) (grade_one_map D H hHG U hMode hOmega)
  let T := (B.symm.trans V).trans B
  have hCurrent (x : Coordinates D) : U (current D x) = current D (T x) := by
    rw [← currentBasis_equivFun_symm_coe D hPos hRoot x,
      ← currentBasis_equivFun_symm_coe D hPos hRoot (T x)]
    change U (B.symm x : Carrier D) = (B.symm (B (V (B.symm x))) : Carrier D)
    rw [B.symm_apply_apply]
    rfl
  refine ⟨T, hCurrent, fun x y => ?_⟩
  have h := hMode (current D x) 1 (current D y)
  rw [current_one, map_smul, vacuum_fixed D U hMode, hCurrent, hCurrent, current_one] at h
  exact (smul_left_injective ℂ (vacuum_nonzero D) h).symm

private theorem gram_separates (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (x y : Coordinates D) (h : ∀ z, gram D z x = gram D z y) : x = y := by
  have hVec : gramComplex D *ᵥ x = gramComplex D *ᵥ y := by
    funext i
    simpa only [Matrix.toBilin'_apply', single_dotProduct, one_mul]
      using h (Pi.single i 1)
  simpa only [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
    using congrArg (fun v => H *ᵥ v) hVec

private theorem occupied_charge (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hMode : PreservesModes D U)
    (T : Coordinates D ≃ₗ[ℂ] Coordinates D)
    (hCurrent : ∀ x, U (current D x) = current D (T x))
    (hGram : ∀ x y, gram D (T x) (T y) = gram D x y)
    (a : Charge D) (p : Oscillator D) (q : Label D)
    (hq : carrierCoeffEquiv D (U (Finsupp.single a p)) q ≠ 0) :
    chargeVector D q.1 = T (chargeVector D a) := by
  apply gram_separates D H hHG
  intro z
  obtain ⟨x, rfl⟩ := T.surjective z
  have h := hMode (current D x) 0 (Finsupp.single a p)
  rw [current_zero_single, map_smul, hCurrent] at h
  have he := congrArg (fun w : Carrier D => carrierCoeffEquiv D w q) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, current_zero_coeff] at he
  exact (mul_right_cancel₀ hq he.symm).trans (hGram x (chargeVector D a)).symm

private abbrev ground (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single a (1 : Oscillator D)

private theorem ground_eq_basis (D : LatticeData) (a : Charge D) :
    ground D a = carrierBasis D (a, 0) := by
  simp [ground, monomial_zero']

private theorem exists_occupied_ground (D : LatticeData)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (a : Charge D) :
    ∃ q : Label D, carrierCoeffEquiv D (U (ground D a)) q ≠ 0 := by
  by_contra! h
  have hz : carrierCoeffEquiv D (U (ground D a)) = 0 := Finsupp.ext h
  have hGround : ground D a = 0 := by
    apply (((U.trans (carrierCoeffEquiv D)) : Carrier D ≃ₗ[ℂ] (Label D →₀ ℂ))).injective
    simpa only [LinearEquiv.trans_apply, map_zero] using hz
  exact (by simp [ground] : ground D a ≠ 0) hGround

/-- Every occupied coefficient in the image of a single charge sector has the
charge obtained by restricting the grade-one current action to the lattice.
This integral isometry is unique because every ground state has nonzero image. -/
theorem conformal_charge_transport (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (U : Carrier D ≃ₗ[ℂ] Carrier D)
    (hMode : ∀ u n v, U (((Y D u)[[n]]) v) = ((Y D (U u))[[n]]) (U v))
    (hOmega : U (omega D H) = omega D H) :
    ∃! s : Charge D ≃+ Charge D,
      (∀ a b, bilinear D (s a) (s b) = bilinear D a b) ∧
      ∀ (a : Charge D) (p : Oscillator D) (q : Label D),
        carrierCoeffEquiv D (U (Finsupp.single a p)) q ≠ 0 → q.1 = s a := by
  obtain ⟨T, hCurrent, hGram⟩ := current_transport D hPos hRoot H hHG U hMode hOmega
  have hForward (a : Charge D) : ∃ b, chargeVector D b = T (chargeVector D a) := by
    obtain ⟨q, hq⟩ := exists_occupied_ground D U a
    exact ⟨q.1, occupied_charge D H hHG U hMode T hCurrent hGram a 1 q hq⟩
  have hCurrentInv (x : Coordinates D) : U.symm (current D x) = current D (T.symm x) := by
    apply U.injective
    rw [U.apply_symm_apply, hCurrent, T.apply_symm_apply]
  have hGramInv (x y : Coordinates D) : gram D (T.symm x) (T.symm y) = gram D x y := by
    rw [← hGram (T.symm x) (T.symm y), T.apply_symm_apply, T.apply_symm_apply]
  have hBackward (b : Charge D) : ∃ a, chargeVector D a = T.symm (chargeVector D b) := by
    obtain ⟨q, hq⟩ := exists_occupied_ground D U.symm b
    exact ⟨q.1, occupied_charge D H hHG U.symm (preservesModes_symm D U hMode)
      T.symm hCurrentInv hGramInv b 1 q hq⟩
  choose forward hf using hForward
  choose backward hb using hBackward
  let s : Charge D ≃+ Charge D :=
    { toFun := forward
      invFun := backward
      left_inv := fun a => chargeVector_injective D (by rw [hb, hf, T.symm_apply_apply])
      right_inv := fun b => chargeVector_injective D (by rw [hf, hb, T.apply_symm_apply])
      map_add' := fun a b => chargeVector_injective D (by
        have hAdd (x y : Charge D) :
            chargeVector D (x + y) = chargeVector D x + chargeVector D y := by
          funext i
          exact Int.cast_add _ _
        rw [hf, hAdd, hAdd, map_add, hf, hf]) }
  have hs (a : Charge D) : chargeVector D (s a) = T (chargeVector D a) := hf a
  have hCharge (a : Charge D) (p : Oscillator D) (q : Label D)
      (hq : carrierCoeffEquiv D (U (Finsupp.single a p)) q ≠ 0) : q.1 = s a := by
    apply chargeVector_injective D
    rw [hs]
    exact occupied_charge D H hHG U hMode T hCurrent hGram a p q hq
  refine ⟨s, ⟨?_, hCharge⟩, ?_⟩
  · intro a b
    have h := hGram (chargeVector D a) (chargeVector D b)
    rw [← hs, ← hs, gram_charges, gram_charges] at h
    exact_mod_cast h
  · intro t ht
    apply AddEquiv.ext
    intro a
    obtain ⟨q, hq⟩ := exists_occupied_ground D U a
    exact (ht.2 a 1 q hq).symm.trans (hCharge a 1 q hq)

/-- A conformal automorphism of the actual rootless lattice carrier acts on
the ground lines by an integral additive isometry and nonzero scalars. -/
theorem conformal_ground_transport (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (U : Carrier D ≃ₗ[ℂ] Carrier D)
    (hMode : ∀ u n v, U (((Y D u)[[n]]) v) = ((Y D (U u))[[n]]) (U v))
    (hOmega : U (omega D H) = omega D H) :
    ∃ (s : Charge D ≃+ Charge D) (eta : Charge D → ℂˣ),
      (∀ a b, bilinear D (s a) (s b) = bilinear D a b) ∧
      ∀ a, U (Finsupp.single a (1 : Oscillator D)) =
        (eta a : ℂ) • Finsupp.single (s a) (1 : Oscillator D) := by
  classical
  obtain ⟨s, ⟨hGram, hCharge⟩, _⟩ :=
    conformal_charge_transport D hPos hRoot H hHG U hMode hOmega
  have hLabel (a : Charge D) (q : Label D)
      (hq : carrierCoeffEquiv D (U (ground D a)) q ≠ 0) : q = (s a, 0) := by
    have hFirst := hCharge a 1 q hq
    have hEnergy : chargeEnergy D (s a) = chargeEnergy D a := by
      simp only [chargeEnergy, hGram]
    have hg : ground D a ∈ grade D (chargeEnergy D a) := by
      have hGH : gramComplex D * H = 1 := mul_eq_one_comm.mp hHG
      rw [ground_eq_basis]
      apply (actualL0_eigen_iff_grade D H hHG hGH _ _).mp
      simpa [energy] using actualL0_basis D H hHG hGH (a, 0)
    have hgU := grade_preserved D H hHG U hMode hOmega _ _ hg
    have hOccupiedEnergy : energy D q = chargeEnergy D a := by
      by_contra hn
      exact hq ((mem_grade_iff D _ _).mp hgU q hn)
    have hOsc : oscillatorEnergy q.2 = 0 := by
      rw [energy, hFirst, hEnergy] at hOccupiedEnergy
      omega
    exact Prod.ext hFirst ((oscillatorEnergy_eq_zero_iff D _).mp hOsc)
  let z (a : Charge D) := carrierCoeffEquiv D (U (ground D a)) (s a, 0)
  have hz (a : Charge D) : z a ≠ 0 := by
    obtain ⟨q, hq⟩ := exists_occupied_ground D U a
    rwa [hLabel a q hq] at hq
  refine ⟨s, fun a => Units.mk0 (z a) (hz a), hGram, fun a => ?_⟩
  change U (ground D a) = z a • ground D (s a)
  rw [ground_eq_basis D (s a)]
  apply (carrierCoeffEquiv D).injective
  ext q
  simp only [map_smul, carrierCoeffEquiv_basis, Finsupp.smul_apply]
  by_cases hq : q = (s a, 0)
  · subst q
    simp [z]
  · have hZero : carrierCoeffEquiv D (U (ground D a)) q = 0 :=
      not_ne_iff.mp (fun h => hq (hLabel a q h))
    simp [hZero, Ne.symm hq]

#print axioms conformal_charge_transport
#print axioms conformal_ground_transport

private theorem ground_charge_unique (D : LatticeData) (a b : Charge D) (c d : ℂˣ)
    (h : (c : ℂ) • ground D a = (d : ℂ) • ground D b) : a = b := by
  classical
  by_contra hab
  have hCoeff := congrArg (fun v : Carrier D => v a) h
  have hz : (c : ℂ) • (1 : Oscillator D) = 0 := by
    simpa only [ground, Finsupp.smul_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hab, smul_zero] using hCoeff
  exact (smul_ne_zero c.ne_zero one_ne_zero) hz

/-- Given an identification of the integral isometry group, the recovered
charge action supplies the projection and ground phases of a conformal action. -/
theorem conformal_ground_projection (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    {G K : Type*} [Group G] [Group K]
    (mu : Additive K →+ AddAut (Charge D)) (hInj : Function.Injective mu)
    (hOnto : ∀ s : AddAut (Charge D), (∀ a b, bilinear D (s a) (s b) = bilinear D a b) →
      ∃ k : Additive K, mu k = s)
    (U : G →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (hMode : ∀ g u n v, U g (((Y D u)[[n]]) v) = ((Y D (U g u))[[n]]) (U g v))
    (hOmega : ∀ g, U g (omega D H) = omega D H) :
    ∃ (pi : G →* K) (eta : G → Charge D → ℂˣ), ∀ g a,
      U g (Finsupp.single a (1 : Oscillator D)) =
        (eta g a : ℂ) • Finsupp.single (mu (pi g) a) (1 : Oscillator D) := by
  classical
  have hLift (g : G) : ∃ (s : Charge D ≃+ Charge D) (eta : Charge D → ℂˣ),
      (∀ a b, bilinear D (s a) (s b) = bilinear D a b) ∧
      ∀ a, U g (ground D a) = (eta a : ℂ) • ground D (s a) :=
    conformal_ground_transport D hPos hRoot H hHG (U g) (hMode g) (hOmega g)
  choose s eta hGram hGround using hLift
  choose k hk using fun g => hOnto (s g) (hGram g)
  have hOne : s 1 = 0 := by
    apply AddEquiv.ext
    intro a
    change s 1 a = a
    apply ground_charge_unique D _ _ (eta 1 a) 1
    rw [Units.val_one, one_smul, ← hGround, map_one]
    rfl
  have hMul (g h : G) : s (g * h) = s g + s h := by
    apply AddEquiv.ext
    intro a
    change s (g * h) a = s g (s h a)
    apply ground_charge_unique D _ _ (eta (g * h) a) (eta h a * eta g (s h a))
    calc
      (eta (g * h) a : ℂ) • ground D (s (g * h) a) = U (g * h) (ground D a) :=
        (hGround (g * h) a).symm
      _ = U g (U h (ground D a)) := by
        rw [map_mul]
        rfl
      _ = (↑(eta h a * eta g (s h a)) : ℂ) • ground D (s g (s h a)) := by
        rw [hGround h a, map_smul, hGround g (s h a), smul_smul, Units.val_mul]
  let pi : G →* K :=
    { toFun := fun g => (k g).toMul
      map_one' := show k 1 = (0 : Additive K) by
        apply hInj
        rw [hk, hOne, map_zero]
      map_mul' := fun g h => show k (g * h) = k g + k h by
        apply hInj
        rw [hk, map_add, hk, hk, hMul] }
  refine ⟨pi, eta, fun g a => ?_⟩
  change U g (ground D a) = (eta g a : ℂ) • ground D (mu (k g) a)
  rw [hk]
  exact hGround g a

#print axioms conformal_ground_projection

end
end D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport

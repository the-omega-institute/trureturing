/- GID: D5/S3/VertexAlgebra/Lattice/InvolutionRootlessLowGrades
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/InvolutionRootlessLowGrades
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Production reflection conjugacy and actual fixed Sugawara low-energy orbit basis. -/

import D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
import D5.S3.VertexAlgebra.LatticeInvolution
import Mathlib.Data.Quot
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

/-! Production lattice reflection on complete rootless low-energy spaces.
The fixed basis uses unordered oscillator pairs and free integral charge orbits. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open D5.S3.VertexAlgebra.Lattice.RootlessLowGrades LatticeInvolution LatticeSugawaraCurrents
open MvPolynomial
open scoped BigOperators Classical

private abbrev FixedGrade (D : LatticeData) (n : ℤ) : Submodule ℂ (Carrier D) :=
  fixedSpace D ⊓ grade D n

/-! The actual integral norm-four shell and its free negation orbits. -/

private def normFourNeg (D : LatticeData) (a : NormFour D) : NormFour D :=
  ⟨-a.1, by simpa only [bilinear_neg_neg] using a.2⟩

@[simp] private theorem normFourNeg_involutive (D : LatticeData) (a : NormFour D) :
    normFourNeg D (normFourNeg D a) = a := by
  apply Subtype.ext
  exact neg_neg a.1

private theorem normFour_ne_zero (D : LatticeData) (a : NormFour D) : a.1 ≠ 0 := by
  intro h
  have ha := a.2
  simp [h, bilinear] at ha

/-- Over the actual integral charge functions, a = -a forces every entry
to vanish. The norm-four equation then excludes that charge. -/
private theorem normFourNeg_ne (D : LatticeData) (a : NormFour D) :
    normFourNeg D a ≠ a := by
  intro h
  apply normFour_ne_zero D a
  funext i
  change a.1 i = 0
  have hi := congrArg (fun b : NormFour D => b.1 i) h
  change -a.1 i = a.1 i at hi
  omega

private def normFourOrbitSetoid (D : LatticeData) : Setoid (NormFour D) where
  r a b := a = b ∨ normFourNeg D a = b
  iseqv := by
    refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
    · intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [← h, normFourNeg_involutive])
    · intro a b c hab hbc
      rcases hab with hab | hab
      · subst b
        exact hbc
      · rcases hbc with hbc | hbc
        · exact Or.inr (hab.trans hbc)
        · exact Or.inl (by rw [← hbc, ← hab, normFourNeg_involutive])

abbrev NormFourOrbit (D : LatticeData) := Quotient (normFourOrbitSetoid D)

private def normFourOrbitMk (D : LatticeData) (a : NormFour D) : NormFourOrbit D :=
  Quotient.mk (normFourOrbitSetoid D) a

def normFourOrbitRep (D : LatticeData) (q : NormFourOrbit D) : NormFour D :=
  q.out

@[simp] private theorem normFourOrbitMk_neg (D : LatticeData) (a : NormFour D) :
    normFourOrbitMk D (normFourNeg D a) = normFourOrbitMk D a := by
  apply Quotient.sound
  exact Or.inr (normFourNeg_involutive D a)

@[simp] private theorem normFourOrbitMk_rep (D : LatticeData) (q : NormFourOrbit D) :
    normFourOrbitMk D (normFourOrbitRep D q) = q :=
  Quotient.out_eq q

private theorem normFourOrbit_rep_cases (D : LatticeData) (a : NormFour D) :
    normFourOrbitRep D (normFourOrbitMk D a) = a ∨
      normFourNeg D (normFourOrbitRep D (normFourOrbitMk D a)) = a :=
  Quotient.mk_out (s := normFourOrbitSetoid D) a

/-- A genuine choice of one representative per two-element orbit. No
orientation, enumeration or orbit-cardinality premise is assumed. -/
private def normFourDoubleDecode (D : LatticeData) : NormFourOrbit D × Bool → NormFour D
  | (q, false) => normFourOrbitRep D q
  | (q, true) => normFourNeg D (normFourOrbitRep D q)

@[simp] private theorem normFourDoubleDecode_orbit (D : LatticeData)
    (x : NormFourOrbit D × Bool) :
    normFourOrbitMk D (normFourDoubleDecode D x) = x.1 := by
  rcases x with ⟨q, b⟩
  cases b <;> simp [normFourDoubleDecode]

private theorem normFourDoubleDecode_bijective (D : LatticeData) :
    Function.Bijective (normFourDoubleDecode D) := by
  constructor
  · rintro ⟨q, b⟩ ⟨p, c⟩ h
    have hqp : q = p := by
      have h' := congrArg (normFourOrbitMk D) h
      simpa only [normFourDoubleDecode_orbit] using h'
    subst p
    have hbc : b = c := by
      cases b <;> cases c
      · rfl
      · exact False.elim ((normFourNeg_ne D (normFourOrbitRep D q)) h.symm)
      · exact False.elim ((normFourNeg_ne D (normFourOrbitRep D q)) h)
      · rfl
    exact Prod.ext rfl hbc
  · intro a
    rcases normFourOrbit_rep_cases D a with h | h
    · exact ⟨(normFourOrbitMk D a, false), h⟩
    · exact ⟨(normFourOrbitMk D a, true), h⟩

private def normFourDoubleEquiv (D : LatticeData) :
    NormFourOrbit D × Bool ≃ NormFour D :=
  Equiv.ofBijective (normFourDoubleDecode D) (normFourDoubleDecode_bijective D)

private theorem normFourOrbit_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Finite (NormFourOrbit D) := by
  letI : Finite (NormFour D) := normFour_finite D hD
  apply Finite.of_surjective (normFourOrbitMk D)
  intro q
  exact ⟨normFourOrbitRep D q, normFourOrbitMk_rep D q⟩

private theorem normFour_card_twice_orbits (D : LatticeData) :
    Nat.card (NormFour D) = 2 * Nat.card (NormFourOrbit D) := by
  rw [← Nat.card_congr (normFourDoubleEquiv D), Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm]

/-- Free negation, not a numerical sphere enumeration, proves evenness. -/
private theorem normFourOrbit_card (D : LatticeData) :
    Nat.card (NormFourOrbit D) = Nat.card (NormFour D) / 2 := by
  rw [normFour_card_twice_orbits]
  omega

/-! Literal low-grade coordinates, before transport to the actual carrier. -/

abbrev TwoConfig (D : LatticeData) :=
  (Fin D.rank ⊕ Sym (Fin D.rank) 2) ⊕ NormFour D

abbrev FixedTwoIndex (D : LatticeData) :=
  Sym (Fin D.rank) 2 ⊕ NormFourOrbit D

private def configFlip (D : LatticeData) : TwoConfig D → TwoConfig D
  | Sum.inl x => Sum.inl x
  | Sum.inr a => Sum.inr (normFourNeg D a)

@[simp] private theorem configFlip_involutive (D : LatticeData) (j : TwoConfig D) :
    configFlip D (configFlip D j) = j := by
  rcases j with (i | s) | a <;> simp [configFlip]

private def configSign (D : LatticeData) : TwoConfig D → ℂ
  | Sum.inl (Sum.inl _) => -1
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr _ => 1

@[simp] private theorem configSign_flip (D : LatticeData) (j : TwoConfig D) :
    configSign D (configFlip D j) = configSign D j := by
  rcases j with (i | s) | a <;> rfl

def coordinateTheta (D : LatticeData) : Module.End ℂ (TwoConfig D → ℂ) where
  toFun f j := configSign D j * f (configFlip D j)
  map_add' f g := by funext j; exact mul_add _ _ _
  map_smul' c f := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private def FixedCoordinates (D : LatticeData) : Submodule ℂ (TwoConfig D → ℂ) :=
  LinearMap.ker (coordinateTheta D - LinearMap.id)

@[simp] private theorem mem_fixedCoordinates (D : LatticeData) (f : TwoConfig D → ℂ) :
    f ∈ FixedCoordinates D ↔ coordinateTheta D f = f := by
  simp [FixedCoordinates, LinearMap.mem_ker, sub_eq_zero]

private theorem coordinateTheta_single (D : LatticeData) (j : TwoConfig D) :
    coordinateTheta D (Pi.single j 1) =
      configSign D j • Pi.single (configFlip D j) 1 := by
  classical
  funext i
  by_cases hi : i = configFlip D j
  · subst i
    simp [coordinateTheta, configFlip_involutive, configSign_flip]
  · have hne : configFlip D i ≠ j := by
      intro h
      have hh := congrArg (configFlip D) h
      exact hi (by simpa only [configFlip_involutive] using hh)
    simp [coordinateTheta, Pi.single_apply, hi, Ne.symm hi, hne, Ne.symm hne]

/-- Fill both members of each charge orbit with the SAME coefficient;
the odd neutral sector is zero and the symmetric-pair sector is arbitrary. -/
private def fillFixedCoordinates (D : LatticeData) :
    (FixedTwoIndex D → ℂ) →ₗ[ℂ] (TwoConfig D → ℂ) where
  toFun f
    | Sum.inl (Sum.inl _) => 0
    | Sum.inl (Sum.inr s) => f (Sum.inl s)
    | Sum.inr a => f (Sum.inr (normFourOrbitMk D a))
  map_add' f g := by
    funext j
    rcases j with (i | s) | a <;> simp
  map_smul' c f := by
    funext j
    rcases j with (i | s) | a <;> simp

private theorem fillFixedCoordinates_mem (D : LatticeData) (f : FixedTwoIndex D → ℂ) :
    fillFixedCoordinates D f ∈ FixedCoordinates D := by
  rw [mem_fixedCoordinates]
  funext j
  rcases j with (i | s) | a <;>
    simp [coordinateTheta, configSign, configFlip, fillFixedCoordinates]

private def extractFixedCoordinates (D : LatticeData) :
    FixedCoordinates D →ₗ[ℂ] (FixedTwoIndex D → ℂ) where
  toFun f
    | Sum.inl s => f.1 (Sum.inl (Sum.inr s))
    | Sum.inr q => f.1 (Sum.inr (normFourOrbitRep D q))
  map_add' f g := by funext j; cases j <;> rfl
  map_smul' c f := by funext j; cases j <;> rfl

/-- The fixed coordinate space is exactly one coordinate per even neutral
monomial and per actual ± charge orbit. This is an isomorphism, not a
dimension or trace assumption. It does not require shell finiteness. -/
private def fixedCoordinatesEquiv (D : LatticeData) :
    FixedCoordinates D ≃ₗ[ℂ] (FixedTwoIndex D → ℂ) where
  toFun := extractFixedCoordinates D
  invFun f := ⟨fillFixedCoordinates D f, fillFixedCoordinates_mem D f⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    have hf := (mem_fixedCoordinates D f.1).mp f.2
    rcases j with (i | s) | a
    · have hi := congrFun hf (Sum.inl (Sum.inl i))
      change -1 * f.1 (Sum.inl (Sum.inl i)) = f.1 (Sum.inl (Sum.inl i)) at hi
      change 0 = f.1 (Sum.inl (Sum.inl i))
      linear_combination (1 / 2 : ℂ) * hi
    · rfl
    · change f.1 (Sum.inr (normFourOrbitRep D (normFourOrbitMk D a))) =
        f.1 (Sum.inr a)
      rcases normFourOrbit_rep_cases D a with h | h
      · rw [h]
      · have ha := congrFun hf
          (Sum.inr (normFourOrbitRep D (normFourOrbitMk D a)))
        change (1 : ℂ) *
          f.1 (Sum.inr (normFourNeg D (normFourOrbitRep D (normFourOrbitMk D a)))) =
            f.1 (Sum.inr (normFourOrbitRep D (normFourOrbitMk D a))) at ha
        simpa only [one_mul, h] using ha.symm
  right_inv f := by
    funext j
    rcases j with s | q
    · rfl
    · change f (Sum.inr (normFourOrbitMk D (normFourOrbitRep D q))) = f (Sum.inr q)
      rw [normFourOrbitMk_rep]
  map_add' f g := (extractFixedCoordinates D).map_add f g
  map_smul' c f := (extractFixedCoordinates D).map_smul c f

/-! Production monomials and their actual neutral/charged parity. -/

/-- Expose the existing gradeBasis as the literal actual-carrier monomial.
This is just the supported-Finsupp inverse used by gradeCoeffEquiv. -/
private theorem gradeBasis_coe (D : LatticeData) (n : ℤ) (x : EnergyFiber D n) :
    (gradeBasis D n x : Carrier D) = carrierBasis D x.1 := by
  classical
  change (carrierCoeffEquiv D).symm
      (((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ)
        {a : Label D | energy D a = n}).symm (Finsupp.single x 1)) : Label D →₀ ℂ) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

private theorem occurrences_single_one (D : LatticeData) (x : Index D) :
    (occurrences D (Finsupp.single x 1)).length = 1 := by
  simp [occurrences, Multiset.length_toList]

private theorem occurrences_pairOccupation (D : LatticeData) (s : Sym (Fin D.rank) 2) :
    (occurrences D (pairOccupation D s)).length = 2 := by
  rw [occurrences, Multiset.length_toList, pairOccupation,
    Multiset.toFinsupp_toMultiset, Multiset.card_map]
  exact s.2

private def gradeOneBasis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.Basis (Fin D.rank) ℂ (grade D 1) :=
  (gradeBasis D 1).reindex (energyOneEquiv D hD hroot)

private theorem gradeOneBasis_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (i : Fin D.rank) :
    (gradeOneBasis D hD hroot i : Carrier D) =
      Finsupp.single 0 (monomial (Finsupp.single (i, 0) 1) 1) := by
  rw [gradeOneBasis, Module.Basis.reindex_apply, gradeBasis_coe, carrierBasis_apply]
  rfl

private theorem gradeTwoBasis_odd_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (i : Fin D.rank) :
    (gradeTwoBasis D hD hroot (Sum.inl (Sum.inl i)) : Carrier D) =
      Finsupp.single 0 (monomial (Finsupp.single (i, 1) 1) 1) := by
  rw [gradeTwoBasis, Module.Basis.reindex_apply, gradeBasis_coe, carrierBasis_apply]
  rfl

private theorem gradeTwoBasis_even_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (s : Sym (Fin D.rank) 2) :
    (gradeTwoBasis D hD hroot (Sum.inl (Sum.inr s)) : Carrier D) =
      Finsupp.single 0 (monomial (pairOccupation D s) 1) := by
  rw [gradeTwoBasis, Module.Basis.reindex_apply, gradeBasis_coe, carrierBasis_apply]
  rfl

private theorem gradeTwoBasis_charge_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (a : NormFour D) :
    (gradeTwoBasis D hD hroot (Sum.inr a) : Carrier D) =
      Finsupp.single a.1 1 := by
  rw [gradeTwoBasis, Module.Basis.reindex_apply, gradeBasis_coe, carrierBasis_apply]
  change Finsupp.single a.1 (monomial 0 (1 : ℂ)) = Finsupp.single a.1 1
  simp

/-- The mode index does not affect oscillator parity: a single oscillator
is odd, including the mode-two neutral oscillator. -/
private theorem theta_neutral_single_monomial (D : LatticeData) (x : Index D) :
    theta D (Finsupp.single 0 (monomial (Finsupp.single x 1) (1 : ℂ))) =
      -Finsupp.single (0 : Charge D) (monomial (Finsupp.single x 1) (1 : ℂ)) := by
  change thetaLinear D _ = _
  rw [theta_single, sigma_monomial, occurrences_single_one]
  simp [← Finsupp.smul_single]

private theorem theta_gradeOneBasis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (i : Fin D.rank) :
    theta D (gradeOneBasis D hD hroot i : Carrier D) =
      -(gradeOneBasis D hD hroot i : Carrier D) := by
  rw [gradeOneBasis_coe]
  exact theta_neutral_single_monomial D (i, 0)

private theorem theta_gradeTwoBasis_odd (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (i : Fin D.rank) :
    theta D (gradeTwoBasis D hD hroot (Sum.inl (Sum.inl i)) : Carrier D) =
      -(gradeTwoBasis D hD hroot (Sum.inl (Sum.inl i)) : Carrier D) := by
  rw [gradeTwoBasis_odd_coe]
  exact theta_neutral_single_monomial D (i, 1)

private theorem theta_gradeTwoBasis_even (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (s : Sym (Fin D.rank) 2) :
    theta D (gradeTwoBasis D hD hroot (Sum.inl (Sum.inr s)) : Carrier D) =
      (gradeTwoBasis D hD hroot (Sum.inl (Sum.inr s)) : Carrier D) := by
  rw [gradeTwoBasis_even_coe]
  change thetaLinear D _ = _
  rw [theta_single, sigma_monomial, occurrences_pairOccupation]
  simp

/-- This phase-one identity comes from production theta_single, not from
an assumed lift. theta_involutive is already proved by that implementation. -/
private theorem theta_gradeTwoBasis_charge (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (a : NormFour D) :
    theta D (gradeTwoBasis D hD hroot (Sum.inr a) : Carrier D) =
      (gradeTwoBasis D hD hroot (Sum.inr (normFourNeg D a)) : Carrier D) := by
  rw [gradeTwoBasis_charge_coe, gradeTwoBasis_charge_coe]
  change thetaLinear D (Finsupp.single a.1 1) = Finsupp.single (-a.1) 1
  rw [theta_single, map_one]

private theorem theta_gradeTwoBasis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (j : TwoConfig D) :
    theta D (gradeTwoBasis D hD hroot j : Carrier D) =
      configSign D j • (gradeTwoBasis D hD hroot (configFlip D j) : Carrier D) := by
  rcases j with (i | s) | a
  · simpa only [configSign, configFlip, neg_one_smul] using
      theta_gradeTwoBasis_odd D hD hroot i
  · simpa only [configSign, configFlip, one_smul] using
      theta_gradeTwoBasis_even D hD hroot s
  · simpa only [configSign, configFlip, one_smul] using
      theta_gradeTwoBasis_charge D hD hroot a

/-! Exact identification with production theta, on the whole actual grade. -/

def gradeTwoCoordinateEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    grade D 2 ≃ₗ[ℂ] (TwoConfig D → ℂ) := by
  letI : Finite (NormFour D) := normFour_finite D hD
  exact (gradeTwoBasis D hD hroot).equivFun

private theorem gradeTwoCoordinateEquiv_basis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (j : TwoConfig D) :
    gradeTwoCoordinateEquiv D hD hroot (gradeTwoBasis D hD hroot j) =
      Pi.single j 1 := by
  classical
  letI : Finite (NormFour D) := normFour_finite D hD
  funext i
  simp [gradeTwoCoordinateEquiv, Module.Basis.equivFun_self, Pi.single_apply, eq_comm]

private theorem gradeTwoCoordinateEquiv_symm_single (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (j : TwoConfig D) :
    (gradeTwoCoordinateEquiv D hD hroot).symm (Pi.single j 1) =
      gradeTwoBasis D hD hroot j := by
  apply (gradeTwoCoordinateEquiv D hD hroot).injective
  rw [LinearEquiv.apply_symm_apply, gradeTwoCoordinateEquiv_basis]

/-- The coordinate action is identified with the ACTUAL theta on every
vector of the actual grade, not merely on a substitute coordinate module. -/
theorem theta_gradeTwo_coordinate_transport (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (v : grade D 2) :
    theta D (v : Carrier D) =
      ((gradeTwoCoordinateEquiv D hD hroot).symm
        (coordinateTheta D (gradeTwoCoordinateEquiv D hD hroot v)) : Carrier D) := by
  let e := gradeTwoCoordinateEquiv D hD hroot
  let lhs : grade D 2 →ₗ[ℂ] Carrier D :=
    (thetaLinear D).comp (grade D 2).subtype
  let rhs : grade D 2 →ₗ[ℂ] Carrier D :=
    (grade D 2).subtype.comp
      (e.symm.toLinearMap.comp ((coordinateTheta D).comp e.toLinearMap))
  have he : lhs = rhs := by
    apply (gradeTwoBasis D hD hroot).ext
    intro j
    change theta D (gradeTwoBasis D hD hroot j : Carrier D) =
      (e.symm (coordinateTheta D (e (gradeTwoBasis D hD hroot j))) : Carrier D)
    rw [show e (gradeTwoBasis D hD hroot j) = Pi.single j 1 from
      gradeTwoCoordinateEquiv_basis D hD hroot j]
    rw [coordinateTheta_single, map_smul]
    change _ = configSign D j •
      ((gradeTwoCoordinateEquiv D hD hroot).symm
        (Pi.single (configFlip D j) 1) : Carrier D)
    rw [gradeTwoCoordinateEquiv_symm_single]
    exact theta_gradeTwoBasis D hD hroot j
  exact LinearMap.congr_fun he v

/-- Restrict the proved coordinate conjugacy to the literal intersection
fixedSpace D ∩ grade D 2. The inverse remains an actual carrier vector. -/
private def fixedGradeTwoCoordinateEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    FixedGrade D 2 ≃ₗ[ℂ] FixedCoordinates D := by
  let e := gradeTwoCoordinateEquiv D hD hroot
  exact
    { toFun := fun v => ⟨e ⟨v.1, v.2.2⟩, by
        rw [mem_fixedCoordinates]
        apply e.symm.injective
        rw [LinearEquiv.symm_apply_apply]
        apply Subtype.ext
        exact (theta_gradeTwo_coordinate_transport D hD hroot ⟨v.1, v.2.2⟩).symm.trans
          ((mem_fixedSpace D v.1).mp v.2.1)⟩
      invFun := fun f => ⟨(e.symm f.1 : Carrier D), by
        refine ⟨(mem_fixedSpace D _).mpr ?_, (e.symm f.1).2⟩
        rw [theta_gradeTwo_coordinate_transport D hD hroot]
        change (e.symm (coordinateTheta D (e (e.symm f.1))) : Carrier D) = _
        rw [LinearEquiv.apply_symm_apply, (mem_fixedCoordinates D f.1).mp f.2]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact congrArg (fun w : grade D 2 => (w : Carrier D))
          (e.symm_apply_apply ⟨v.1, v.2.2⟩)
      right_inv := by
        intro f
        apply Subtype.ext
        exact e.apply_symm_apply f.1
      map_add' := by
        intro v w
        apply Subtype.ext
        exact e.map_add ⟨v.1, v.2.2⟩ ⟨w.1, w.2.2⟩
      map_smul' := by
        intro c v
        apply Subtype.ext
        exact e.map_smul c ⟨v.1, v.2.2⟩ }

/-- Exact fixed-space parametrization, with the real low-grade basis
bijections and the production-theta conjugacy both on the proof path. -/
private def fixedGradeTwoEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    FixedGrade D 2 ≃ₗ[ℂ] (FixedTwoIndex D → ℂ) :=
  (fixedGradeTwoCoordinateEquiv D hD hroot).trans (fixedCoordinatesEquiv D)

/-- The inverse has zero coefficient on every mode-two neutral oscillator,
the supplied coefficient on each symmetric mode-one pair, and the same
supplied orbit coefficient on BOTH charged ground states in each ± pair. -/
private def fixedGradeTwoBasis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.Basis (FixedTwoIndex D) ℂ (FixedGrade D 2) := by
  letI : Finite (NormFourOrbit D) := normFourOrbit_finite D hD
  exact Module.Basis.ofEquivFun (fixedGradeTwoEquiv D hD hroot)

/-! Exhibit the actual two-charge fixed vectors, and identify their
coordinates. This makes the charge-pair basis explicit in the carrier. -/

private def chargeOrbitFixedVector (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (q : NormFourOrbit D) : FixedGrade D 2 := by
  let b := gradeTwoBasis D hD hroot
  let a := normFourOrbitRep D q
  refine ⟨(b (Sum.inr a) : Carrier D) +
    (b (Sum.inr (normFourNeg D a)) : Carrier D), ?_, ?_⟩
  · apply (mem_fixedSpace D _).mpr
    rw [map_add]
    rw [theta_gradeTwoBasis_charge, theta_gradeTwoBasis_charge,
      normFourNeg_involutive]
    exact add_comm _ _
  · exact (grade D 2).add_mem (b (Sum.inr a)).2
      (b (Sum.inr (normFourNeg D a))).2

private theorem chargeOrbitFixedVector_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (q : NormFourOrbit D) :
    (chargeOrbitFixedVector D hD hroot q : Carrier D) =
      Finsupp.single (normFourOrbitRep D q).1 1 +
        Finsupp.single (-(normFourOrbitRep D q).1) 1 := by
  change (gradeTwoBasis D hD hroot (Sum.inr (normFourOrbitRep D q)) : Carrier D) +
    (gradeTwoBasis D hD hroot (Sum.inr (normFourNeg D (normFourOrbitRep D q))) :
      Carrier D) = _
  rw [gradeTwoBasis_charge_coe, gradeTwoBasis_charge_coe]
  rfl

private theorem fixedGradeTwoEquiv_chargeOrbitFixedVector (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (q : NormFourOrbit D) :
    fixedGradeTwoEquiv D hD hroot (chargeOrbitFixedVector D hD hroot q) =
      Pi.single (Sum.inr q) 1 := by
  classical
  let e := gradeTwoCoordinateEquiv D hD hroot
  let a := normFourOrbitRep D q
  have hc : e
      ⟨(chargeOrbitFixedVector D hD hroot q : Carrier D),
        (chargeOrbitFixedVector D hD hroot q).2.2⟩ =
      Pi.single (Sum.inr a) 1 + Pi.single (Sum.inr (normFourNeg D a)) 1 := by
    change e (gradeTwoBasis D hD hroot (Sum.inr a) +
      gradeTwoBasis D hD hroot (Sum.inr (normFourNeg D a))) = _
    rw [map_add, gradeTwoCoordinateEquiv_basis, gradeTwoCoordinateEquiv_basis]
  funext j
  rcases j with s | p
  · change e ⟨(chargeOrbitFixedVector D hD hroot q : Carrier D),
      (chargeOrbitFixedVector D hD hroot q).2.2⟩ (Sum.inl (Sum.inr s)) = _
    rw [hc]
    simp [Pi.single_apply]
  · change e ⟨(chargeOrbitFixedVector D hD hroot q : Carrier D),
      (chargeOrbitFixedVector D hD hroot q).2.2⟩ (Sum.inr (normFourOrbitRep D p)) = _
    rw [hc]
    by_cases hp : q = p
    · subst p
      have hna := normFourNeg_ne D a
      simp [a, Pi.single_apply, hna, Ne.symm hna]
    · have hrep : a ≠ normFourOrbitRep D p := by
        intro h
        apply hp
        have h' := congrArg (normFourOrbitMk D) h
        simpa only [a, normFourOrbitMk_rep] using h'
      have hneg : normFourNeg D a ≠ normFourOrbitRep D p := by
        intro h
        apply hp
        have h' := congrArg (normFourOrbitMk D) h
        simpa only [normFourOrbitMk_neg, a, normFourOrbitMk_rep] using h'
      simp [Pi.single_apply, hrep, Ne.symm hrep, hneg, Ne.symm hneg, hp, Ne.symm hp]

private theorem fixedGradeTwoBasis_coordinates (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (j : FixedTwoIndex D) :
    fixedGradeTwoEquiv D hD hroot (fixedGradeTwoBasis D hD hroot j) =
      Pi.single j 1 := by
  classical
  letI : Finite (NormFourOrbit D) := normFourOrbit_finite D hD
  let e := fixedGradeTwoEquiv D hD hroot
  change e (Module.Basis.ofEquivFun e j) = Pi.single j 1
  have hb : Module.Basis.ofEquivFun e j = e.symm (Pi.single j 1) :=
    congrFun (Module.Basis.coe_ofEquivFun e) j
  rw [hb, LinearEquiv.apply_symm_apply]

/-- Each charge-orbit basis vector is literally e^a + e^(-a), for the
production phase-one lift. Its independence and spanning follow from
fixedGradeTwoEquiv, not from an orbit-count hypothesis. -/
private theorem fixedGradeTwoBasis_charge_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (q : NormFourOrbit D) :
    (fixedGradeTwoBasis D hD hroot (Sum.inr q) : Carrier D) =
      Finsupp.single (normFourOrbitRep D q).1 1 +
        Finsupp.single (-(normFourOrbitRep D q).1) 1 := by
  have h : fixedGradeTwoBasis D hD hroot (Sum.inr q) =
      chargeOrbitFixedVector D hD hroot q := by
    apply (fixedGradeTwoEquiv D hD hroot).injective
    rw [fixedGradeTwoBasis_coordinates, fixedGradeTwoEquiv_chargeOrbitFixedVector]
  rw [h, chargeOrbitFixedVector_coe]

/-! Energy zero and one: actual vacuum and actual odd neutral sector. -/

private theorem grade_zero_le_fixedSpace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    grade D 0 ≤ fixedSpace D := by
  rw [grade_zero D hD]
  apply Submodule.span_le.mpr
  intro v hv
  have hv' : v = vacuum D := Set.mem_singleton_iff.mp hv
  rw [hv']
  exact (mem_fixedSpace D _).mpr (theta_vacuum D)

private theorem fixedGrade_zero_eq (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    FixedGrade D 0 = grade D 0 :=
  inf_eq_right.mpr (grade_zero_le_fixedSpace D hD)

private theorem theta_grade_one (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (v : grade D 1) :
    theta D (v : Carrier D) = -(v : Carrier D) := by
  have h : (thetaLinear D).comp (grade D 1).subtype = -(grade D 1).subtype := by
    apply (gradeOneBasis D hD hroot).ext
    intro i
    exact theta_gradeOneBasis D hD hroot i
  exact LinearMap.congr_fun h v

private theorem fixedGrade_one_eq_bot (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    FixedGrade D 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  have hfixed : theta D v = v := (mem_fixedSpace D v).mp hv.1
  have hodd : theta D v = -v := theta_grade_one D hD hroot ⟨v, hv.2⟩
  have heq : v = -v := hfixed.symm.trans hodd
  have hz : (2 : ℂ) • v = 0 := by
    calc
      (2 : ℂ) • v = v + v := two_smul ℂ v
      _ = v + -v := congrArg (fun w : Carrier D => v + w) heq
      _ = 0 := add_neg_cancel v
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem fixedGrade_zero_finrank (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Module.finrank ℂ (FixedGrade D 0) = 1 := by
  rw [fixedGrade_zero_eq D hD,
    Module.finrank_eq_nat_card_basis (gradeBasis D 0),
    Nat.card_congr (energyZeroEquiv D hD)]
  simp

private theorem fixedGrade_one_finrank (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.finrank ℂ (FixedGrade D 1) = 0 := by
  rw [fixedGrade_one_eq_bot D hD hroot]
  simp

private theorem fixedGrade_two_finrank (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.finrank ℂ (FixedGrade D 2) =
      Nat.choose (D.rank + 1) 2 + Nat.card (NormFour D) / 2 := by
  letI : Finite (NormFourOrbit D) := normFourOrbit_finite D hD
  have hn : Nat.card (Fin D.rank) + 2 - 1 = D.rank + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hs : Nat.card (Sym (Fin D.rank) 2) = Nat.choose (D.rank + 1) 2 := by
    rw [Sym.natCard_sym_eq_choose, hn]
  rw [Module.finrank_eq_nat_card_basis (fixedGradeTwoBasis D hD hroot)]
  change Nat.card (Sym (Fin D.rank) 2 ⊕ NormFourOrbit D) = _
  rw [Nat.card_sum, hs, normFourOrbit_card]

/-! Canonical Sugawara L0, with the actual fixed-VA carrier intersection. -/

private theorem canonicalFixedEnergy_eq_fixedGrade (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) :
    fixedSpace D ⊓
        (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (n : ℂ) =
      FixedGrade D n := by
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists D hD
  have hH : (gramComplex D)⁻¹ = H := Matrix.inv_eq_left_inv hHG
  rw [hH, actualL0_eigenspace_eq_grade D H hHG hGH n]

/-- The basis of the literal fixed-space intersection with the canonical
energy-two Sugawara eigenspace, indexed by neutral pairs and charge orbits. -/
def actualFixedEnergyTwoBasis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.Basis (FixedTwoIndex D) ℂ
      ↥(fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)) :=
  (fixedGradeTwoBasis D hD hroot).map
    (LinearEquiv.ofEq _ _ (canonicalFixedEnergy_eq_fixedGrade D hD 2)).symm

/-- The charge-orbit vector in the literal canonical L0 eigenspace. -/
theorem actualFixedEnergyTwoBasis_charge_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (q : NormFourOrbit D) :
    (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q) : Carrier D) =
      Finsupp.single (normFourOrbitRep D q).1 1 +
        Finsupp.single (-(normFourOrbitRep D q).1) 1 := by
  exact fixedGradeTwoBasis_charge_coe D hD hroot q

/-- Arbitrary rank, including rank zero. The only premises are positivity
and rootlessness of the supplied even LatticeData. These are the literal
fixedSpace intersections in the production actual fixed vertex algebra.
No trace, fixed dimension, orbit count, shell count or degree-classification
conclusion is assumed. The low-grade basis supplies energyZeroEquiv,
energyOneEquiv and gradeTwoBasis. -/
theorem actual_theta_fixed_rootless_low_spectrum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.finrank ℂ
      ↥(fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 0) = 1 ∧
    Module.finrank ℂ
      ↥(fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 1) = 0 ∧
    Module.finrank ℂ
      ↥(fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 2) =
        Nat.choose (D.rank + 1) 2 +
          Nat.card {a : Charge D // bilinear D a a = 4} / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have he := canonicalFixedEnergy_eq_fixedGrade D hD 0
    rw [Int.cast_zero] at he
    rw [he]
    exact fixedGrade_zero_finrank D hD
  · have he := canonicalFixedEnergy_eq_fixedGrade D hD 1
    rw [Int.cast_one] at he
    rw [he]
    exact fixedGrade_one_finrank D hD hroot
  · change Module.finrank ℂ
      ↥(fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace ((2 : ℤ) : ℂ)) = _
    rw [canonicalFixedEnergy_eq_fixedGrade D hD 2]
    exact fixedGrade_two_finrank D hD hroot


#print axioms theta_gradeTwo_coordinate_transport
#print axioms actualFixedEnergyTwoBasis
#print axioms actualFixedEnergyTwoBasis_charge_coe
#print axioms actual_theta_fixed_rootless_low_spectrum

end D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades


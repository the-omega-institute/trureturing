/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete charged mixed Jacobi and three supports at every rational mode. -/

/-
proof_shape: mixed_jacobi: content.
escape_witness: The complete ambient Borcherds identity descends through
neutral invariant sectors and both ordered projection corrections. Its three
finite supports descend separately. Every off-coset family is identically
zero, including after each integral shift of the rational mode.
consumers: mixed_jacobi -> LatticeDualCosetFusion.canonical_lawful.
Private uncorrected_product is a consumed bind-only specialization of the
zero-Schur projection correction, used by mixed_integer; mixed_integer is
the live integer-coset content in mixed_jacobi. Private mode_off is a
bind-only coefficient-support helper consumed by mixed_jacobi and both
rational derivative laws in LatticeCosetCanonicalLaws.
admission_basis: escape-witness.

Classical lattice-field conventions: Bakalov--Kac, math/0402315v1,
section 4.1. Native residue and Sugawara suppliers retain their Scott
Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical
realization, categorical completion or string completion is claimed.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalNeutral

/-! Mixed Jacobi for every rational mode, with three separate finite supports. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeFiniteNegativeGeneration
open LatticeCosetCompression LatticeCosetOperatorCorrection LatticeDiscriminantTheta
open LatticeAllStateReconstruction LatticeAllStateJacobi
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

variable (D : LatticeData) {e : ℕ} (B : Matrix (Fin D.rank) (Fin e) ℤ)

private theorem uncorrected_product (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (hs : schur D B 0 a b = 0)
    (u v w : Carrier D) (p k : ℤ) :
    projection D B 0 zeroSymm zeroEven (a+b+c)
      (((Y (ambient D e B 0 zeroSymm zeroEven) (injection D B 0 zeroSymm zeroEven a u))[[p]])
        (((Y (ambient D e B 0 zeroSymm zeroEven) (injection D B 0 zeroSymm zeroEven b v))[[k]])
          (injection D B 0 zeroSymm zeroEven c w))) =
    compressed D B 0 zeroSymm zeroEven a (b+c) u p
      (compressed D B 0 zeroSymm zeroEven b c v k w) := by
  rw [(intermediate_projection_correction D B 0 zeroSymm zeroEven hD a b c u v w p k).2,
    finsum_eq_single _ 0]
  · simp [correction, hs]
  · intro j hj
    simp [correction, hs, Ring.choose_zero_pos ℚ (Nat.pos_of_ne_zero hj)]

def mixedLeft (a b : Fin e → ℤ) (h u v : Carrier D) (p r : ℤ) (tau : ℚ)
    (i : ℕ) : Carrier D :=
  integerBinomial p i • mode D B a b
    (((LatticeDualCosetModule.action D (Matrix.mulVec B a) h)[[r+i]]) u)
    ((p : ℚ)+tau-i) v

def mixedFirst (a b : Fin e → ℤ) (h u v : Carrier D) (p r : ℤ) (tau : ℚ)
    (i : ℕ) : Carrier D :=
  ((-1 : ℂ)^i * integerBinomial r i) •
    ((LatticeDualCosetModule.action D (Matrix.mulVec B a + Matrix.mulVec B b) h)[[p+r-i]])
      (mode D B a b u (tau+i) v)

def mixedSecond (a b : Fin e → ℤ) (h u v : Carrier D) (p r : ℤ) (tau : ℚ)
    (i : ℕ) : Carrier D :=
  ((-1 : ℂ)^i * integerBinomial r i) •
    ((-1 : ℂ)^r • mode D B a b u (tau+r-i)
      (((LatticeDualCosetModule.action D (Matrix.mulVec B b) h)[[p+i]]) v))

private theorem mixed_integer (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (h u v : Carrier D) (p k r : ℤ) :
    Function.HasFiniteSupport (mixedLeft D B a b h u v p r ((k : ℚ)-shift D B a b)) ∧
    Function.HasFiniteSupport (mixedFirst D B a b h u v p r ((k : ℚ)-shift D B a b)) ∧
    Function.HasFiniteSupport (mixedSecond D B a b h u v p r ((k : ℚ)-shift D B a b)) ∧
    (∑ᶠ i, mixedLeft D B a b h u v p r ((k : ℚ)-shift D B a b) i) =
      (∑ᶠ i, mixedFirst D B a b h u v p r ((k : ℚ)-shift D B a b) i) -
      (∑ᶠ i, mixedSecond D B a b h u v p r ((k : ℚ)-shift D B a b) i) := by
  let E := ambient D e B 0 zeroSymm zeroEven
  let J := injection D B 0 zeroSymm zeroEven
  let P := projection D B 0 zeroSymm zeroEven (a+b)
  obtain ⟨hfL,hfA,hfB,he⟩ := borcherds E (J 0 h) (J a u) (J b v) p k r
  have left (i : ℕ) : P (jacobiLeftTerm E p k r (J 0 h) (J a u) (J b v) i) =
      mixedLeft D B a b h u v p r ((k : ℚ)-shift D B a b) i := by
    simp only [jacobiLeftTerm, mu, map_smul]
    rw [show ((Y E (J 0 h))[[r+i]]) (J a u) = J a
      (((LatticeDualCosetModule.action D (Matrix.mulVec B a) h)[[r+i]]) u) from
      neutral_action_invariance D B hD a h u (r+i)]
    unfold mixedLeft
    rw [show (p : ℚ)+((k : ℚ)-shift D B a b)-i =
      ((p+k-(i : ℤ) : ℤ) : ℚ)-shift D B a b by push_cast; ring, mode_integer]
    rfl
  have first (i : ℕ) : P (jacobiRightFirstTerm E p k r (J 0 h) (J a u) (J b v) i) =
      mixedFirst D B a b h u v p r ((k : ℚ)-shift D B a b) i := by
    simp only [jacobiRightFirstTerm, mu, map_smul]
    have hp := uncorrected_product D B hD 0 a b (by simp [schur]) h u v (p+r-i) (k+i)
    simp only [zero_add, compressed_neutral D B hD, Matrix.mulVec_add] at hp
    rw [show P _ = _ from hp]
    unfold mixedFirst
    rw [show ((k : ℚ)-shift D B a b)+i =
      ((k+(i : ℤ) : ℤ) : ℚ)-shift D B a b by push_cast; ring, mode_integer]
  have second (i : ℕ) : P (jacobiRightSecondTerm E p k r (J 0 h) (J a u) (J b v) i) =
      mixedSecond D B a b h u v p r ((k : ℚ)-shift D B a b) i := by
    simp only [jacobiRightSecondTerm, mu, map_smul]
    have hp := uncorrected_product D B hD a 0 b (by simp [schur]) u h v (k+r-i) (p+i)
    simp only [add_zero, zero_add, compressed_neutral D B hD] at hp
    rw [show P _ = _ from hp]
    unfold mixedSecond
    rw [show (k : ℚ)-shift D B a b+r-i =
      ((k+r-(i : ℤ) : ℤ) : ℚ)-shift D B a b by push_cast; ring, mode_integer]
    rfl
  have fL : Function.HasFiniteSupport
      (mixedLeft D B a b h u v p r ((k : ℚ)-shift D B a b)) := by
    simpa only [← funext left] using hfL.fun_comp P.map_zero
  have fA : Function.HasFiniteSupport
      (mixedFirst D B a b h u v p r ((k : ℚ)-shift D B a b)) := by
    simpa only [← funext first] using hfA.fun_comp P.map_zero
  have fB : Function.HasFiniteSupport
      (mixedSecond D B a b h u v p r ((k : ℚ)-shift D B a b)) := by
    simpa only [← funext second] using hfB.fun_comp P.map_zero
  refine ⟨fL,fA,fB,?_⟩
  simp_rw [smul_sub] at he
  change (∑ᶠ i, jacobiLeftTerm E p k r (J 0 h) (J a u) (J b v) i) =
    ∑ᶠ i, (jacobiRightFirstTerm E p k r (J 0 h) (J a u) (J b v) i -
      jacobiRightSecondTerm E p k r (J 0 h) (J a u) (J b v) i) at he
  rw [finsum_sub_distrib hfA hfB] at he
  have hh := congrArg P he
  have mapL : P (∑ᶠ i, jacobiLeftTerm E p k r (J 0 h) (J a u) (J b v) i) =
      ∑ᶠ i, P (jacobiLeftTerm E p k r (J 0 h) (J a u) (J b v) i) :=
    P.toAddMonoidHom.map_finsum hfL
  have mapA : P (∑ᶠ i, jacobiRightFirstTerm E p k r (J 0 h) (J a u) (J b v) i) =
      ∑ᶠ i, P (jacobiRightFirstTerm E p k r (J 0 h) (J a u) (J b v) i) :=
    P.toAddMonoidHom.map_finsum hfA
  have mapB : P (∑ᶠ i, jacobiRightSecondTerm E p k r (J 0 h) (J a u) (J b v) i) =
      ∑ᶠ i, P (jacobiRightSecondTerm E p k r (J 0 h) (J a u) (J b v) i) :=
    P.toAddMonoidHom.map_finsum hfB
  rw [map_sub, mapL, mapA, mapB] at hh
  simpa only [left, first, second] using hh

private theorem mode_off (a b : Fin e → ℤ) (u v : Carrier D) (tau : ℚ)
    (ht : ¬ ∃ m : ℤ, tau = (m : ℚ)-shift D B a b) : mode D B a b u tau v = 0 := by
  apply field_coeff_off
  rintro ⟨k,hk⟩
  apply ht
  refine ⟨-k-1,?_⟩
  change shift D B a b+(k : ℚ) = -tau-1 at hk
  push_cast
  linarith

/-- Complete mixed Jacobi, with three separate finite supports, at every rational mode. -/
theorem mixed_jacobi (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (h u v : Carrier D) (p r : ℤ) (tau : ℚ) :
    Function.HasFiniteSupport (mixedLeft D B a b h u v p r tau) ∧
    Function.HasFiniteSupport (mixedFirst D B a b h u v p r tau) ∧
    Function.HasFiniteSupport (mixedSecond D B a b h u v p r tau) ∧
    (∑ᶠ i, mixedLeft D B a b h u v p r tau i) =
      (∑ᶠ i, mixedFirst D B a b h u v p r tau i) -
      (∑ᶠ i, mixedSecond D B a b h u v p r tau i) := by
  by_cases ht : ∃ k : ℤ, tau = (k : ℚ)-shift D B a b
  · obtain ⟨k,rfl⟩ := ht
    exact mixed_integer D B hD a b h u v p k r
  · have off (z : ℤ) : ¬ ∃ k : ℤ, tau+(z : ℚ) = (k : ℚ)-shift D B a b := by
      rintro ⟨k,hk⟩
      apply ht
      refine ⟨k-z,?_⟩
      push_cast
      linarith
    have hL : mixedLeft D B a b h u v p r tau = 0 := by
      funext i
      unfold mixedLeft
      rw [show (p : ℚ)+tau-i = tau+((p-(i : ℤ) : ℤ) : ℚ) by push_cast; ring,
        mode_off D B _ _ _ _ _ (off _), smul_zero]
      rfl
    have hA : mixedFirst D B a b h u v p r tau = 0 := by
      funext i
      unfold mixedFirst
      rw [show tau+i = tau+((i : ℤ) : ℚ) by simp,
        mode_off D B _ _ _ _ _ (off _), map_zero, smul_zero]
      rfl
    have hB : mixedSecond D B a b h u v p r tau = 0 := by
      funext i
      unfold mixedSecond
      rw [show tau+r-i = tau+((r-(i : ℤ) : ℤ) : ℚ) by push_cast; ring,
        mode_off D B _ _ _ _ _ (off _), smul_zero, smul_zero]
      rfl
    simp [hL,hA,hB,Function.HasFiniteSupport]

end
end D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner

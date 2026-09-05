/- GID: D5/S3/Midline/Cayley/FiniteMirrorKreinGramInertia
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/FiniteMirrorKreinGramInertia
   mirror-E: none(waiver:canonical-zeta-krein-interface)
   anchors: []
   digest: Compute the actual mirror-Krein Gram matrix of the finite odd basis and prove its RHLinalg negative index equals the multiplicity-weighted off-line mirror count. -/

import D5.S3.Midline.Cayley.CanonicalZetaMirrorEvenOddDecomposition
import D5.S3.Midline.Cayley.FiniteMirrorKreinIndex
import D5.S3.SpectralTopology.FiniteSpectralLocalizer
import Mathlib.Tactic

/-!
# Actual finite mirror Krein Gram inertia

The preceding finite-index node constructs an abstract negative coordinate
form of the correct dimension.  This node closes the stronger matrix statement.
It embeds every selected mirror-pair representative and every analytic-
multiplicity copy into the actual zero Hilbert space, takes the Gram matrix of
the genuine mirror Krein form on the resulting odd vectors, and proves that
this Gram matrix is exactly `-2 I`.

Consequently the repository's spectral `RHLinalg.negIndex` of the actual Gram
matrix equals the multiplicity-weighted number of nonfixed mirror pairs.  This
is an inertia theorem for a concrete Gram matrix, rather than a renamed
cardinality definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.FiniteMirrorKreinGramInertia

open Matrix Finset
open D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
open D5.S3.Midline.Cayley.CanonicalZetaMirrorEvenOddDecomposition
open D5.S3.Midline.Cayley.FiniteMirrorKreinIndex
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open RHLinalg
open scoped BigOperators ComplexOrder ENNReal InnerProduct lp Matrix

/-- The actual multiplicity-expanded zero coordinate represented by a finite
mirror-odd coordinate. -/
noncomputable def mirrorOddSourceCoordinate (Z : ZeroData) (T : ℝ)
    (i : MirrorOddCoordinate Z T) : ZeroCoordinate Z :=
  ⟨i.1.1, i.2⟩

/-- The source-coordinate embedding is injective. -/
theorem mirrorOddSourceCoordinate_injective (Z : ZeroData) (T : ℝ) :
    Function.Injective (mirrorOddSourceCoordinate Z T) := by
  intro i j hij
  rcases i with ⟨i, ki⟩
  rcases j with ⟨j, kj⟩
  have hindex : i.1 = j.1 := congrArg Sigma.fst hij
  have hsubtype : i = j := Subtype.ext hindex
  subst j
  have hvalue : ki.val = kj.val :=
    congrArg (fun v : ZeroCoordinate Z => v.2.val) hij
  have hk : ki = kj := Fin.ext hvalue
  subst kj
  rfl

/-- Every selected source coordinate is moved by the mirror. -/
theorem mirrorOddSourceCoordinate_moved (Z : ZeroData) (T : ℝ)
    (i : MirrorOddCoordinate Z T) :
    mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T i) ≠
      mirrorOddSourceCoordinate Z T i := by
  intro hfixed
  have hindex :=
    (mirrorCoordinatePerm_fixed_iff Z (mirrorOddSourceCoordinate Z T i)).1 hfixed
  have hlt := (Finset.mem_filter.mp i.1.2).2
  exact hlt.ne hindex.symm

/-- A selected source coordinate never equals the mirror of another selected
source coordinate.  This is where the one-representative-per-two-cycle choice
is used. -/
theorem mirrorOddSourceCoordinate_ne_mirror (Z : ZeroData) (T : ℝ)
    (i j : MirrorOddCoordinate Z T) :
    mirrorOddSourceCoordinate Z T i ≠
      mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T j) := by
  intro hcross
  have hnm : i.1.1 = mirrorIndex Z j.1.1 :=
    congrArg Sigma.fst hcross
  have hmn : mirrorIndex Z i.1.1 = j.1.1 := by
    calc
      mirrorIndex Z i.1.1 =
          mirrorIndex Z (mirrorIndex Z j.1.1) :=
        congrArg (mirrorIndex Z) hnm
      _ = j.1.1 := mirrorIndex_involutive Z j.1.1
  have hi : i.1.1 < mirrorIndex Z i.1.1 :=
    (Finset.mem_filter.mp i.1.2).2
  have hj : j.1.1 < mirrorIndex Z j.1.1 :=
    (Finset.mem_filter.mp j.1.2).2
  omega

private theorem inner_single_one (Z : ZeroData)
    (v w : ZeroCoordinate Z) :
    ⟪lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1,
      lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 w 1⟫_Complex =
      if v = w then 1 else 0 := by
  rw [lp.inner_single_left]
  by_cases h : v = w
  · subst w
    simp
  · simp [lp.single_apply, Pi.single_apply, h]

/-- The genuine odd vector attached to a finite odd coordinate is the
difference of the two mirror basis vectors. -/
theorem mirrorOddVector_source_eq (Z : ZeroData) (T : ℝ)
    (i : MirrorOddCoordinate Z T) :
    mirrorOddVector Z (mirrorOddSourceCoordinate Z T i) =
      lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2
          (mirrorOddSourceCoordinate Z T i) 1 -
        lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2
          (mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T i)) 1 := by
  rw [mirrorOddVector, mirrorOddPart,
    mirrorFundamentalSymmetry_single]

/-- The Hilbert Gram matrix of the selected odd vectors is exactly `2 I`. -/
theorem mirrorOddVector_source_inner (Z : ZeroData) (T : ℝ)
    (i j : MirrorOddCoordinate Z T) :
    ⟪mirrorOddVector Z (mirrorOddSourceCoordinate Z T i),
      mirrorOddVector Z (mirrorOddSourceCoordinate Z T j)⟫_Complex =
      if i = j then 2 else 0 := by
  rw [mirrorOddVector_source_eq, mirrorOddVector_source_eq,
    inner_sub_left, inner_sub_right, inner_sub_right,
    inner_single_one, inner_single_one, inner_single_one, inner_single_one]
  by_cases hij : i = j
  · subst j
    have hmove := mirrorOddSourceCoordinate_moved Z T i
    have hreverse : mirrorOddSourceCoordinate Z T i ≠
        mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T i) :=
      fun h => hmove h.symm
    simp [hmove, hreverse]
  · have hsource : mirrorOddSourceCoordinate Z T i ≠
        mirrorOddSourceCoordinate Z T j := by
      intro h
      exact hij (mirrorOddSourceCoordinate_injective Z T h)
    have hcross : mirrorOddSourceCoordinate Z T i ≠
        mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T j) :=
      mirrorOddSourceCoordinate_ne_mirror Z T i j
    have hcross' : mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T i) ≠
        mirrorOddSourceCoordinate Z T j := by
      intro h
      exact mirrorOddSourceCoordinate_ne_mirror Z T j i h.symm
    have hmirror :
        mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T i) ≠
          mirrorCoordinatePerm Z (mirrorOddSourceCoordinate Z T j) := by
      intro h
      exact hsource ((mirrorCoordinatePerm Z).injective h)
    simp [hij, hsource, hcross, hcross', hmirror]

/-- The actual Krein Gram entry is `-2` on the diagonal and zero off the
diagonal. -/
theorem mirrorOddVector_source_krein (Z : ZeroData) (T : ℝ)
    (i j : MirrorOddCoordinate Z T) :
    mirrorKreinForm Z
        (mirrorOddVector Z (mirrorOddSourceCoordinate Z T i))
        (mirrorOddVector Z (mirrorOddSourceCoordinate Z T j)) =
      if i = j then -2 else 0 := by
  rw [mirrorKreinForm]
  have hodd :
      mirrorFundamentalSymmetry Z
          (mirrorOddVector Z (mirrorOddSourceCoordinate Z T j)) =
        -mirrorOddVector Z (mirrorOddSourceCoordinate Z T j) := by
    exact mirrorOddPart_eigenvalue_neg_one Z
      (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2
        (mirrorOddSourceCoordinate Z T j) 1)
  rw [hodd, inner_neg_right, mirrorOddVector_source_inner]
  by_cases hij : i = j <;> simp [hij]

/-- The genuine finite mirror-odd Gram matrix in the actual zero Hilbert
space. -/
noncomputable def finiteMirrorOddKreinGram (Z : ZeroData) (T : ℝ) :
    Matrix (MirrorOddCoordinate Z T) (MirrorOddCoordinate Z T) Complex :=
  fun i j => mirrorKreinForm Z
    (mirrorOddVector Z (mirrorOddSourceCoordinate Z T i))
    (mirrorOddVector Z (mirrorOddSourceCoordinate Z T j))

/-- The actual Gram matrix is the scalar matrix `-2 I`. -/
theorem finiteMirrorOddKreinGram_eq (Z : ZeroData) (T : ℝ) :
    finiteMirrorOddKreinGram Z T =
      (-2 : Complex) •
        (1 : Matrix (MirrorOddCoordinate Z T)
          (MirrorOddCoordinate Z T) Complex) := by
  ext i j
  rw [finiteMirrorOddKreinGram, mirrorOddVector_source_krein]
  by_cases hij : i = j <;> simp [hij]

/-- The actual finite mirror-odd Gram matrix is Hermitian. -/
theorem finiteMirrorOddKreinGram_isHermitian (Z : ZeroData) (T : ℝ) :
    (finiteMirrorOddKreinGram Z T).IsHermitian := by
  rw [finiteMirrorOddKreinGram_eq]
  exact Matrix.isHermitian_one.smul (by simp)

/-- The negative of the actual Gram matrix is positive definite. -/
theorem neg_finiteMirrorOddKreinGram_posDef (Z : ZeroData) (T : ℝ) :
    (-finiteMirrorOddKreinGram Z T).PosDef := by
  rw [finiteMirrorOddKreinGram_eq]
  simpa using
    (Matrix.PosDef.one.smul (show (0 : ℝ) < 2 by norm_num) :
      ((2 : ℝ) •
        (1 : Matrix (MirrorOddCoordinate Z T)
          (MirrorOddCoordinate Z T) Complex)).PosDef)

/-- The spectral negative index of the actual Gram matrix is exactly the
multiplicity-weighted number of nonfixed mirror pairs. -/
theorem finiteMirrorOddKreinGram_negIndex (Z : ZeroData) (T : ℝ) :
    negIndex (finiteMirrorOddKreinGram_isHermitian Z T) =
      finiteMirrorKreinIndex Z T := by
  let hG := finiteMirrorOddKreinGram_isHermitian Z T
  have hNegative := neg_finiteMirrorOddKreinGram_posDef Z T
  calc
    negIndex hG = posIndex hG.neg :=
      (posIndex_neg_eq_negIndex hG).symm
    _ = Fintype.card (MirrorOddCoordinate Z T) := by
      unfold posIndex
      rw [Finset.filter_eq_self.2]
      · exact Finset.card_univ
      · intro i hi
        exact hNegative.eigenvalues_pos i
    _ = finiteMirrorKreinIndex Z T := mirrorOddCoordinate_card Z T

/-- The actual Gram negative index is positive exactly when the finite window
contains an off-line zero. -/
theorem finiteMirrorOddKreinGram_negIndex_pos_iff_exists_offLine
    (Z : ZeroData) (T : ℝ) :
    0 < negIndex (finiteMirrorOddKreinGram_isHermitian Z T) ↔
      ∃ n ∈ Z.symmetricIndices T,
        (Z.zero n).re ≠ criticalAbscissa := by
  rw [finiteMirrorOddKreinGram_negIndex,
    finiteMirrorKreinIndex_pos_iff_exists_offLine]

/-- The actual Gram negative index vanishes exactly on a critical finite
window. -/
theorem finiteMirrorOddKreinGram_negIndex_zero_iff_critical
    (Z : ZeroData) (T : ℝ) :
    negIndex (finiteMirrorOddKreinGram_isHermitian Z T) = 0 ↔
      ∀ n ∈ Z.symmetricIndices T,
        (Z.zero n).re = criticalAbscissa := by
  rw [finiteMirrorOddKreinGram_negIndex,
    finite_mirror_krein_index_zero_iff_critical]

/-- Parameter-free zeta specialization. -/
theorem zetaFiniteMirrorOddKreinGram_negIndex (T : ℝ) :
    negIndex (finiteMirrorOddKreinGram_isHermitian zetaZeroData T) =
      zetaFiniteMirrorKreinIndex T := by
  exact finiteMirrorOddKreinGram_negIndex zetaZeroData T

/-- Final concrete finite inertia package for the canonical zeta presentation. -/
theorem canonical_zeta_finite_mirror_gram_inertia (T : ℝ) :
    finiteMirrorOddKreinGram zetaZeroData T =
        (-2 : Complex) •
          (1 : Matrix (MirrorOddCoordinate zetaZeroData T)
            (MirrorOddCoordinate zetaZeroData T) Complex) ∧
      negIndex (finiteMirrorOddKreinGram_isHermitian zetaZeroData T) =
        zetaFiniteMirrorKreinIndex T ∧
      (0 < negIndex
          (finiteMirrorOddKreinGram_isHermitian zetaZeroData T) ↔
        ∃ n ∈ zetaZeroData.symmetricIndices T,
          (zetaZeroData.zero n).re ≠ criticalAbscissa) := by
  exact ⟨finiteMirrorOddKreinGram_eq zetaZeroData T,
    zetaFiniteMirrorOddKreinGram_negIndex T,
    finiteMirrorOddKreinGram_negIndex_pos_iff_exists_offLine
      zetaZeroData T⟩

#print axioms mirrorOddVector_source_inner
#print axioms finiteMirrorOddKreinGram_eq
#print axioms finiteMirrorOddKreinGram_negIndex
#print axioms finiteMirrorOddKreinGram_negIndex_pos_iff_exists_offLine
#print axioms canonical_zeta_finite_mirror_gram_inertia

end D5.S3.Midline.Cayley.FiniteMirrorKreinGramInertia

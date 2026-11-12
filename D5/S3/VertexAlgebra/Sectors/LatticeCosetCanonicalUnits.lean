/-
SOURCE ONLY / UNCOMPILED / UNACCEPTED.

Original canonical zero-charge units.  C below is the literal accepted
intertwiner with B = 1.  No replacement of the original action is made.
The two ambient lattices are compared only at original seed coefficients.

Mathematical sources: Bakalov--Kac, math/0402315v1, section 4.1;
the accepted native residue suppliers retain their Carnahan attribution.
The completed unit Pro answer (sha256 77394b7246258769d89c66b5168980bb56fbf197d40017d88d051d56471ba59d)
is mathematical advice, not a native theorem supplier.

The finite Jacobi and scalar convolution proofs are preserved below. The
finite falling-covariance and triangular reindexing proofs extend them to the
original general right-input formula. Every new proof is source-only and
requires native checking. The full original goal remains incomplete.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetTransport
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
import D5.S3.VertexAlgebra.LatticeActualOrderedProducts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCanonicalUnits

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeDualCosetModule LatticeDualCosetConformal
open LatticeDiscriminantTheta LatticeCosetCanonicalIntertwiner
open LatticeActualStateFieldCalculus FieldNormalProduct MvPolynomial
open LatticeActualGeneratorLocality LatticeActualProductKernel LatticeActualOrderedProducts
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator Matrix

noncomputable section

open private action_ground_field action_current_field
  from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetTransport
open private polynomialProjection_injection injection_single projection_single
  from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private compressedField_modes
  from D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion
open private inverseGram_left inverseGram_right
  from D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification

/-- Exactly the canonical B = identity matrix intertwiner. -/
abbrev C (D : LatticeData) (a b : Charge D) :=
  intertwiner D (1 : Matrix (Fin D.rank) (Fin D.rank) ℤ) a b

abbrev cmode (D : LatticeData) (a b : Charge D) (u : Carrier D) (tau : ℚ) :=
  LatticeCosetCanonicalIntertwiner.mode D (1 : Matrix _ _ ℤ) a b u tau

abbrev E (D : LatticeData) :=
  LatticeCosetCompression.ambient D D.rank (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven

abbrev J (D : LatticeData) (a : Charge D) :=
  LatticeCosetCompression.injection D (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a

abbrev P (D : LatticeData) (a : Charge D) :=
  LatticeCosetCompression.projection D (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a

private theorem convolution_support (D : LatticeData) (a : Charge D) (k : ℤ)
    (q : Polynomial (Oscillator D)) :
    convolution D a k q = ∑ d ∈ q.support, q.coeff d • creationCoeff D a (k+d) := by
  classical
  rw [convolution_finsum]
  rw [finsum_eq_sum_of_support_subset _ (show Function.support
      (fun d : ℕ => q.coeff d * creationCoeff D a (k+d)) ⊆ q.support from by
    intro d hd
    exact Polynomial.mem_support_iff.mpr (fun he => hd (by simp [he])))]
  simp only [smul_eq_mul]

private theorem action_zero_ground (D : LatticeData) (a : Charge D) :
    action D 0 (Finsupp.single a (1 : Oscillator D)) = actualField D a := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  apply Finsupp.lhom_ext
  intro n p
  rw [action_ground_coefficients, actual_modes, raw_single_convolution, convolution_support]
  simp [shiftedRawSingle]


private theorem action_zero_current (D : LatticeData) (i : Fin D.rank) :
    action D 0 (Finsupp.single (0 : Charge D) (X (i, 0))) = neutralField D i := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    neutralField_ncoeff]
  apply Finsupp.lhom_ext
  intro n p
  rw [action_current_coefficients, neutralMode_single]
  simp [shiftedCurrentPolynomial, neutralPolynomialMode]

/-- Literal recursion comparison; the extra-coordinate ambients are not identified. -/
theorem shiftedWord_zero (D : LatticeData) (a : Charge D) (w : List (Index D)) :
    shiftedWord D 0 a w = wordField D a w := by
  induction w with
  | nil =>
    rw [shiftedWord, wordField, ← action_ground_field, action_zero_ground]
  | cons x w ih =>
    rw [shiftedWord, wordField, ← action_current_field, action_zero_current, ih]

/-- Equality of the actual all-state linear maps, without positivity. -/
theorem action_zero_eq_Y (D : LatticeData) : action D 0 = Y D := by
  apply LinearMap.ext
  intro h
  rw [action_expansion, stateField_expansion]
  simp_rw [shiftedWord_zero]

/-- The coefficient version retains every original state, mode and input. -/
theorem action_zero_mode (D : LatticeData) (h v : Carrier D) (m : ℤ) :
    ((action D 0 h)[[m]]) v = ((Y D h)[[m]]) v := by
  rw [action_zero_eq_Y]

/-- Projection after injection on the original full carrier. No Gram hypothesis. -/
theorem projection_injection (D : LatticeData) (a : Charge D) (u : Carrier D) :
    P D a (J D a u) = u := by
  have hp : (P D a).comp (J D a) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro n p
    change P D a (J D a (Finsupp.single n p)) = Finsupp.single n p
    rw [injection_single, projection_single, polynomialProjection_injection]
    have he : LatticeCosetCompression.externalCharge D (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven
        (LatticeCosetCompression.liftCharge D (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a n) = a := by
      funext i
      simp [LatticeCosetCompression.externalCharge, LatticeCosetCompression.liftCharge, Fin.addCases]
    have hn : LatticeCosetCompression.oldCharge D (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven
        (LatticeCosetCompression.liftCharge D (1 : Matrix _ _ ℤ) 0 zeroSymm zeroEven a n) = n := by
      funext i
      simp [LatticeCosetCompression.oldCharge, LatticeCosetCompression.liftCharge, Fin.addCases]
    rw [he, if_pos rfl, hn]
  exact congrArg (fun f : Module.End ℂ (Carrier D) => f u) hp

theorem injection_zero_vacuum (D : LatticeData) :
    J D 0 (vacuum D) = vacuum (E D) := by
  rw [vacuum, injection_single, map_one]
  congr 1
  funext i
  induction i using Fin.addCases <;>
    simp [LatticeCosetCompression.liftCharge, Fin.addCases]

@[simp] theorem shift_zero_left (D : LatticeData) (b : Charge D) :
    shift D (1 : Matrix _ _ ℤ) 0 b = 0 := by simp [LatticeCosetCanonicalIntertwiner.shift]

@[simp] theorem shift_zero_right (D : LatticeData) (a : Charge D) :
    shift D (1 : Matrix _ _ ℤ) a 0 = 0 := by simp [LatticeCosetCanonicalIntertwiner.shift]

private theorem coeff_compressed (D : LatticeData) (a b : Charge D)
    (hs : shift D (1 : Matrix _ _ ℤ) a b = 0)
    (u v : Carrier D) (k : ℤ) :
    (C D a b u).coeff (k : ℚ) v =
      P D (a+b) (((Y (E D) (J D a u))[[-k-1]]) (J D b v)) := by
  change HVertexOperator.coeff (field D (1 : Matrix _ _ ℤ) a b u) (k : ℚ) v = _
  rw [show (k : ℚ) = shift D (1 : Matrix _ _ ℤ) a b + (k : ℚ) by rw [hs]; simp,
    field_coeff, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
  rfl

private theorem coeff_off (D : LatticeData) (a b : Charge D)
    (hs : shift D (1 : Matrix _ _ ℤ) a b = 0)
    (u v : Carrier D) (q : ℚ)
    (hq : q ∉ Set.range (fun k : ℤ => (k : ℚ))) :
    (C D a b u).coeff q v = 0 := by
  apply field_coeff_off
  rintro ⟨k,hk⟩
  apply hq
  refine ⟨k, ?_⟩
  simpa [exponentEmbedding, hs] using hk

/-- All rational coefficients of the actual source vacuum. -/
theorem canonical_zero_vacuum_coeff (D : LatticeData) (b : Charge D)
    (v : Carrier D) (q : ℚ) :
    (C D 0 b (vacuum D)).coeff q v = if q = 0 then v else 0 := by
  classical
  by_cases hq : q ∈ Set.range (fun k : ℤ => (k : ℚ))
  · obtain ⟨k,rfl⟩ := hq
    rw [coeff_compressed D 0 b (shift_zero_left D b), injection_zero_vacuum,
      stateField_vacuum, identity_modes]
    by_cases hk : k = 0
    · subst k
      simp [projection_injection]
    · have hm : -k-1 ≠ -1 := by omega
      simp [hk, hm]
  · rw [coeff_off D 0 b (shift_zero_left D b) _ _ _ hq]
    have hz : q ≠ 0 := by
      intro hz
      apply hq
      exact ⟨0, by simpa using hz.symm⟩
    simp [hz]

private theorem vacuum_mode (D : LatticeData) (b : Charge D)
    (v : Carrier D) (tau : ℚ) :
    cmode D 0 b (vacuum D) tau v = if tau = -1 then v else 0 := by
  change (C D 0 b (vacuum D)).coeff (-tau-1) v = _
  rw [canonical_zero_vacuum_coeff]
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

private theorem left_family_zero_index (D : LatticeData) (b : Charge D)
    (h v : Carrier D) (tau : ℚ) :
    (∑ᶠ i, mixedLeft D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v 0 (-1) tau i) =
      cmode D 0 b h tau v := by
  rw [finsum_eq_single _ 0]
  · simp [mixedLeft, integerBinomial, action_zero_eq_Y, stateField_creation, cmode]
  · intro i hi
    simp [mixedLeft, integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem left_first_term (D : LatticeData) (b : Charge D)
    (h v : Carrier D) (tau : ℚ) (i : ℕ) :
    mixedFirst D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v 0 (-1) tau i =
      if tau + (i : ℚ) = -1 then ((action D b h)[[-1-(i : ℤ)]]) v else 0 := by
  simp only [mixedFirst, Matrix.one_mulVec, zero_add, minus_one_binomial, one_smul]
  rw [show LatticeCosetCanonicalIntertwiner.mode D (1 : Matrix _ _ ℤ)
      0 b (vacuum D) (tau+i) v =
      if tau+(i : ℚ) = -1 then v else 0 from vacuum_mode D b v (tau+i)]
  split_ifs <;> simp

private theorem left_second_term (D : LatticeData) (b : Charge D)
    (h v : Carrier D) (tau : ℚ) (i : ℕ) :
    mixedSecond D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v 0 (-1) tau i =
      if tau - 1 - (i : ℚ) = -1 then -((action D b h)[[(i : ℤ)]]) v else 0 := by
  simp only [mixedSecond, Matrix.one_mulVec, zero_add, minus_one_binomial, one_smul]
  rw [show (-1 : ℂ)^(-1 : ℤ) = -1 by norm_num]
  norm_num only [Int.cast_neg, Int.cast_one, ← sub_eq_add_neg]
  change (-1 : ℂ) • cmode D 0 b (vacuum D) (tau-1-i)
    (((action D b h)[[(i : ℤ)]]) v) = _
  rw [vacuum_mode]
  split_ifs <;> simp

/-- Negative integer modes: first support lies in {-m-1}, second support is empty. -/
theorem left_negative_supports (D : LatticeData) (b : Charge D)
    (h v : Carrier D) (m : ℤ) (hm : m ≤ -1) :
    Function.support (mixedFirst D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
      0 (-1) (m : ℚ)) ⊆ {(-m-1).toNat} ∧
    Function.support (mixedSecond D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
      0 (-1) (m : ℚ)) = ∅ := by
  constructor
  · intro i hi
    simp only [Set.mem_singleton_iff]
    by_contra hn
    apply hi
    rw [left_first_term, if_neg]
    intro he
    have ht : ((-m-1).toNat : ℤ) = -m-1 := Int.toNat_of_nonneg (by omega)
    have hei : m+(i : ℤ) = -1 := by exact_mod_cast he
    omega
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    apply hi
    rw [left_second_term, if_neg]
    intro he
    have hei : m-1-(i : ℤ) = -1 := by exact_mod_cast he
    omega

/-- Nonnegative integer modes: first support is empty, second lies in {m}. -/
theorem left_nonnegative_supports (D : LatticeData) (b : Charge D)
    (h v : Carrier D) (m : ℤ) (hm : 0 ≤ m) :
    Function.support (mixedFirst D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
      0 (-1) (m : ℚ)) = ∅ ∧
    Function.support (mixedSecond D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
      0 (-1) (m : ℚ)) ⊆ {m.toNat} := by
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    apply hi
    rw [left_first_term, if_neg]
    intro he
    have hei : m+(i : ℤ) = -1 := by exact_mod_cast he
    omega
  · intro i hi
    simp only [Set.mem_singleton_iff]
    by_contra hn
    apply hi
    rw [left_second_term, if_neg]
    intro he
    have ht : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
    have hei : m-1-(i : ℤ) = -1 := by exact_mod_cast he
    omega

/-- Off integer modes neither vacuum singleton can occur. -/
theorem left_off_supports (D : LatticeData) (b : Charge D)
    (h v : Carrier D) (tau : ℚ)
    (ht : tau ∉ Set.range (fun m : ℤ => (m : ℚ))) :
    (∀ i, mixedFirst D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v 0 (-1) tau i = 0) ∧
    (∀ i, mixedSecond D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v 0 (-1) tau i = 0) := by
  constructor
  · intro i
    rw [left_first_term, if_neg]
    intro hi
    apply ht
    refine ⟨-(i : ℤ)-1, ?_⟩
    push_cast
    linarith
  · intro i
    rw [left_second_term, if_neg]
    intro hi
    apply ht
    exact ⟨(i : ℤ), by push_cast; linarith⟩

theorem canonical_zero_left_mode_integer (D : LatticeData)
    (hD : (gramReal D).PosDef) (b : Charge D) (h v : Carrier D) (m : ℤ) :
    cmode D 0 b h (m : ℚ) v = ((action D b h)[[m]]) v := by
  classical
  have hj := (mixed_jacobi D (1 : Matrix _ _ ℤ) hD 0 b h (vacuum D) v
    0 (-1) (m : ℚ)).2.2.2
  rw [left_family_zero_index] at hj
  by_cases hm : m ≤ -1
  · have f : (∑ᶠ i, mixedFirst D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
        0 (-1) (m : ℚ) i) = ((action D b h)[[m]]) v := by
      rw [finsum_eq_single _ (-m-1).toNat]
      · rw [left_first_term]
        have ht : ((-m-1).toNat : ℤ) = -m-1 := Int.toNat_of_nonneg (by omega)
        have hq : (m : ℚ)+((-m-1).toNat : ℚ) = -1 := by exact_mod_cast (by omega : m+((-m-1).toNat : ℤ) = -1)
        rw [if_pos hq, show -1-(((-m-1).toNat : ℕ) : ℤ) = m by omega]
      · intro i hi
        by_contra hn
        exact hi ((left_negative_supports D b h v m hm).1 hn)
    have s : (∑ᶠ i, mixedSecond D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
        0 (-1) (m : ℚ) i) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      by_contra hn
      have hi : i ∈ Function.support (mixedSecond D (1 : Matrix _ _ ℤ)
          0 b h (vacuum D) v 0 (-1) (m : ℚ)) := hn
      rw [(left_negative_supports D b h v m hm).2] at hi
      exact hi
    simpa only [f,s,sub_zero] using hj
  · have hm' : 0 ≤ m := by omega
    have f : (∑ᶠ i, mixedFirst D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
        0 (-1) (m : ℚ) i) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      by_contra hn
      have hi : i ∈ Function.support (mixedFirst D (1 : Matrix _ _ ℤ)
          0 b h (vacuum D) v 0 (-1) (m : ℚ)) := hn
      rw [(left_nonnegative_supports D b h v m hm').1] at hi
      exact hi
    have s : (∑ᶠ i, mixedSecond D (1 : Matrix _ _ ℤ) 0 b h (vacuum D) v
        0 (-1) (m : ℚ) i) = -((action D b h)[[m]]) v := by
      rw [finsum_eq_single _ m.toNat]
      · rw [left_second_term]
        have ht : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm'
        have hq : (m : ℚ)-1-(m.toNat : ℚ) = -1 := by exact_mod_cast (by omega : m-1-(m.toNat : ℤ) = -1)
        simp [hq, ht]
      · intro i hi
        by_contra hn
        exact hi ((left_nonnegative_supports D b h v m hm').2 hn)
    simpa only [f,s,zero_sub,neg_neg] using hj

/-- Raw integer exponent k means original mode -k-1. -/
theorem canonical_zero_left_integer (D : LatticeData)
    (hD : (gramReal D).PosDef) (b : Charge D) (h v : Carrier D) (k : ℤ) :
    (C D 0 b h).coeff (k : ℚ) v = ((action D b h)[[-k-1]]) v := by
  have hh := canonical_zero_left_mode_integer D hD b h v (-k-1)
  simpa only [cmode, LatticeCosetCanonicalIntertwiner.mode,
    show -((-k-1 : ℤ) : ℚ)-1 = (k : ℚ) by push_cast; ring] using hh

theorem canonical_zero_left_off (D : LatticeData) (b : Charge D)
    (h v : Carrier D) (q : ℚ)
    (hq : q ∉ Set.range (fun k : ℤ => (k : ℚ))) :
    (C D 0 b h).coeff q v = 0 :=
  coeff_off D 0 b (shift_zero_left D b) h v q hq

/-- Original ambient creation, followed by the actual projection/injection identity. -/
theorem canonical_right_creation_zero (D : LatticeData) (a : Charge D) (u : Carrier D) :
    (C D a 0 u).coeff 0 (vacuum D) = u := by
  rw [show (0 : ℚ) = ((0 : ℤ) : ℚ) by rfl,
    coeff_compressed D a 0 (shift_zero_right D a), injection_zero_vacuum]
  simpa only [neg_zero, zero_sub, add_zero, stateField_creation] using
    projection_injection D a u

theorem canonical_right_off (D : LatticeData) (a : Charge D)
    (u v : Carrier D) (q : ℚ)
    (hq : q ∉ Set.range (fun k : ℤ => (k : ℚ))) :
    (C D a 0 u).coeff q v = 0 :=
  coeff_off D a 0 (shift_zero_right D a) u v q hq

theorem canonical_right_creation_negative (D : LatticeData) (a : Charge D)
    (u : Carrier D) (q : ℚ) (hq : q < 0) :
    (C D a 0 u).coeff q (vacuum D) = 0 := by
  classical
  by_cases hi : q ∈ Set.range (fun k : ℤ => (k : ℚ))
  · obtain ⟨k,hkq⟩ := hi
    change (k : ℚ) = q at hkq
    subst q
    have hk : k < 0 := by exact_mod_cast hq
    rw [coeff_compressed D a 0 (shift_zero_right D a), injection_zero_vacuum,
      stateField_creativity (E D) (J D a u) (-k-1) (by omega), map_zero]
  · exact canonical_right_off D a u (vacuum D) q hi

/-- The actual original-sector omega-zero, equivalently moduleL inverseGram (-1). -/
def sectorTranslation (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Charge D) : Module.End ℂ (Carrier D) :=
  ((action D a (LatticeActualConformalState.omega D
    (Modules.ActualWeakModuleClassification.inverseGram hD)))[[0]])

theorem sectorTranslation_eq_moduleL (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Charge D) :
    sectorTranslation D hD a = moduleL D a
      (Modules.ActualWeakModuleClassification.inverseGram hD) (-1) := rfl

theorem sectorTranslation_zero_vacuum (D : LatticeData) (hD : (gramReal D).PosDef) :
    sectorTranslation D hD 0 (vacuum D) = 0 := by
  unfold sectorTranslation
  rw [action_zero_eq_Y]
  exact stateField_creativity D _ 0 (by omega)

private theorem target_raw (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b : Charge D) (u v : Carrier D) (k : ℤ) :
    sectorTranslation D hD (a+b) ((C D a b u).coeff (k : ℚ) v) -
      (C D a b u).coeff (k : ℚ) (sectorTranslation D hD b v) =
      ((k : ℂ)+1) • (C D a b u).coeff ((k+1 : ℤ) : ℚ) v := by
  have hh := target_derivative D (1 : Matrix _ _ ℤ) hD
    (Modules.ActualWeakModuleClassification.inverseGram hD)
    (inverseGram_left hD) (inverseGram_right hD) a b u v (-(k : ℚ)-1)
  have ht : -(-(k : ℚ)-1)-1 = (k : ℚ) := by ring
  have hs : -(-(k : ℚ)-1-1)-1 = ((k+1 : ℤ) : ℚ) := by push_cast; ring
  simp only [Matrix.one_mulVec, ← sectorTranslation_eq_moduleL,
    LatticeCosetCanonicalIntertwiner.mode, ht, hs] at hh
  have hc : -((-(k : ℚ)-1 : ℚ) : ℂ) = (k : ℂ)+1 := by push_cast; ring
  rw [hc] at hh
  exact hh

/-- The recurrence comes from the actual canonical target law. -/
theorem canonical_right_creation_recurrence (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Charge D) (u : Carrier D) (k : ℕ) :
    ((k+1 : ℕ) : ℂ) • (C D a 0 u).coeff ((k+1 : ℕ) : ℚ) (vacuum D) =
      sectorTranslation D hD a ((C D a 0 u).coeff (k : ℚ) (vacuum D)) := by
  have hh := target_raw D hD a 0 u (vacuum D) (k : ℤ)
  rw [sectorTranslation_zero_vacuum, map_zero, sub_zero, add_zero] at hh
  simpa only [Nat.cast_add, Nat.cast_one, Int.cast_natCast, Int.cast_add,
    Int.cast_one] using hh.symm

/-- Every natural creation coefficient, with the ORIGINAL sector translation. -/
theorem canonical_right_creation_nat (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Charge D) (u : Carrier D) (k : ℕ) :
    (C D a 0 u).coeff (k : ℚ) (vacuum D) =
      (k.factorial : ℂ)⁻¹ • ((sectorTranslation D hD a)^k) u := by
  induction k with
  | zero => simpa using canonical_right_creation_zero D a u
  | succ k ih =>
    have hr := canonical_right_creation_recurrence D hD a u k
    rw [ih, map_smul] at hr
    have hk : ((k+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    calc
      _ = (((k+1 : ℕ) : ℂ)⁻¹) •
          (sectorTranslation D hD a ((k.factorial : ℂ)⁻¹ •
            ((sectorTranslation D hD a)^k) u)) := by
        rw [map_smul, ← hr, smul_smul, inv_mul_cancel₀ hk, one_smul]
      _ = _ := by
        rw [map_smul, smul_smul, Nat.factorial_succ, Nat.cast_mul,
          mul_inv_rev, mul_comm, pow_succ', Module.End.mul_apply]

/-- An integer-indexed creation coefficient, zero at negative exponents. -/
def creationCoefficient (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Charge D) (u : Carrier D) (t : ℤ) : Carrier D :=
  if 0 ≤ t then (t.toNat.factorial : ℂ)⁻¹ •
    ((sectorTranslation D hD a)^t.toNat) u else 0

theorem canonical_right_creation_integer (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Charge D) (u : Carrier D) (t : ℤ) :
    (C D a 0 u).coeff (t : ℚ) (vacuum D) = creationCoefficient D hD a u t := by
  by_cases ht : 0 ≤ t
  · have he : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht
    have hh := canonical_right_creation_nat D hD a u t.toNat
    have hq : (t.toNat : ℚ) = (t : ℚ) := by exact_mod_cast he
    rw [hq] at hh
    simpa only [creationCoefficient, if_pos ht] using hh
  · rw [canonical_right_creation_negative D a u (t : ℚ) (by exact_mod_cast (by omega : t < 0))]
    simp [creationCoefficient, ht]

/-- Exact all-rational support, including rank zero and the zero vector. -/
theorem canonical_right_creation_support (D : LatticeData)
    (a : Charge D) (u : Carrier D) (q : ℚ)
    (hq : q ∉ Set.range (fun k : ℕ => (k : ℚ))) :
    (C D a 0 u).coeff q (vacuum D) = 0 := by
  classical
  by_cases hi : q ∈ Set.range (fun k : ℤ => (k : ℚ))
  · obtain ⟨k,hkq⟩ := hi
    change (k : ℚ) = q at hkq
    subst q
    have hk : k < 0 := by
      by_contra hn
      apply hq
      refine ⟨k.toNat, ?_⟩
      change (k.toNat : ℚ) = (k : ℚ)
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ k)
    exact canonical_right_creation_negative D a u _ (by exact_mod_cast hk)
  · exact canonical_right_off D a u _ q hi

/-- Actual covariance derived from the completed ALL-STATE left-unit theorem. -/
theorem sectorTranslation_covariance (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Charge D) (v u : Carrier D) (m : ℤ) :
    sectorTranslation D hD a (((action D a v)[[m]]) u) -
      ((action D a v)[[m]]) (sectorTranslation D hD a u) =
      -(m : ℂ) • ((action D a v)[[m-1]]) u := by
  have hh := target_raw D hD 0 a v u (-m-1)
  rw [zero_add, canonical_zero_left_integer D hD, canonical_zero_left_integer D hD,
    canonical_zero_left_integer D hD] at hh
  simpa only [show -(-m-1)-1 = m by omega,
    show -(-m-1+1)-1 = m-1 by omega, Int.cast_sub, Int.cast_neg,
    Int.cast_one, sub_add_cancel, neg_neg, neg_add_rev] using hh

/-- A bound for this single original pair exists by actual field truncation. -/
theorem original_pair_cutoff (D : LatticeData) (a : Charge D) (u v : Carrier D) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → ((action D a v)[[m]]) u = 0 := by
  refine ⟨(-((HahnModule.of ℂ).symm (action D a v u)).order).toNat, ?_⟩
  intro m hm
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  omega

private theorem integerBinomial_nat (N i : ℕ) :
    integerBinomial (N : ℤ) i = (N.choose i : ℂ) := by
  simp [integerBinomial, Ring.choose_natCast]

private theorem original_vacuum_mode (D : LatticeData) (v : Carrier D) (i : ℕ) :
    ((action D 0 v)[[-1+(i : ℤ)]]) (vacuum D) = if i = 0 then v else 0 := by
  by_cases hi : i = 0
  · subst i
    simp [action_zero_eq_Y, stateField_creation]
  · simp only [hi, ↓reduceIte, action_zero_eq_Y]
    exact stateField_creativity D v (-1+i) (by omega)

/-- Exact zero left family, before summation or cancellation. -/
theorem right_jacobi_left_zero (D : LatticeData) (a : Charge D)
    (u v : Carrier D) (N : ℕ) (tau : ℚ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → ((action D a v)[[m]]) u = 0) (i : ℕ) :
    mixedLeft D (1 : Matrix _ _ ℤ) a 0 v u (vacuum D) (-1) (N : ℤ) tau i = 0 := by
  simp [mixedLeft, Matrix.one_mulVec, hN ((N : ℤ)+i) (by omega),
    LatticeCosetCanonicalIntertwiner.mode]

/-- First-family support is bounded by N, solely from ordinary binomial support. -/
theorem right_jacobi_first_support (D : LatticeData) (a : Charge D)
    (u v : Carrier D) (N : ℕ) (tau : ℚ) :
    Function.support (mixedFirst D (1 : Matrix _ _ ℤ) a 0 v u (vacuum D)
      (-1) (N : ℤ) tau) ⊆ Finset.range (N+1) := by
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  apply hi
  simp [mixedFirst, integerBinomial_nat, Nat.choose_eq_zero_of_lt (by omega : N < i)]

/-- True creation makes the second family supported at index zero. -/
theorem right_jacobi_second_support (D : LatticeData) (a : Charge D)
    (u v : Carrier D) (N : ℕ) (tau : ℚ) :
    Function.support (mixedSecond D (1 : Matrix _ _ ℤ) a 0 v u (vacuum D)
      (-1) (N : ℤ) tau) ⊆ {0} := by
  intro i hi
  simp only [Set.mem_singleton_iff]
  by_contra hn
  apply hi
  simp [mixedSecond, Matrix.one_mulVec, original_vacuum_mode, hn,
    LatticeCosetCanonicalIntertwiner.mode]

/-- The actual p=-1,r=N Jacobi equation, with its separate finite supports. -/
theorem canonical_right_finite_jacobi_mode (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Charge D) (u v : Carrier D)
    (N : ℕ) (tau : ℚ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → ((action D a v)[[m]]) u = 0) :
    (-1 : ℂ)^N • cmode D a 0 u (tau+N) v =
      ∑ i ∈ Finset.range (N+1),
        ((-1 : ℂ)^i * (N.choose i : ℂ)) •
          ((action D a v)[[-1+(N : ℤ)-i]])
            (cmode D a 0 u (tau+i) (vacuum D)) := by
  classical
  have hj := (mixed_jacobi D (1 : Matrix _ _ ℤ) hD a 0 v u (vacuum D)
    (-1) (N : ℤ) tau).2.2.2
  have hL : (∑ᶠ i, mixedLeft D (1 : Matrix _ _ ℤ) a 0 v u (vacuum D)
      (-1) (N : ℤ) tau i) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    exact right_jacobi_left_zero D a u v N tau hN
  have hF : (∑ᶠ i, mixedFirst D (1 : Matrix _ _ ℤ) a 0 v u (vacuum D)
      (-1) (N : ℤ) tau i) =
      ∑ i ∈ Finset.range (N+1),
        ((-1 : ℂ)^i * (N.choose i : ℂ)) •
          ((action D a v)[[-1+(N : ℤ)-i]])
            (cmode D a 0 u (tau+i) (vacuum D)) := by
    rw [finsum_eq_sum_of_support_subset _ (right_jacobi_first_support D a u v N tau)]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mixedFirst, Matrix.one_mulVec, add_zero, integerBinomial_nat, cmode]
  have hS : (∑ᶠ i, mixedSecond D (1 : Matrix _ _ ℤ) a 0 v u (vacuum D)
      (-1) (N : ℤ) tau i) = (-1 : ℂ)^N • cmode D a 0 u (tau+N) v := by
    rw [finsum_eq_single _ 0]
    · simp [mixedSecond, integerBinomial, Matrix.one_mulVec, original_vacuum_mode,
        cmode, zpow_natCast, action_zero_mode, stateField_creation]
    · intro i hi
      by_contra hn
      exact hi (right_jacobi_second_support D a u v N tau hn)
  rw [hL,hF,hS] at hj
  exact (sub_eq_zero.mp hj.symm).symm

private theorem sign_reverse (N i : ℕ) (hi : i ≤ N) :
    (-1 : ℂ)^N * (-1 : ℂ)^i = (-1 : ℂ)^(N-i) := by
  have hsq : (-1 : ℂ)^i * (-1 : ℂ)^i = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℂ)^(N-i) * (-1 : ℂ)^i) * (-1 : ℂ)^i := by
      nth_rw 1 [← Nat.sub_add_cancel hi]
      rw [pow_add]
    _ = _ := by rw [mul_assoc, hsq, mul_one]

/-- Raw finite Jacobi formula before reversing the finite index. -/
theorem canonical_right_finite_jacobi_reverse (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Charge D) (u v : Carrier D)
    (k : ℤ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → ((action D a v)[[m]]) u = 0) :
    (C D a 0 u).coeff (k : ℚ) v =
      ∑ i ∈ Finset.range (N+1),
        ((-1 : ℂ)^(N-i) * (N.choose i : ℂ)) •
          ((action D a v)[[-1+(N : ℤ)-i]])
            (creationCoefficient D hD a u (k+N-i)) := by
  have hj := canonical_right_finite_jacobi_mode D hD a u v N
    (-(k : ℚ)-1-N) hN
  have hm (i : ℕ) : cmode D a 0 u (-(k : ℚ)-1-N+i) (vacuum D) =
      creationCoefficient D hD a u (k+N-i) := by
    change (C D a 0 u).coeff (-(-(k : ℚ)-1-N+i)-1) (vacuum D) = _
    rw [show -(-(k : ℚ)-1-N+i)-1 = ((k+N-i : ℤ) : ℚ) by push_cast; ring]
    exact canonical_right_creation_integer D hD a u _
  have hm0 : cmode D a 0 u (-(k : ℚ)-1-N+N) v =
      (C D a 0 u).coeff (k : ℚ) v := by
    change (C D a 0 u).coeff (-(-(k : ℚ)-1-N+N)-1) v = _
    congr 2 <;> ring
  rw [hm0] at hj
  simp_rw [hm] at hj
  have he := congrArg (fun x : Carrier D => (-1 : ℂ)^N • x) hj
  have hsq : (-1 : ℂ)^N * (-1 : ℂ)^N = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [smul_smul, hsq, one_smul, Finset.smul_sum] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, ← mul_assoc, sign_reverse N i (by simpa using Finset.mem_range.mp hi)]

/-- The concrete all-state finite Jacobi consumer, j=0,...,N. -/
theorem canonical_right_finite_jacobi (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Charge D) (u v : Carrier D)
    (k : ℤ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → ((action D a v)[[m]]) u = 0) :
    (C D a 0 u).coeff (k : ℚ) v =
      ∑ j ∈ Finset.range (N+1),
        ((-1 : ℂ)^j * (N.choose j : ℂ)) •
          ((action D a v)[[(j : ℤ)-1]])
            (creationCoefficient D hD a u (k+j)) := by
  rw [canonical_right_finite_jacobi_reverse D hD a u v k N hN]
  apply Finset.sum_bij (fun i _ => N-i)
  · intro i hi
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  · intro j hj
    refine ⟨N-j, Finset.mem_range.mpr (by omega), ?_⟩
    have hj' := Finset.mem_range.mp hj
    omega
  · intro i hi
    have hi' : i ≤ N := by have hh := Finset.mem_range.mp hi; omega
    have he : ((N-i : ℕ) : ℤ) = (N : ℤ)-i := by omega
    have hc : N.choose (N-i) = N.choose i := Nat.choose_symm hi'
    rw [hc, he]
    rw [show -1+(N : ℤ)-(i : ℤ) = (N : ℤ)-(i : ℤ)-1 by omega,
      show k+(N : ℤ)-(i : ℤ) = k+((N : ℤ)-(i : ℤ)) by omega]

/-- A substantive support consequence of the finite Jacobi consumer. -/
theorem canonical_right_integer_below_cutoff (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Charge D) (u v : Carrier D)
    (k : ℤ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → ((action D a v)[[m]]) u = 0)
    (hk : k < -(N : ℤ)) : (C D a 0 u).coeff (k : ℚ) v = 0 := by
  rw [canonical_right_finite_jacobi D hD a u v k N hN]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp [creationCoefficient, show ¬ 0 ≤ k+(j : ℤ) by omega]


/- The scalar in Pro (5.7), proved by a finite Pascal convolution. -/

private def binomialWeight (N j : ℕ) : ℂ := (-1 : ℂ)^j * (N.choose j : ℂ)

private def binomialTransform (N : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N+1), binomialWeight N j * f j

private theorem binomialWeight_succ (N j : ℕ) :
    binomialWeight (N+1) (j+1) = binomialWeight N (j+1) - binomialWeight N j := by
  simp only [binomialWeight, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

private theorem sum_zero_and_tail (f : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), f j) = f 0 + ∑ j ∈ Finset.range n, f (j+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private theorem binomialTransform_succ (N : ℕ) (f : ℕ → ℂ) :
    binomialTransform (N+1) f =
      binomialTransform N f - binomialTransform N (fun j => f (j+1)) := by
  have htail : (∑ j ∈ Finset.range (N+1), binomialWeight N (j+1) * f (j+1)) =
      ∑ j ∈ Finset.range N, binomialWeight N (j+1) * f (j+1) := by
    rw [Finset.sum_range_succ]
    have hz : binomialWeight N (N+1) = 0 := by
      simp [binomialWeight, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N)]
    rw [hz, zero_mul, add_zero]
  have hsplit := sum_zero_and_tail (fun j => binomialWeight N j * f j) N
  simp only [binomialWeight, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, one_mul] at hsplit
  unfold binomialTransform
  rw [sum_zero_and_tail, show binomialWeight (N+1) 0 = 1 by simp [binomialWeight], one_mul]
  simp_rw [binomialWeight_succ, sub_mul]
  rw [Finset.sum_sub_distrib, htail]
  change f 0 + ((∑ j ∈ Finset.range N, binomialWeight N (j+1) * f (j+1)) -
    ∑ j ∈ Finset.range (N+1), binomialWeight N j * f (j+1)) = _
  have hs : (∑ j ∈ Finset.range (N+1), binomialWeight N j * f j) =
      f 0 + ∑ j ∈ Finset.range N, binomialWeight N (j+1) * f (j+1) := by
    simpa only [binomialWeight] using hsplit
  rw [hs]
  ring

/-- Negative lower indices are interpreted as zero, never as a toNat alias for zero. -/
def conjugationKernel (j : ℕ) (k : ℤ) : ℂ :=
  if 0 ≤ k+(j : ℤ) then integerBinomial ((j : ℤ)-1) (k+j).toNat else 0

private theorem conjugationKernel_succ (j : ℕ) (k : ℤ) :
    conjugationKernel (j+1) k = conjugationKernel j k + conjugationKernel j (k+1) := by
  by_cases hk : 0 ≤ k+(j : ℤ)
  · have hk1 : 0 ≤ k+(j+1 : ℕ) := by omega
    have hk2 : 0 ≤ k+1+(j : ℤ) := by omega
    have ht : (k+((j+1 : ℕ) : ℤ)).toNat = (k+(j : ℤ)).toNat+1 := by omega
    have ht' : (k+1+(j : ℤ)).toNat = (k+(j : ℤ)).toNat+1 := by omega
    simp only [conjugationKernel, hk, hk1, hk2, ↓reduceIte, ht, ht', integerBinomial]
    rw [show ((j+1 : ℕ) : ℤ)-1 = ((j : ℤ)-1)+1 by omega, Ring.choose_succ_succ]
    push_cast
    ring
  · by_cases he : k+(j : ℤ) = -1
    · have hk1 : k+((j : ℤ)+1) = 0 := by omega
      have hk2 : k+1+(j : ℤ) = 0 := by omega
      simp [conjugationKernel, hk, hk1, hk2, integerBinomial]
    · have hk1 : ¬ 0 ≤ k+((j : ℤ)+1) := by omega
      have hk2 : ¬ 0 ≤ k+1+(j : ℤ) := by omega
      simp [conjugationKernel, hk, hk1, hk2]

private theorem minus_one_choose (n : ℕ) : integerBinomial (-1) n = (-1 : ℂ)^n := by
  unfold integerBinomial
  rw [Ring.choose_neg', Ring.multichoose_one]
  simp [Units.smul_def, Int.cast_negOnePow_natCast]

private theorem conjugationKernel_zero (k : ℤ) :
    conjugationKernel 0 k = if 0 ≤ k then (-1 : ℂ)^k else 0 := by
  by_cases hk : 0 ≤ k
  · simp only [conjugationKernel, Nat.cast_zero, add_zero, hk, ↓reduceIte,
      zero_sub, minus_one_choose]
    have ht : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
    calc
      _ = (-1 : ℂ)^((k.toNat : ℕ) : ℤ) := by rw [zpow_natCast]
      _ = _ := by rw [ht]
  · simp [conjugationKernel, hk]

private theorem conjugationTransform_succ (N : ℕ) (k : ℤ) :
    binomialTransform (N+1) (fun j => conjugationKernel j k) =
      -binomialTransform N (fun j => conjugationKernel j (k+1)) := by
  rw [binomialTransform_succ]
  simp_rw [conjugationKernel_succ]
  unfold binomialTransform
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

/-- Full finite scalar identity used in Pro (5.7), including the empty-support case. -/
theorem pro57_finite_binomial_identity (N : ℕ) (k : ℤ) :
    (∑ j ∈ Finset.range (N+1),
      if 0 ≤ k+(j : ℤ) then
        ((-1 : ℂ)^j * (N.choose j : ℂ)) *
          integerBinomial ((j : ℤ)-1) (k+j).toNat
      else 0) = if 0 ≤ k+(N : ℤ) then (-1 : ℂ)^k else 0 := by
  have hh : ∀ (N : ℕ) (k : ℤ),
      binomialTransform N (fun j => conjugationKernel j k) =
        if 0 ≤ k+(N : ℤ) then (-1 : ℂ)^k else 0 := by
    intro N
    induction N with
    | zero =>
      intro k
      simpa [binomialTransform, binomialWeight] using conjugationKernel_zero k
    | succ N ih =>
      intro k
      rw [conjugationTransform_succ, ih]
      have he : k+1+(N : ℤ) = k+((N+1 : ℕ) : ℤ) := by omega
      rw [he]
      split_ifs
      · have hs : (-1 : ℂ)^(k+1) = -((-1 : ℂ)^k) := by
          rw [zpow_add₀ (by norm_num)]
          norm_num
        rw [hs, neg_neg]
      · simp
  have hc := hh N k
  unfold binomialTransform conjugationKernel binomialWeight at hc
  convert hc using 1
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with h <;> simp_all

/-- The nonempty scalar branch is exactly (-1)^k, with no analytic interpretation. -/
theorem pro57_finite_binomial_nonempty (N : ℕ) (k : ℤ) (hk : -(N : ℤ) ≤ k) :
    (∑ j ∈ Finset.range (N+1),
      if 0 ≤ k+(j : ℤ) then
        ((-1 : ℂ)^j * (N.choose j : ℂ)) *
          integerBinomial ((j : ℤ)-1) (k+j).toNat
      else 0) = (-1 : ℂ)^k := by
  rw [pro57_finite_binomial_identity, if_pos (by omega)]

/- Finite divided-power commutation.  All powers are finite powers of the
   actual endomorphism supplied to this lemma. -/
private theorem sum_head_tail {V : Type*} [AddCommMonoid V]
    (f : ℕ → V) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), f j) = f 0 + ∑ j ∈ Finset.range n, f (j+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ac_rfl

private theorem binomial_falling_step (m : ℤ) (t : ℕ) :
    (m : ℂ) * integerBinomial (m-1) t =
      ((t+1 : ℕ) : ℂ) * integerBinomial m (t+1) := by
  have h := Ring.choose_smul_choose m (n := t+1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel,
    nsmul_eq_mul] at h
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  simpa only [integerBinomial, Int.cast_mul, Int.cast_natCast, Int.natCast_one] using hc.symm

private theorem factorial_inverse_step (r : ℕ) :
    (r.factorial : ℂ)⁻¹ =
      ((r+1 : ℕ) : ℂ) * (((r+1).factorial : ℂ)⁻¹) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hr : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hs : ((r+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  field_simp [hr, hs] <;> ring

private def dividedTerm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (A : ℤ → Module.End ℂ V)
    (r t : ℕ) (m : ℤ) (x : V) : V :=
  (integerBinomial m t * ((r-t).factorial : ℂ)⁻¹) •
    (T^(r-t)) (A (m-(t : ℤ)) x)

/-- The falling, finite covariance formula. No infinite operator series occurs. -/
theorem finite_covariance_divided_power {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (A : ℤ → Module.End ℂ V)
    (h : ∀ (m : ℤ) (x : V), T (A m x) - A m (T x) =
      -(m : ℂ) • A (m-1) x)
    (m : ℤ) (R : ℕ) (x : V) :
    A m ((R.factorial : ℂ)⁻¹ • (T^R) x) =
      ∑ t ∈ Finset.range (R+1),
        integerBinomial m t •
          (((R-t).factorial : ℂ)⁻¹ • (T^(R-t)) (A (m-(t : ℤ)) x)) := by
  classical
  have comm (m : ℤ) (y : V) :
      A m (T y) = T (A m y) + (m : ℂ) • A (m-1) y := by
    have hh := h m y
    linear_combination (norm := module) -hh
  have expansion : ∀ R : ℕ, ∀ m : ℤ,
      A m ((R.factorial : ℂ)⁻¹ • (T^R) x) =
        ∑ t ∈ Finset.range (R+1), dividedTerm T A R t m x := by
    intro R
    induction R with
    | zero => intro m; simp [dividedTerm, integerBinomial]
    | succ R ih =>
      intro m
      let f := fun t => dividedTerm T A (R+1) t m x
      have interior (s : ℕ) (hs : s < R) :
          T (dividedTerm T A R (s+1) m x) +
            (m : ℂ) • dividedTerm T A R s (m-1) x =
          ((R+1 : ℕ) : ℂ) • f (s+1) := by
        have he : R-s = (R-(s+1))+1 := by omega
        have hf : ((R-(s+1)).factorial : ℂ)⁻¹ =
            ((R-s : ℕ) : ℂ) * ((R-s).factorial : ℂ)⁻¹ := by
          simpa only [← he] using factorial_inverse_step (R-(s+1))
        have hp : R+1-(s+1) = R-s := by omega
        have hm : m-1-(s : ℤ) = m-((s+1 : ℕ) : ℤ) := by omega
        have hb := binomial_falling_step m s
        have hcast : ((R-s : ℕ) : ℂ) + ((s+1 : ℕ) : ℂ) =
            ((R+1 : ℕ) : ℂ) := by exact_mod_cast (show R-s+(s+1)=R+1 by omega)
        simp only [f, dividedTerm, map_smul, ← Module.End.mul_apply,
          ← pow_succ', ← he, hp, hm, smul_smul, hf]
        simp only [← mul_assoc, ← pow_succ', ← he]
        rw [← add_smul]
        congr 1
        linear_combination ((R-s).factorial : ℂ)⁻¹ * hb +
          integerBinomial m (s+1) * ((R-s).factorial : ℂ)⁻¹ * hcast
      have first : T (dividedTerm T A R 0 m x) =
          ((R+1 : ℕ) : ℂ) • f 0 := by
        simp only [f, dividedTerm, Nat.sub_zero, integerBinomial,
          Ring.choose_zero_right, Int.cast_one, one_mul, Int.natCast_zero,
          sub_zero, map_smul, pow_succ', Module.End.mul_apply, smul_smul]
        rw [← factorial_inverse_step]
      have last : (m : ℂ) • dividedTerm T A R R (m-1) x =
          ((R+1 : ℕ) : ℂ) • f (R+1) := by
        simp only [f, dividedTerm, Nat.sub_self, Nat.factorial_zero,
          Nat.cast_one, inv_one, mul_one, pow_zero, Module.End.one_apply,
          smul_smul]
        rw [show m-1-(R : ℤ) = m-((R+1 : ℕ) : ℤ) by omega,
          binomial_falling_step]
      have combine :
          T (∑ t ∈ Finset.range (R+1), dividedTerm T A R t m x) +
            (m : ℂ) • (∑ t ∈ Finset.range (R+1), dividedTerm T A R t (m-1) x) =
          ((R+1 : ℕ) : ℂ) • ∑ t ∈ Finset.range (R+1+1), f t := by
        rw [map_sum, sum_head_tail, Finset.smul_sum,
          Finset.sum_range_succ (f := fun t => (m : ℂ) • dividedTerm T A R t (m-1) x),
          first, last]
        have hi : (∑ s ∈ Finset.range R, T (dividedTerm T A R (s+1) m x)) +
            (∑ s ∈ Finset.range R, (m : ℂ) • dividedTerm T A R s (m-1) x) =
            ∑ s ∈ Finset.range R, ((R+1 : ℕ) : ℂ) • f (s+1) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun s hs => interior s (Finset.mem_range.mp hs))
        rw [sum_head_tail f (R+1), Finset.sum_range_succ,
          smul_add, smul_add, Finset.smul_sum]
        linear_combination (norm := module) hi
      have step : ((R+1 : ℕ) : ℂ) •
          A m ((((R+1).factorial : ℂ)⁻¹) • (T^(R+1)) x) =
          ((R+1 : ℕ) : ℂ) • ∑ t ∈ Finset.range (R+1+1), f t := by
        calc
          _ = A m (T ((R.factorial : ℂ)⁻¹ • (T^R) x)) := by
            simp only [map_smul, smul_smul, pow_succ', Module.End.mul_apply]
            rw [← factorial_inverse_step]
          _ = _ := by rw [comm, ih, ih, combine]
      have hn : ((R+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero R
      calc
        _ = (((R+1 : ℕ) : ℂ)⁻¹) •
            (((R+1 : ℕ) : ℂ) • A m ((((R+1).factorial : ℂ)⁻¹) • (T^(R+1)) x)) := by
          rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
        _ = _ := by rw [step, smul_smul, inv_mul_cancel₀ hn, one_smul]
  simpa only [dividedTerm, smul_smul] using expansion R m

/-- Apply the finite formula to the ORIGINAL omega-zero covariance. -/
theorem canonical_mode_divided_translation (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Charge D) (u v : Carrier D) (m : ℤ) (R : ℕ) :
    ((action D a v)[[m]])
        ((R.factorial : ℂ)⁻¹ • ((sectorTranslation D hD a)^R) u) =
      ∑ t ∈ Finset.range (R+1), integerBinomial m t •
        (((R-t).factorial : ℂ)⁻¹ • ((sectorTranslation D hD a)^(R-t))
          (((action D a v)[[m-(t : ℤ)]]) u)) :=
  finite_covariance_divided_power (sectorTranslation D hD a)
    (fun m => (action D a v)[[m]])
    (fun m x => sectorTranslation_covariance D hD a v x m) m R u

private theorem sum_reverse_range {V : Type*} [AddCommMonoid V]
    (R : ℕ) (f : ℕ → V) :
    (∑ t ∈ Finset.range (R+1), f t) =
      ∑ i ∈ Finset.range (R+1), f (R-i) := by
  apply Finset.sum_bij (fun t _ => R-t)
  · intro t ht; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp ht; omega)
  · intro t ht s hs he
    have := Finset.mem_range.mp ht; have := Finset.mem_range.mp hs; omega
  · intro i hi
    refine ⟨R-i, Finset.mem_range.mpr (by omega), ?_⟩
    have := Finset.mem_range.mp hi; omega
  · intro t ht
    have := Finset.mem_range.mp ht
    congr 1; omega

/-- Faithful finite triangle conversion, with only the ORIGINAL pair cutoff. -/
theorem canonical_right_general_integer
    (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Charge D) (u v : Carrier D) (k : ℤ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → ((action D a v)[[m]]) u = 0) :
    (C D a 0 u).coeff (k : ℚ) v =
      ∑ j ∈ Finset.range (((N : ℤ)+k+1).toNat),
        (((-1 : ℂ)^(k-(j : ℤ))) / (j.factorial : ℂ)) •
          ((sectorTranslation D hD a)^j)
            (((action D a v)[[(j : ℤ)-k-1]]) u) := by
  classical
  let M := ((N : ℤ)+k+1).toNat
  let d := fun i : ℕ => (i.factorial : ℂ)⁻¹ •
    ((sectorTranslation D hD a)^i) (((action D a v)[[(i : ℤ)-k-1]]) u)
  let K := fun j i : ℕ =>
    if 0 ≤ k-(i : ℤ)+(j : ℤ) then
      integerBinomial ((j : ℤ)-1) (k-i+j).toNat else 0
  have row (j : ℕ) (hj : j ∈ Finset.range (N+1)) :
      ((action D a v)[[(j : ℤ)-1]]) (creationCoefficient D hD a u (k+j)) =
        ∑ i ∈ Finset.range M, K j i • d i := by
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    by_cases hR : 0 ≤ k+(j : ℤ)
    · let R := (k+(j : ℤ)).toNat
      have hRz : (R : ℤ) = k+j := Int.toNat_of_nonneg hR
      rw [creationCoefficient, if_pos hR,
        canonical_mode_divided_translation D hD a u v ((j : ℤ)-1) R,
        sum_reverse_range]
      have hs : Finset.range (R+1) ⊆ Finset.range M := by
        intro i hi
        apply Finset.mem_range.mpr
        have := Finset.mem_range.mp hi
        dsimp [M]; omega
      calc
        _ = ∑ i ∈ Finset.range (R+1), K j i • d i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiR : i ≤ R := by have := Finset.mem_range.mp hi; omega
          have hp : R-(R-i) = i := by omega
          have ht : R-i = (k-(i : ℤ)+(j : ℤ)).toNat := by omega
          have hm : (j : ℤ)-1-((R-i : ℕ) : ℤ) = (i : ℤ)-k-1 := by omega
          simp only [hp, hm, K, if_pos (by omega : 0 ≤ k-(i : ℤ)+(j : ℤ)), d]
          rw [ht]
        _ = _ := by
          apply Finset.sum_subset hs
          intro i hi hin
          have hiR : R < i := by have hh := hin; simp only [Finset.mem_range, not_lt] at hh; omega
          simp [K, show ¬ 0 ≤ k-(i : ℤ)+(j : ℤ) by omega]
    · rw [creationCoefficient, if_neg hR, map_zero]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      simp [K, show ¬ 0 ≤ k-(i : ℤ)+(j : ℤ) by omega]
  rw [canonical_right_finite_jacobi D hD a u v k N hN]
  trans ∑ j ∈ Finset.range (N+1),
      ∑ i ∈ Finset.range M, ((-1 : ℂ)^j * (N.choose j : ℂ)) • (K j i • d i)
  · apply Finset.sum_congr rfl
    intro j hj
    rw [row j hj, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hKi : 0 ≤ k-(i : ℤ)+(N : ℤ) := by
    have := Finset.mem_range.mp hi
    dsimp [M] at this
    omega
  have scalar : (∑ j ∈ Finset.range (N+1),
      ((-1 : ℂ)^j * (N.choose j : ℂ)) * K j i) = (-1 : ℂ)^(k-(i : ℤ)) := by
    have hh := pro57_finite_binomial_identity N (k-(i : ℤ))
    rw [if_pos hKi] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [K]
    split_ifs <;> simp
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, scalar]
  simp only [d, smul_smul, div_eq_mul_inv]

end
end D5.S3.VertexAlgebra.LatticeCosetCanonicalUnits

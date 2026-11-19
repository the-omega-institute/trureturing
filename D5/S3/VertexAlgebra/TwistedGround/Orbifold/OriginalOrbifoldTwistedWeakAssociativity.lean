/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedWeakAssociativity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedWeakAssociativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cleared three-twisted associativity has a nonzero vacuum-normalized coefficient. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumFusion

/-! The original orbifold Borcherds identity restricted to three negative
twisted inputs, with its weight-two vacuum normalization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedWeakAssociativity

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open LatticeInvolution (FixedCarrier fixedVacuum)
open MixedIntertwiner (originalRightCoefficient)
open OriginalFourMChargeCoset (originalI originalI_homogeneous)
open OriginalOrbifoldField (Y Y_fixed_ncoeff_apply Y_twisted_ncoeff_apply Y_ncoeff mode_tail)
open OriginalOrbifoldSectorModules (fixedParityY fixedParitySlice_vacuum_ncoeff)
open OriginalOrbifoldTwistedVacuumFusion
  (NegativeTwisted canonical_mode_int canonical_mode_three canonical_vacuum_witness firstOscillator)
open OriginalOrbifoldVacuumChannel
  (intoTwisted stateField_twisted_twisted vacuumCoefficient weightTwo)
open OriginalOrbifoldVertexAlgebra (originalVertexAlgebra)
open StateFieldResidueReconstruction (integerBinomial)
open private original_negative_grade_zero from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private tensor_energy from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumChannel

local notation "D" => leechData
private theorem hu : IsUnit leechData.G.det := leech_spec.2.1
private theorem hD : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
private theorem h24 : leechData.rank = 24 := leech_spec.1

local notation "X" => NegativeTwisted
local notation "A" => originalVertexAlgebra D hu hD h24
local notation "I" => originalI D hu hD

/-- The iterate summand through the fixed sector. -/
def iterateTerm (u v w : X) (p q r : ℤ) (i : ℕ) : X :=
  integerBinomial p i • ((fixedParitySlice D hu (-1) (I (r + i) u v))[[p + q - i]]) w

/-- The product summand using the original right action on the fixed output. -/
def productTerm (u v w : X) (p q r : ℤ) (i : ℕ) : X :=
  ((-1 : ℂ)^i * integerBinomial r i) •
    originalRightCoefficient D hu (p + r - i) u (I (q + i) v w)

/-- Lower truncation supplies a clearing index for any pair of twisted states. -/
theorem clearing_index_exists (u w : X) :
    ∃ p : ℤ, ∀ i : ℕ, I (p + i) u w = 0 := by
  obtain ⟨p, hp⟩ := mode_tail D hu hD (0, u) (0, w)
  refine ⟨p, fun i => ?_⟩
  have h : (((A).stateField (0, u))[[p + i]]) (0, w) = 0 := by
    change ((Y D hu hD (0, u))[[p + i]]) (0, w) = 0
    rw [Y_ncoeff]
    exact hp _ (by omega)
  rw [stateField_twisted_twisted] at h
  exact congrArg Prod.fst h

/-- After clearing the reverse product, both sums have finite support and the
fixed-sector iterate equals the ordered product in the actual twisted sector. -/
theorem cleared_weak_associativity (u v w : X) (p q r : ℤ)
    (hclear : ∀ i : ℕ, I (p + i) u w = 0) :
    Function.HasFiniteSupport (iterateTerm u v w p q r) ∧
      Function.HasFiniteSupport (productTerm u v w p q r) ∧
      (∑ᶠ i : ℕ, iterateTerm u v w p q r i) =
        ∑ᶠ i : ℕ, productTerm u v w p q r i := by
  have reverse_zero (i : ℕ) :
      (((A).stateField (0, v))[[q + r - i]]) ((((A).stateField (0, u))[[p + i]]) (0, w)) =
        0 := by
    rw [stateField_twisted_twisted, hclear i]
    exact map_zero _
  obtain ⟨hIterate, hProduct, _, h⟩ := (A).borcherds (0, u) (0, v) (0, w) p q r
  dsimp only at hIterate hProduct h
  simp only [reverse_zero, smul_zero, sub_zero] at h
  let proj := LinearMap.snd ℂ (FixedCarrier D) X
  refine ⟨?_, ?_, ?_⟩
  · apply (hIterate.fun_comp (map_zero proj)).subset
    intro i hi hz
    apply hi
    simpa only [proj, iterateTerm, originalVertexAlgebra, Y_twisted_ncoeff_apply,
      Y_fixed_ncoeff_apply, map_zero, LinearMap.snd_apply, Prod.smul_snd] using hz
  · apply (hProduct.fun_comp (map_zero proj)).subset
    intro i hi hz
    apply hi
    simpa only [proj, productTerm, originalVertexAlgebra, Y_twisted_ncoeff_apply,
      LinearMap.snd_apply, Prod.smul_snd] using hz
  · have hProjected := congrArg proj h
    rw [map_finsum proj hIterate, map_finsum proj hProduct] at hProjected
    simpa only [proj, iterateTerm, productTerm, originalVertexAlgebra,
      Y_twisted_ncoeff_apply, Y_fixed_ncoeff_apply, map_zero,
      LinearMap.snd_apply, Prod.smul_snd] using hProjected

/-- Above mode three the homogeneous fixed output has negative grade. -/
theorem weight_two_mode_zero (u v : weightTwo) (n : ℤ) (hn : 3 < n) :
    I n (intoTwisted u) (intoTwisted v) = 0 := by
  have zeroInGrade (e : ℤ) (he : e < 0) (x : MixedIntertwiner.fixedGrade D e) :
      x.val = 0 :=
    original_negative_grade_zero D hD e x.val x.property.1 he
  rw [originalI_homogeneous D hu hD h24 2 2 n _ _ (tensor_energy u) (tensor_energy v)]
  apply Subtype.ext
  exact zeroInGrade (2 + 2 - n - 1) (by omega) _

/-- At `r = 3` and `q = -p-1`, the common coefficient is the mode-three
vacuum scalar times the third twisted state. -/
theorem vacuum_normalized (u v w : weightTwo) (p : ℤ) (hp : 4 ≤ p) :
    (∑ᶠ i : ℕ, iterateTerm (intoTwisted u) (intoTwisted v) (intoTwisted w)
        p (-p - 1) 3 i) = vacuumCoefficient u v • intoTwisted w ∧
      (∑ᶠ i : ℕ, productTerm (intoTwisted u) (intoTwisted v) (intoTwisted w)
        p (-p - 1) 3 i) = vacuumCoefficient u v • intoTwisted w := by
  have hclear (i : ℕ) : I (p + i) (intoTwisted u) (intoTwisted w) = 0 :=
    weight_two_mode_zero u w _ (by omega)
  have hAssoc := (cleared_weak_associativity (intoTwisted u) (intoTwisted v) (intoTwisted w)
    p (-p - 1) 3 hclear).2.2
  have hThree : I 3 (intoTwisted u) (intoTwisted v) = vacuumCoefficient u v • fixedVacuum D :=
    (canonical_mode_int (intoTwisted u) (intoTwisted v) 3).symm.trans (canonical_mode_three u v)
  have hIterate : (∑ᶠ i : ℕ, iterateTerm (intoTwisted u) (intoTwisted v) (intoTwisted w)
      p (-p - 1) 3 i) = vacuumCoefficient u v • intoTwisted w := by
    rw [finsum_eq_single _ 0]
    · have hIndex : p + (-p - 1) = -1 := by omega
      simp only [iterateTerm, Nat.cast_zero, add_zero, sub_zero, hIndex, hThree,
        integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul]
      change ((fixedParityY D hu (-1) (vacuumCoefficient u v • fixedVacuum D))[[(-1 : ℤ)]])
        (intoTwisted w) = _
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
        fixedParitySlice_vacuum_ncoeff, ite_true]
    · intro i hi
      have hiMode := weight_two_mode_zero u v (3 + i) (by omega)
      unfold iterateTerm
      rw [hiMode]
      change integerBinomial p i • ((fixedParityY D hu (-1) 0)[[p + (-p - 1) - i]])
        (intoTwisted w) = 0
      simp
  exact ⟨hIterate, hAssoc.symm.trans hIterate⟩

/-- For every first oscillator, its vacuum partner can also serve as the
third state, giving a nonzero coefficient at every clearing index `p ≥ 4`. -/
theorem vacuum_normalized_witness (i : Fin leechData.rank) :
    ∃ v : weightTwo, vacuumCoefficient (firstOscillator i) v ≠ 0 ∧
      ∀ p : ℤ, 4 ≤ p →
        (∑ᶠ j : ℕ, productTerm (intoTwisted (firstOscillator i)) (intoTwisted v)
          (intoTwisted v) p (-p - 1) 3 j) ≠ 0 := by
  obtain ⟨v, hv, _⟩ := canonical_vacuum_witness i
  have hvTwisted : intoTwisted v ≠ 0 := by
    intro hz
    have hvZero : v = 0 := Subtype.ext (congrArg (fun w : X => w.val) hz)
    exact hv (by rw [hvZero, map_zero])
  refine ⟨v, hv, fun p hp => ?_⟩
  rw [(vacuum_normalized (firstOscillator i) v v p hp).2]
  exact smul_ne_zero hv hvTwisted

#print axioms clearing_index_exists
#print axioms cleared_weak_associativity
#print axioms weight_two_mode_zero
#print axioms vacuum_normalized
#print axioms vacuum_normalized_witness

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedWeakAssociativity

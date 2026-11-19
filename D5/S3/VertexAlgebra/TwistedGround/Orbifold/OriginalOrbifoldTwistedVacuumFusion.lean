/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The negative twisted Leech pair intertwines nontrivially to the fixed algebra. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumChannel
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldCrossedChannel

/-! The negative twisted Leech pair intertwines into the fixed Leech algebra.
The full operator space allows rational modes and uses the actual module
actions in the mixed Borcherds identity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumFusion

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier fixedMode fixedTranslation fixedVacuum)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open OriginalFourMChargeCoset (originalI)
open OriginalOrbifoldConformal
  (conformalVector L L_eq_mode L_minus_one_eq_translation)
open OriginalOrbifoldField (Y_fixed_ncoeff_apply)
open OriginalOrbifoldVertexAlgebra (originalVertexAlgebra)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldVacuumChannel (weightTwo intoTwisted vacuumCoefficient
  vacuumCoefficient_nondegenerate stateField_twisted_twisted
  projected_L_minus_one_derivative projected_mixed_borcherds stateField_modeThree)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open VacuumFirstIntertwinerDraft (mode rationalMode rationalMode_int inducedField)
open private rationalMode_nonintegral nonintegral_shift finite_map
  sum_choose_zero sum_signed_choose_zero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion

local notation "D" => leechData
private theorem hu : IsUnit leechData.G.det := leech_spec.2.1
private theorem hD : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
private theorem h24 : leechData.rank = 24 := leech_spec.1

abbrev NegativeTwisted := paritySpace D hu (-1)
abbrev FixedLeech := FixedCarrier D
abbrev Fields := VacuumFirstIntertwinerDraft.Fields NegativeTwisted NegativeTwisted FixedLeech

local notation "X" => NegativeTwisted
local notation "V" => FixedLeech
local notation "A" => originalVertexAlgebra D hu hD h24
local notation "ρ" => fixedParityY D hu (-1)
local notation "ω" => Prod.fst (conformalVector D hu)

/-- The iterate and the two ordered products in mixed coefficient Jacobi. -/
def leftTerm (J : Fields) (a : V) (u v : X) (p r : ℤ) (q : ℚ) (i : ℕ) : V :=
  integerBinomial p i • mode J (((ρ a)[[r + i]]) u) ((p : ℚ) + q - i) v

def firstTerm (J : Fields) (a : V) (u v : X) (p r : ℤ) (q : ℚ) (i : ℕ) : V :=
  ((-1 : ℂ)^i * integerBinomial r i) •
    fixedMode D a (p + r - i) (mode J u (q + i) v)

def secondTerm (J : Fields) (a : V) (u v : X) (p r : ℤ) (q : ℚ) (i : ℕ) : V :=
  ((-1 : ℂ)^i * integerBinomial r i) •
    (epsilon r • mode J u (q + (r : ℚ) - i) (((ρ a)[[p + i]]) v))

/-- Full coefficient laws. Pointwise lower truncation comes from the
Hahn field type, and the target translation law follows from Jacobi. -/
structure Lawful (J : Fields) : Prop where
  source : ∀ (u : X) (q : ℚ) (v : X),
    mode J (((ρ ω)[[0]]) u) q v = -(q : ℂ) • mode J u (q - 1) v
  jacobi : ∀ (a : V) (u v : X) (p r : ℤ) (q : ℚ),
    Function.HasFiniteSupport (leftTerm J a u v p r q) ∧
    Function.HasFiniteSupport (firstTerm J a u v p r q) ∧
    Function.HasFiniteSupport (secondTerm J a u v p r q) ∧
      (∑ᶠ i, leftTerm J a u v p r q i) =
        (∑ᶠ i, firstTerm J a u v p r q i) - (∑ᶠ i, secondTerm J a u v p r q i)

private theorem lawful_add {J K : Fields} (hJ : Lawful J) (hK : Lawful K) :
    Lawful (J + K) where
  source u q v := by
    simpa [mode, smul_add] using congrArg₂ (· + ·) (hJ.source u q v) (hK.source u q v)
  jacobi a u v p r q := by
    have hl : leftTerm (J + K) a u v p r q =
        leftTerm J a u v p r q + leftTerm K a u v p r q := by
      funext i
      simp [leftTerm, mode, smul_add]
    have hf : firstTerm (J + K) a u v p r q =
        firstTerm J a u v p r q + firstTerm K a u v p r q := by
      funext i
      simp [firstTerm, mode, smul_add]
    have hs : secondTerm (J + K) a u v p r q =
        secondTerm J a u v p r q + secondTerm K a u v p r q := by
      funext i
      simp [secondTerm, mode, smul_add]
    obtain ⟨hJl, hJf, hJs, hJe⟩ := hJ.jacobi a u v p r q
    obtain ⟨hKl, hKf, hKs, hKe⟩ := hK.jacobi a u v p r q
    rw [hl, hf, hs]
    refine ⟨hJl.add hKl, hJf.add hKf, hJs.add hKs, ?_⟩
    simp only [Pi.add_apply]
    rw [finsum_add_distrib hJl hKl, finsum_add_distrib hJf hKf,
      finsum_add_distrib hJs hKs, hJe, hKe]
    abel

private theorem lawful_smul (c : ℂ) {J : Fields} (hJ : Lawful J) :
    Lawful (c • J) where
  source u q v := by
    simpa [mode, smul_comm c] using congrArg (c • ·) (hJ.source u q v)
  jacobi a u v p r q := by
    have hl : leftTerm (c • J) a u v p r q = c • leftTerm J a u v p r q := by
      funext i
      simp [leftTerm, mode, smul_comm c]
    have hf : firstTerm (c • J) a u v p r q = c • firstTerm J a u v p r q := by
      funext i
      simp [firstTerm, mode, smul_comm c]
    have hs : secondTerm (c • J) a u v p r q = c • secondTerm J a u v p r q := by
      funext i
      simp [secondTerm, mode, smul_comm c]
    obtain ⟨hJl, hJf, hJs, hJe⟩ := hJ.jacobi a u v p r q
    rw [hl, hf, hs]
    refine ⟨hJl.smul_right (fun _ => c), hJf.smul_right (fun _ => c),
      hJs.smul_right (fun _ => c), ?_⟩
    simp only [Pi.smul_apply, ← smul_finsum' c hJl, ← smul_finsum' c hJf,
      ← smul_finsum' c hJs, hJe, smul_sub]

/-- The full complex vector space of type `(FixedLeech; NegativeTwisted, NegativeTwisted)`. -/
def operatorSpace : Submodule ℂ Fields where
  carrier := {J | Lawful J}
  zero_mem' := by
    change Lawful (0 : Fields)
    constructor
    · intros
      simp [mode]
    · intros
      simp [leftTerm, firstTerm, secondTerm, mode, Function.HasFiniteSupport, Function.support]
  add_mem' := fun hJ hK => lawful_add hJ hK
  smul_mem' := fun c _ hJ => lawful_smul c hJ

private theorem fixed_state_mode (a b : V) (v : X) (n : ℤ) :
    (((A).stateField (a, 0))[[n]]) (b, v) =
      (fixedMode D a n b, (((ρ a)[[n]]) v)) :=
  Y_fixed_ncoeff_apply D hu hD n a (b, v)

/-- The conformal zero mode restricts to the two literal sector translations. -/
private theorem conformal_zero (a : V) (u : X) :
    L D hu hD (-1) (a, u) = (fixedMode D ω 0 a, (((ρ ω)[[0]]) u)) := by
  rw [L_eq_mode D hu hD h24, show (-1 : ℤ) + 1 = 0 by decide]
  change (((A).stateField (ω, 0))[[0]]) (a, u) = _
  exact fixed_state_mode ω a u 0

private theorem fixed_conformal_zero (a : V) :
    fixedMode D ω 0 a = fixedTranslation D a := by
  have h := congrArg Prod.fst (conformal_zero a 0)
  rw [L_minus_one_eq_translation D hu hD h24] at h
  exact h.symm

/-- Lower truncation of every field in this operator space, at each pair of states. -/
theorem lower_truncation (J : operatorSpace) (u v : X) :
    ∃ bound : ℚ, ∀ q : ℚ, bound < q → mode J.val u q v = 0 :=
  VacuumFirstIntertwinerDraft.lower_truncation J.val u v

/-- The target translation commutator, obtained from the conformal
mode zero specialization of full mixed Jacobi and the source derivative. -/
theorem Lawful.target {J : Fields} (hJ : Lawful J) (u v : X) (q : ℚ) :
    fixedTranslation D (mode J u q v) - mode J u q (((ρ ω)[[0]]) v) =
      -(q : ℂ) • mode J u (q - 1) v := by
  have h := (hJ.jacobi ω u v 0 0 q).2.2.2
  simp only [leftTerm, firstTerm, secondTerm, sum_choose_zero, sum_signed_choose_zero,
    Nat.cast_zero, Int.cast_zero, add_zero, zero_add, sub_zero, epsilon, zpow_zero,
    one_smul, fixed_conformal_zero] at h
  exact h.symm.trans (hJ.source u q v)

private abbrev inclusion : X →ₗ[ℂ] OriginalOrbifoldField.Carrier D hu :=
  LinearMap.inr ℂ V X

private abbrev projection : OriginalOrbifoldField.Carrier D hu →ₗ[ℂ] V :=
  LinearMap.fst ℂ V X

/-- Include the twisted inputs in the full original field and project the
output to the fixed sector, with the normalized integer embedding in ℚ. -/
def canonicalField : Fields :=
  (inducedField ((A).stateField.comp inclusion) projection).compl₂ inclusion

/-- Exact comparison at every rational mode with the full original state field. -/
theorem canonical_mode_projected (u v : X) (q : ℚ) :
    mode canonicalField u q v =
      (rationalMode ((A).stateField (0, u)) q (0, v)).1 := rfl

/-- The projected field has the original normalized mode at every integer index. -/
@[simp] theorem canonical_mode_int (u v : X) (n : ℤ) :
    mode canonicalField u (n : ℚ) v = originalI D hu hD n u v := by
  rw [canonical_mode_projected, rationalMode_int, stateField_twisted_twisted]

/-- Rational indices outside the image of ℤ have zero canonical coefficient. -/
theorem canonical_mode_nonintegral (u v : X) (q : ℚ)
    (hq : ¬ ∃ n : ℤ, (n : ℚ) = q) : mode canonicalField u q v = 0 := by
  rw [canonical_mode_projected, rationalMode_nonintegral _ _ hq]
  rfl

private theorem canonical_integer_jacobi (a : V) (u v : X) (p n r : ℤ) :
    Function.HasFiniteSupport (leftTerm canonicalField a u v p r (n : ℚ)) ∧
    Function.HasFiniteSupport (firstTerm canonicalField a u v p r (n : ℚ)) ∧
    Function.HasFiniteSupport (secondTerm canonicalField a u v p r (n : ℚ)) ∧
      (∑ᶠ i, leftTerm canonicalField a u v p r (n : ℚ) i) =
        (∑ᶠ i, firstTerm canonicalField a u v p r (n : ℚ) i) -
          (∑ᶠ i, secondTerm canonicalField a u v p r (n : ℚ) i) := by
  let l (i : ℕ) : V := integerBinomial p i •
    originalI D hu hD (p + n - i) (((ρ a)[[r + i]]) u) v
  let f (i : ℕ) : V := ((-1 : ℂ)^i * integerBinomial r i) •
    fixedMode D a (p + r - i) (originalI D hu hD (n + i) u v)
  let s (i : ℕ) : V := ((-1 : ℂ)^i * integerBinomial r i) •
    (epsilon r • originalI D hu hD (n + r - i) u (((ρ a)[[p + i]]) v))
  have leftIndex (i : ℕ) : (p : ℚ) + (n : ℚ) - i = ((p + n - i : ℤ) : ℚ) := by push_cast; ring
  have firstIndex (i : ℕ) : (n : ℚ) + i = ((n + i : ℤ) : ℚ) := by push_cast; ring
  have secondIndex (i : ℕ) : (n : ℚ) + (r : ℚ) - i = ((n + r - i : ℤ) : ℚ) := by
    push_cast
    ring
  have el : leftTerm canonicalField a u v p r (n : ℚ) = l := by
    funext i
    simp only [leftTerm, leftIndex, canonical_mode_int, l]
  have ef : firstTerm canonicalField a u v p r (n : ℚ) = f := by
    funext i
    simp only [firstTerm, firstIndex, canonical_mode_int, f]
  have es : secondTerm canonicalField a u v p r (n : ℚ) = s := by
    funext i
    simp only [secondTerm, secondIndex, canonical_mode_int, s]
  obtain ⟨hl, hf, hs, _⟩ := (A).borcherds (a, 0) (0, u) (0, v) p n r
  have hl' : Function.HasFiniteSupport l := by
    simpa only [l, fixed_state_mode, stateField_twisted_twisted, map_zero,
      Prod.smul_fst, LinearMap.fst_apply]
      using finite_map projection hl
  have hf' : Function.HasFiniteSupport f := by
    simpa only [f, fixed_state_mode, stateField_twisted_twisted,
      Prod.smul_fst, LinearMap.fst_apply]
      using finite_map projection hf
  have hs' : Function.HasFiniteSupport s := by
    simpa only [s, fixed_state_mode, stateField_twisted_twisted, map_zero,
      Prod.smul_fst, LinearMap.fst_apply]
      using finite_map projection hs
  rw [el, ef, es]
  refine ⟨hl', hf', hs', ?_⟩
  have h := projected_mixed_borcherds a u v p n r
  dsimp only at h
  simp only [smul_sub] at h
  rw [← finsum_sub_distrib hf' hs']
  exact h

/-- The canonical field satisfies the actual mixed laws on all rational modes. -/
theorem canonical_lawful : Lawful canonicalField where
  source u q v := by
    by_cases hq : ∃ n : ℤ, (n : ℚ) = q
    · obtain ⟨n, rfl⟩ := hq
      have h := projected_L_minus_one_derivative n u v
      rw [conformal_zero] at h
      rw [show (n : ℚ) - 1 = ((n - 1 : ℤ) : ℚ) by push_cast; ring]
      simpa only [canonical_mode_int, Rat.cast_intCast] using h
    · have hshift := nonintegral_shift hq (-1)
        (show q - 1 = q + ((-1 : ℤ) : ℚ) by push_cast; ring)
      simp only [canonical_mode_nonintegral _ _ _ hq,
        canonical_mode_nonintegral _ _ _ hshift, smul_zero]
  jacobi a u v p r q := by
    by_cases hq : ∃ n : ℤ, (n : ℚ) = q
    · obtain ⟨n, rfl⟩ := hq
      exact canonical_integer_jacobi a u v p n r
    · have hl : leftTerm canonicalField a u v p r q = 0 := by
        funext i
        have hs := nonintegral_shift hq (p - (i : ℤ))
          (show (p : ℚ) + q - i = q + ((p - (i : ℤ) : ℤ) : ℚ) by push_cast; ring)
        simp [leftTerm, canonical_mode_nonintegral _ _ _ hs]
      have hf : firstTerm canonicalField a u v p r q = 0 := by
        funext i
        have hs := nonintegral_shift hq (i : ℤ)
          (show q + i = q + ((i : ℤ) : ℚ) by push_cast; ring)
        simp [firstTerm, canonical_mode_nonintegral _ _ _ hs]
      have hs : secondTerm canonicalField a u v p r q = 0 := by
        funext i
        have hh := nonintegral_shift hq (r - (i : ℤ))
          (show q + (r : ℚ) - i = q + ((r - (i : ℤ) : ℤ) : ℚ) by push_cast; ring)
        simp [secondTerm, canonical_mode_nonintegral _ _ _ hh]
      rw [hl, hf, hs]
      simp [Function.HasFiniteSupport, Function.support]

/-- The canonical negative-twisted vacuum-output intertwiner. -/
def canonicalIntertwiner : operatorSpace :=
  ⟨canonicalField, canonical_lawful⟩

open OriginalOrbifoldCrossedChannel (oneParticleState leech_neutralCurrent_channels)

/-- A first oscillator of an actual Leech colour, regarded in weight two. -/
def firstOscillator (i : Fin leechData.rank) : weightTwo :=
  ⟨(oneParticleState i).val, (oneParticleState i).property,
    Module.End.mem_eigenspace_iff.mpr (leech_neutralCurrent_channels i).2.1⟩

/-- On actual twisted weight two, the canonical mode three has the original
vacuum coefficient with its original normalization. -/
theorem canonical_mode_three (u v : weightTwo) :
    mode canonicalIntertwiner.val (intoTwisted u) 3 (intoTwisted v) =
      vacuumCoefficient u v • fixedVacuum D := by
  have h := congrArg Prod.fst (stateField_modeThree u v).1
  change mode canonicalField (intoTwisted u) 3 (intoTwisted v) = _
  rw [canonical_mode_projected, show (3 : ℚ) = ((3 : ℤ) : ℚ) by norm_num, rationalMode_int]
  exact h

/-- Each actual first oscillator has a weight-two partner with a nonzero
vacuum coefficient, so the exact mode-three output is nonzero. -/
theorem canonical_vacuum_witness (i : Fin leechData.rank) :
    ∃ v : weightTwo, vacuumCoefficient (firstOscillator i) v ≠ 0 ∧
      mode canonicalIntertwiner.val (intoTwisted (firstOscillator i)) 3 (intoTwisted v) ≠ 0 := by
  have hparticle := leech_neutralCurrent_channels i
  dsimp only at hparticle
  have hfirst : firstOscillator i ≠ 0 := by
    intro hz
    have hw : oneParticleState i = 0 := by
      apply Subtype.ext
      exact congrArg (fun w : weightTwo => w.val) hz
    exact hparticle.2.2.2.1 (hparticle.2.2.1.trans hw)
  obtain ⟨v, hv⟩ : ∃ v, vacuumCoefficient (firstOscillator i) v ≠ 0 := by
    by_contra! h
    exact hfirst (vacuumCoefficient_nondegenerate.1 _ h)
  have hVac : fixedVacuum D ≠ 0 := by
    intro hz
    have h := congrArg (fun a : V => a.val (0 : LatticeGeneratingFieldLocality.Charge D)) hz
    simp [fixedVacuum, LatticeAllStateField.vacuum] at h
  exact ⟨v, hv, by rw [canonical_mode_three]; exact smul_ne_zero hv hVac⟩

/-- The actual negative-twisted pair has a nonzero full-law channel to the fixed algebra. -/
theorem canonicalIntertwiner_ne_zero : canonicalIntertwiner ≠ 0 := by
  let i : Fin leechData.rank := ⟨0, by rw [h24]; decide⟩
  obtain ⟨v, _, hv⟩ := canonical_vacuum_witness i
  intro hz
  apply hv
  rw [hz]
  simp [mode]

#print axioms operatorSpace
#print axioms lower_truncation
#print axioms Lawful.target
#print axioms canonical_mode_projected
#print axioms canonical_mode_int
#print axioms canonical_mode_nonintegral
#print axioms canonical_lawful
#print axioms canonicalIntertwiner
#print axioms canonical_mode_three
#print axioms canonical_vacuum_witness
#print axioms canonicalIntertwiner_ne_zero

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumFusion

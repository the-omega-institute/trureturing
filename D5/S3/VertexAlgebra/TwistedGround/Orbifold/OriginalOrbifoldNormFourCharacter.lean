/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The norm-four character intertwines all modes on the original two-sector orbifold. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInputs
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter
import D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

/-! The all-mode norm-four character on the actual two-sector orbifold. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldNormFourCharacter

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear paritySign)
open LatticeInvolution (FixedCarrier fixedSpace mem_fixedSpace theta thetaLinear theta_single
  fixedMode)
open Lattice.NormFourPeirceInvolution
open LatticeActualGeneratorLocality (paritySign_square)
open LatticeFiniteNegativeGeneration (bilinear_neg_right)
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace
open LatticeHalfFockParityT HalfFock.LatticeHalfFockParityField
open HalfFock.LatticeHalfFockGroundCharacter LatticeHalfFockCorrectedField
open LatticeSugawaraCurrents LatticePositiveEnergy
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open ActualChargedAdjoint MixedIntertwiner OriginalFourMChargeCoset OriginalFourMInputs
open SourceBPZ.OriginalSourcePairing
open OriginalOrbifoldField (Carrier Y Y_fixed_ncoeff_apply Y_ncoeff_apply)

variable (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (s : ℂ)

private theorem chi_theta (x : LatticeGeneratingFieldLocality.Carrier D) :
    theta D (chi D a x) = chi D a (theta D x) := by
  change (thetaLinear D).comp (chiLinear D a) x = (chiLinear D a).comp (thetaLinear D) x
  have h : (thetaLinear D).comp (chiLinear D a) =
      (chiLinear D a).comp (thetaLinear D) := by
    apply Finsupp.lhom_ext
    intro b p
    simp only [LinearMap.comp_apply, chi_single, map_smul, theta_single]
    rw [show phase D a (-b) = phase D a b by
      simp [phase, bilinear_neg_right, paritySign, even_neg] ]
  exact LinearMap.congr_fun h x

set_option maxHeartbeats 1200000 in
-- The restriction unfolds the original theta-fixed carrier during elaboration.
private def fixedAction : Module.End ℂ (FixedCarrier D) :=
  (chiLinear D a).restrict (fun x hx => (mem_fixedSpace D _).mpr
    ((chi_theta D a x).trans (congrArg (chi D a) ((mem_fixedSpace D x).mp hx))))

/-- On the negative twisted sector the plus Ising axis uses minus the lifted
ground action. The parameter `s` is the sign in the norm-four axis. -/
private def groundSign : Module.End ℂ (ActualGround D hu) :=
  (-s) • groundAction D hu a

private abbrev insert : Module.End ℂ (ActualTensor D hu) :=
  actualGroundInsert D hu (groundSign D hu a s)

private theorem insert_parity (x : ActualTensor D hu) :
    actualParity D hu (insert D hu a s x) = insert D hu a s (actualParity D hu x) := by
  have h : (actualParity D hu).comp (insert D hu a s) =
      (insert D hu a s).comp (actualParity D hu) := by
    apply TensorProduct.ext'
    intro p g
    simp only [actualParity, actualGroundInsert, groundSign, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply]
  exact LinearMap.congr_fun h x

private def twistedAction : Module.End ℂ (paritySpace D hu (-1)) :=
  (insert D hu a s).restrict (by
    intro x hx
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [insert_parity, hx, map_smul])

/-- The literal block action on the original fixed and negative twisted carrier. -/
def character : Module.End ℂ (Carrier D hu) :=
  ((fixedAction D a).comp (LinearMap.fst ℂ _ _)).prod
    ((twistedAction D hu a s).comp (LinearMap.snd ℂ _ _))

private theorem character_apply (x : Carrier D hu) :
    character D hu a s x = (fixedAction D a x.1, twistedAction D hu a s x.2) := rfl

private theorem groundSign_square (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) :
    groundSign D hu a s * groundSign D hu a s = 1 := by
  rw [groundSign, smul_mul_smul_comm, HalfFock.NormFourLowestGrades.ground_square D hu a ha,
    neg_mul_neg, ← pow_two, hs, one_smul]

/-- The normalized block action squares to the identity. -/
theorem character_involutive (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) :
    Function.Involutive (character D hu a s) := by
  intro x
  apply Prod.ext
  · apply Subtype.ext
    exact chi_involutive D a x.1.val
  · apply Subtype.ext
    change (insert D hu a s * insert D hu a s) x.2.val = _
    simp only [actualGroundInsert, ← TensorProduct.map_mul, groundSign_square D hu a s ha hs]
    change TensorProduct.map (1 * 1) (1 : Module.End ℂ (ActualGround D hu)) x.2.val = _
    simp

/-- The involution as a complex-linear equivalence of the actual carrier. -/
def symmetry (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) :
    Carrier D hu ≃ₗ[ℂ] Carrier D hu :=
  LinearEquiv.ofInvolutive (character D hu a s) (character_involutive D hu a s ha hs)

private theorem fixedMode_character (n : ℤ) (u v : FixedCarrier D) :
    fixedAction D a (fixedMode D u n v) =
      fixedMode D (fixedAction D a u) n (fixedAction D a v) := by
  apply Subtype.ext
  exact stateField_chi D a u.val v.val n

private theorem insert_character (x : ActualTensor D hu) :
    insert D hu a s x = (-s) • actualGroundInsert D hu (groundAction D hu a) x := by
  have h : insert D hu a s = (-s) • actualGroundInsert D hu (groundAction D hu a) := by
    apply TensorProduct.ext'
    intro p g
    simp only [actualGroundInsert, groundSign, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.smul_apply, TensorProduct.tmul_smul]
  exact LinearMap.congr_fun h x

private theorem fixedSlice_character (n : ℤ) (u : FixedCarrier D)
    (v : paritySpace D hu (-1)) :
    twistedAction D hu a s (((fixedParitySlice D hu (-1) u)[[n]]) v) =
      ((fixedParitySlice D hu (-1) (fixedAction D a u))[[n]]) (twistedAction D hu a s v) := by
  apply Subtype.ext
  change insert D hu a s
      ((correctedField D hu u.val).coeff (2 * (-n - 1)) v.val) =
    (correctedField D hu (chi D a u.val)).coeff (2 * (-n - 1)) (insert D hu a s v.val)
  simp only [insert_character, map_smul, correctedField_ground_character]

variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

/-- Every integer mode with fixed-sector input intertwines on the entire carrier. -/
theorem Y_fixed_character (n : ℤ) (u : FixedCarrier D) (v : Carrier D hu) :
    character D hu a s (((Y D hu hD (u, 0))[[n]]) v) =
      ((Y D hu hD (character D hu a s (u, 0)))[[n]]) (character D hu a s v) := by
  have h : character D hu a s (u, 0) = (fixedAction D a u, 0) :=
    Prod.ext rfl (map_zero (twistedAction D hu a s))
  rw [h, Y_fixed_ncoeff_apply, Y_fixed_ncoeff_apply]
  exact Prod.ext (fixedMode_character D a n u v.1) (fixedSlice_character D hu a s n u v.2)

private theorem chi_omega :
    chi D a (LatticeActualConformalState.omega D (actualInverse D)) =
      LatticeActualConformalState.omega D (actualInverse D) := by
  change chiLinear D a (LatticeActualConformalState.omega D _) =
    LatticeActualConformalState.omega D _
  rw [LatticeActualConformalState.omega, chi_single]
  simp [phase, bilinear, paritySign]

private theorem twisted_translation (x : paritySpace D hu (-1)) :
    twistedAction D hu a s (translation D hu x) =
      translation D hu (twistedAction D hu a s x) := by
  apply Subtype.ext
  change insert D hu a s
      ((correctedField D hu (LatticeActualConformalState.omega D (actualInverse D))).coeff
        (-2) x.val) =
    (correctedField D hu (LatticeActualConformalState.omega D (actualInverse D))).coeff
      (-2) (insert D hu a s x.val)
  conv_rhs => rw [← chi_omega D a]
  simp only [insert_character, map_smul, correctedField_ground_character]

set_option maxHeartbeats 1200000 in
-- Unfolding the right coefficient compares the actual restricted mode maps.
private theorem right_character (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (n : ℤ) (u : paritySpace D hu (-1)) (v : FixedCarrier D) :
    twistedAction D hu a s (originalRightCoefficient D hu n u v) =
      originalRightCoefficient D hu n (twistedAction D hu a s u) (fixedAction D a v) := by
  have hinj : Function.Injective (twistedAction D hu a s) := by
    apply Function.Involutive.injective
    intro x
    exact congrArg Prod.snd (character_involutive D hu a s ha hs (0, x))
  have hp (j : ℕ) (x : paritySpace D hu (-1)) :
      twistedAction D hu a s ((translation D hu ^ j) x) =
        (translation D hu ^ j) (twistedAction D hu a s x) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, twisted_translation, ih, Module.End.mul_apply]
  let term (w : paritySpace D hu (-1)) (b : FixedCarrier D) (j : ℕ) :=
    ((-1 : ℂ) ^ (n + (j : ℤ) + 1) * (j.factorial : ℂ)⁻¹) •
      (translation D hu ^ j) (((fixedParitySlice D hu (-1) b)[[n + (j : ℤ)]]) w)
  change twistedAction D hu a s (∑ᶠ j, term u v j) =
    ∑ᶠ j, term (twistedAction D hu a s u) (fixedAction D a v) j
  calc
    _ = ∑ᶠ j, twistedAction D hu a s (term u v j) :=
      (twistedAction D hu a s).toAddMonoidHom.map_finsum_of_injective hinj (term u v)
    _ = _ := by
      apply finsum_congr
      intro j
      simp only [term, map_smul, hp, fixedSlice_character]

private theorem sourcePairing_character (x y : LatticeGeneratingFieldLocality.Carrier D) :
    sourcePairing D (chi D a x) (chi D a y) = sourcePairing D x y := by
  change sourcePairing D (chiLinear D a x) (chiLinear D a y) = _
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | single b p =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | single c q =>
      simp only [chi_single, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
        sourcePairing_single_single]
      split_ifs with h
      · subst c
        rw [← mul_assoc, show phase D a (-b) = phase D a b by
          simp [phase, bilinear_neg_right, paritySign, even_neg], phase, paritySign_square, one_mul]
      · simp

private theorem insert_form (hs : s ^ 2 = 1) (x y : ActualTensor D hu) :
    actualForm D hu (insert D hu a s x) (insert D hu a s y) = actualForm D hu x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul p u =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul q v =>
      simp only [actualGroundInsert, TensorProduct.map_tmul, LinearMap.id_apply, groundSign,
        LinearMap.smul_apply]
      let G := Classical.choice (InvariantPairing.actual_ground_pairing D hu)
      let B := SignedOscillatorWick.wick D
      change G.form ((-s) • groundAction D hu a u) ((-s) • groundAction D hu a v) * B p q =
        G.form u v * B p q
      rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
        ← mul_assoc, neg_mul_neg, ← pow_two, hs, one_mul]
      exact congrArg (· * B p q) (G.invariant (groundLift D a) u v)

private theorem insert_tensorL (m : ℤ) (x : ActualTensor D hu) :
    insert D hu a s (tensorL D (ActualGround D hu) (actualInverse D) m x) =
      tensorL D (ActualGround D hu) (actualInverse D) m (insert D hu a s x) := by
  have h : (insert D hu a s).comp (tensorL D (ActualGround D hu) (actualInverse D) m) =
      (tensorL D (ActualGround D hu) (actualInverse D) m).comp (insert D hu a s) := by
    apply TensorProduct.ext'
    intro p g
    simp only [LinearMap.comp_apply, actualGroundInsert, tensorL, tensorEnd,
      TensorProduct.map_tmul, LinearMap.id_apply]
  exact LinearMap.congr_fun h x

private theorem twisted_energy (H : ℕ) (u : paritySpace D hu (-1))
    (he : actualTensorL0 D hu u.val = (H : ℂ) • u.val) :
    actualTensorL0 D hu (twistedAction D hu a s u).val =
      (H : ℂ) • (twistedAction D hu a s u).val := by
  change actualTensorL0 D hu (insert D hu a s u.val) = (H : ℂ) • insert D hu a s u.val
  rw [actualTensorL0, ← insert_tensorL]
  change insert D hu a s (actualTensorL0 D hu u.val) = _
  rw [he, map_smul]

include hu in
private theorem grade_chi (d : ℤ) (u : fixedGrade D d) :
    chi D a u.val ∈ fixedGrade D d := by
  have he := actualL0_eigen_iff_grade D (actualInverse D) (actualInverse_left D hu)
    (actualInverse_right D hu) d
  refine ⟨(he _).mp ?_, (mem_fixedSpace D _).mpr ?_⟩
  · have hh := stateField_chi D a (LatticeActualConformalState.omega D (actualInverse D))
      u.val 1
    rw [chi_omega D a] at hh
    have hm := LatticeActualConformalState.omega_modes D (actualInverse D) 0
    change (LatticeAllStateField.Y D (LatticeActualConformalState.omega D (actualInverse D)))[[1]] =
      sugawaraMode D (actualInverse D) 0 at hm
    rw [hm, (he _).mpr u.property.1, map_smul] at hh
    exact hh.symm
  · rw [chi_theta, (mem_fixedSpace D _).mp u.property.2]

private def gradeAction (d : ℤ) (u : fixedGrade D d) : fixedGrade D d :=
  ⟨chi D a u.val, grade_chi D hu a d u⟩

private theorem gradeAction_twice (d : ℤ) (u : fixedGrade D d) :
    gradeAction D hu a d (gradeAction D hu a d u) = u := by
  apply Subtype.ext
  exact chi_involutive D a u.val

private theorem coefficient_character (h24 : D.rank = 24) (hs : s ^ 2 = 1) (H K : ℕ)
    (n d : ℤ) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) (b : fixedGrade D d) :
    normalizedCoefficient D hu n (twistedAction D hu a s u) (twistedAction D hu a s v)
      d (gradeAction D hu a d b) = normalizedCoefficient D hu n u v d b := by
  rw [normalizedCoefficient_pairing D hu h24 H K n (twistedAction D hu a s u)
      (twistedAction D hu a s v)
      (twisted_energy D hu a s H u huH) (twisted_energy D hu a s K v hvK) d
      (gradeAction D hu a d b),
    normalizedCoefficient_pairing D hu h24 H K n u v huH hvK d b]
  let L := tensorL D (ActualGround D hu) (actualInverse D) 1
  have hp (j : ℕ) (x : ActualTensor D hu) :
      (L ^ j) (insert D hu a s x) = insert D hu a s ((L ^ j) x) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, Module.End.mul_apply]
      exact (insert_tensorL D hu a s 1 _).symm
  have hc (e : ℤ) (x : ActualTensor D hu) :
      (correctedField D hu (chi D a b.val)).coeff e (insert D hu a s x) =
        insert D hu a s ((correctedField D hu b.val).coeff e x) := by
    simp only [insert_character, map_smul, correctedField_ground_character]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  change _ * actualForm D hu ((L ^ p) (insert D hu a s v.val))
      ((correctedField D hu (chi D a b.val)).coeff _ ((L ^ q) (insert D hu a s u.val))) =
    _ * actualForm D hu ((L ^ p) v.val) ((correctedField D hu b.val).coeff _ ((L ^ q) u.val))
  rw [hp, hp, hc, insert_form D hu a s hs]

private theorem inverse_pairing_character (d : ℤ)
    (E : fixedGrade D d ≃ₗ[ℂ] Module.Dual ℂ (fixedGrade D d))
    (eval : ∀ f b, sourcePairing D (E.symm f).val b.val = f b)
    (f g : Module.Dual ℂ (fixedGrade D d))
    (hfg : ∀ b, g (gradeAction D hu a d b) = f b) :
    gradeAction D hu a d (E.symm f) = E.symm g := by
  let z := gradeAction D hu a d (E.symm f)
  change z = E.symm g
  apply E.injective
  rw [E.apply_symm_apply]
  apply LinearMap.ext
  intro b
  have hz := eval (E z) b
  rw [E.symm_apply_apply] at hz
  rw [← hz, ← gradeAction_twice D hu a d b, hfg, ← eval]
  have hp := sourcePairing_character D a (E.symm f).val (gradeAction D hu a d b).val
  change sourcePairing D z.val (gradeAction D hu a d (gradeAction D hu a d b)).val =
    sourcePairing D (E.symm f).val (gradeAction D hu a d b).val at hp
  simpa only [gradeAction_twice] using hp

set_option maxHeartbeats 2800000 in
-- The original source-grade inverse elaborates through the fixed submodule.
private theorem originalI_character_homogeneous (h24 : D.rank = 24) (hs : s ^ 2 = 1)
    (n : ℤ) (H K : ℕ) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    fixedAction D a (originalI D hu hD n u v) =
      originalI D hu hD n (twistedAction D hu a s u) (twistedAction D hu a s v) := by
  rw [originalI_homogeneous D hu hD h24 H K n u v huH hvK,
    originalI_homogeneous D hu hD h24 H K n (twistedAction D hu a s u)
      (twistedAction D hu a s v)
      (twisted_energy D hu a s H u huH) (twisted_energy D hu a s K v hvK)]
  let d : ℤ := (H : ℤ) + (K : ℤ) - n - 1
  apply Subtype.ext
  change (gradeAction D hu a d _).val = (_ : fixedGrade D d).val
  exact congrArg Subtype.val (inverse_pairing_character D hu a d _
    (sourceGradePairingEquiv_evaluation D hu hD d) _ _
    (coefficient_character D hu a s h24 hs H K n d u v huH hvK))

set_option maxHeartbeats 1200000 in
-- The homogeneous test uses nested linear maps on two restricted carriers.
private theorem originalI_character (h24 : D.rank = 24) (hs : s ^ 2 = 1)
    (n : ℤ) (u v : paritySpace D hu (-1)) :
    fixedAction D a (originalI D hu hD n u v) =
      originalI D hu hD n (twistedAction D hu a s u) (twistedAction D hu a s v) := by
  by_cases hu0 : u = 0
  · simp [hu0]
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hu0
  let I := originalI D hu hD n
  let M := twistedAction D hu a s
  let B := I.compr₂ (fixedAction D a) - I.compl₁₂ M M
  -- Test the bilinear difference with a third slot detected by l.
  let F := B.compr₂ (((LinearMap.lsmul ℂ (FixedCarrier D)).comp l).flip)
  have h := input_trilinear_ext D hu h24 F (fun H K _ P Q R hP hQ hR x y z hx hy _ => by
    have he := originalI_character_homogeneous D hu a s hD h24 hs n H K
      (tensorInput D hu P hP.1 x) (tensorInput D hu Q hQ.1 y) hx hy
    change l (tensorInput D hu R hR.1 z) •
      (fixedAction D a (I (tensorInput D hu P hP.1 x) (tensorInput D hu Q hQ.1 y)) -
        I (M (tensorInput D hu P hP.1 x)) (M (tensorInput D hu Q hQ.1 y))) = 0
    rw [he, sub_self, smul_zero]) u v u
  change l u • (fixedAction D a (I u v) - I (M u) (M v)) = 0 at h
  rwa [hl, one_smul, sub_eq_zero] at h

set_option maxHeartbeats 1200000 in
-- Projecting the fixed-source identity compares the two restricted field modes.
/-- The signed norm-four character acts on every original state-field mode
for arbitrary inputs in both slots. -/
theorem Y_character (h24 : D.rank = 24) (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (n : ℤ) (u v : Carrier D hu) :
    symmetry D hu a s ha hs (((Y D hu hD u)[[n]]) v) =
      ((Y D hu hD (symmetry D hu a s ha hs u))[[n]]) (symmetry D hu a s ha hs v) := by
  change character D hu a s (((Y D hu hD u)[[n]]) v) =
    ((Y D hu hD (character D hu a s u))[[n]]) (character D hu a s v)
  have hfixed := Y_fixed_character D hu a s hD n u.1 v
  simp only [character_apply, map_zero, Y_fixed_ncoeff_apply] at hfixed
  simp only [Y_ncoeff_apply, character_apply, map_add]
  have hf := congrArg Prod.fst hfixed
  have ht := congrArg Prod.snd hfixed
  dsimp only at hf ht
  rw [hf, ht, right_character D hu a s ha hs,
    originalI_character D hu a s hD h24 hs]

#print axioms symmetry
#print axioms character_involutive
#print axioms Y_fixed_character
#print axioms originalI_character
#print axioms Y_character

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldNormFourCharacter

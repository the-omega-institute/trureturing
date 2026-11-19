/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumDetection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vacuum coefficients detect the full negative-pair Leech fusion space. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumFusion

/-! The original source BPZ identity and the finite mixed Ward identity
detect all rational coefficients of a negative-pair intertwiner. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumDetection

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeAllStateField (Y vacuum)
open LatticeInvolution (fixedMode fixedSpace fixedVacuum)
open LatticePositiveEnergy
open LatticeSugawaraConformal (translation)
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open SourceBPZ.OriginalSourcePairing
  (sourcePairing sourcePairing_nondegenerate sourcePairing_vacuum)
open SourceBPZ.OriginalSourceCoevaluation (gradeVacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade sourcePairing_theta)
open FixedGradedDuality
  (FixedGrade fixedGradeProjection fixedGradeNondegenerate)
open OriginalOrbifoldTwistedVacuumFusion
open OriginalOrbifoldSectorModules (fixedParityY)
open VacuumFirstIntertwinerDraft (mode)
open StateFieldResidueReconstruction (epsilon)
open private originalL1 original_l1_grade original_l1_fixed from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private original_negative_grade_zero from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private theta_projection from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
open private right_grade_projection_pairing from
  D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
open private sum_signed_choose_zero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion

local notation "D" => leechData
local notation "V" => FixedLeech
local notation "X" => NegativeTwisted
local notation "B" => sourcePairing leechData

private theorem hu : IsUnit leechData.G.det := leech_spec.2.1
private theorem hD : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1

/-- Pair with the normalized fixed vacuum in the original source form. -/
def vacuumFunctional : V →ₗ[ℂ] ℂ :=
  (LinearMap.BilinForm.flip B (fixedVacuum D).val).comp (fixedSpace D).subtype

private theorem gradePairing (d : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (w : V) :
    B (gradeProjection D d w.val) a = B w.val a :=
  right_grade_projection_pairing D B
    (fun m n x y hx hy hmn => sourcePairing_grade D m n hmn x y hx hy) d a ha w.val

/-- The scalar readout is the coefficient of the actual vacuum in grade zero. -/
theorem gradeProjection_zero_eq (w : V) :
    gradeProjection D 0 w.val = vacuumFunctional w • (fixedVacuum D).val := by
  have hp := gradeProjection_mem D 0 w.val
  rw [grade_zero D hD] at hp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hp
  have h := gradePairing 0 (vacuum D) (gradeVacuum D).property.1 w
  change B (gradeProjection D 0 w.val) (vacuum D) = vacuumFunctional w at h
  rw [← hc, LinearMap.BilinForm.smul_left, sourcePairing_vacuum, mul_one] at h
  exact hc.symm.trans (congrArg (· • (vacuum D)) h)

private theorem pairing_translation_pow (w : V)
    (h : ∀ (a : V) (m : ℤ), vacuumFunctional (fixedMode D a m w) = 0)
    (d : ℕ) (a : V) (ha : a.val ∈ grade D (d : ℤ)) (p : ℕ) :
    B w.val ((translation D ^ p) a.val) = 0 := by
  -- Keep the translation power arbitrary as every lower-weight term increases it.
  induction d using Nat.strong_induction_on generalizing a p with
  | h d ih =>
    classical
    let m : ℤ := 2 * (d : ℤ) + (p : ℤ) - 1
    let R := a.val.support.sup (fun α =>
      MvPolynomial.weightedTotalDegree (LatticeHalfFockFiniteCorrection.sourceWeight D)
        (a.val α))
    let term (j : ℕ) := (j.factorial : ℂ)⁻¹ *
      B w.val (((Y D ((originalL1 D ^ j) a.val))[[2 * (d : ℤ) - (j : ℤ) - m - 2]])
        (vacuum D))
    have term_eq (j : ℕ) : term j = (j.factorial : ℂ)⁻¹ * ((p + j).factorial : ℂ)⁻¹ *
        B w.val ((translation D ^ (p + j)) ((originalL1 D ^ j) a.val)) := by
      have idx : 2 * (d : ℤ) - (j : ℤ) - m - 2 = -((p + j : ℕ) : ℤ) - 1 := by
        dsimp [m]
        ring
      have hc := StateField.SkewSymmetry.creation_coeff
        (LatticeActualVertexAlgebra.actualVertexAlgebra D) ((originalL1 D ^ j) a.val) (p + j)
      change ((Y D ((originalL1 D ^ j) a.val))[[-((p + j : ℕ) : ℤ) - 1]]) (vacuum D) =
        ((p + j).factorial : ℂ)⁻¹ •
          (translation D ^ (p + j)) ((originalL1 D ^ j) a.val) at hc
      dsimp only [term]
      rw [idx, hc, LinearMap.BilinForm.smul_right, mul_assoc]
    have hz : 0 = (-1 : ℂ) ^ (d : ℤ) * ∑ j ∈ Finset.range (R + 1), term j := by
      have hbpz := sourcePairing_allState D hu (d : ℤ) m a.val ha w.val (vacuum D)
      change vacuumFunctional (fixedMode D a m w) = _ at hbpz
      rw [h a m] at hbpz
      exact hbpz
    have hsum : (∑ j ∈ Finset.range (R + 1), term j) = term 0 := by
      apply Finset.sum_eq_single 0
      · intro j _ hj
        have hjgrade := original_l1_grade D hu (d : ℤ) a.val ha j
        rw [term_eq]
        by_cases he : 0 ≤ (d : ℤ) - (j : ℤ)
        · let e := ((d : ℤ) - (j : ℤ)).toNat
          have hecast : (e : ℤ) = (d : ℤ) - (j : ℤ) := Int.toNat_of_nonneg he
          have hed : e < d := by omega
          let b : V := ⟨(originalL1 D ^ j) a.val,
            (LatticeInvolution.mem_fixedSpace D _).mpr
              (original_l1_fixed D hu a.val a.property j)⟩
          have hb : b.val ∈ grade D (e : ℤ) := by
            rw [hecast]
            exact hjgrade
          rw [ih e hed b hb (p + j), mul_zero]
        · rw [original_negative_grade_zero D hD _ _ hjgrade (by omega),
            map_zero, map_zero, mul_zero]
      · intro hn
        exact (hn (Finset.mem_range.mpr (Nat.zero_lt_succ R))).elim
    rw [hsum, term_eq] at hz
    simp only [add_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
      pow_zero, Module.End.one_apply] at hz
    have hfac : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz.symm).resolve_left
      (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))).resolve_left (inv_ne_zero hfac)

/-- Fixed-state modes followed by vacuum evaluation separate the fixed carrier. -/
theorem eq_zero_of_fixedMode_vacuum (w : V)
    (h : ∀ (a : V) (m : ℤ), vacuumFunctional (fixedMode D a m w) = 0) :
    w = 0 := by
  classical
  have hproj (d : ℤ) : gradeProjection D d w.val = 0 := by
    let x := fixedGradeProjection D (theta_projection D) d w
    have nd := fixedGradeNondegenerate D B (sourcePairing_nondegenerate D hu)
      (theta_projection D) (sourcePairing_theta D)
      (fun m n u v hm hn hmn => sourcePairing_grade D m n hmn u v hm hn) hD d
    have hx : x = 0 := nd.1 x (by
      intro a
      change B (gradeProjection D d w.val) a.val.val = 0
      rw [gradePairing d a.val.val a.property w]
      by_cases hd : 0 ≤ d
      · have ha : a.val.val ∈ grade D (d.toNat : ℤ) := by
          rw [Int.toNat_of_nonneg hd]
          exact a.property
        simpa only [pow_zero, Module.End.one_apply] using
          pairing_translation_pow w h d.toNat a.val ha 0
      · rw [original_negative_grade_zero D hD d a.val.val a.property (by omega), map_zero])
    exact congrArg (fun a : FixedGrade D d => a.val.val) hx
  apply Subtype.ext
  change w.val = 0
  rw [← sum_gradeProjections D w.val]
  exact Finset.sum_eq_zero fun d _ => hproj d

private theorem ward_vacuum (J : operatorSpace)
    (h : ∀ (u : X) (q : ℚ) (v : X), vacuumFunctional (mode J.val u q v) = 0)
    (a : V) (u v : X) (m : ℤ) (q : ℚ) :
    vacuumFunctional (fixedMode D a m (mode J.val u q v)) = 0 := by
  obtain ⟨hl, _, _, hj⟩ := J.property.jacobi a u v m 0 q
  simp only [firstTerm, secondTerm, sum_signed_choose_zero, epsilon, zpow_zero,
    one_smul, Nat.cast_zero, Int.cast_zero, add_zero, sub_zero] at hj
  have hleft : vacuumFunctional (∑ᶠ i, leftTerm J.val a u v m 0 q i) = 0 := by
    rw [map_finsum vacuumFunctional hl]
    simp only [leftTerm, map_smul, h, smul_zero, finsum_zero]
  have hrs := congrArg vacuumFunctional hj
  rw [hleft, map_sub, h, sub_zero] at hrs
  exact hrs.symm

/-- Vanishing of every rational vacuum coefficient forces the full lawful field to vanish. -/
theorem eq_zero_of_vacuumCoefficients (J : operatorSpace)
    (h : ∀ (u : X) (q : ℚ) (v : X), vacuumFunctional (mode J.val u q v) = 0) :
    J = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  have hz := eq_zero_of_fixedMode_vacuum (mode J.val u (-e - 1) v)
    (fun a m => ward_vacuum J h a u v m (-e - 1))
  rw [mode, show -(-e - 1) - 1 = e by ring] at hz
  simpa only [Submodule.coe_zero, LinearMap.zero_apply, map_zero, Pi.zero_apply] using hz

/-- The complete family of scalar vacuum coefficients on the full operator space. -/
def vacuumCoefficients : operatorSpace →ₗ[ℂ] (X → ℚ → X → ℂ) where
  toFun J u q v := vacuumFunctional (mode J.val u q v)
  map_add' J K := by
    funext u q v
    simp [mode]
  map_smul' c J := by
    funext u q v
    simp [mode]

/-- The complete vacuum coefficient family embeds the full operator space. -/
theorem vacuumCoefficients_injective : Function.Injective vacuumCoefficients := by
  apply (injective_iff_map_eq_zero vacuumCoefficients).mpr
  intro J hJ
  exact eq_zero_of_vacuumCoefficients J (fun u q v => congrFun (congrFun (congrFun hJ u) q) v)

#print axioms vacuumFunctional
#print axioms gradeProjection_zero_eq
#print axioms eq_zero_of_fixedMode_vacuum
#print axioms eq_zero_of_vacuumCoefficients
#print axioms vacuumCoefficients
#print axioms vacuumCoefficients_injective

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumDetection

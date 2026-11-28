/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeFusion/P48qOppositeVertex
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native BPZ opposite vertex series at rational physical exponents. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum

/-! Grade selection turns the BPZ evaluations into a rational Hahn series.
The algebraic energy decompositions extend it to both full inputs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

open scoped BigOperators DirectSum
open P48qFixedSourceBPZ (fixedGrade fixedGradeForm fixedGradeForm_nondegenerate)
open P48qFullEnergySpectrum (totalLZero_exact_eigenvalues)
open P48qNativeConformalSector (fixedStates sector fixedVacuum)
open P48qNativeGradingRotation (gradingRotation gradingRotation_coeff gradingRotation_cube)
open P48qNativeOppositeEvaluation (evaluation evaluation_pairing evaluation_eq_zero_of_grade_ne
  evaluation_sourcePairing evaluation_ground_vacuum evaluation_ground_ne_zero)
open P48qNativeOppositeVacuum (exponent invertedCoeff ground groundFunctional)
open P48qNativeRestrictedDualField (ActualGrade GradeDual RestrictedDual stateDecompose)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero totalLZero_coeff totalLZero_vacuum)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open private fixedGradeInclusion fixedGrade_eq_zero_of_lt evaluation_pairing_fixed from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
open private inversionTerm rightInsertionEval_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private def energy (h : ℤ) : ℝ := (h : ℝ) / 9

private theorem energy_complex (h : ℤ) : ((energy h : ℝ) : ℂ) = (h : ℂ) / 9 := by
  simp only [energy, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]

private theorem energy_injective : Function.Injective energy := by
  intro a b hab
  have he : (a : ℝ) = (b : ℝ) := by
    dsimp only [energy] at hab
    linarith only [hab]
  exact_mod_cast he

private theorem exists_energy_of_ne_zero {w : ℝ} (v : ActualGrade w) (hv : v ≠ 0) :
    ∃ h : ℤ, energy h = w := by
  obtain ⟨n, hn⟩ := (totalLZero_exact_eigenvalues (w : ℂ)).mp
    ⟨v.val, fun hz => hv (Subtype.ext hz), Module.End.mem_eigenspace_iff.mp v.property⟩
  refine ⟨16 + 3 * (n : ℤ), Complex.ofReal_injective ?_⟩
  rw [energy_complex, hn]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
-- Pairing extensionality expands the finite inversion sum in each argument.
private def evaluationBilinear (s : Fin 3) (h : ℤ) (w : ℝ) (k d : ℤ) :
    sector s →ₗ[ℂ] GradeDual w →ₗ[ℂ] fixedGrade d where
  toFun u :=
    { toFun := fun f => evaluation s h (w : ℂ) u f k d
      map_add' f g := by
        apply sub_eq_zero.mp
        apply (fixedGradeForm_nondegenerate d).1
        intro a
        simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, evaluation_pairing,
          invertedCoeff, inversionTerm, Finset.sum_add_distrib, mul_add, sub_self]
      map_smul' c f := by
        apply sub_eq_zero.mp
        apply (fixedGradeForm_nondegenerate d).1
        intro a
        simp only [RingHom.id_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          evaluation_pairing, invertedCoeff, inversionTerm, smul_eq_mul, Finset.mul_sum,
          mul_left_comm, sub_self] }
  map_add' u v := by
    apply LinearMap.ext
    intro f
    apply sub_eq_zero.mp
    apply (fixedGradeForm_nondegenerate d).1
    intro a
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, map_sub,
      LinearMap.sub_apply, evaluation_pairing, invertedCoeff, inversionTerm,
      ← rightInsertionEval_apply, Finset.sum_add_distrib, mul_add, sub_self]
  map_smul' c u := by
    apply LinearMap.ext
    intro f
    apply sub_eq_zero.mp
    apply (fixedGradeForm_nondegenerate d).1
    intro a
    simp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      map_sub, map_smul, LinearMap.sub_apply, evaluation_pairing, invertedCoeff, inversionTerm,
      ← rightInsertionEval_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm, sub_self]

private theorem exponent_injective (h : ℤ) : Function.Injective (exponent h) := by
  intro k l hkl
  have he : (k : ℚ) = (l : ℚ) := by
    dsimp only [exponent] at hkl
    linarith only [hkl]
  exact_mod_cast he

private theorem grade_unique {h k d e : ℤ} {w : ℝ}
    (hd : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ))
    (he : (w : ℂ) = (h : ℂ) / 9 + (e : ℂ) - (k : ℂ)) : d = e := by
  have hde : (d : ℂ) = (e : ℂ) := by linear_combination he - hd
  exact_mod_cast hde

open Classical in
private def gradeCoefficient (s : Fin 3) (h : ℤ) (w : ℝ) (x : ℚ) :
    sector s →ₗ[ℂ] GradeDual w →ₗ[ℂ] fixedStates :=
  if hk : ∃ k : ℤ, exponent h k = x then
    if hd : ∃ d : ℤ, (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (hk.choose : ℂ) then
      (evaluationBilinear s h w hk.choose hd.choose).compr₂ (fixedGradeInclusion hd.choose)
    else 0
  else 0

private theorem gradeCoefficient_of_grade (s : Fin 3) (h : ℤ) (w : ℝ) (u : sector s)
    (f : GradeDual w) (k d : ℤ)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)) :
    gradeCoefficient s h w (exponent h k) u f =
      fixedGradeInclusion d (evaluation s h (w : ℂ) u f k d) := by
  let hk : ∃ l : ℤ, exponent h l = exponent h k := ⟨k, rfl⟩
  have hIndex : hk.choose = k := exponent_injective h hk.choose_spec
  have hd : ∃ e : ℤ, (w : ℂ) = (h : ℂ) / 9 + (e : ℂ) - (hk.choose : ℂ) :=
    ⟨d, by rw [hIndex, hw]⟩
  have hGrade : hd.choose = d := grade_unique hd.choose_spec (by rwa [hIndex])
  rw [gradeCoefficient, dite_eq_left hk, dite_eq_left hd]
  exact congrArg₂ (fun i j => fixedGradeInclusion j (evaluation s h (w : ℂ) u f i j))
    hIndex hGrade

private theorem gradeCoefficient_eq_zero_of_no_grade (s : Fin 3) (h : ℤ) (w : ℝ)
    (x : ℚ) (hn : ¬ ∃ k d : ℤ, exponent h k = x ∧
      (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)) :
    gradeCoefficient s h w x = 0 := by
  unfold gradeCoefficient
  split
  · rename_i hk
    rw [dite_eq_right (fun hd => hn ⟨hk.choose, hd.choose, hk.choose_spec, hd.choose_spec⟩)]
  · rfl

private theorem gradeCoefficient_support (s : Fin 3) (h b : ℤ) (w : ℝ) (hb : energy b = w)
    (u : sector s) (f : GradeDual w) :
    Function.support (fun x => gradeCoefficient s h w x u f) ⊆
      Set.range (fun n : ℕ => (n : ℚ) - (b : ℚ) / 9 - (h : ℚ) / 9) := by
  intro x hx
  have hkd : ∃ k d : ℤ, exponent h k = x ∧
      (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ) := by
    by_contra hn
    exact hx (by simp only [gradeCoefficient_eq_zero_of_no_grade s h w x hn, LinearMap.zero_apply])
  obtain ⟨k, d, rfl, hw⟩ := hkd
  have hd : 0 ≤ d := by
    by_contra! hd
    apply hx
    change gradeCoefficient s h w (exponent h k) u f = 0
    rw [gradeCoefficient_of_grade s h w u f k d hw,
      fixedGrade_eq_zero_of_lt hd (evaluation s h (w : ℂ) u f k d), map_zero]
  have he : (b : ℂ) / 9 = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ) := by
    rwa [← hb, energy_complex] at hw
  refine ⟨d.toNat, ?_⟩
  change (d.toNat : ℚ) - (b : ℚ) / 9 - (h : ℚ) / 9 = exponent h k
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hd]
  apply (Rat.cast_injective (α := ℂ))
  simp only [exponent, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_intCast, Rat.cast_ofNat]
  linear_combination -he

private theorem gradeCoefficient_isPWO (s : Fin 3) (h : ℤ) (w : ℝ)
    (u : sector s) (f : GradeDual w) :
    (Function.support (fun x => gradeCoefficient s h w x u f)).IsPWO := by
  by_cases hf : f = 0
  · apply Set.isPWO_empty.mono
    intro x hx
    exact hx (by simp only [hf, map_zero])
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra! hz
    exact hf (LinearMap.ext fun v => (hz v).trans (LinearMap.zero_apply v).symm)
  obtain ⟨b, hb⟩ := exists_energy_of_ne_zero v (fun hz => hv (by rw [hz, map_zero]))
  have hmono : Monotone (fun n : ℕ => (n : ℚ) - (b : ℚ) / 9 - (h : ℚ) / 9) :=
    fun _ _ hnm => sub_le_sub_right (sub_le_sub_right (by exact_mod_cast hnm) _) _
  have hRange := (Set.isPWO_of_wellQuasiOrderedLE (Set.univ : Set ℕ)).image_of_monotone hmono
  rw [Set.image_univ] at hRange
  exact hRange.mono (gradeCoefficient_support s h b w hb u f)

private def gradeVertex (s : Fin 3) (h : ℤ) (w : ℝ) :
    sector s →ₗ[ℂ] HVertexOperator ℚ ℂ (GradeDual w) fixedStates where
  toFun u := HVertexOperator.of_coeff (fun x => gradeCoefficient s h w x u)
    (gradeCoefficient_isPWO s h w u)
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext x
    change gradeCoefficient s h w x (u + v) = C (_ + _) x
    rw [map_add, map_add, Pi.add_apply]
    rfl
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext x
    change gradeCoefficient s h w x (c • u) = C (_ • _) x
    rw [map_smul, map_smul, Pi.smul_apply]
    rfl

private def weightVertex (s : Fin 3) (h : ℤ) :
    sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates :=
  (DirectSum.toModule ℂ ℝ (sector s →ₗ[ℂ] HahnModule ℚ ℂ fixedStates)
    (fun w => (gradeVertex s h w).flip)).flip

private theorem weightVertex_coeff_lof (s : Fin 3) (h : ℤ) (u : sector s) (w : ℝ)
    (f : GradeDual w) (x : ℚ) :
    C (weightVertex s h u) x (DirectSum.lof ℂ ℝ GradeDual w f) =
      gradeCoefficient s h w x u f := by
  change ((HahnModule.of ℂ).symm
    (DirectSum.toModule ℂ ℝ _ (fun w => (gradeVertex s h w).flip)
      (DirectSum.lof ℂ ℝ GradeDual w f) u)).coeff x = _
  rw [DirectSum.toModule_lof]
  rfl

private def normalizedRotation (s : Fin 3) : Module.End ℂ State :=
  (ζ ^ s.val)⁻¹ • gradingRotation

private theorem rotationPhase_ne_zero (s : Fin 3) : ζ ^ s.val ≠ 0 :=
  pow_ne_zero _ (IsPrimitiveRoot.ne_zero
    (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive) (by decide))

private theorem normalizedRotation_cube (s : Fin 3) : normalizedRotation s ^ 3 = 1 := by
  have hz : ζ ^ (3 : ℕ) = 1 :=
    (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive).pow_eq_one
  rw [normalizedRotation, smul_pow, gradingRotation_cube, inv_pow, pow_right_comm ζ, hz, one_pow,
    inv_one, one_smul]

private def sectorAverage (s : Fin 3) : Module.End ℂ State :=
  (3 : ℂ)⁻¹ • (1 + normalizedRotation s + normalizedRotation s ^ 2)

private theorem average_mem_sector (s : Fin 3) (v : State) : sectorAverage s v ∈ sector s := by
  let R := normalizedRotation s
  have hR : R * sectorAverage s = sectorAverage s := by
    change R * ((3 : ℂ)⁻¹ • (1 + R + R ^ 2)) = (3 : ℂ)⁻¹ • (1 + R + R ^ 2)
    rw [mul_smul_comm, mul_add, mul_add, mul_one, ← pow_two, ← pow_succ',
      normalizedRotation_cube s]
    ac_rfl
  have hv := LinearMap.congr_fun hR v
  change (ζ ^ s.val)⁻¹ • gradingRotation (sectorAverage s v) = sectorAverage s v at hv
  apply Module.End.mem_eigenspace_iff.mpr
  calc
    gradingRotation (sectorAverage s v) =
        ζ ^ s.val • ((ζ ^ s.val)⁻¹ • gradingRotation (sectorAverage s v)) := by
      rw [smul_smul, mul_inv_cancel₀ (rotationPhase_ne_zero s), one_smul]
    _ = _ := by rw [hv]

private theorem average_of_sector (s : Fin 3) (v : sector s) : sectorAverage s v.val = v.val := by
  let R := normalizedRotation s
  have hv : gradingRotation v.val = (ζ ^ s.val) • v.val :=
    Module.End.mem_eigenspace_iff.mp v.property
  have hR : R v.val = v.val := by
    change (ζ ^ s.val)⁻¹ • gradingRotation v.val = v.val
    rw [hv, smul_smul, inv_mul_cancel₀ (rotationPhase_ne_zero s), one_smul]
  change (3 : ℂ)⁻¹ • (v.val + R v.val + (R ^ 2) v.val) = v.val
  rw [pow_two, Module.End.mul_apply, hR, hR]
  have hp : v.val + v.val + v.val = (3 : ℂ) • v.val := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  rw [hp, smul_smul]
  norm_num

private theorem rotation_commutes_energy (v : State) :
    totalLZero (gradingRotation v) = gradingRotation (totalLZero v) := by
  apply Finsupp.ext
  intro p
  apply MvPolynomial.ext
  intro d
  rw [totalLZero_coeff, gradingRotation_coeff, gradingRotation_coeff, totalLZero_coeff]
  ring

private theorem average_preserves_energy (s : Fin 3) (w : ℝ) (v : ActualGrade w) :
    sectorAverage s v.val ∈ totalLZero.eigenspace (w : ℂ) := by
  let R := normalizedRotation s
  have hR (x : State) (hx : x ∈ totalLZero.eigenspace (w : ℂ)) :
      R x ∈ totalLZero.eigenspace (w : ℂ) := by
    have hg : gradingRotation x ∈ totalLZero.eigenspace (w : ℂ) := by
      apply Module.End.mem_eigenspace_iff.mpr
      rw [rotation_commutes_energy, Module.End.mem_eigenspace_iff.mp hx, map_smul]
    exact Submodule.smul_mem _ _ hg
  change (3 : ℂ)⁻¹ • (v.val + R v.val + (R ^ 2) v.val) ∈ totalLZero.eigenspace (w : ℂ)
  rw [pow_two, Module.End.mul_apply]
  exact Submodule.smul_mem _ _
    (Submodule.add_mem _ (Submodule.add_mem _ v.property (hR _ v.property))
      (hR _ (hR _ v.property)))

private def sectorProjection (s : Fin 3) : State →ₗ[ℂ] sector s :=
  (sectorAverage s).codRestrict (sector s) (average_mem_sector s)

open Classical in
private def vertexOnGrade (s : Fin 3) (w : ℝ) :
    ActualGrade w →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates :=
  if hw : ∃ h : ℤ, energy h = w then
    (weightVertex s hw.choose).comp
      ((sectorProjection s).comp (totalLZero.eigenspace (w : ℂ)).subtype)
  else 0

private theorem vertexOnGrade_at_energy (s : Fin 3) (h : ℤ) (v : ActualGrade (energy h)) :
    vertexOnGrade s (energy h) v = weightVertex s h (sectorProjection s v.val) := by
  let hh : ∃ a : ℤ, energy a = energy h := ⟨h, rfl⟩
  rw [vertexOnGrade, dite_eq_left hh, energy_injective hh.choose_spec]
  rfl

/-- The BPZ opposite vertex series from a native twisted sector and the full
actual restricted dual to the fixed source, in the physical coordinate. -/
def oppositeVertex (s : Fin 3) :
    sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates :=
  (DirectSum.toModule ℂ ℝ _ (vertexOnGrade s)).comp
    (stateDecompose.toLinearMap.comp (sector s).subtype)

/-- Every twisted input is a finite sum of genuine homogeneous sector inputs
at energies h/9. The components are obtained from the actual energy decomposition. -/
theorem sector_homogeneous_span (s : Fin 3) :
    Submodule.span ℂ {u : sector s | ∃ h : ℤ, totalLZero u.val = ((h : ℂ) / 9) • u.val} = ⊤ := by
  classical
  apply top_unique
  intro u _
  let assemble := DirectSum.coeLinearMap (fun w : ℝ => totalLZero.eigenspace (w : ℂ))
  let pieces := stateDecompose u.val
  have hAssemble : assemble pieces = u.val := stateDecompose.symm_apply_apply u.val
  have hSelf : sectorProjection s u.val = u := Subtype.ext (average_of_sector s u)
  have hsum : (∑ w ∈ pieces.support, sectorProjection s (pieces w).val) = u := by
    have hPieces : (∑ w ∈ pieces.support, DirectSum.lof ℂ ℝ ActualGrade w (pieces w)) = pieces :=
      DirectSum.sum_support_of pieces
    have h := congrArg (fun p => sectorProjection s (assemble p)) hPieces
    change sectorProjection s (assemble (∑ w ∈ pieces.support,
      DirectSum.lof ℂ ℝ ActualGrade w (pieces w))) = sectorProjection s (assemble pieces) at h
    rw [hAssemble, hSelf] at h
    simpa only [map_sum, assemble, DirectSum.coeLinearMap_lof] using h
  rw [← hsum]
  apply Submodule.sum_mem
  intro w hw
  have hv : pieces w ≠ 0 := DFinsupp.mem_support_iff.mp hw
  obtain ⟨h, hh⟩ := exists_energy_of_ne_zero (pieces w) hv
  apply Submodule.subset_span
  refine ⟨h, ?_⟩
  change totalLZero (sectorAverage s (pieces w).val) =
    ((h : ℂ) / 9) • sectorAverage s (pieces w).val
  have he := Module.End.mem_eigenspace_iff.mp (average_preserves_energy s w (pieces w))
  have hcast : (w : ℂ) = (h : ℂ) / 9 :=
    (congrArg (fun t : ℝ => (t : ℂ)) hh.symm).trans (energy_complex h)
  exact he.trans (congrArg (· • sectorAverage s (pieces w).val) hcast)

private theorem oppositeVertex_of_homogeneous (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) :
    oppositeVertex s u = weightVertex s h u := by
  let v : ActualGrade (energy h) := ⟨u.val, Module.End.mem_eigenspace_iff.mpr (by
    rw [energy_complex]
    exact hu)⟩
  have hDecompose : stateDecompose u.val = DirectSum.lof ℂ ℝ ActualGrade (energy h) v := by
    apply stateDecompose.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change u.val =
      DirectSum.coeLinearMap (fun w : ℝ => totalLZero.eigenspace (w : ℂ))
        (DirectSum.lof ℂ ℝ ActualGrade (energy h) v)
    rw [DirectSum.coeLinearMap_lof]
  have hProjection : sectorProjection s v.val = u := Subtype.ext (average_of_sector s u)
  change DirectSum.toModule ℂ ℝ _ (vertexOnGrade s) (stateDecompose u.val) = _
  rw [hDecompose, DirectSum.toModule_lof, vertexOnGrade_at_energy, hProjection]

/-- At a physical exponent, the full operator recovers the actual evaluation
in the selected output grade. -/
theorem oppositeVertex_coeff_of_grade (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (f : GradeDual w) (k d : ℤ)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)) :
    C (oppositeVertex s u) (exponent h k) (DirectSum.lof ℂ ℝ GradeDual w f) =
      fixedGradeInclusion d (evaluation s h (w : ℂ) u f k d) := by
  rw [oppositeVertex_of_homogeneous s h u hu, weightVertex_coeff_lof,
    gradeCoefficient_of_grade s h w u f k d hw]

/-- If either the physical exponent or the output grade fails the selection
rule, the homogeneous coefficient vanishes. -/
theorem oppositeVertex_coeff_eq_zero_of_no_grade (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (f : GradeDual w) (x : ℚ)
    (hn : ¬ ∃ k d : ℤ, exponent h k = x ∧
      (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)) :
    C (oppositeVertex s u) x (DirectSum.lof ℂ ℝ GradeDual w f) = 0 := by
  rw [oppositeVertex_of_homogeneous s h u hu, weightVertex_coeff_lof,
    gradeCoefficient_eq_zero_of_no_grade s h w x hn, LinearMap.zero_apply, LinearMap.zero_apply]

/-- Every fixed test state reads the explicit finite inverted coefficient
through the native BPZ pairing at the physical exponent. -/
theorem oppositeVertex_coeff_pairing (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (f : GradeDual w) (k d : ℤ)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)) (a : fixedStates) :
    sourcePairing lattice
      (C (oppositeVertex s u) (exponent h k) (DirectSum.lof ℂ ℝ GradeDual w f)).val a.val =
        invertedCoeff s h (w : ℂ) u f a k := by
  rw [oppositeVertex_coeff_of_grade s h u hu w f k d hw]
  exact evaluation_pairing_fixed s h (w : ℂ) u hu f k d hw a

/-- Every homogeneous fixed test reads its evaluation grade, including when
the grade test forces that evaluation to vanish. -/
theorem oppositeVertex_coeff_pairing_on_grade (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (f : GradeDual w) (k d : ℤ)
    (a : fixedGrade d) :
    sourcePairing lattice
      (C (oppositeVertex s u) (exponent h k) (DirectSum.lof ℂ ℝ GradeDual w f)).val a.val =
        invertedCoeff s h (w : ℂ) u f (fixedGradeInclusion d a) k := by
  by_cases hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)
  · exact oppositeVertex_coeff_pairing s h u hu w f k d hw (fixedGradeInclusion d a)
  have hz := evaluation_eq_zero_of_grade_ne s h (w : ℂ) u hu f k d hw
  have hp := evaluation_pairing s h (w : ℂ) u f k d a
  change _ = invertedCoeff s h (w : ℂ) u f (fixedGradeInclusion d a) k at hp
  rw [← hp, hz, map_zero, LinearMap.zero_apply]
  by_cases he : ∃ e : ℤ, (w : ℂ) = (h : ℂ) / 9 + (e : ℂ) - (k : ℂ)
  · obtain ⟨e, he⟩ := he
    have hne : e ≠ d := fun hd => hw (hd ▸ he)
    rw [oppositeVertex_coeff_of_grade s h u hu w f k e he]
    change sourcePairing lattice (evaluation s h (w : ℂ) u f k e).val a.val = 0
    rw [evaluation_sourcePairing, ite_eq_right hne]
  · have hn : ¬ ∃ l e : ℤ, exponent h l = exponent h k ∧
        (w : ℂ) = (h : ℂ) / 9 + (e : ℂ) - (l : ℂ) := by
      rintro ⟨l, e, hl, he'⟩
      exact he ⟨e, exponent_injective h hl ▸ he'⟩
    rw [oppositeVertex_coeff_eq_zero_of_no_grade s h u hu w f (exponent h k) hn]
    simp only [Submodule.coe_zero, map_zero, LinearMap.zero_apply]

/-- The physical support of a homogeneous pair with dual energy b/9
is contained in the translate of the nonnegative integers by -(h+b)/9. -/
theorem oppositeVertex_homogeneous_support (s : Fin 3) (h b : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (hb : w = (b : ℝ) / 9)
    (f : GradeDual w) :
    Function.support (fun x => C (oppositeVertex s u) x (DirectSum.lof ℂ ℝ GradeDual w f)) ⊆
      Set.range (fun n : ℕ => (n : ℚ) - (b : ℚ) / 9 - (h : ℚ) / 9) := by
  simp only [oppositeVertex_of_homogeneous s h u hu, weightVertex_coeff_lof]
  exact gradeCoefficient_support s h b w hb.symm u f

/-- The ground functional in the real grading used by the restricted dual. -/
def groundDual : GradeDual (16 / 9 : ℝ) :=
  ((MvPolynomial.lcoeff ℂ 0).comp (Finsupp.lapply 0)).comp
    (totalLZero.eigenspace ((16 / 9 : ℝ) : ℂ)).subtype

/-- In the ground/ground channel the coefficient of z^(-32/9) is the
actual fixed vacuum with its BPZ phase, and is nonzero. -/
theorem oppositeVertex_ground_vacuum :
    let coefficient := C (oppositeVertex 0 ground) (-32 / 9)
      (DirectSum.lof ℂ ℝ GradeDual (16 / 9) groundDual)
    coefficient = Complex.exp (16 * (Real.pi : ℂ) * Complex.I / 9) • fixedVacuum ∧
      coefficient ≠ 0 := by
  have hu : totalLZero ground.val = (((16 : ℤ) : ℂ) / 9) • ground.val := by
    simpa only [ground, Int.cast_ofNat] using totalLZero_vacuum
  have hCast : ((16 / 9 : ℝ) : ℂ) = 16 / 9 := by norm_num
  have hw : ((16 / 9 : ℝ) : ℂ) = ((16 : ℤ) : ℂ) / 9 + ((0 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) := by
    norm_num
  have hc : (-32 / 9 : ℚ) = exponent 16 0 := by norm_num [exponent]
  let dualAt (w : ℂ) : Module.Dual ℂ (totalLZero.eigenspace w) :=
    ((MvPolynomial.lcoeff ℂ 0).comp (Finsupp.lapply 0)).comp (totalLZero.eigenspace w).subtype
  have hEval : evaluation 0 16 ((16 / 9 : ℝ) : ℂ) ground groundDual 0 0 =
      evaluation 0 16 (16 / 9) ground groundFunctional 0 0 :=
    congrArg (fun w => evaluation 0 16 w ground (dualAt w) 0 0) hCast
  dsimp only
  rw [hc, oppositeVertex_coeff_of_grade 0 16 ground hu (16 / 9) groundDual 0 0 hw, hEval]
  constructor
  · exact Subtype.ext evaluation_ground_vacuum
  · intro hz
    apply evaluation_ground_ne_zero
    apply Submodule.inclusion_injective inf_le_left
    exact hz.trans (map_zero (fixedGradeInclusion 0)).symm

#print axioms oppositeVertex
#print axioms sector_homogeneous_span
#print axioms oppositeVertex_coeff_of_grade
#print axioms oppositeVertex_coeff_eq_zero_of_no_grade
#print axioms oppositeVertex_coeff_pairing
#print axioms oppositeVertex_coeff_pairing_on_grade
#print axioms oppositeVertex_homogeneous_support
#print axioms oppositeVertex_ground_vacuum
#print axioms P48qNativeOppositeEvaluation.evaluation_mixedJacobi

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8GroundTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8GroundTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: The quaternion intertwiners on the rank-128 ground have normalized trace product 2^32. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Rank128Lattice
import D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.WeylIntertwinerTraceProduct
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.WeylCovariantOperator
import Batteries.Tactic.OpenPrivate

/-!
# Normalized quaternion trace on the rank-128 Barnes–Wall ground

The two published lift phases give covariant operators on the reflection-quotient
ground space of the rank-128 lattice in arXiv:2411.13646v2.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Q8GroundTrace

open LatticeTwistedGroundRealization (Ground sign_zero sign_one)
open LatticeTwistedGroundRealization.SignQuotient
open OperatorAlgebra (chargeLift chargeOperator)
open Q8TraceSign (Word Index Charge CommonImage actionI actionJ phaseI phaseJ displacement
  actual_preimages displacement_images preimageI preimageJ defectGroundExponent
  defect_ground_gauss_sum label halfGram generatorRow correction displacementRow)
open Rank128Lattice (latticeData gram gram_det modTwoCocycle_eq_halfGram actual_rank128_ground)
open scoped BigOperators

open private evenWord flip indexOf label_indexOf H commonImageEquiv addBasis
  rowsLinear rowsLinear_single liftForm pairRows pairRows_apply x₁ z₁ x₂ z₂
  from D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Q8TraceSign
open private reduced_lift from D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra

noncomputable section

local notation "W" => LinearMap.range displacement
local notation "tr" => LinearMap.trace ℂ (Ground 64)

private abbrev basisVector (u : Word) : Charge := Pi.single u 1

private theorem binary_cases : ∀ s : F₂, s = 0 ∨ s = 1 := by
  decide +kernel

private theorem label_even : ∀ t : Index, evenWord (label t) := by
  decide +kernel

private theorem displacement_single (t : Index) :
    displacement (Pi.single t 1) = basisVector (label t) := by
  simp [displacement, displacementRow, rowsLinear_single, addBasis, basisVector]

private theorem even_single_mem (u : Word) (hu : evenWord u) : basisVector u ∈ W := by
  exact ⟨Pi.single (indexOf u) 1, by rw [displacement_single, label_indexOf u hu]⟩

private theorem mem_displacement_iff (w : Charge) :
    w ∈ W ↔ ∀ u : Word, ¬ evenWord u → w u = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ u hu
    change (∑ t, x t • addBasis (displacementRow t)) u = 0
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro t _
    have hne : label t ≠ u := fun h => hu (h ▸ label_even t)
    simp [displacementRow, addBasis, Ne.symm hne]
  · intro hw
    have hexpand : (∑ u : Word, w u • basisVector u) = w := by
      simpa only [Pi.basisFun_apply, Pi.basisFun_repr, basisVector] using
        (Pi.basisFun F₂ Word).sum_repr w
    rw [← hexpand]
    apply Submodule.sum_mem
    intro u _
    by_cases hu : evenWord u
    · exact Submodule.smul_mem _ _ (even_single_mem u hu)
    · rw [hw u hu, zero_smul]
      exact Submodule.zero_mem _

private theorem generator_row_of_even (mask : ℕ) (isSign : Bool) {u : Word}
    (hu : evenWord u) : generatorRow mask isSign u = [u] := by
  have he : evenWord u = true := hu
  simp [generatorRow, he]

private theorem generator_fixes_displacement (mask : ℕ) (isSign : Bool) :
    (rowsLinear (generatorRow mask isSign)).comp displacement = displacement := by
  apply (Pi.basisFun F₂ Index).ext
  intro t
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, displacement_single, basisVector,
    rowsLinear_single, generator_row_of_even mask isSign (label_even t),
    addBasis, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

private theorem lift_form_zero_on_displacement (mask : ℕ) (isSign : Bool) :
    (liftForm (generatorRow mask isSign)).comp displacement displacement = 0 := by
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun F₂ Index)
  intro u v
  simp only [Pi.basisFun_apply, LinearMap.BilinForm.comp_apply, displacement_single,
    basisVector, liftForm, Matrix.toBilin'_single, Matrix.of_apply, LinearMap.zero_apply]
  simp [correction, generator_row_of_even mask isSign (label_even u),
    generator_row_of_even mask isSign (label_even v), pairRows, CharTwo.add_self_eq_zero]

private theorem fixed_and_phase_zero (w : Charge) (hw : w ∈ W) :
    (actionI w = w ∧ phaseI w = 0) ∧ (actionJ w = w ∧ phaseJ w = 0) := by
  rcases hw with ⟨x, rfl⟩
  have fix (mask : ℕ) (isSign : Bool) :
      rowsLinear (generatorRow mask isSign) (displacement x) = displacement x :=
    LinearMap.congr_fun (generator_fixes_displacement mask isSign) x
  have phase (mask : ℕ) (isSign : Bool) :
      liftForm (generatorRow mask isSign) (displacement x) (displacement x) = 0 := by
    simpa only [LinearMap.BilinForm.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun (LinearMap.congr_fun (lift_form_zero_on_displacement mask isSign) x) x
  simp [actionI, actionJ, phaseI, phaseJ, x₁, z₁, x₂, z₂, fix, phase]

private theorem displacement_ker (g : Charge →ₗ[F₂] Charge)
    (himage : LinearMap.range (g + LinearMap.id) = W) (hfix : ∀ w ∈ W, g w = w) :
    LinearMap.ker (g + LinearMap.id) = W := by
  have hle : W ≤ LinearMap.ker (g + LinearMap.id) := by
    intro w hw
    exact LinearMap.mem_ker.mpr (by
      change g w + w = 0
      rw [hfix w hw]
      ext t
      exact CharTwo.add_self_eq_zero _)
  have hW : Module.finrank F₂ W = 64 := by
    rw [← (LinearEquiv.ofInjective displacement Q8TraceSign.displacement_injective).finrank_eq,
      Module.finrank_pi, Fintype.card_fin]
  have hdim : Module.finrank F₂ Charge = 128 := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have h := (g + LinearMap.id).finrank_range_add_finrank_ker
  rw [himage, hW, hdim] at h
  have hr : Module.finrank F₂ ↥(LinearMap.ker (g + LinearMap.id)) =
      Module.finrank F₂ W := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hr.symm).symm

set_option maxHeartbeats 0 in
-- Evaluate the finite half-Gram table one row at a time.
private theorem halfGram_even_even : ∀ u v : Word, evenWord u → evenWord v →
    halfGram u v = 0 := by
  intro u
  fin_cases u <;> decide +kernel

private theorem displacement_isotropic : ∀ u ∈ W, ∀ v ∈ W, H u v = 0 := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  have hz : H.comp displacement displacement = 0 := by
    apply LinearMap.BilinForm.ext_basis (Pi.basisFun F₂ Index)
    intro i j
    simp only [Pi.basisFun_apply, LinearMap.BilinForm.comp_apply, displacement_single,
      basisVector, Matrix.toBilin'_single, Matrix.of_apply, LinearMap.zero_apply]
    exact halfGram_even_even _ _ (label_even i) (label_even j)
  exact LinearMap.congr_fun (LinearMap.congr_fun hz u) v

private def generatorDifference (mask : ℕ) (isSign : Bool) (u v : Word) : F₂ :=
  let g := generatorRow mask isSign
  halfGram u v + pairRows halfGram (g u) (g v)

set_option maxHeartbeats 0 in
-- Normalize the four Pauli corrections on pairs of basis vectors.
private theorem generator_correction_check : ∀ u v : Word,
    ∀ mask : Fin 2, ∀ isSign : Bool,
    let bit := if mask = 0 then 64 else 32
    let g := generatorRow bit isSign
    correction g u v + correction g v u = generatorDifference bit isSign u v := by
  intro u
  fin_cases u <;> decide +kernel

private theorem generator_correction_symm (mask : Fin 2) (isSign : Bool) :
    let bit := if mask = 0 then 64 else 32
    let g := generatorRow bit isSign
    let G := rowsLinear g
    (liftForm g) + (liftForm g).flip = H + H.comp G G := by
  dsimp only
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun F₂ Word)
  intro u v
  simp only [Pi.basisFun_apply, LinearMap.BilinForm.add_apply, LinearMap.BilinForm.flip_apply,
    LinearMap.BilinForm.comp_apply, liftForm, Matrix.toBilin'_single, Matrix.of_apply,
    rowsLinear_single, pairRows_apply]
  exact generator_correction_check u v mask isSign

private theorem phase_generator_polar (mask : Fin 2) (isSign : Bool) (x y : Charge) :
    let bit := if mask = 0 then 64 else 32
    let g := generatorRow bit isSign
    let G := rowsLinear g
    liftForm g (x + y) (x + y) = liftForm g x x + liftForm g y y +
      (H x y + H (G x) (G y)) := by
  dsimp only
  let bit := if mask = 0 then 64 else 32
  let g := generatorRow bit isSign
  have h := LinearMap.congr_fun (LinearMap.congr_fun
    (generator_correction_symm mask isSign) x) y
  simp only [LinearMap.BilinForm.add_apply, LinearMap.BilinForm.flip_apply,
    LinearMap.BilinForm.comp_apply] at h
  rw [← h]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
  abel

private theorem compose_phase_polar
    (f g : Charge →ₗ[F₂] Charge) (p q : Charge → F₂)
    (hp : ∀ x y, p (x + y) = p x + p y + (H x y + H (f x) (f y)))
    (hq : ∀ x y, q (x + y) = q x + q y + (H x y + H (g x) (g y)))
    (x y : Charge) :
    (p (x + y) + q (f (x + y))) =
      (p x + q (f x)) + (p y + q (f y)) + (H x y + H (g (f x)) (g (f y))) := by
  rw [map_add, hp, hq]
  have hzero : H (f x) (f y) + H (f x) (f y) = 0 := CharTwo.add_self_eq_zero _
  calc
    _ = ((p x + q (f x)) + (p y + q (f y)) + (H x y + H (g (f x)) (g (f y)))) +
        (H (f x) (f y) + H (f x) (f y)) := by abel
    _ = _ := by rw [hzero, add_zero]

private theorem phaseI_polar (x y : Charge) :
    phaseI (x + y) = phaseI x + phaseI y + (H x y + H (actionI x) (actionI y)) :=
  compose_phase_polar (rowsLinear x₁) (rowsLinear z₁)
    (fun a => liftForm x₁ a a) (fun a => liftForm z₁ a a)
    (phase_generator_polar 0 false) (phase_generator_polar 0 true) x y

private theorem phaseJ_polar (x y : Charge) :
    phaseJ (x + y) = phaseJ x + phaseJ y + (H x y + H (actionJ x) (actionJ y)) :=
  compose_phase_polar ((rowsLinear x₂).comp (rowsLinear x₁)) (rowsLinear z₂)
    (fun a => liftForm x₁ a a + liftForm x₂ (rowsLinear x₁ a) (rowsLinear x₁ a))
    (fun a => liftForm z₂ a a)
    (compose_phase_polar (rowsLinear x₁) (rowsLinear x₂)
      (fun a => liftForm x₁ a a) (fun a => liftForm x₂ a a)
      (phase_generator_polar 0 false) (phase_generator_polar 1 false))
    (phase_generator_polar 1 true) x y

private theorem pairing_eq_halfGram (a b : Charge) :
    modTwoPairing latticeData a b = H a b + H b a := by
  exact (mod_two_cocycle_symmetrization latticeData a b).symm.trans
    (congrArg₂ (· + ·) (modTwoCocycle_eq_halfGram a b) (modTwoCocycle_eq_halfGram b a))

-- Evaluate the 128 rows against the 64 even labels in the kernel.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
-- The row checks normalize the half-Gram entries and both order comparisons.
private theorem halfGram_even_entry : ∀ u v : Word, evenWord v →
    halfGram u v + halfGram v u = (if u = flip 127 v then 1 else 0) := by
  intro u
  fin_cases u <;> decide +kernel

private theorem complement_facts : ∀ u : Word,
    flip 127 (flip 127 u) = u ∧ (¬ evenWord u → evenWord (flip 127 u)) := by
  decide +kernel

private theorem pairing_with_even_single (w : Charge) (v : Word) (hv : evenWord v) :
    modTwoPairing latticeData w (basisVector v) = w (flip 127 v) := by
  have h :
      (modTwoPairing latticeData).flip (basisVector v) =
        (LinearMap.proj (flip 127 v) : Charge →ₗ[F₂] F₂) := by
    apply (Pi.basisFun F₂ Word).ext
    intro u
    change modTwoPairing latticeData ((Pi.basisFun F₂ Word) u) (basisVector v) =
      (Pi.basisFun F₂ Word) u (flip 127 v)
    simp only [Pi.basisFun_apply, basisVector, pairing_eq_halfGram, H,
      Matrix.toBilin'_single, Matrix.of_apply, halfGram_even_entry u v hv, Pi.single_apply]
    by_cases he : u = flip 127 v
    · simp [he]
    · simp [he, Ne.symm he]
  exact LinearMap.congr_fun h w

private theorem separates_outside_displacement (w : Charge) (hw : w ∉ W) :
    ∃ t ∈ W, H w t + H t w = 1 := by
  have hodd : ∃ u : Word, ¬ evenWord u ∧ w u ≠ 0 := by
    by_contra hn
    apply hw
    apply (mem_displacement_iff w).2
    intro u hu
    by_contra hne
    exact hn ⟨u, hu, hne⟩
  obtain ⟨u, hu, hne⟩ := hodd
  have he := (complement_facts u).2 hu
  refine ⟨basisVector (flip 127 u), even_single_mem _ he, ?_⟩
  rw [← pairing_eq_halfGram, pairing_with_even_single _ _ he, (complement_facts u).1]
  exact (binary_cases (w u)).resolve_left hne

private theorem perfect_pairing (w : Charge) (hw : w ≠ 0) :
    ∃ t : Charge, H w t + H t w = 1 := by
  have hu : IsUnit latticeData.G.det := by
    change IsUnit gram.det
    rw [gram_det]
    exact isUnit_one
  have hex : ∃ t : Charge, modTwoPairing latticeData w t ≠ 0 := by
    by_contra! h
    exact hw ((mod_two_pairing_nondegenerate latticeData hu).1 w h)
  obtain ⟨t, ht⟩ := hex
  exact ⟨t, (pairing_eq_halfGram w t).symm.trans
    ((binary_cases (modTwoPairing latticeData w t)).resolve_left ht)⟩

/-- The irreducible negative-sign representation of the actual reflection quotient. -/
def groundRepresentation : Representation ℂ (Extension latticeData ⧸ K latticeData) (Ground 64) :=
  Classical.choose actual_rank128_ground

private theorem ground_finrank : Module.finrank ℂ (Ground 64) = 2 ^ 64 :=
  (Classical.choose_spec actual_rank128_ground).2.2

/-- The actual quotient operator for the lift of a charge with sign exponent zero. -/
def groundOperator (a : Charge) : Module.End ℂ (Ground 64) :=
  chargeOperator latticeData groundRepresentation a

private abbrev centralLift (s : F₂) : Extension latticeData ⧸ K latticeData :=
  QuotientGroup.mk (⟨s, 0⟩ : Extension latticeData)

private theorem ground_central (s : F₂) :
    groundRepresentation (centralLift s) = complexSign s • (1 : Module.End ℂ (Ground 64)) := by
  rcases binary_cases s with rfl | rfl
  · rw [sign_zero, one_smul]
    change groundRepresentation (QuotientGroup.mk (1 : Extension latticeData)) = 1
    rw [QuotientGroup.mk_one, map_one]
  · rw [sign_one, neg_one_smul]
    exact (Classical.choose_spec actual_rank128_ground).2.1

private theorem ground_operator_zero : groundOperator 0 = 1 := by
  have h : chargeLift latticeData (0 : ModTwoCharge latticeData) = 1 := by
    apply (quotientEquiv latticeData).injective
    rw [reduced_lift, map_one]
    all_goals rfl
  exact (congrArg groundRepresentation h).trans (map_one groundRepresentation)

private theorem ground_operator_mul (a b : Charge) :
    groundOperator a * groundOperator b = complexSign (H a b) • groundOperator (a + b) := by
  have h : chargeLift latticeData a * chargeLift latticeData b =
      centralLift (H a b) * chargeLift latticeData (a + b) := by
    apply (quotientEquiv latticeData).injective
    have ha := reduced_lift latticeData a
    have hb := reduced_lift latticeData b
    have hab := reduced_lift latticeData (a + b)
    have hc : quotientEquiv latticeData (centralLift (H a b)) =
        (⟨H a b, 0⟩ : ReducedExtension latticeData) := by
      change reduction latticeData ⟨H a b, 0⟩ = _
      simp [reduction]
    rw [map_mul, map_mul, ha, hb, hab, hc]
    change (⟨0, a⟩ : ReducedExtension latticeData) * ⟨0, b⟩ =
      (⟨H a b, 0⟩ : ReducedExtension latticeData) * ⟨0, a + b⟩
    apply SignExtension.ext
    · change 0 + 0 + modTwoCocycle latticeData a b =
        H a b + 0 + modTwoCocycle latticeData 0 (a + b)
      have hzero : modTwoCocycle latticeData 0 (a + b) = 0 := by
        have hz := (modTwoCocycle latticeData).map_zero
        exact DFunLike.congr_fun hz (a + b)
      rw [zero_add, zero_add, add_zero, hzero, add_zero]
      exact modTwoCocycle_eq_halfGram a b
    · exact (zero_add (a + b)).symm
  unfold groundOperator chargeOperator
  rw [← map_mul, h, map_mul, ground_central, smul_mul_assoc, one_mul]

/-- The normalized trace product on the rank-128 Barnes–Wall negative-sign ground.
Covariance specifies the two physical intertwiners through their action on the
actual quotient charge operators. -/
theorem normalized_trace_mul_eq_two_pow_32
    {Ui Uj : Module.End ℂ (Ground 64)} (hneI : Ui ≠ 0) (hneJ : Uj ≠ 0)
    (hcovI : ∀ x : Charge, Ui * groundOperator x =
      complexSign (phaseI x) • (groundOperator (actionI x) * Ui))
    (hcovJ : ∀ x : Charge, Uj * groundOperator x =
      complexSign (phaseJ x) • (groundOperator (actionJ x) * Uj)) :
    ((2 : ℂ) ^ 64 * tr (Ui * Uj)) / (tr Ui * tr Uj) = (2 : ℂ) ^ 32 := by
  have hcard : Fintype.card Charge = (Module.finrank ℂ (Ground 64)) ^ 2 := by
    change Fintype.card (Fin 128 → ZMod 2) = (Module.finrank ℂ (Ground 64)) ^ 2
    rw [Fintype.card_pi_const, ZMod.card, ground_finrank, ← pow_mul]
  have hW : LinearMap.range (actionI + LinearMap.id) ⊓
      LinearMap.range (actionJ + LinearMap.id) = W := by
    rw [displacement_images.1, displacement_images.2, inf_idem]
  let a : CommonImage → Charge := fun w => preimageI (commonImageEquiv.symm w)
  let b : CommonImage → Charge := fun w => preimageJ (commonImageEquiv.symm w)
  have hw (w : CommonImage) : displacement (commonImageEquiv.symm w) = (w : Charge) := by
    change (commonImageEquiv (commonImageEquiv.symm w)).val = w.val
    rw [Equiv.apply_symm_apply]
  have ha (w : CommonImage) : actionI (a w) + a w = (w : Charge) :=
    (actual_preimages (commonImageEquiv.symm w)).1.trans (hw w)
  have hb (w : CommonImage) : actionJ (b w) + b w = (w : Charge) :=
    (actual_preimages (commonImageEquiv.symm w)).2.trans (hw w)
  have hfixedI (t : Charge) (ht : t ∈ LinearMap.range (actionI + LinearMap.id) ⊓
      LinearMap.range (actionJ + LinearMap.id)) : actionI t = t ∧ phaseI t = 0 :=
    (fixed_and_phase_zero t (hW ▸ ht)).1
  have hfixedJ (t : Charge) (ht : t ∈ LinearMap.range (actionI + LinearMap.id) ⊓
      LinearMap.range (actionJ + LinearMap.id)) : actionJ t = t ∧ phaseJ t = 0 :=
    (fixed_and_phase_zero t (hW ▸ ht)).2
  have hseparate : ∀ w ∉ LinearMap.range (actionI + LinearMap.id) ⊓
      LinearMap.range (actionJ + LinearMap.id),
      ∃ t ∈ LinearMap.range (actionI + LinearMap.id) ⊓
        LinearMap.range (actionJ + LinearMap.id), H w t + H t w = 1 := by
    rw [hW]
    exact separates_outside_displacement
  have htrace := WeylIntertwinerTraceProduct.normalized_trace_mul_eq_gauss_sum
    ground_operator_zero ground_operator_mul perfect_pairing hcard hcovI hcovJ
    a b ha hb hfixedI hfixedJ hseparate hneI hneJ
  have hdim : (Module.finrank ℂ (Ground 64) : ℂ) = (2 : ℂ) ^ 64 := by
    rw [ground_finrank, Nat.cast_pow, Nat.cast_ofNat]
  rw [← defect_ground_gauss_sum]
  simpa only [hdim, defectGroundExponent, a, b] using htrace

/-- The prescribed generator phases admit intertwiners on the actual quotient ground,
and they can simultaneously be normalized to trace `2^64`. -/
theorem exists_quaternion_intertwiners :
    ∃ Ui Uj : Module.End ℂ (Ground 64), Ui ≠ 0 ∧ Uj ≠ 0 ∧
      (∀ x : Charge, Ui * groundOperator x =
        complexSign (phaseI x) • (groundOperator (actionI x) * Ui)) ∧
      (∀ x : Charge, Uj * groundOperator x =
        complexSign (phaseJ x) • (groundOperator (actionJ x) * Uj)) ∧
      tr Ui = (2 : ℂ) ^ 64 ∧ tr Uj = (2 : ℂ) ^ 64 ∧
      tr (Ui * Uj) = (2 : ℂ) ^ 96 := by
  have htrace (w : W) (hw : (w : Charge) ≠ 0) : tr (groundOperator w) = 0 :=
    WeylIntertwinerTraceProduct.displacement_trace_eq_zero
      ground_operator_zero ground_operator_mul perfect_pairing hw
  obtain ⟨Ui, hUi, hcovI, htrI⟩ := WeylCovariantOperator.exists_covariant_operator
    (g := actionI) (H := H) (q := phaseI)
    (displacement_ker _ displacement_images.1 (fun w hw => (fixed_and_phase_zero w hw).1.1))
    displacement_isotropic (fun w hw => (fixed_and_phase_zero w hw).1.2) phaseI_polar
    displacement_images.1 ground_operator_zero ground_operator_mul htrace
  obtain ⟨Uj, hUj, hcovJ, htrJ⟩ := WeylCovariantOperator.exists_covariant_operator
    (g := actionJ) (H := H) (q := phaseJ)
    (displacement_ker _ displacement_images.2 (fun w hw => (fixed_and_phase_zero w hw).2.1))
    displacement_isotropic (fun w hw => (fixed_and_phase_zero w hw).2.2) phaseJ_polar
    displacement_images.2 ground_operator_zero ground_operator_mul htrace
  have hdim : (Module.finrank ℂ (Ground 64) : ℂ) = (2 : ℂ) ^ 64 := by
    rw [ground_finrank, Nat.cast_pow, Nat.cast_ofNat]
  rw [hdim] at htrI htrJ
  refine ⟨Ui, Uj, hUi, hUj, hcovI, hcovJ, htrI, htrJ, ?_⟩
  have h := normalized_trace_mul_eq_two_pow_32 hUi hUj hcovI hcovJ
  have hbase : (2 : ℂ) ≠ 0 := by norm_num
  have hd : (2 : ℂ) ^ 64 ≠ 0 := pow_ne_zero _ hbase
  rw [htrI, htrJ] at h
  apply mul_left_cancel₀ hd
  calc
    _ = (2 : ℂ) ^ 32 * ((2 : ℂ) ^ 64 * (2 : ℂ) ^ 64) :=
      (div_eq_iff (mul_ne_zero hd hd)).mp h
    _ = _ := by rw [← pow_add, ← pow_add, ← pow_add]

#print axioms exists_quaternion_intertwiners
#print axioms normalized_trace_mul_eq_two_pow_32

end

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Q8GroundTrace

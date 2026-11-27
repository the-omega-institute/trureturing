/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionSimplicity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionSimplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simplicity for the literal modes of the actual Leech extension. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddFixedModeIrreducibility
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldFaithfulness

/-! Simplicity follows from the odd sector's fixed-mode irreducibility,
the faithful fixed action, and a twisted mode-three vacuum product. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef weight_zero_vacuum)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open HalfFock.LatticeHalfFockOddFixedModeIrreducibility (fixedParitySlice_odd_irreducible)
open LatticeInvolution (FixedCarrier fixedMode fixedField_ncoeff fixedVacuum fixedY)
open LatticeHalfFockCorrectedField (correctedField)
open MixedIntertwiner (fixedParitySlice_faithful originalI_three_eq_vacuum originalRightCoefficient)
open OriginalFourMChargeCoset (originalI)
open StateField.SkewSymmetry (skew_symmetry)

private abbrev Odd := paritySpace leechData leechUnit (-1)

private theorem right_mode_mem (I : Submodule ℂ Orbifold)
    (stable : ∀ (a : Orbifold) (n : ℤ), ∀ b ∈ I,
      ((leechVertexAlgebra.stateField a)[[n]]) b ∈ I)
    (a : Orbifold) (ha : a ∈ I) (b : Orbifold) (n : ℤ) :
    ((leechVertexAlgebra.stateField a)[[n]]) b ∈ I := by
  have translation_mem (x : Orbifold) (hx : x ∈ I) :
      leechVertexAlgebra.translation x ∈ I := by
    rw [← virasoro_minus_one, virasoro_mode_eq]
    exact stable conformalVector 0 x hx
  have power_mem (j : ℕ) (x : Orbifold) (hx : x ∈ I) :
      (leechVertexAlgebra.translation ^ j) x ∈ I := by
    induction j with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hx
    | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact translation_mem _ ih
  have hskew := (skew_symmetry leechVertexAlgebra a b).1 n
  rw [hskew.2, finsum_eq_sum _ hskew.1]
  exact I.sum_mem fun j _ => I.smul_mem _ (power_mem j _ (stable b (n + j) a ha))

/-- Every complex submodule closed under all left modes of the actual Leech
extension state-field map is either zero or the whole extension. -/
theorem leechVertexAlgebra_simple (I : Submodule ℂ Orbifold)
    (stable : ∀ (a : Orbifold) (n : ℤ), ∀ b ∈ I,
      ((leechVertexAlgebra.stateField a)[[n]]) b ∈ I) :
    I = ⊥ ∨ I = ⊤ := by
  have h24 : leechData.rank = 24 := leech_spec.1
  have hrank : 2 ≤ leechData.rank := by omega
  let oddProjection : Orbifold →ₗ[ℂ] Odd := LinearMap.snd ℂ (FixedCarrier leechData) Odd
  let oddInclusion : Odd →ₗ[ℂ] Orbifold := LinearMap.inr ℂ (FixedCarrier leechData) Odd
  have fixed_action (a : FixedCarrier leechData) (n : ℤ) (x : Orbifold) :
      ((leechVertexAlgebra.stateField (a, 0))[[n]]) x =
        (fixedMode leechData a n x.1,
          ((fixedParitySlice leechData leechUnit (-1) a)[[n]]) x.2) := by
    rw [stateField_eq, OriginalOrbifoldField.Y_fixed_ncoeff_apply]
  have odd_image_stable (a : FixedCarrier leechData) (n : ℤ) (w : Odd)
      (hw : w ∈ I.map oddProjection) :
      ((fixedParitySlice leechData leechUnit (-1) a)[[n]]) w ∈ I.map oddProjection := by
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨_, stable (a, 0) n x hx, ?_⟩
    rw [fixed_action]
    rfl
  have odd_part_stable (a : FixedCarrier leechData) (n : ℤ) (w : Odd)
      (hw : w ∈ I.comap oddInclusion) :
      ((fixedParitySlice leechData leechUnit (-1) a)[[n]]) w ∈ I.comap oddInclusion := by
    change (0, w) ∈ I at hw
    change (0, ((fixedParitySlice leechData leechUnit (-1) a)[[n]]) w) ∈ I
    have h := stable (a, 0) n (0, w) hw
    rw [fixed_action] at h
    simpa only [map_zero] using h
  rcases fixedParitySlice_odd_irreducible leechData leechUnit hrank _ odd_image_stable with
    himage | himage
  · left
    have snd_eq_zero (x : Orbifold) (hx : x ∈ I) : x.2 = 0 := by
      have h : oddProjection x ∈ I.map oddProjection := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot ℂ).mp (himage ▸ h)
    apply (I.eq_bot_iff).mpr
    rintro ⟨a, w⟩ hx
    have hw : w = 0 := snd_eq_zero (a, w) hx
    subst w
    have ha : a = 0 := by
      apply fixedParitySlice_faithful leechData leechUnit leechPosDef h24
      intro n v
      have h := snd_eq_zero _ (right_mode_mem I stable (a, 0) hx (0, v) n)
      rwa [fixed_action] at h
    exact Prod.ext ha rfl
  · right
    apply top_unique
    have vacuum_mem : leechVertexAlgebra.vacuum ∈ I := by
      obtain ⟨u, v, huv⟩ := originalI_three_eq_vacuum leechData leechUnit leechPosDef h24
      have mode_three_fst (x : Orbifold) (hx : x.2 = v) :
          (((leechVertexAlgebra.stateField (0, u))[[3]]) x).1 = leechVertexAlgebra.vacuum.1 := by
        rw [stateField_eq, OriginalOrbifoldField.Y_ncoeff_apply]
        have hfixed : fixedMode leechData 0 3 = 0 := by
          rw [← fixedField_ncoeff]
          change (fixedY leechData 0)[[3]] = 0
          simp only [map_zero, Pi.zero_apply]
        change fixedMode leechData 0 3 x.1 + originalI leechData leechUnit leechPosDef 3 u x.2 =
          fixedVacuum leechData
        rw [hfixed, LinearMap.zero_apply, zero_add, hx]
        exact huv
      rcases fixedParitySlice_odd_irreducible leechData leechUnit hrank _ odd_part_stable with
        hpart | hpart
      · have hv : v ∈ I.map oddProjection := himage ▸ Submodule.mem_top
        obtain ⟨x, hx, hxv⟩ := Submodule.mem_map.mp hv
        let y : Orbifold := ((leechVertexAlgebra.stateField (0, u))[[3]]) x
        have hy : y ∈ I := stable (0, u) 3 x hx
        have hyvac : y.1 = leechVertexAlgebra.vacuum.1 := mode_three_fst x hxv
        -- L(0) kills the fixed component and leaves an element of the pure odd part of I.
        have energy_fst (z : Orbifold) :
            (virasoroMatter.mode 0 z).1 = fixedMode leechData conformalVector.1 1 z.1 := by
          rw [virasoro_mode_eq]
          exact congrArg Prod.fst (fixed_action conformalVector.1 1 z)
        have hzero : (virasoroMatter.mode 0 y).1 = 0 := by
          rw [energy_fst, hyvac, ← energy_fst, virasoro_vacuum 0 (by norm_num)]
          rfl
        have henergy : virasoroMatter.mode 0 y ∈ I := by
          rw [virasoro_mode_eq]
          exact stable conformalVector 1 y hy
        have hodd : (virasoroMatter.mode 0 y).2 ∈ I.comap oddInclusion := by
          change (0, (virasoroMatter.mode 0 y).2) ∈ I
          rwa [← hzero, Prod.mk.eta]
        have hz : virasoroMatter.mode 0 y = 0 :=
          Prod.ext hzero ((Submodule.mem_bot ℂ).mp (hpart ▸ hodd))
        have hysnd : y.2 = 0 := by
          have h := congrArg Prod.snd (weight_zero_vacuum y hz)
          change y.2 = _ • (0 : Odd) at h
          simpa only [smul_zero] using h
        exact (Prod.ext hyvac hysnd : y = leechVertexAlgebra.vacuum) ▸ hy
      · have hv : v ∈ I.comap oddInclusion := hpart ▸ Submodule.mem_top
        change (0, v) ∈ I at hv
        have h := stable (0, u) 3 (0, v) hv
        have hmode :
            ((leechVertexAlgebra.stateField (0, u))[[3]]) (0, v) = leechVertexAlgebra.vacuum := by
          apply Prod.ext (mode_three_fst (0, v) rfl)
          rw [stateField_eq, OriginalOrbifoldField.Y_ncoeff_apply]
          change ((fixedParitySlice leechData leechUnit (-1) 0)[[3]]) v +
            originalRightCoefficient leechData leechUnit 3 u 0 = 0
          rw [map_zero, add_zero]
          apply Subtype.ext
          change (correctedField leechData leechUnit 0).coeff (2 * (-3 - 1)) v.val = 0
          simp
        exact hmode ▸ h
    intro a _
    rw [← leechVertexAlgebra.creation a]
    exact stable a (-1) leechVertexAlgebra.vacuum vacuum_mem

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra

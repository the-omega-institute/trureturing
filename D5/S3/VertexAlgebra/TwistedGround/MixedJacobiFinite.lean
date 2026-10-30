/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-source signed two-twisted-input mixed Jacobi in the actual restricted dual. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube

/-! Finite families, restricted-dual evaluation and actual homogeneous
expansions extend the common-cube identity to every original input. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator DirectSum
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace
open LatticeHalfFockFiniteCorrection (sourceWeight)
open LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open ActualChargedAdjoint LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField

private def mixedMode (D : LatticeData) (hu : IsUnit D.G.det) (t : ℤ) :
    FixedCarrier D →ₗ[ℂ] Module.End ℂ (paritySpace D hu (-1)) where
  toFun a := (fixedParitySlice D hu (-1) a)[[t]]
  map_add' a b := by
    ext x
    change (correctedField D hu (a.val+b.val)).coeff (2*(-t-1)) x.val = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' z a := by
    ext x
    change (correctedField D hu (z • a.val)).coeff (2*(-t-1)) x.val = _
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
    rfl

private def mixedLeftTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) (j : ℕ) :
    FixedRestrictedDual D :=
  Ring.choose (m : ℂ) j • normalizedCoefficient D hu (m+n-(j : ℤ))
    (mixedMode D hu (r+(j : ℤ)) a u) v

private def mixedFirstTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) (j : ℕ) :
    FixedRestrictedDual D :=
  ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
    oppositeAction D hu hD (m+r-(j : ℤ)) a
      (normalizedCoefficient D hu (n+(j : ℤ)) u v)

private def mixedSecondTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) (j : ℕ) :
    FixedRestrictedDual D :=
  (((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * (-1 : ℂ)^r) •
    normalizedCoefficient D hu (n+r-(j : ℤ)) u (mixedMode D hu (m+(j : ℤ)) a v)

private theorem mixed_mode_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (t : ℤ) (a : FixedCarrier D) (u : paritySpace D hu (-1)) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → mixedMode D hu (t+(j : ℤ)) a u = 0 := by
  let A := fixedParitySlice D hu (-1) a
  let b : ℤ := ((HahnModule.of ℂ).symm (A u)).order
  refine ⟨(-t-1-b).toNat+1, ?_⟩
  intro j hj
  exact VertexOperator.ncoeff_eq_zero_of_lt_order A (t+(j : ℤ)) u
    (by dsimp [b] at *; omega)

private theorem mixed_families_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (mixedLeftTerm D hu m n r a u v) ∧
    Function.HasFiniteSupport (mixedFirstTerm D hu hD m n r a u v) ∧
    Function.HasFiniteSupport (mixedSecondTerm D hu m n r a u v) := by
  classical
  obtain ⟨L, hL⟩ := mixed_mode_tail D hu r a u
  obtain ⟨R, hR⟩ := mixed_mode_tail D hu m a v
  let J := ((ActualEnergyRestrictedDual.maxOddWeight D hu u.val : ℤ)+
    (ActualEnergyRestrictedDual.maxOddWeight D hu v.val : ℤ)+4-n).toNat
  refine ⟨(Finset.range L).finite_toSet.subset ?_,
    (Finset.range J).finite_toSet.subset ?_, (Finset.range R).finite_toSet.subset ?_⟩
  · intro j hj
    by_contra outside
    apply hj
    simp only [mixedLeftTerm, hL j (by simpa using outside), map_zero,
      LinearMap.zero_apply, smul_zero]
  · intro j hj
    by_contra outside
    have zero := normalizedCoefficient_truncation D hu hD u v (n+(j : ℤ))
      (by have := Finset.mem_range.not.mp outside; dsimp [J] at *; omega)
    apply hj
    simp only [mixedFirstTerm, zero, map_zero, smul_zero]
  · intro j hj
    by_contra outside
    apply hj
    simp only [mixedSecondTerm, hR j (by simpa using outside), map_zero, smul_zero]

private def mixedTriples (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m n r : ℤ) :
    FixedCarrier D →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ]
        (ℕ → FixedRestrictedDual D × FixedRestrictedDual D × FixedRestrictedDual D) where
  toFun a := {
    toFun u := {
      toFun v := fun j => (mixedLeftTerm D hu m n r a u v j,
        mixedFirstTerm D hu hD m n r a u v j, mixedSecondTerm D hu m n r a u v j)
      map_add' v w := by
        funext j
        simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_add,
          LinearMap.add_apply, smul_add, Prod.mk_add_mk, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      map_smul' z v := by
        funext j
        simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_smul,
          LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk, Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
        apply Prod.ext
        · module
        · apply Prod.ext <;> module }
    map_add' u w := by
      apply LinearMap.ext
      intro v
      funext j
      simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_add,
        LinearMap.add_apply, smul_add, Prod.mk_add_mk, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    map_smul' z u := by
      apply LinearMap.ext
      intro v
      funext j
      simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_smul,
        LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk, Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
      apply Prod.ext
      · module
      · apply Prod.ext <;> module }
  map_add' a b := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    funext j
    simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_add,
      LinearMap.add_apply, smul_add, Prod.mk_add_mk, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  map_smul' z a := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    funext j
    simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk, Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    apply Prod.ext
    · module
    · apply Prod.ext <;> module

private theorem mixed_triples_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (mixedTriples D hu hD m n r a u v) := by
  obtain ⟨hl, hf, hs⟩ := mixed_families_finite D hu hD m n r a u v
  change (Function.support (fun j => (mixedLeftTerm D hu m n r a u v j,
    mixedFirstTerm D hu hD m n r a u v j, mixedSecondTerm D hu m n r a u v j))).Finite
  rw [Function.support_prodMk, Function.support_prodMk]
  exact hl.union (hf.union hs)

private def mixedBalance (D : LatticeData) :
    (FixedRestrictedDual D × FixedRestrictedDual D × FixedRestrictedDual D) →ₗ[ℂ]
      FixedRestrictedDual D where
  toFun x := x.1-x.2.1+x.2.2
  map_add' x y := by dsimp; abel
  map_smul' z x := by simp only [Prod.smul_fst, Prod.smul_snd, smul_sub, smul_add, RingHom.id_apply]

private def mixedResidual (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m n r : ℤ) :
    FixedCarrier D →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ] FixedRestrictedDual D where
  toFun a := {
    toFun u := {
      toFun v := mixedBalance D (∑ᶠ j, mixedTriples D hu hD m n r a u v j)
      map_add' v w := by
        simp only [map_add, LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
        rw [finsum_add_distrib (mixed_triples_finite D hu hD m n r a u v)
          (mixed_triples_finite D hu hD m n r a u w), map_add]
      map_smul' z v := by
        simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← smul_finsum, map_smul] }
    map_add' u w := by
      apply LinearMap.ext
      intro v
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [finsum_add_distrib (mixed_triples_finite D hu hD m n r a u v)
        (mixed_triples_finite D hu hD m n r a w v), map_add]
    map_smul' z u := by
      apply LinearMap.ext
      intro v
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← smul_finsum, map_smul] }
  map_add' a b := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [finsum_add_distrib (mixed_triples_finite D hu hD m n r a u v)
      (mixed_triples_finite D hu hD m n r b u v), map_add]
  map_smul' z a := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← smul_finsum, map_smul]

private theorem mixed_residual_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    mixedResidual D hu hD m n r a u v =
      (∑ᶠ j, mixedLeftTerm D hu m n r a u v j) -
      (∑ᶠ j, mixedFirstTerm D hu hD m n r a u v j) +
      (∑ᶠ j, mixedSecondTerm D hu m n r a u v j) := by
  let F := mixedTriples D hu hD m n r a u v
  have finite := mixed_triples_finite D hu hD m n r a u v
  have fst := map_finsum (LinearMap.fst ℂ (FixedRestrictedDual D)
    (FixedRestrictedDual D × FixedRestrictedDual D)) finite
  have snd := map_finsum (LinearMap.snd ℂ (FixedRestrictedDual D)
    (FixedRestrictedDual D × FixedRestrictedDual D)) finite
  have finiteSnd : Function.HasFiniteSupport (fun j => (F j).2) := finite.snd
  have sf := map_finsum (LinearMap.fst ℂ (FixedRestrictedDual D) (FixedRestrictedDual D)) finiteSnd
  have ss := map_finsum (LinearMap.snd ℂ (FixedRestrictedDual D) (FixedRestrictedDual D)) finiteSnd
  change (∑ᶠ j, F j).1-(∑ᶠ j, F j).2.1+(∑ᶠ j, F j).2.2 = _
  change (∑ᶠ j, F j).1 = ∑ᶠ j, (F j).1 at fst
  change (∑ᶠ j, F j).2 = ∑ᶠ j, (F j).2 at snd
  change (∑ᶠ j, (F j).2).1 = ∑ᶠ j, (F j).2.1 at sf
  change (∑ᶠ j, (F j).2).2 = ∑ᶠ j, (F j).2.2 at ss
  rw [fst, snd, sf, ss]
  rfl

private def restrictedEvaluation (D : LatticeData) (E : ℤ) (b : fixedGrade D E) :
    FixedRestrictedDual D →ₗ[ℂ] ℂ where
  toFun f := f E b
  map_add' f g := rfl
  map_smul' z f := rfl

open private homogeneous_coefficient ambientCoefficient liftGrade kernel
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private fixed_mode_energy_int from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi

private theorem normalized_off_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (t E : ℤ)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (b : fixedGrade D E) (outside : E ≠ (H : ℤ)+(K : ℤ)-t-1) :
    normalizedCoefficient D hu t u v E b = 0 := by
  change ambientCoefficient D hu t u.val v.val E b = 0
  rw [homogeneous_coefficient D hu h24 H K t u.val v.val huH hvK]
  simp [liftGrade, DirectSum.lof_eq_of, DirectSum.of_apply, outside, Ne.symm outside]

private theorem mixed_input_off_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (b : fixedGrade D E) (outside : E ≠ (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (j : ℕ) :
    normalizedCoefficient D hu (m+n-(j : ℤ))
      (mixedMode D hu (r+(j : ℤ)) (⟨a.val,a.property.2⟩ : FixedCarrier D) u) v E b = 0 ∧
    normalizedCoefficient D hu (n+r-(j : ℤ)) u
      (mixedMode D hu (m+(j : ℤ)) (⟨a.val,a.property.2⟩ : FixedCarrier D) v) E b = 0 := by
  have firstEnergy := fixed_mode_energy_int D hu H ((H : ℤ)+d-(r+(j : ℤ))-1)
    d (r+(j : ℤ)) a u huH rfl
  have secondEnergy := fixed_mode_energy_int D hu K ((K : ℤ)+d-(m+(j : ℤ))-1)
    d (m+(j : ℤ)) a v hvK rfl
  constructor
  · by_cases negative : (H : ℤ)+d-(r+(j : ℤ))-1 < 0
    · have zero := integer_energy_zero D hu h24 _ _ firstEnergy (by omega)
      have input : mixedMode D hu (r+(j : ℤ))
          (⟨a.val,a.property.2⟩ : FixedCarrier D) u = 0 := Subtype.ext zero
      simp only [input, map_zero, LinearMap.zero_apply, DirectSum.zero_apply]
    · let W := ((H : ℤ)+d-(r+(j : ℤ))-1).toNat
      have hW : (W : ℤ) = (H : ℤ)+d-(r+(j : ℤ))-1 := Int.toNat_of_nonneg (by omega)
      have hWC : (W : ℂ) = (((H : ℤ)+d-(r+(j : ℤ))-1 : ℤ) : ℂ) := by
        exact_mod_cast hW
      exact normalized_off_grade D hu h24 W K (m+n-(j : ℤ)) E _ v
        (by simpa only [hWC, mixedMode, LinearMap.coe_mk, AddHom.coe_mk] using firstEnergy)
        hvK b (by omega)
  · by_cases negative : (K : ℤ)+d-(m+(j : ℤ))-1 < 0
    · have zero := integer_energy_zero D hu h24 _ _ secondEnergy (by omega)
      have input : mixedMode D hu (m+(j : ℤ))
          (⟨a.val,a.property.2⟩ : FixedCarrier D) v = 0 := Subtype.ext zero
      simp only [input, map_zero, LinearMap.zero_apply, DirectSum.zero_apply]
    · let W := ((K : ℤ)+d-(m+(j : ℤ))-1).toNat
      have hW : (W : ℤ) = (K : ℤ)+d-(m+(j : ℤ))-1 := Int.toNat_of_nonneg (by omega)
      have hWC : (W : ℂ) = (((K : ℤ)+d-(m+(j : ℤ))-1 : ℤ) : ℂ) := by
        exact_mod_cast hW
      exact normalized_off_grade D hu h24 H W (n+r-(j : ℤ)) E u _ huH
        (by simpa only [hWC, mixedMode, LinearMap.coe_mk, AddHom.coe_mk] using secondEnergy)
        b (by omega)

private theorem mixed_dual_off_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (b : fixedGrade D E) (outside : E ≠ (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (j : ℕ) :
    oppositeAction D hu hD (m+r-(j : ℤ))
      (⟨a.val,a.property.2⟩ : FixedCarrier D)
      (normalizedCoefficient D hu (n+(j : ℤ)) u v) E b = 0 := by
  rw [oppositeAction_homogeneous]
  change (oppositeHomogeneous D hu hD d (m+r-(j : ℤ)) a
    (ambientCoefficient D hu (n+(j : ℤ)) u.val v.val)) E b = 0
  rw [homogeneous_coefficient D hu h24 H K (n+(j : ℤ)) u.val v.val huH hvK]
  change (oppositeHomogeneous D hu hD d (m+r-(j : ℤ)) a
    (DirectSum.lof ℂ ℤ (fun f => Module.Dual ℂ (fixedGrade D f))
      ((H : ℤ)+(K : ℤ)-(n+(j : ℤ))-1)
      ((fixedGrade D ((H : ℤ)+(K : ℤ)-(n+(j : ℤ))-1)).dualRestrict
        (kernel D hu H K (n+(j : ℤ)) u.val v.val)))) E b = 0
  simp only [oppositeHomogeneous, LinearMap.coe_mk, AddHom.coe_mk,
    DirectSum.toModule_lof, LinearMap.comp_apply]
  have target : (H : ℤ)+(K : ℤ)-(n+(j : ℤ))-1+d-(m+r-(j : ℤ))-1 =
      (H : ℤ)+(K : ℤ)+d-m-n-r-2 := by ring
  simp [DirectSum.lof_eq_of, DirectSum.of_apply, target, outside, Ne.symm outside]

private theorem mixed_residual_homogeneous (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    mixedResidual D hu hD m n r (⟨a.val,a.property.2⟩ : FixedCarrier D) u v = 0 := by
  classical
  let A : FixedCarrier D := ⟨a.val,a.property.2⟩
  obtain ⟨hl, hf, hs⟩ := mixed_families_finite D hu hD m n r A u v
  rw [mixed_residual_expansion]
  apply DFinsupp.ext
  intro E
  apply LinearMap.ext
  intro b
  let ev := restrictedEvaluation D E b
  change ev ((∑ᶠ j, mixedLeftTerm D hu m n r A u v j) -
    (∑ᶠ j, mixedFirstTerm D hu hD m n r A u v j) +
    (∑ᶠ j, mixedSecondTerm D hu m n r A u v j)) = 0
  rw [map_add, map_sub, map_finsum ev hl, map_finsum ev hf, map_finsum ev hs]
  by_cases hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2
  · have identity := mixed_homogeneous_grade_pairing D hu hD h24 H K d m n r E
      a b u v huH hvK hE
    have firstEval := map_finsum ev hf
    change (∑ᶠ j, mixedFirstTerm D hu hD m n r A u v j) E b = _ at firstEval
    dsimp only [mixedFirstTerm, A] at firstEval ⊢
    rw [firstEval] at identity
    have signedSecond : (∑ᶠ j, ev (mixedSecondTerm D hu m n r A u v j)) =
        (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
          normalizedCoefficient D hu (n+r-(j : ℤ)) u
            (((fixedParitySlice D hu (-1)
              (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) := by
      rw [mul_finsum]
      apply finsum_congr
      intro j
      change (((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * (-1 : ℂ)^r) * _ = _
      dsimp only [mixedMode, A, LinearMap.coe_mk, AddHom.coe_mk]
      ring
    rw [signedSecond]
    change (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v E b) - _ + _ = 0
    linear_combination identity
  · have zl : ∀ j, ev (mixedLeftTerm D hu m n r A u v j) = 0 := by
      intro j
      have zero := (mixed_input_off_grade D hu h24 H K d m n r E a u v huH hvK b hE j).1
      change Ring.choose (m : ℂ) j * _ = 0
      rw [zero, mul_zero]
    have zf : ∀ j, ev (mixedFirstTerm D hu hD m n r A u v j) = 0 := by
      intro j
      have zero := mixed_dual_off_grade D hu hD h24 H K d m n r E a u v huH hvK b hE j
      change ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * _ = 0
      rw [zero, mul_zero]
    have zs : ∀ j, ev (mixedSecondTerm D hu m n r A u v j) = 0 := by
      intro j
      have zero := (mixed_input_off_grade D hu h24 H K d m n r E a u v huH hvK b hE j).2
      change (((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * (-1 : ℂ)^r) * _ = 0
      rw [zero, mul_zero]
    simp only [zl, zf, zs, finsum_zero, sub_zero, add_zero]

open private basis_parity negative_support
  from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private fixedProjection from D5.S3.VertexAlgebra.TwistedGround.MixedOpposite

private def actualInputBasis (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1))
    (i : {i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu) //
      i ∈ ((actualAmbientBasis D hu).repr u.val).support}) : paritySpace D hu (-1) :=
  ⟨actualAmbientBasis D hu i.val, by
    have odd := negative_support D hu u i.val i.property
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rw [basis_parity, neg_one_pow_eq_pow_mod_two, odd]
    norm_num⟩

private theorem actual_input_basis_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1)) :
    (∑ i ∈ ((actualAmbientBasis D hu).repr u.val).support.attach,
      ((actualAmbientBasis D hu).repr u.val i.val) • actualInputBasis D hu u i) = u := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change (∑ i ∈ ((actualAmbientBasis D hu).repr u.val).support.attach,
    ((actualAmbientBasis D hu).repr u.val i.val) • actualAmbientBasis D hu i.val) = u.val
  rw [Finset.sum_attach _ (fun i =>
    ((actualAmbientBasis D hu).repr u.val i) • actualAmbientBasis D hu i)]
  exact (actualAmbientBasis D hu).linearCombination_repr u.val

private theorem actual_input_basis_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (u : paritySpace D hu (-1))
    (i : {i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu) //
      i ∈ ((actualAmbientBasis D hu).repr u.val).support}) :
    actualTensorL0 D hu (actualInputBasis D hu u i).val =
      (((oddWeight D i.val.1+3)/2 : ℕ) : ℂ) • (actualInputBasis D hu u i).val := by
  have odd := negative_support D hu u i.val i.property
  have energy := actual_basis_eigenvalue D hu i.val.1 i.val.2
  change actualTensorL0 D hu (actualAmbientBasis D hu i.val) = _
  rw [energy, h24]
  congr 1
  have h : oddWeight D i.val.1+3 = 2*((oddWeight D i.val.1+3)/2) := by omega
  have hc : (oddWeight D i.val.1 : ℂ)+3 =
      2*(((oddWeight D i.val.1+3)/2 : ℕ) : ℂ) := by exact_mod_cast h
  linear_combination hc / 2

private def fixedSourceInclusion (D : LatticeData) (d : ℤ) :
    fixedGrade D d →ₗ[ℂ] FixedCarrier D where
  toFun a := ⟨a.val,a.property.2⟩
  map_add' a b := rfl
  map_smul' z a := rfl

private theorem fixed_source_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (a : FixedCarrier D) :
    (∑ d ∈ stateEnergies D a.val,
      fixedSourceInclusion D d (fixedProjection D hu d a)) = a := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change (∑ d ∈ stateEnergies D a.val,
    (2 : ℂ)⁻¹ • (gradeProjection D d a.val + theta D (gradeProjection D d a.val))) = a.val
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  change (2 : ℂ)⁻¹ • ((∑ d ∈ stateEnergies D a.val, gradeProjection D d a.val) +
    ∑ d ∈ stateEnergies D a.val, thetaLinear D (gradeProjection D d a.val)) = a.val
  have fixed : thetaLinear D a.val = a.val := (mem_fixedSpace D a.val).mp a.property
  rw [← map_sum, sum_gradeProjections, fixed]
  module

private theorem mixed_residual_fixed_source (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (d m n r : ℤ) (a : fixedGrade D d) (u v : paritySpace D hu (-1)) :
    mixedResidual D hu hD m n r (⟨a.val,a.property.2⟩ : FixedCarrier D) u v = 0 := by
  classical
  rw [← actual_input_basis_expansion D hu u, ← actual_input_basis_expansion D hu v]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    RingHom.id_apply, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  rw [mixed_residual_homogeneous D hu hD h24
    ((oddWeight D i.val.1+3)/2) ((oddWeight D j.val.1+3)/2) d m n r a
    (actualInputBasis D hu u i) (actualInputBasis D hu v j)
    (actual_input_basis_energy D hu h24 u i) (actual_input_basis_energy D hu h24 v j)]
  simp only [smul_zero]

private theorem mixed_residual_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    mixedResidual D hu hD m n r a u v = 0 := by
  classical
  rw [← fixed_source_expansion D hu a]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  exact mixed_residual_fixed_source D hu hD h24 d m n r (fixedProjection D hu d a) u v

/-- The complete signed two-twisted-input mixed Jacobi law, with the actual
opposite action on the original fixed restricted dual. The three actual
families have finite support before any interchange of sums. The source and
both inputs are extended through their actual finite homogeneous expansions;
no generating-source, sign-of-mode or selected target-grade restriction is
present. This identity supplies no three-twisted crossing premise. -/
theorem mixed_jacobi (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1) a)[[r+(j : ℤ)]]) u) v) =
    ∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      (oppositeAction D hu hD (m+r-(j : ℤ)) a
        (normalizedCoefficient D hu (n+(j : ℤ)) u v) -
       (-1 : ℂ)^r • normalizedCoefficient D hu (n+r-(j : ℤ)) u
         (((fixedParitySlice D hu (-1) a)[[m+(j : ℤ)]]) v)) := by
  have zero := mixed_residual_zero D hu hD h24 m n r a u v
  rw [mixed_residual_expansion] at zero
  obtain ⟨hl, hf, hs⟩ := mixed_families_finite D hu hD m n r a u v
  change (∑ᶠ j, mixedLeftTerm D hu m n r a u v j) = _
  calc
    _ = (∑ᶠ j, mixedFirstTerm D hu hD m n r a u v j) -
        (∑ᶠ j, mixedSecondTerm D hu m n r a u v j) := by
      apply eq_of_sub_eq_zero
      convert zero using 1 <;> abel
    _ = ∑ᶠ j, (mixedFirstTerm D hu hD m n r a u v j -
        mixedSecondTerm D hu m n r a u v j) := (finsum_sub_distrib hf hs).symm
    _ = _ := by
      apply finsum_congr
      intro j
      simp only [mixedFirstTerm, mixedSecondTerm, mixedMode, smul_sub, smul_smul,
        LinearMap.coe_mk, AddHom.coe_mk]

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

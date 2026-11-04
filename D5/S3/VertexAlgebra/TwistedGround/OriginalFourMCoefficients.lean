/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global original inverse, statewise finite Jacobi channels and scalar cutoffs. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
import D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import Batteries.Tactic.OpenPrivate

/-! The original all-state source inverse and finite three-M scalar channels.
All fields and carriers are the existing ones. This does not prove Jacobi. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticePositiveEnergy LatticeAllStateField LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint MixedIntertwiner
open private sourceGradePairingEquiv from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private ambientCoefficient homogeneous_coefficient liftGrade from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

/-- The GLOBAL original source-valued coefficient. DirectSum.toModule evaluates
only the actual finite graded support already supplied by normalizedCoefficient.
Each summand uses the SAME existing sourceGradePairingEquiv, with no rescaling. -/
def originalI (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (k : ℤ) :
    HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1) →ₗ[ℂ]
      HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1) →ₗ[ℂ] FixedCarrier D :=
  let inverse : FixedRestrictedDual D →ₗ[ℂ] FixedCarrier D :=
    DirectSum.toModule ℂ ℤ (FixedCarrier D) (fun h =>
      (Submodule.inclusion (show fixedGrade D h ≤ fixedSpace D from inf_le_right)).comp
        (sourceGradePairingEquiv D hu hD h).symm.toLinearMap)
  { toFun := fun u => inverse.comp (normalizedCoefficient D hu k u)
    map_add' := by
      intro u v
      ext w
      simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply]
    map_smul' := by
      intro c u
      ext v
      simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_apply, RingHom.id_apply] }

private theorem normalized_single (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (k : ℤ)
    (u v : HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    normalizedCoefficient D hu k u v =
      DirectSum.lof ℂ ℤ (fun h => Module.Dual ℂ (fixedGrade D h))
        ((H : ℤ)+(K : ℤ)-k-1)
        (normalizedCoefficient D hu k u v ((H : ℤ)+(K : ℤ)-k-1)) := by
  change ambientCoefficient D hu k u.val v.val =
    DirectSum.lof ℂ ℤ (fun h => Module.Dual ℂ (fixedGrade D h))
      ((H : ℤ)+(K : ℤ)-k-1)
      (ambientCoefficient D hu k u.val v.val ((H : ℤ)+(K : ℤ)-k-1))
  simp only [homogeneous_coefficient D hu h24 H K k u.val v.val huH hvK]
  simp [liftGrade, DirectSum.lof_eq_of, DirectSum.of_apply]

/-- Homogeneous realization of the global all-state coefficient in the precise
inverse used by OriginalFourMContraction. -/
theorem originalI_homogeneous (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k : ℤ)
    (u v : HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    originalI D hu hD k u v =
      Submodule.inclusion (show fixedGrade D ((H : ℤ)+(K : ℤ)-k-1) ≤ fixedSpace D
        from inf_le_right)
        ((sourceGradePairingEquiv D hu hD ((H : ℤ)+(K : ℤ)-k-1)).symm
          (normalizedCoefficient D hu k u v ((H : ℤ)+(K : ℤ)-k-1))) := by
  change DirectSum.toModule ℂ ℤ (FixedCarrier D) _ (normalizedCoefficient D hu k u v) = _
  conv_lhs => rw [normalized_single D hu h24 H K k u v huH hvK, DirectSum.toModule_lof]
  rfl

/-- The current original cutoff, for every actual input, survives the SAME
finite graded inverse. This is consumed to bound the all-state j-sums below. -/
theorem originalI_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (u v : HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1)) (k : ℤ)
    (hk : (ActualEnergyRestrictedDual.maxOddWeight D hu u.val : ℤ)+
      (ActualEnergyRestrictedDual.maxOddWeight D hu v.val : ℤ)+3 < k) :
    originalI D hu hD k u v = 0 := by
  change DirectSum.toModule ℂ ℤ (FixedCarrier D) _ (normalizedCoefficient D hu k u v) = 0
  rw [normalizedCoefficient_truncation D hu hD u v k hk, map_zero]

private theorem originalI_sharp (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k : ℤ)
    (u v : HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hk : (H : ℤ)+(K : ℤ)-1 < k) : originalI D hu hD k u v = 0 := by
  change DirectSum.toModule ℂ ℤ (FixedCarrier D) _ (normalizedCoefficient D hu k u v) = 0
  rw [normalizedCoefficient_homogeneous_truncation D hu hD h24 H K k u v huH hvK hk,
    map_zero]

private def jacobiLeftTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) (j : ℕ) : paritySpace D hu (-1) :=
  Ring.choose (m : ℂ) j •
    mixedMode D hu (m+n-(j : ℤ)) (originalI D hu hD (r+(j : ℤ)) u v) w

private def jacobiFirstTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) (j : ℕ) : paritySpace D hu (-1) :=
  ((-1 : ℂ)^(j : ℤ) * Ring.choose (r : ℂ) j) •
    originalRightCoefficient D hu (m+r-(j : ℤ)) u (originalI D hu hD (n+(j : ℤ)) v w)

private def jacobiSecondTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) (j : ℕ) : paritySpace D hu (-1) :=
  ((-1 : ℂ)^((j : ℤ)+r) * Ring.choose (r : ℂ) j) •
    originalRightCoefficient D hu (n+r-(j : ℤ)) v (originalI D hu hD (m+(j : ℤ)) u w)

/-- The original, all-state, all-integer bosonic three-M coefficient law.
This is only a proposition naming the target; no instance of it is assumed
or proved. identityK above/below is independently defined by explicit kernels. -/
def originalJacobi (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) : Prop :=
  (∑ᶠ j : ℕ, jacobiLeftTerm D hu hD m n r u v w j) =
    (∑ᶠ j : ℕ, jacobiFirstTerm D hu hD m n r u v w j) -
    (∑ᶠ j : ℕ, jacobiSecondTerm D hu hD m n r u v w j)

private theorem originalI_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a b : paritySpace D hu (-1)) (s : ℤ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → originalI D hu hD (s+(j : ℤ)) a b = 0 := by
  let cutoff : ℤ := (ActualEnergyRestrictedDual.maxOddWeight D hu a.val : ℤ)+
    (ActualEnergyRestrictedDual.maxOddWeight D hu b.val : ℤ)+3
  refine ⟨(cutoff+1-s).toNat, ?_⟩
  intro j hj
  apply originalI_truncation
  have bound : cutoff+1-s ≤ ((cutoff+1-s).toNat : ℤ) := Int.self_le_toNat _
  dsimp only [cutoff] at *
  omega

/-- The actual iterate channel is statewise finite on ALL original inputs. -/
theorem original_jacobi_left_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (jacobiLeftTerm D hu hD m n r u v w) := by
  obtain ⟨J, hJ⟩ := originalI_tail D hu hD u v r
  apply (Finset.range J).finite_toSet.subset
  intro j hj
  by_contra outside
  have bound : J ≤ j := by simpa using outside
  exact hj (by simp [jacobiLeftTerm, hJ j bound])

/-- The first actual right channel is statewise finite on ALL original inputs. -/
theorem original_jacobi_first_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (jacobiFirstTerm D hu hD m n r u v w) := by
  obtain ⟨J, hJ⟩ := originalI_tail D hu hD v w n
  apply (Finset.range J).finite_toSet.subset
  intro j hj
  by_contra outside
  have bound : J ≤ j := by simpa using outside
  exact hj (by simp [jacobiFirstTerm, hJ j bound])

/-- The second actual right channel is statewise finite on ALL original inputs. -/
theorem original_jacobi_second_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (jacobiSecondTerm D hu hD m n r u v w) := by
  obtain ⟨J, hJ⟩ := originalI_tail D hu hD u w m
  apply (Finset.range J).finite_toSet.subset
  intro j hj
  by_contra outside
  have bound : J ≤ j := by simpa using outside
  exact hj (by simp [jacobiSecondTerm, hJ j bound])

/-- Sharp j cutoffs for the genuine original law, at arbitrary integer modes. -/
theorem original_jacobi_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val) :
    originalJacobi D hu hD m n r u v w ↔
      (∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
        jacobiLeftTerm D hu hD m n r u v w j) =
      (∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
        jacobiFirstTerm D hu hD m n r u v w j) -
      (∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
        jacobiSecondTerm D hu hD m n r u v w j) := by
  have left : Function.support (jacobiLeftTerm D hu hD m n r u v w) ⊆
      (Finset.range ((H : ℤ)+(K : ℤ)-r).toNat : Set ℕ) := by
    intro j hj
    by_contra outside
    have lower : ((H : ℤ)+(K : ℤ)-r).toNat ≤ j := by simpa using outside
    have bound : (H : ℤ)+(K : ℤ)-r ≤ (((H : ℤ)+(K : ℤ)-r).toNat : ℤ) := Int.self_le_toNat _
    have zero := originalI_sharp D hu hD h24 H K (r+(j : ℤ)) u v huH hvK (by omega)
    exact hj (by simp [jacobiLeftTerm, zero])
  have first : Function.support (jacobiFirstTerm D hu hD m n r u v w) ⊆
      (Finset.range ((K : ℤ)+(L : ℤ)-n).toNat : Set ℕ) := by
    intro j hj
    by_contra outside
    have lower : ((K : ℤ)+(L : ℤ)-n).toNat ≤ j := by simpa using outside
    have bound : (K : ℤ)+(L : ℤ)-n ≤ (((K : ℤ)+(L : ℤ)-n).toNat : ℤ) := Int.self_le_toNat _
    have zero := originalI_sharp D hu hD h24 K L (n+(j : ℤ)) v w hvK hwL (by omega)
    exact hj (by simp [jacobiFirstTerm, zero])
  have second : Function.support (jacobiSecondTerm D hu hD m n r u v w) ⊆
      (Finset.range ((H : ℤ)+(L : ℤ)-m).toNat : Set ℕ) := by
    intro j hj
    by_contra outside
    have lower : ((H : ℤ)+(L : ℤ)-m).toNat ≤ j := by simpa using outside
    have bound : (H : ℤ)+(L : ℤ)-m ≤ (((H : ℤ)+(L : ℤ)-m).toNat : ℤ) := Int.self_le_toNat _
    have zero := originalI_sharp D hu hD h24 H L (m+(j : ℤ)) u w huH hwL (by omega)
    exact hj (by simp [jacobiSecondTerm, zero])
  unfold originalJacobi
  rw [finsum_eq_sum_of_support_subset _ left,
    finsum_eq_sum_of_support_subset _ first, finsum_eq_sum_of_support_subset _ second]

/-- The exact N < 2 branch vanishes on the ORIGINAL negative parity module.
The physical rank/16 ground is not substituted for that module. -/
theorem original_jacobi_below_two (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val)
    (hN : (H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-2 < 2) :
    originalJacobi D hu hD m n r u v w := by
  have leftZero : jacobiLeftTerm D hu hD m n r u v w = 0 := by
    funext j
    let a := originalI D hu hD (r+(j : ℤ)) u v
    let h : ℤ := (H : ℤ)+(K : ℤ)-(r+(j : ℤ))-1
    have ha : a.val ∈ grade D h := by
      dsimp only [a]
      rw [originalI_homogeneous D hu hD h24 H K _ u v huH hvK]
      exact ((sourceGradePairingEquiv D hu hD h).symm
        (normalizedCoefficient D hu (r+(j : ℤ)) u v h)).property.1
    have negative : (L : ℤ)+h-(m+n-(j : ℤ))-1 < 2 := by dsimp [h]; omega
    have right := original_right_skew_finite D hu h24 L h (m+n-(j : ℤ)) a ha w hwL 0
    dsimp only at right
    have rawZero := (right.2.1 negative).1 0
    change mixedMode D hu ((m+n-(j : ℤ))+(0 : ℤ)) a w = 0 at rawZero
    simp only [add_zero] at rawZero
    change Ring.choose (m : ℂ) j • mixedMode D hu (m+n-(j : ℤ)) a w = 0
    rw [rawZero, smul_zero]
  have firstZero : jacobiFirstTerm D hu hD m n r u v w = 0 := by
    funext j
    let a := originalI D hu hD (n+(j : ℤ)) v w
    let h : ℤ := (K : ℤ)+(L : ℤ)-(n+(j : ℤ))-1
    have ha : a.val ∈ grade D h := by
      dsimp only [a]
      rw [originalI_homogeneous D hu hD h24 K L _ v w hvK hwL]
      exact ((sourceGradePairingEquiv D hu hD h).symm
        (normalizedCoefficient D hu (n+(j : ℤ)) v w h)).property.1
    have negative : (H : ℤ)+h-(m+r-(j : ℤ))-1 < 2 := by dsimp [h]; omega
    have right := original_right_skew_finite D hu h24 H h (m+r-(j : ℤ)) a ha u huH 0
    dsimp only at right
    have zero := (right.2.1 negative).2
    change _ • originalRightCoefficient D hu (m+r-(j : ℤ)) u a = 0
    rw [zero, smul_zero]
  have secondZero : jacobiSecondTerm D hu hD m n r u v w = 0 := by
    funext j
    let a := originalI D hu hD (m+(j : ℤ)) u w
    let h : ℤ := (H : ℤ)+(L : ℤ)-(m+(j : ℤ))-1
    have ha : a.val ∈ grade D h := by
      dsimp only [a]
      rw [originalI_homogeneous D hu hD h24 H L _ u w huH hwL]
      exact ((sourceGradePairingEquiv D hu hD h).symm
        (normalizedCoefficient D hu (m+(j : ℤ)) u w h)).property.1
    have negative : (K : ℤ)+h-(n+r-(j : ℤ))-1 < 2 := by dsimp [h]; omega
    have right := original_right_skew_finite D hu h24 K h (n+r-(j : ℤ)) a ha v hvK 0
    dsimp only at right
    have zero := (right.2.1 negative).2
    change _ • originalRightCoefficient D hu (n+r-(j : ℤ)) v a = 0
    rw [zero, smul_zero]
  unfold originalJacobi
  rw [leftZero, firstZero, secondZero]
  simp

/-- Scalar on the exact global original coefficient, with no new source duality. -/
def fourMScalar (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (k t : ℤ) (u v : HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1))
    (w d : ActualTensor D hu) : ℂ :=
  actualForm D hu d ((correctedField D hu (originalI D hu hD k u v).val).coeff (-2*t-2) w)

private theorem fourMScalar_below_two (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (k t : ℤ) (u v w : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val)
    (low : (H : ℤ)+(K : ℤ)+(L : ℤ)-k-t-2 < 2) (d : ActualTensor D hu) :
    fourMScalar D hu hD k t u v w.val d = 0 := by
  let a := originalI D hu hD k u v
  let h : ℤ := (H : ℤ)+(K : ℤ)-k-1
  have ha : a.val ∈ grade D h := by
    dsimp only [a]
    rw [originalI_homogeneous D hu hD h24 H K k u v huH hvK]
    exact ((sourceGradePairingEquiv D hu hD h).symm
      (normalizedCoefficient D hu k u v h)).property.1
  have negative : (L : ℤ)+h-t-1 < 2 := by dsimp [h]; omega
  have right := original_right_skew_finite D hu h24 L h t a ha w hwL d
  have zero := (right.2.1 negative).1 0
  change mixedMode D hu (t+(0 : ℤ)) a w = 0 at zero
  rw [add_zero] at zero
  have paired := congrArg (fun q : paritySpace D hu (-1) => actualForm D hu d q.val) zero
  change actualForm D hu d
    ((correctedField D hu a.val).coeff (2*(-t-1)) w.val) = _ at paired
  simpa only [fourMScalar, a, show 2*(-t-1) = -2*t-2 by ring,
    Submodule.coe_zero, map_zero] using paired

set_option maxHeartbeats 4000000 in
/-- S: actual original Jacobi scalarization, including all integer phases,
the THREE sharp j cutoffs, and the COMMON ell < N-1 cutoff. Detectors range
over the full ActualTensor in the FIRST pairing slot. This is an equivalence
with an explicit scalar obligation, not a proof of that obligation. -/
theorem original_jacobi_scalar_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val) :
    originalJacobi D hu hD m n r u v w ↔
    ∀ d : ActualTensor D hu,
      (∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
        Ring.choose (m : ℂ) j * fourMScalar D hu hD (r+(j : ℤ)) (m+n-(j : ℤ)) u v w.val d) =
      (∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
        ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
          Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
            fourMScalar D hu hD (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ)) v w u.val
              ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d)) -
      (∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
        ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
          Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
            fourMScalar D hu hD (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ)) u w v.val
              ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d)) := by
  by_cases hN : 2 ≤ (H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-2
  ·
    classical
    let N : ℤ := (H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-2
    have rho (a : FixedCarrier D) (s : ℤ) (x : paritySpace D hu (-1))
        (d : ActualTensor D hu) : actualForm D hu d (mixedMode D hu s a x).val =
        actualForm D hu d ((correctedField D hu a.val).coeff (-2*s-2) x.val) := by
      change actualForm D hu d ((correctedField D hu a.val).coeff (2*(-s-1)) x.val) = _
      rw [show 2*(-s-1) = -2*s-2 by ring]
    have rhoSlice (a : FixedCarrier D) (s : ℤ) (x : paritySpace D hu (-1))
        (d : ActualTensor D hu) :
        actualForm D hu d (((fixedParitySlice D hu (-1) a)[[s]]) x).val =
        actualForm D hu d ((correctedField D hu a.val).coeff (-2*s-2) x.val) := rho a s x d
    have firstTransport (d : ActualTensor D hu) (j : ℕ) :
        ((-1 : ℂ)^(j : ℤ) * Ring.choose (r : ℂ) j) *
          actualForm D hu d (originalRightCoefficient D hu (m+r-(j : ℤ)) u
            (originalI D hu hD (n+(j : ℤ)) v w)).val =
        ∑ ell ∈ Finset.range (N-1).toNat,
          Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
            fourMScalar D hu hD (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ)) v w u.val
              ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d) := by
      let a := originalI D hu hD (n+(j : ℤ)) v w
      let h : ℤ := (K : ℤ)+(L : ℤ)-(n+(j : ℤ))-1
      have ha : a.val ∈ grade D h := by
        dsimp only [a]
        rw [originalI_homogeneous D hu hD h24 K L _ v w hvK hwL]
        exact ((sourceGradePairingEquiv D hu hD h).symm
          (normalizedCoefficient D hu (n+(j : ℤ)) v w h)).property.1
      have common : (H : ℤ)+h-(m+r-(j : ℤ))-1 = N := by dsimp [h, N]; ring
      have right := original_right_skew_finite D hu h24 H h (m+r-(j : ℤ)) a ha u huH d
      dsimp only at right
      have positive : 2 ≤ (H : ℤ)+h-(m+r-(j : ℤ))-1 := by rw [common]; exact hN
      have transported := (right.2.2 positive).2.2.2.2.1 m r j rfl
      simpa only [common, rhoSlice, fourMScalar, a] using transported
    have secondTransport (d : ActualTensor D hu) (j : ℕ) :
        ((-1 : ℂ)^((j : ℤ)+r) * Ring.choose (r : ℂ) j) *
          actualForm D hu d (originalRightCoefficient D hu (n+r-(j : ℤ)) v
            (originalI D hu hD (m+(j : ℤ)) u w)).val =
        ∑ ell ∈ Finset.range (N-1).toNat,
          Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
            fourMScalar D hu hD (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ)) u w v.val
              ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d) := by
      let a := originalI D hu hD (m+(j : ℤ)) u w
      let h : ℤ := (H : ℤ)+(L : ℤ)-(m+(j : ℤ))-1
      have ha : a.val ∈ grade D h := by
        dsimp only [a]
        rw [originalI_homogeneous D hu hD h24 H L _ u w huH hwL]
        exact ((sourceGradePairingEquiv D hu hD h).symm
          (normalizedCoefficient D hu (m+(j : ℤ)) u w h)).property.1
      have common : (K : ℤ)+h-(n+r-(j : ℤ))-1 = N := by dsimp [h, N]; ring
      have right := original_right_skew_finite D hu h24 K h (n+r-(j : ℤ)) a ha v hvK d
      dsimp only at right
      have positive : 2 ≤ (K : ℤ)+h-(n+r-(j : ℤ))-1 := by rw [common]; exact hN
      have transported := (right.2.2 positive).2.2.2.2.2 n r j rfl
      simpa only [common, rhoSlice, fourMScalar, a] using transported
    let leftState := ∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
      jacobiLeftTerm D hu hD m n r u v w j
    let firstState := ∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
      jacobiFirstTerm D hu hD m n r u v w j
    let secondState := ∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
      jacobiSecondTerm D hu hD m n r u v w j
    let ev (d : ActualTensor D hu) : paritySpace D hu (-1) →ₗ[ℂ] ℂ :=
      (actualForm D hu d).comp (paritySpace D hu (-1)).subtype
    have leftEval (d : ActualTensor D hu) :
        ev d leftState = ∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
          Ring.choose (m : ℂ) j * fourMScalar D hu hD (r+(j : ℤ)) (m+n-(j : ℤ)) u v w.val d := by
      simp only [leftState, jacobiLeftTerm, map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      change _ * actualForm D hu d (mixedMode D hu _ _ w).val = _
      rw [rho]
      rfl
    have firstEval (d : ActualTensor D hu) :
        ev d firstState = ∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
          ∑ ell ∈ Finset.range (N-1).toNat,
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
              fourMScalar D hu hD (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ)) v w u.val
                ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d) := by
      simp only [firstState, jacobiFirstTerm, map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      exact firstTransport d j
    have secondEval (d : ActualTensor D hu) :
        ev d secondState = ∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
          ∑ ell ∈ Finset.range (N-1).toNat,
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
              fourMScalar D hu hD (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ)) u w v.val
                ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d) := by
      simp only [secondState, jacobiSecondTerm, map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      exact secondTransport d j
    rw [original_jacobi_finite D hu hD h24 H K L m n r u v w huH hvK hwL]
    change (leftState = firstState-secondState) ↔ _
    have cutoff : N-1 = (H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3 := by dsimp [N]; ring
    constructor
    · intro vectors d
      have h := congrArg (ev d) vectors
      rw [map_sub, leftEval, firstEval, secondEval, cutoff] at h
      exact h
    · intro scalars
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply (actualForm_nondegenerate D hu).2
      intro d
      have h := scalars d
      rw [← cutoff, ← leftEval, ← firstEval, ← secondEval] at h
      change actualForm D hu d (leftState.val - (firstState-secondState).val) = 0
      simpa only [ev, LinearMap.comp_apply, map_sub, Submodule.coe_sub, Submodule.subtype_apply] using sub_eq_zero.mpr h

  · have low : (H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-2 < 2 := by omega
    constructor
    · intro _ d
      have cutoff : ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat = 0 :=
        Int.toNat_eq_zero.mpr (by omega)
      simp only [cutoff, Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero, sub_zero]
      apply Finset.sum_eq_zero
      intro j hj
      rw [fourMScalar_below_two D hu hD h24 H K L (r+(j : ℤ)) (m+n-(j : ℤ))
        u v w huH hvK hwL (by omega) d, mul_zero]
    · intro _
      exact original_jacobi_below_two D hu hD h24 H K L m n r u v w huH hvK hwL low


end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

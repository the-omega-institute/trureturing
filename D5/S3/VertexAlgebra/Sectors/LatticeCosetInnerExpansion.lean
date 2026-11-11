/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native compressed fields retain the actual source multiplication recursion. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCreationSeparation

/-! Compression uses the literal native fields, integral external charges and
original epsilon. Native statewise truncation supplies the Laurent bound.
The source recurrence is the native normalMinusOne multiplication recurrence
of Bakalov--Kac lattice fields, math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetInnerExpansion

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraCurrents FieldNormalProduct
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeCosetFieldSeparation LatticeCosetCreationSeparation LatticeDiscriminantTheta
open MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private injection_single projection_single from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private mixedState_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
open private high_modes_finite from D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation
open private multiplication_recursion from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- The actual compressed field, with truncation inherited by composition. -/
def compressedField (a d : Fin e → ℤ) (u : Carrier D) : VertexOperator ℂ (Carrier D) :=
  VertexOperator.of_coeff (fun k =>
    (projection D B C hC hCe (a+d)).comp
      ((HVertexOperator.coeff
        (Y (ambient D e B C hC hCe) (injection D B C hC hCe a u)) k).comp
          (injection D B C hC hCe d))) (by
    intro g
    let F := Y (ambient D e B C hC hCe) (injection D B C hC hCe a u)
    let v := injection D B C hC hCe d g
    refine ⟨((HahnModule.of ℂ).symm (F v)).order, ?_⟩
    intro k hk
    by_contra hn
    have hz : HVertexOperator.coeff F k v = 0 :=
      VertexOperator.coeff_eq_zero_of_lt_order F k v (by omega)
    exact hk (by
      change projection D B C hC hCe (a+d) (HVertexOperator.coeff F k v) = 0
      rw [hz, map_zero]))

private theorem compressedField_modes (a d : Fin e → ℤ) (u g : Carrier D) (m : ℤ) :
    ((compressedField D B C hC hCe a d u)[[m]]) g =
      compressed D B C hC hCe a d u m g := by
  rw [compressedField, VertexOperator.ncoeff_of_coeff]
  rfl

private def current (d : Fin e → ℤ) (i : Fin D.rank) : VertexOperator ℂ (Carrier D) :=
  LatticeDualCosetModule.action D (Matrix.mulVec B d)
    (Finsupp.single (0 : Charge D) (X (i,0)))

private theorem projection_current_modes (hD : (gramReal D).PosDef)
    (d : Fin e → ℤ) (i : Fin D.rank) (m : ℤ)
    (v : Carrier (ambient D e B C hC hCe)) :
    projection D B C hC hCe d
        (neutralMode (ambient D e B C hC hCe) (i.castAdd e) m v) =
      ((current D B d i)[[m]]) (projection D B C hC hCe d v) := by
  have he : (projection D B C hC hCe d).comp
      (neutralMode (ambient D e B C hC hCe) (i.castAdd e) m) =
      ((current D B d i)[[m]]).comp (projection D B C hC hCe d) := by
    apply Finsupp.lhom_ext
    intro n f
    simp only [LinearMap.comp_apply, neutralMode, Finsupp.lsum_single,
      Finsupp.lsingle_apply, projection_single]
    by_cases hn : externalCharge D B C hC hCe n = d
    · simp only [hn, ↓reduceIte]
      rw [show ((current D B d i)[[m]]) (Finsupp.single (oldCharge D B C hC hCe n)
          (polynomialProjection D B C hC hCe f)) = _ from
        LatticeDualCosetModule.action_current_coefficients D (Matrix.mulVec B d) i
          (oldCharge D B C hC hCe n) (polynomialProjection D B C hC hCe f) m]
      rw [projection_current_polynomial D B C hC hCe hD, hn]
    · simp [hn]
  exact DFunLike.congr_fun he v

private theorem current_injection_modes (hD : (gramReal D).PosDef)
    (d : Fin e → ℤ) (i : Fin D.rank) (m : ℤ) (g : Carrier D) :
    neutralMode (ambient D e B C hC hCe) (i.castAdd e) m
        (injection D B C hC hCe d g) =
      injection D B C hC hCe d (((current D B d i)[[m]]) g) := by
  have hmix : mixedState D B C hC hCe d (1 : MvPolynomial (Fin e × ℕ) ℂ) =
      injection D B C hC hCe d := by
    apply Finsupp.lhom_ext
    intro n f
    simp [mixedState_single, injection_single]
  simpa only [hmix, current] using current_mixed D B C hC hCe hD i d m g 1

private theorem current_negative (d d' : Fin e → ℤ) (i : Fin D.rank) (m : ℤ)
    (hm : m < 0) : ((current D B d i)[[m]]) = ((current D B d' i)[[m]]) := by
  apply Finsupp.lhom_ext
  intro n f
  simp only [current, LatticeDualCosetModule.action_current_coefficients]
  simp [LatticeDualCosetModule.shiftedCurrentPolynomial, hm]

private theorem derivative_injection (hD : (gramReal D).PosDef)
    (d : Fin e → ℤ) (x : Index D) (m : ℤ) (g : Carrier D) :
    ((dividedDerivative x.2 (neutralField (ambient D e B C hC hCe) (x.1.castAdd e)))[[m]])
        (injection D B C hC hCe d g) =
      injection D B C hC hCe d (((dividedDerivative x.2 (current D B d x.1))[[m]]) g) := by
  change Ring.choose (-m-1+x.2) x.2 •
      HVertexOperator.coeff (neutralField (ambient D e B C hC hCe) (x.1.castAdd e))
        (-m-1+x.2) (injection D B C hC hCe d g) =
    injection D B C hC hCe d (Ring.choose (-m-1+x.2) x.2 •
      HVertexOperator.coeff (current D B d x.1) (-m-1+x.2) g)
  rw [map_zsmul, VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    LatticeSugawaraCurrents.neutralField_ncoeff, current_injection_modes D B C hC hCe hD]

private theorem derivative_negative_projection (hD : (gramReal D).PosDef)
    (d d' : Fin e → ℤ) (x : Index D) (j : ℕ)
    (v : Carrier (ambient D e B C hC hCe)) :
    projection D B C hC hCe d'
        (((dividedDerivative x.2 (neutralField (ambient D e B C hC hCe) (x.1.castAdd e)))
          [[-(j : ℤ)-1]]) v) =
      ((dividedDerivative x.2 (current D B d x.1))[[-(j : ℤ)-1]])
        (projection D B C hC hCe d' v) := by
  change projection D B C hC hCe d' (Ring.choose (-(-(j : ℤ)-1)-1+x.2) x.2 •
      HVertexOperator.coeff (neutralField (ambient D e B C hC hCe) (x.1.castAdd e))
        (-(-(j : ℤ)-1)-1+x.2) v) =
    Ring.choose (-(-(j : ℤ)-1)-1+x.2) x.2 •
      HVertexOperator.coeff (current D B d x.1) (-(-(j : ℤ)-1)-1+x.2)
        (projection D B C hC hCe d' v)
  rw [map_zsmul, VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    LatticeSugawaraCurrents.neutralField_ncoeff, projection_current_modes D B C hC hCe hD,
    current_negative D B d' d x.1 _ (by omega)]

/-- Complete native source multiplication descends to the already truncated
compressed field, with the integral shifted current of the target sector. -/
theorem compressed_multiplication_recursion (hD : (gramReal D).PosDef)
    (a d : Fin e → ℤ) (x : Index D) (n : Charge D) (f : Oscillator D) :
    compressedField D B C hC hCe a d (Finsupp.single n (X x*f)) =
      (normalMinusOne (dividedDerivative x.2 (current D B d x.1))
        (compressedField D B C hC hCe a d (Finsupp.single n f))).1 := by
  have hrec : Y (ambient D e B C hC hCe)
      (injection D B C hC hCe a (Finsupp.single n (X x*f))) =
      (normalMinusOne
        (dividedDerivative x.2 (neutralField (ambient D e B C hC hCe) (x.1.castAdd e)))
        (Y (ambient D e B C hC hCe)
          (injection D B C hC hCe a (Finsupp.single n f)))).1 := by
    rw [injection_single, map_mul]
    have hx : polynomialInjection D B C hC hCe (X x) = X (x.1.castAdd e, x.2) := by
      simp [polynomialInjection]
    rw [hx, injection_single D B C hC hCe a n f]
    exact multiplication_recursion _ _ _ _
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro g
  simp only [VertexOperator.coeff_eq_ncoeff, compressedField_modes]
  change projection D B C hC hCe (a+d)
      (((Y (ambient D e B C hC hCe)
        (injection D B C hC hCe a (Finsupp.single n (X x*f))))[[-k-1]])
          (injection D B C hC hCe d g)) = _
  rw [hrec]
  let A := dividedDerivative x.2 (neutralField (ambient D e B C hC hCe) (x.1.castAdd e))
  let F := Y (ambient D e B C hC hCe) (injection D B C hC hCe a (Finsupp.single n f))
  have mapSum (s : ℕ → Carrier (ambient D e B C hC hCe))
      (hs : Function.HasFiniteSupport s) :
      projection D B C hC hCe (a+d) (∑ᶠ j, s j) =
        ∑ᶠ j, projection D B C hC hCe (a+d) (s j) :=
    (projection D B C hC hCe (a+d)).toAddMonoidHom.map_finsum hs
  rw [(normalMinusOne A F).2, map_add,
    mapSum _ (high_modes_finite F (fun j => ((A)[[-(j : ℤ)-1]])) (-k-1)
      (injection D B C hC hCe d g)),
    mapSum _ (by simpa only [zero_add] using (high_modes_finite A
      (fun j => ((F)[[-k-1-j-1]])) 0 (injection D B C hC hCe d g))),
    (normalMinusOne _ _).2]
  congr 1 <;> apply finsum_congr <;> intro j
  · rw [derivative_negative_projection D B C hC hCe hD d (a+d) x j]
    rfl
  · rw [derivative_injection D B C hC hCe hD]
    rfl

end
end D5.S3.VertexAlgebra.LatticeCosetInnerExpansion

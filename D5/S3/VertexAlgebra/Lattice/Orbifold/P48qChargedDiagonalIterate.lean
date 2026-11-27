/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedDiagonalIterate
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular charged collision coefficients agree with the native ground-state iterate. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qRetainedDiagonalComparison
import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalTransport

/-!
On every finite twisted state, all regular charged collision coefficients
are coefficients of the actual native iterate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators LaurentSeries VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear epsilon)
open P48qTwistedChargeAction (lattice g Momentum)
open P48qCurrentChargedIterate (chargedGround)
open P48qTwistedHeisenberg (mode mode_zero_apply mode_positive_apply mode_negative_apply)
open P48qSignedNormalWord (signedWordCoeff signedWordCoeff_nil insertMode_apply wordTerm)
open P48qJetNormalOrdering (normalOrderedCoeff jetTerm jetTerm_finite)
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil normalWick_step)
open P48qAllJetWickField (nativeField nativePolynomialField nativePolynomialField_monomial
  NativePolynomial NativeIndex Jet allJetField allJetField_coeff allJetCoeff)
open LatticeActualVertexAlgebra (actualVertexAlgebra)
open PowerSeries (coeff)

open private signedWordCoeff_cons from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord
open private evalAt map_normalWick from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeChargedWickFactorization

local notation "shift" => ThirdTwistedChargeAction.shift lattice g

private theorem mode_eq_zero_at (u : Cartan) (m : ℤ) (v : State) (q : Momentum)
    (hq : v q = 0) : mode u m v q = 0 := by
  cases m with
  | negSucc n => simp [mode_negative_apply, hq]
  | ofNat n =>
    cases n with
    | zero => simp [mode_zero_apply, hq]
    | succ n =>
      rw [mode_positive_apply, hq]
      simp

private theorem mode_single (u : Cartan) (m : ℤ) (p : Momentum) (P : Fock) :
    mode u m (Finsupp.single p P) = Finsupp.single p (mode u m (Finsupp.single p P) p) := by
  ext q
  by_cases h : q = p
  · subst q
    simp
  · rw [Finsupp.single_eq_of_ne h, mode_eq_zero_at u m _ q (Finsupp.single_eq_of_ne h)]

private theorem signedWordCoeff_off_momentum (a : Charge lattice) (k : ℤ)
    (word : List (Cartan × ℤ)) (p q : Momentum) (P : Fock) (hq : q ≠ shift a p) :
    signedWordCoeff a k word (Finsupp.single p P) q = 0 := by
  induction word generalizing k P with
  | nil => rw [signedWordCoeff_nil, fieldCoeff_single, Finsupp.single_eq_of_ne hq]
  | cons head tail ih =>
    obtain ⟨u, m⟩ := head
    rw [signedWordCoeff_cons, insertMode_apply]
    split_ifs
    · exact mode_eq_zero_at u m _ q (ih _ _)
    · rw [Module.End.mul_apply, mode_single u m p P]
      exact ih _ _

private theorem normalOrderedCoeff_off_momentum (a : Charge lattice) (k : ℤ) (jets : List Jet)
    (p q : Momentum) (P : Fock) (hq : q ≠ shift a p) :
    normalOrderedCoeff a k jets (Finsupp.single p P) q = 0 := by
  change (Finsupp.lapply q : State →ₗ[ℂ] Fock).toAddMonoidHom
    (∑ᶠ i, jetTerm a k jets i (Finsupp.single p P)) = 0
  rw [(Finsupp.lapply q : State →ₗ[ℂ] Fock).toAddMonoidHom.map_finsum
    (jetTerm_finite a k jets (Finsupp.single p P))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  change (jetTerm a k jets i (Finsupp.single p P)) q = 0
  simp only [jetTerm, wordTerm, LinearMap.smul_apply, Finsupp.smul_apply,
    signedWordCoeff_off_momentum _ _ _ _ _ _ hq, smul_zero]

private theorem normalWick_zero (A : Matrix Jet Jet ℂ) (μ : Jet → ℂ)
    (pending kept : List Jet) : normalWick A μ (fun _ => (0 : Fock)) pending kept = 0 := by
  cases pending with
  | nil => rw [normalWick_nil]
  | cons x xs =>
    simp only [normalWick_step, normalWick_zero A μ xs (kept ++ [x]),
      normalWick_zero A μ xs kept, normalWick_zero A μ (xs.eraseIdx _) kept, smul_zero,
      Finset.sum_const_zero, add_zero]
termination_by pending.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private theorem allJetField_off_momentum (a : Charge lattice) (k : ℤ) (jets : List Jet)
    (p q : Momentum) (P : Fock) (hq : q ≠ shift a p) :
    HVertexOperator.coeff (allJetField a jets) k (Finsupp.single p P) q = 0 := by
  rw [allJetField_coeff]
  change evalAt (Finsupp.single p P) q (allJetCoeff a k jets) = 0
  rw [allJetCoeff, normalWickWord, map_normalWick]
  have hleaf : (fun kept => evalAt (Finsupp.single p P) q
      (normalOrderedCoeff a (k + P48qAllJetWickField.leafShift jets kept) kept)) =
      fun _ => (0 : Fock) := by
    funext kept
    exact normalOrderedCoeff_off_momentum a _ kept p q P hq
  rw [hleaf, normalWick_zero]

private theorem nativePolynomialField_off_momentum (a : Charge lattice) (k : ℤ)
    (Q : NativePolynomial) (p q : Momentum) (P : Fock) (hq : q ≠ shift a p) :
    HVertexOperator.coeff (nativePolynomialField a Q) k (Finsupp.single p P) q = 0 := by
  let L : NativePolynomial →ₗ[ℂ] Fock :=
    (evalAt (Finsupp.single p P) q).comp
      ((LinearMap.proj k).comp ((HVertexOperator.coeff (R := ℂ)).comp
        (nativePolynomialField a)))
  have hL : L = 0 := by
    apply (MvPolynomial.basisMonomials NativeIndex ℂ).ext
    intro e
    change HVertexOperator.coeff
      (nativePolynomialField a (MvPolynomial.monomial e 1)) k (Finsupp.single p P) q = 0
    rw [nativePolynomialField_monomial]
    exact allJetField_off_momentum a k _ p q P hq
  exact DFunLike.congr_fun hL Q

/-- The actual untwisted ground-field coefficients, with the collision power
restored in the Laurent index. In negative normalized degree the source coefficient vanishes. -/
theorem untwistedChargedGround_coeff (a b : Charge lattice) (r : ℤ) :
    HVertexOperator.coeff ((actualVertexAlgebra lattice).stateField (chargedGround a))
      (bilinear lattice a b + r) (chargedGround b) =
      epsilon lattice a b • Finsupp.single (a + b)
        (LatticeGeneratingFieldLocality.creationCoeff lattice a r) := by
  change HVertexOperator.coeff (LatticeAllStateField.Y lattice (Finsupp.single a 1))
    (bilinear lattice a b + r) (Finsupp.single b 1) = _
  rw [LatticeAllStateField.stateField_ground]
  change LatticeGeneratingFieldLocality.rawCoeff lattice a (bilinear lattice a b + r)
    (Finsupp.single b 1) = _
  rw [LatticeActualOrderedProducts.raw_ground, add_sub_cancel_left]

/-- Coefficients of the full regular diagonal expansion on every twisted state.
The source coefficient is taken in the untwisted lattice state-field map.
Writing the collision variable as the right physical coordinate times `t`
contributes `3d` to the cover degree, after the collision power is removed. -/
theorem chargedDiagonalRegular_coeff_eq_nativeField (a b : Charge lattice) (v : State)
    (h : ℤ) (d : ℕ) :
    (∑ p ∈ v.support, Finsupp.single (shift (a + b) p)
      (coeff d ((chargedDiagonalRegular fixedDualBases a b p (v p)).coeff
        (h - momentumExponent (a + b) p)))) =
      HVertexOperator.coeff (nativeField
        (HVertexOperator.coeff ((actualVertexAlgebra lattice).stateField (chargedGround a))
          (bilinear lattice a b + (d : ℤ)) (chargedGround b))) (h - 3 * (d : ℤ)) v := by
  classical
  let Q := coeff d (LatticeGeneratingFieldLocality.creationExponential lattice a)
  let k := h - 3 * (d : ℤ)
  have hc : LatticeGeneratingFieldLocality.creationCoeff lattice a (d : ℤ) = Q := by
    simp [LatticeGeneratingFieldLocality.creationCoeff, Q]
  rw [untwistedChargedGround_coeff, hc, map_smul]
  have hf : nativeField (Finsupp.single (a + b) Q) = nativePolynomialField (a + b) Q := by
    rw [nativeField, Finsupp.lsum_single]
  rw [hf, map_smul, Pi.smul_apply, LinearMap.smul_apply]
  calc
    _ = ∑ p ∈ v.support, epsilon lattice a b •
        HVertexOperator.coeff (nativePolynomialField (a + b) Q) k (Finsupp.single p (v p)) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finsupp.ext
      intro q
      by_cases hq : q = shift (a + b) p
      · subst q
        simpa only [Finsupp.single_eq_same, Finsupp.smul_apply, Q, k] using
          chargedDiagonalRegular_coeff_eq_nativeIterate a b h p (v p) d
      · rw [Finsupp.single_eq_of_ne hq, Finsupp.smul_apply,
          nativePolynomialField_off_momentum _ _ _ _ _ _ hq, smul_zero]
    _ = _ := by
      have hv : (∑ p ∈ v.support, Finsupp.single p (v p)) = v := Finsupp.sum_single v
      rw [← Finset.smul_sum, ← map_sum, hv]

open private finiteCoverSlices diagonalCoverReadout_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalTransport
open private orbitExponent clearedOrderedProduct_single from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality
open private mapScalarToFock from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision

local notation "Xc" => (coverMonomial 1 0 (1 : Fock))
local notation "Yc" => (coverMonomial 0 1 (1 : Fock))
local notation "ιF" => HahnSeries.ofPowerSeries ℤ Fock

private theorem coeff_collision_shift (S : PowerSeries Fock) (m : ℕ) (r : ℤ) :
    (ιF (mapScalarToFock ((PowerSeries.X : PowerSeries ℂ) ^ m) * S)).coeff r =
      (ιF S).coeff (r - (m : ℤ)) := by
  rw [map_mul, map_pow, mapScalarToFock, PowerSeries.map_X, map_pow,
    HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one,
    HahnSeries.coeff_single_mul, one_mul]

/-- Charged-generator weak associativity on the physical cover, in coefficients
of the common numerator. Write `x³ = z`, `y³ = w` and `t = (z-w)/w`, using
the branch `x = y (1+t)^(1/3)`. The left side substitutes into the actual
ordered product cleared by `(z-w)^N`. The right side reads the actual
iterated field at source degree `r`. Multiplication by `(z-w)^N` and
conversion from `z-w` to `t` give degree `r+N` in `t` and add
`3(r+N)` to the right cover degree. This equality includes every Laurent
degree and every twisted input state. -/
theorem chargedGround_weakAssociativity_cover_coeff (a b : Charge lattice) (v : State)
    (q : Momentum) (N : ℕ) (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j)
    (h r : ℤ) :
    (ιF (diagonalCoverReadout ((Xc ^ 3 - Yc ^ 3) ^ N *
      orderedChargedProduct fixedDualBases a b v q) h)).coeff (r + (N : ℤ)) =
      HVertexOperator.coeff (nativeField
        (HVertexOperator.coeff ((actualVertexAlgebra lattice).stateField (chargedGround a))
          r (chargedGround b))) (h - 3 * (r + (N : ℤ))) v q := by
  classical
  let A : Momentum → CoverSeries Fock := fun p =>
    (Xc ^ 3 - Yc ^ 3) ^ N *
      orderedChargedProduct fixedDualBases a b (Finsupp.single p (v p)) q
  have hA (p : Momentum) (_ : p ∈ v.support) : finiteCoverSlices (A p) :=
    fun k => clearedOrderedChargedProduct_finiteSlice fixedDualBases a b p q (v p) N hN k
  have hsum : (Xc ^ 3 - Yc ^ 3) ^ N * orderedChargedProduct fixedDualBases a b v q =
      ∑ p ∈ v.support, A p := by
    have hv : (∑ p ∈ v.support, Finsupp.single p (v p)) = v := Finsupp.sum_single v
    conv_lhs => rw [← hv]
    simp only [A, map_sum, Finset.sum_apply', Finset.mul_sum]
  rw [hsum, diagonalCoverReadout_sum v.support A hA, map_sum, HahnSeries.coeff_sum]
  let e := bilinear lattice a b
  let k := h - 3 * ((N : ℤ) + e)
  have he : 0 ≤ (N : ℤ) + e := hN 0 (by decide)
  let m := ((N : ℤ) + e).toNat
  have hcast : (m : ℤ) = (N : ℤ) + e := Int.toNat_of_nonneg he
  have hsingle (p : Momentum) :
      (ιF (diagonalCoverReadout (A p) h)).coeff (r + (N : ℤ)) =
      (Finsupp.single (shift (a + b) p)
        ((ιF ((chargedDiagonalRegular fixedDualBases a b p (v p)).coeff
          (k - momentumExponent (a + b) p))).coeff (r - e)) : State) q := by
    by_cases hp : q = shift (a + b) p
    · subst q
      dsimp only [A]
      rw [clearedOrderedChargedProduct_diagonalRegular fixedDualBases a b p (v p) N hN,
        coeff_collision_shift, Finsupp.single_eq_same]
      have hdegree : r + (N : ℤ) - (m : ℤ) = r - e := by omega
      have hcover : h - (momentumExponent (a + b) p + 3 * ((N : ℤ) + e)) =
          k - momentumExponent (a + b) p := by dsimp [k]; omega
      rw [hdegree, hcover]
    · dsimp only [A]
      rw [Finsupp.single_eq_of_ne hp,
        clearedOrderedProduct_single fixedDualBases a b p q (v p) N hN,
        ite_eq_right (Ne.symm hp)]
      simp [diagonalCoverReadout]
  simp_rw [hsingle]
  by_cases hr : r < e
  · simp only [PowerSeries.coeff_coe, show r - e < 0 by omega, ite_true, Finsupp.single_zero,
      Finsupp.zero_apply, Finset.sum_const_zero]
    have hg : HVertexOperator.coeff ((actualVertexAlgebra lattice).stateField (chargedGround a))
        r (chargedGround b) = 0 := by
      conv_lhs => rw [show r = bilinear lattice a b + (r - e) by omega]
      rw [untwistedChargedGround_coeff]
      simp [LatticeGeneratingFieldLocality.creationCoeff, show r - e < 0 by omega]
    rw [hg, map_zero, map_zero, Pi.zero_apply, LinearMap.zero_apply, Finsupp.zero_apply]
  · let d := (r - e).toNat
    have hd : (d : ℤ) = r - e := Int.toNat_of_nonneg (by omega)
    have hcoeff (S : PowerSeries Fock) : (ιF S).coeff (r - e) = coeff d S := by
      rw [← hd, HahnSeries.ofPowerSeries_apply_coeff]
    simp_rw [hcoeff]
    have hc := congrArg (fun w : State => w q)
      (chargedDiagonalRegular_coeff_eq_nativeField a b v k d)
    simp only [Finset.sum_apply'] at hc
    have hs : bilinear lattice a b + (d : ℤ) = r := by omega
    have ht : k - 3 * (d : ℤ) = h - 3 * (r + (N : ℤ)) := by dsimp [k]; omega
    rw [hs, ht] at hc
    exact hc

/-- The charged-generator iterate after writing the collision variable as
`y³ t`, at fixed total cover degree `h` and output momentum `q`. -/
def chargedGroundIterateLaurent (a b : Charge lattice) (v : State) (q : Momentum) (h : ℤ) :
    LaurentSeries Fock where
  coeff r := HVertexOperator.coeff (nativeField
    (HVertexOperator.coeff ((actualVertexAlgebra lattice).stateField (chargedGround a))
      r (chargedGround b))) (h - 3 * r) v q
  isPWO_support' := by
    refine (BddBelow.isWF ⟨bilinear lattice a b, ?_⟩).isPWO
    intro r hr
    by_contra hn
    apply hr
    have hlt : r - bilinear lattice a b < 0 := by omega
    have hzero : HVertexOperator.coeff
        ((actualVertexAlgebra lattice).stateField (chargedGround a)) r (chargedGround b) = 0 := by
      conv_lhs => rw [show r = bilinear lattice a b + (r - bilinear lattice a b) by omega]
      rw [untwistedChargedGround_coeff]
      simp [LatticeGeneratingFieldLocality.creationCoeff, hlt]
    change HVertexOperator.coeff (nativeField
      (HVertexOperator.coeff ((actualVertexAlgebra lattice).stateField (chargedGround a))
        r (chargedGround b))) (h - 3 * r) v q = 0
    simp only [hzero, map_zero, Pi.zero_apply, LinearMap.zero_apply, Finsupp.zero_apply]

/-- Laurent collision identity for the two charged generators on every twisted
state. The factor `t⁻ᴺ` and the cover shift `h+3N` remove the single physical
clearing factor `(z-w)^N = y^(3N) t^N`. -/
theorem chargedGround_weakAssociativity_laurent (a b : Charge lattice) (v : State)
    (q : Momentum) (N : ℕ) (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j)
    (h : ℤ) :
    HahnSeries.single (-(N : ℤ)) 1 *
      ιF (diagonalCoverReadout ((Xc ^ 3 - Yc ^ 3) ^ N *
        orderedChargedProduct fixedDualBases a b v q) (h + 3 * (N : ℤ))) =
      chargedGroundIterateLaurent a b v q h := by
  apply HahnSeries.ext
  funext r
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add,
    chargedGround_weakAssociativity_cover_coeff a b v q N hN]
  change HVertexOperator.coeff (nativeField _) (h + 3 * (N : ℤ) - 3 * (r + (N : ℤ))) v q =
    HVertexOperator.coeff (nativeField _) (h - 3 * r) v q
  rw [show h + 3 * (N : ℤ) - 3 * (r + (N : ℤ)) = h - 3 * r by omega]

#print axioms untwistedChargedGround_coeff
#print axioms chargedDiagonalRegular_coeff_eq_nativeField
#print axioms chargedGround_weakAssociativity_cover_coeff
#print axioms chargedGround_weakAssociativity_laurent

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

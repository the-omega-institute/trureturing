/- GID: D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forty-eight actual Leech Ising axes and their commuting orbifold modes. -/

import D5.S3.VertexAlgebra.Lattice.LeechFrame.ActualLeechNormFourFrame
import D5.S3.VertexAlgebra.Lattice.LeechFrame.NormFourMixedProducts
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing

/-! The conformal sum and commuting modes of the two signed norm-four axes
in each of the 24 explicit Leech directions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechIsingFrame

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechNormFourFrame (Index charge charge_norm complexBasis complexVector
  complexBasis_apply complex_pairing charge_orthogonal)
open LatticeGeneratingFieldLocality (LatticeData Charge Oscillator)
open LatticeAllStateReconstruction (mu)
open LatticeActualStateFieldCalculus (mode_commutator commutatorTerm)
open LatticeInvolution (FixedCarrier fixedMode)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open LatticeLightConeCoordinates (E g pairing)
open HalfFockSpectralFiberSource (actualInverse actualInverse_right)
open LatticeActualConformalState (omega conformalPolynomial)
open LatticeSugawaraConformal (chargePolynomial)
open Lattice.NormFourVirasoroVector (vector quadraticState opposite_sign_products orthogonal_products)
open TwistedGround.Orbifold
open HalfFock.NormFourFirstGradeSpectrum (normFourFixedSource)
open scoped BigOperators VertexOperator

local notation "D" => leechData

private theorem basis_coeff (x : E D) (p : Index) :
    complexBasis.repr x p = (1 / 4 : ℂ) * g D (complexVector p) x := by
  classical
  have h := congrArg (pairing D (complexVector p)) (complexBasis.sum_repr x)
  change pairing D (complexVector p) (∑ q, complexBasis.repr x q • complexBasis q) =
    g D (complexVector p) x at h
  simp only [map_sum, map_smul, complexBasis_apply] at h
  change (∑ q, complexBasis.repr x q * g D (complexVector p) (complexVector q)) = _ at h
  simp only [complex_pairing, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true] at h
  linear_combination (1 / 4 : ℂ) * h

/-- The inverse of the original Gram matrix as a sum of frame outer products. -/
theorem actualInverse_entry (i j : Fin leechData.rank) :
    actualInverse D i j = (1 / 4 : ℂ) * ∑ p : Index, (charge p i : ℂ) * (charge p j : ℂ) := by
  classical
  let x : E D := fun k => actualInverse D k j
  have hx (p : Index) : g D (complexVector p) x = (charge p j : ℂ) := by
    change (∑ a, ∑ b, (charge p a : ℂ) * (leechData.G a b : ℂ) * actualInverse D b j) = _
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have h (a : Fin leechData.rank) : (∑ b, (leechData.G a b : ℂ) * actualInverse D b j) =
        if a = j then 1 else 0 := by
      simpa only [Matrix.mul_apply, Matrix.one_apply, LatticeHalfFock.gramComplex, Matrix.map_apply] using
        congrFun (congrFun (actualInverse_right D leech_spec.2.1) a) j
    simp [h, mul_ite]
  have h := congrFun (complexBasis.sum_repr x) i
  simp only [Finset.sum_apply, Pi.smul_apply, complexBasis_apply, basis_coeff, hx,
    smul_eq_mul] at h
  change (∑ p, ((1 / 4 : ℂ) * (charge p j : ℂ)) * (charge p i : ℂ)) =
    actualInverse D i j at h
  rw [← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

private theorem chargePolynomial_sq {L : LatticeData} (a : Charge L) :
    chargePolynomial L a ^ 2 = ∑ i : Fin L.rank, ∑ j : Fin L.rank,
      ((a i : ℂ) * (a j : ℂ)) •
        (MvPolynomial.X (i, 0) * MvPolynomial.X (j, 0) : Oscillator L) := by
  unfold chargePolynomial
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (a j : ℂ) (a i : ℂ)]

private theorem conformalPolynomial_eq {L : LatticeData} (a : Index → Charge L)
    (H : Matrix (Fin L.rank) (Fin L.rank) ℂ)
    (hH : ∀ i j, H i j = (1 / 4 : ℂ) * ∑ p : Index, (a p i : ℂ) * (a p j : ℂ)) :
    (∑ p : Index, (1 / 8 : ℂ) • chargePolynomial L (a p) ^ 2) =
      conformalPolynomial L H := by
  simp only [conformalPolynomial, chargePolynomial_sq, hH, Finset.mul_sum,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  ring

private theorem opposite_sign_sum (a : Charge D) :
    vector D a 1 + vector D a (-1) = (1 / 8 : ℂ) • quadraticState D a := by
  unfold vector
  module

/-- The actual 48 lattice states sum to the original inverse-Gram Sugawara state. -/
theorem lattice_conformal_sum :
    (∑ p : Index, (vector D (charge p) 1 + vector D (charge p) (-1))) =
      omega D (actualInverse D) := by
  classical
  let insert : Oscillator D →ₗ[ℂ] LatticeGeneratingFieldLocality.Carrier D :=
    Finsupp.lsingle 0
  have h := conformalPolynomial_eq charge (actualInverse D) actualInverse_entry
  simpa only [opposite_sign_sum, quadraticState, omega, map_sum, map_smul, insert,
    Finsupp.lsingle_apply] using congrArg insert h

abbrev AxisIndex := Index × Bool

def sign (s : Bool) : ℂ := if s then 1 else -1

private theorem sign_sq (s : Bool) : sign s ^ 2 = 1 := by
  cases s <;> norm_num [sign]

private theorem leech_unit : IsUnit leechData.G.det := leech_spec.2.1

private theorem leech_positive :
    Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) :=
  leech_spec.2.2.1

abbrev Orbifold := OriginalOrbifoldField.Carrier D leech_unit

/-- The original norm-four fixed state, embedded in the full orbifold. -/
def axis (p : AxisIndex) : Orbifold := (normFourFixedSource D (charge p.1) (sign p.2), 0)

/-- The stress state used by the original orbifold translation. -/
def conformalState : Orbifold :=
  (⟨omega D (actualInverse D), by
    rw [← lattice_conformal_sum]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.add_mem _ (normFourFixedSource D (charge p) 1).property
        (normFourFixedSource D (charge p) (-1)).property⟩, 0)

/-- The axes of both signs in all 24 directions sum to the original stress state. -/
theorem conformal_sum : (∑ p : AxisIndex, axis p) = conformalState := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool, axis, sign, Bool.false_eq_true, ite_false, ite_true]
  apply Prod.ext
  · apply Subtype.ext
    let proj : Orbifold →ₗ[ℂ] LatticeGeneratingFieldLocality.Carrier D :=
      (LatticeInvolution.fixedSpace D).subtype.comp (LinearMap.fst ℂ _ _)
    change proj (∑ p : Index, (normFourFixedSource D (charge p) 1 +
      normFourFixedSource D (charge p) (-1), 0)) = proj conformalState
    rw [map_sum]
    exact lattice_conformal_sum
  · change (LinearMap.snd ℂ _ _) (∑ p : Index, (normFourFixedSource D (charge p) 1 +
      normFourFixedSource D (charge p) (-1), 0)) = 0
    rw [map_sum]
    exact Finset.sum_const_zero

/-- The literal coefficient of the original orbifold axis field. -/
def axisMode (p : AxisIndex) (m : ℤ) : Module.End ℂ Orbifold :=
  (OriginalOrbifoldField.Y D leech_unit leech_positive (axis p))[[m + 1]]

/-- The literal coefficient of the original orbifold stress field. -/
def conformalMode (m : ℤ) : Module.End ℂ Orbifold :=
  (OriginalOrbifoldField.Y D leech_unit leech_positive conformalState)[[m + 1]]

/-- The conformal mode splits on the entire original orbifold carrier. -/
theorem conformal_mode_sum (m : ℤ) : (∑ p : AxisIndex, axisMode p m) = conformalMode m := by
  let coeff : Orbifold →ₗ[ℂ] Module.End ℂ Orbifold :=
    (LinearMap.proj (m + 1)).comp
      (VertexOperator.ncoeff.comp (OriginalOrbifoldField.Y D leech_unit leech_positive))
  change (∑ p : AxisIndex, coeff (axis p)) = coeff conformalState
  rw [← map_sum, conformal_sum]

theorem axis_virasoro (p : AxisIndex) (m n : ℤ) (x : Orbifold) :
    axisMode p m (axisMode p n x) - axisMode p n (axisMode p m x) =
      ((m : ℂ) - (n : ℂ)) • axisMode p (m + n) x +
        (if m + n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) • x else 0) := by
  exact FixedSourceIsing.embedded_virasoro D leech_unit (charge p.1) (sign p.2)
    leech_positive (charge_norm p.1) (sign_sq p.2) m n x

/-- All nonnegative products between different axes vanish in the lattice VOA. -/
theorem lattice_mixed_products {p q : AxisIndex} (hpq : p ≠ q) (k : ℤ) (hk : 0 ≤ k) :
    mu D (vector D (charge p.1) (sign p.2)) k (vector D (charge q.1) (sign q.2)) = 0 := by
  by_cases h : p.1 = q.1
  · have ht : p.2 ≠ q.2 := fun ht => hpq (Prod.ext h ht)
    have hsign : sign q.2 = -sign p.2 := by
      cases hp : p.2 <;> cases hq : q.2 <;> simp_all [sign]
    rw [← h, hsign]
    exact opposite_sign_products D _ (charge_norm _) _ (sign_sq _) k hk
  · exact orthogonal_products D _ _ (charge_orthogonal h) _ _ k hk

/-- Different indices give different actual axis states. -/
theorem axis_injective : Function.Injective axis := by
  intro p q h
  by_contra hpq
  have hvec := congrArg (fun z : Orbifold => z.1.val) h
  change vector D (charge p.1) (sign p.2) = vector D (charge q.1) (sign q.2) at hvec
  have hz := lattice_mixed_products hpq 3 (by omega)
  rw [← hvec] at hz
  have hself := Lattice.NormFourVirasoroVector.self_products
    D (charge p.1) (charge_norm p.1) (sign p.2) (sign_sq p.2)
  rw [hself.2.2.2.1] at hz
  have hvac := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hone := congrArg (fun v : LatticeGeneratingFieldLocality.Carrier D => v 0) hvac
  change Finsupp.single (0 : Charge D) (1 : Oscillator D) 0 =
    (0 : LatticeGeneratingFieldLocality.Carrier D) 0 at hone
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply, one_ne_zero] at hone

/-- The nonnegative products vanish for the original fields of the embedded axes. -/
theorem orbifold_mixed_products {p q : AxisIndex} (hpq : p ≠ q) (k : ℤ) (hk : 0 ≤ k) :
    ((OriginalOrbifoldField.Y D leech_unit leech_positive (axis p))[[k]]) (axis q) = 0 := by
  rw [axis, axis, OriginalOrbifoldField.Y_fixed_ncoeff_apply, map_zero]
  exact Prod.ext (Subtype.ext (lattice_mixed_products hpq k hk)) rfl

/-- An embedded fixed pair with regular mutual products commutes on both sectors. -/
private theorem embedded_modes_commute {L : LatticeData} {hu : IsUnit L.G.det}
    (hL : Matrix.PosDef (L.G.map (Int.cast : ℤ → ℝ)))
    (u v : FixedCarrier L) (hregular : ∀ i : ℕ, mu L u.val i v.val = 0) (p q : ℤ) :
    Commute ((OriginalOrbifoldField.Y L hu hL (u, 0))[[p]])
      ((OriginalOrbifoldField.Y L hu hL (v, 0))[[q]]) := by
  show _ * _ = _ * _
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, OriginalOrbifoldField.Y_fixed_ncoeff_apply]
  apply Prod.ext
  · apply Subtype.ext
    have h := mode_commutator L u.val v.val p q
    have hz : (∑ᶠ i : ℕ, commutatorTerm L u.val v.val p q i) = 0 := by
      simp only [commutatorTerm, hregular, map_zero, VertexOperator.ncoeff, Pi.zero_apply,
        smul_zero, finsum_zero]
    rw [hz] at h
    exact congrArg (fun M : Module.End ℂ (LatticeGeneratingFieldLocality.Carrier L) =>
      M x.1.val) (sub_eq_zero.mp h)
  · have hfixed (i : ℕ) : fixedMode L u i v = 0 := Subtype.ext (hregular i)
    have hzero (n : ℤ) : ((fixedParitySlice L hu (-1) (0 : FixedCarrier L))[[n]]) x.2 = 0 := by
      have h := congrArg Prod.snd
        (OriginalOrbifoldField.Y_fixed_ncoeff_apply L hu hL n 0 (0, x.2))
      change (((OriginalOrbifoldField.Y L hu hL 0)[[n]]) (0, x.2)).2 = _ at h
      rw [OriginalOrbifoldField.Y_ncoeff, map_zero, LinearMap.zero_apply] at h
      exact h.symm
    apply sub_eq_zero.mp
    rw [FixedSourceIsing.odd_commutator]
    simp only [hfixed, hzero, smul_zero, finsum_zero]

/-- All integer Virasoro modes of different axes commute on the whole orbifold. -/
theorem axis_modes_commute {p q : AxisIndex} (hpq : p ≠ q) (m n : ℤ) :
    Commute (axisMode p m) (axisMode q n) := by
  unfold axisMode axis
  refine embedded_modes_commute leech_positive _ _ ?_ (m + 1) (n + 1)
  intro i
  exact lattice_mixed_products hpq i (Int.natCast_nonneg i)

end D5.S3.VertexAlgebra.ActualLeechIsingFrame

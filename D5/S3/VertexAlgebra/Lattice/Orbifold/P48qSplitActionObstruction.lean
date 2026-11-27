/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qSplitActionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qSplitActionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A split P48q action has independent fixed quadratics or a cubic twisted weight obstruction. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeSpectrumTransport
import OmegaBuild.Commands

/-! The integral lattice action extends on the standard coordinate basis to
the rational Cartan space. The vacuum and current coefficients of the product
of opposite charged ground states identify this extension with the actual
current action. Cauchy's theorem supplies the cubic sector when the subgroup
order is divisible by three. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction

open LatticeGeneratingFieldLocality (LatticeData Charge Carrier Oscillator unitCharge bilinear epsilon)
open LatticeAllStateField (Y vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (currentState)
open LatticePositiveEnergy (grade vacuum_nonzero)
open LatticeSugawaraConformal (chargePolynomial)
open Lattice.Automorphisms.ConformalGroundTransport (current)
open DiagonalCharacterConjugacy (PreservesModes ground)
open P48qInvariantQuadratics (RationalCartan rationalGram rationalCurrent)
open P48qOrderThreeSpectrumTransport (CubicTwistedModuleLaw conformalZeroMode)
open P48qTwistedChargeAction (lattice)
open scoped VertexOperator

open private additive_expansion ground_current_product from
  D5.S3.VertexAlgebra.Lattice.IsometryLift
open private vacuum_fixed from
  D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport
open private ground_mul mode_smul epsilon_ne_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy
open private currentLinear castCoordinates from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics

noncomputable section

private def chargeCast (D : LatticeData) (a : Charge D) : RationalCartan D :=
  fun i => (a i : ℚ)

private theorem chargeCast_unit (D : LatticeData) (i : Fin D.rank) :
    chargeCast D (unitCharge D i) = Pi.basisFun ℚ (Fin D.rank) i := by
  rw [Pi.basisFun_apply]
  funext j
  by_cases h : j = i <;> simp [chargeCast, unitCharge, Pi.single_apply, h]

private def rationalExtension (D : LatticeData) (s : AddAut (Charge D)) :
    Module.End ℚ (RationalCartan D) :=
  (Pi.basisFun ℚ (Fin D.rank)).constr ℚ (fun i => chargeCast D (s (unitCharge D i)))

private theorem rationalExtension_charge (D : LatticeData) (s : AddAut (Charge D))
    (a : Charge D) : rationalExtension D s (chargeCast D a) = chargeCast D (s a) := by
  funext j
  have h := congrArg (fun v : Charge D => (v j : ℚ))
    (additive_expansion D s.toAddMonoidHom a)
  simpa [rationalExtension, chargeCast, Finset.sum_apply, zsmul_eq_mul, smul_eq_mul] using h.symm

private def rationalAction (D : LatticeData) :
    Multiplicative (AddAut (Charge D)) →* Module.End ℚ (RationalCartan D) where
  toFun s := rationalExtension D s.toAdd
  map_one' := by
    apply (Pi.basisFun ℚ (Fin D.rank)).ext
    intro i
    rw [← chargeCast_unit]
    exact rationalExtension_charge D (0 : AddAut (Charge D)) (unitCharge D i)
  map_mul' s t := by
    apply (Pi.basisFun ℚ (Fin D.rank)).ext
    intro i
    rw [← chargeCast_unit]
    change rationalExtension D (s.toAdd + t.toAdd) (chargeCast D (unitCharge D i)) =
      rationalExtension D s.toAdd (rationalExtension D t.toAdd (chargeCast D (unitCharge D i)))
    rw [rationalExtension_charge, rationalExtension_charge, rationalExtension_charge] <;> rfl

private theorem rationalAction_injective (D : LatticeData) :
    Function.Injective (rationalAction D) := by
  intro s t h
  apply Multiplicative.toAdd.injective
  apply AddEquiv.ext
  intro a
  have ha := LinearMap.congr_fun h (chargeCast D a)
  change rationalExtension D s.toAdd (chargeCast D a) =
    rationalExtension D t.toAdd (chargeCast D a) at ha
  rw [rationalExtension_charge, rationalExtension_charge] at ha
  funext j
  exact Int.cast_injective (α := ℚ) (congrFun ha j)

private theorem rationalGram_charge (D : LatticeData) (a b : Charge D) :
    rationalGram D (chargeCast D a) (chargeCast D b) = (bilinear D a b : ℚ) := by
  rw [rationalGram, Matrix.toBilin'_apply]
  simp only [chargeCast, bilinear, Matrix.map_apply, Int.cast_sum, Int.cast_mul]

private theorem rationalExtension_preserves_gram (D : LatticeData) (s : AddAut (Charge D))
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b) (x y : RationalCartan D) :
    rationalGram D (rationalExtension D s x) (rationalExtension D s y) = rationalGram D x y := by
  have he : (rationalGram D).compl₁₂ (rationalExtension D s) (rationalExtension D s) =
      rationalGram D := by
    apply LinearMap.ext_basis (Pi.basisFun ℚ (Fin D.rank)) (Pi.basisFun ℚ (Fin D.rank))
    intro i j
    simp only [LinearMap.compl₁₂_apply, ← chargeCast_unit D, rationalExtension_charge,
      rationalGram_charge, hs]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

private theorem current_charge (D : LatticeData) (a : Charge D) :
    current D (fun i => (a i : ℂ)) = Finsupp.single 0 (chargePolynomial D a) := by
  let includeNeutral : Oscillator D →ₗ[ℂ] Carrier D := Finsupp.lsingle 0
  change (∑ i, (a i : ℂ) • includeNeutral (MvPolynomial.X (i, 0))) =
    includeNeutral (∑ i, (a i : ℂ) • MvPolynomial.X (i, 0))
  rw [map_sum]
  simp only [map_smul]

private theorem current_lift_charge (D : LatticeData) (s : AddAut (Charge D))
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (phase : Charge D → ℂˣ)
    (hMode : PreservesModes D U)
    (hGround : ∀ a, U (ground D a) = (phase a : ℂ) • ground D (s a)) (a : Charge D) :
    U (current D (fun i => (a i : ℂ))) = current D (fun i => (s a i : ℂ)) := by
  let c : ℂ := (phase a : ℂ) * (phase (-a) : ℂ)
  have hProduct (n : ℤ) : U (mu D (ground D a) n (ground D (-a))) =
      c • mu D (ground D (s a)) n (ground D (-(s a))) := by
    change U (((Y D (ground D a))[[n]]) (ground D (-a))) = _
    rw [hMode, hGround a, hGround (-a), map_neg, mode_smul] <;> rfl
  have hVacuum := vacuum_fixed D U (fun u n v => hMode u v n)
  have hOpposite (b : Charge D) :
      mu D (ground D b) (-bilinear D b (-b) - 1) (ground D (-b)) =
        epsilon D b (-b) • vacuum D := by
    change ((Y D (ground D b))[[-bilinear D b (-b) - 1]]) (ground D (-b)) = _
    rw [ground_mul, add_neg_cancel] <;> rfl
  have hNorm : bilinear D (s a) (-(s a)) = bilinear D a (-a) := by
    simpa only [map_neg] using hs a (-a)
  have hScalar := hProduct (-bilinear D a (-a) - 1)
  rw [hOpposite a, map_smul, hVacuum, ← hNorm, hOpposite (s a), smul_smul] at hScalar
  have hPhase := smul_left_injective ℂ (vacuum_nonzero D) hScalar
  have hCurrent := hProduct (bilinear D a a - 2)
  rw [ground_current_product D a, map_smul, ← hs a a, ground_current_product D (s a),
    smul_smul, ← hPhase] at hCurrent
  rw [current_charge, current_charge]
  exact smul_right_injective (Carrier D) (epsilon_ne_zero D a (-a)) hCurrent

private theorem rationalCurrent_lift (D : LatticeData) (s : AddAut (Charge D))
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (phase : Charge D → ℂˣ)
    (hMode : PreservesModes D U)
    (hGround : ∀ a, U (ground D a) = (phase a : ℂ) • ground D (s a)) (x : RationalCartan D) :
    U (rationalCurrent D x) = rationalCurrent D (rationalExtension D s x) := by
  let J := ((currentLinear D).restrictScalars ℚ).comp (castCoordinates D)
  have he : (U.toLinearMap.restrictScalars ℚ).comp J = J.comp (rationalExtension D s) := by
    apply (Pi.basisFun ℚ (Fin D.rank)).ext
    intro i
    rw [← chargeCast_unit]
    change U (rationalCurrent D (chargeCast D (unitCharge D i))) =
      rationalCurrent D (rationalExtension D s (chargeCast D (unitCharge D i)))
    rw [rationalExtension_charge]
    simpa only [rationalCurrent, chargeCast, Rat.cast_intCast] using
      current_lift_charge D s hs U phase hMode hGround (unitCharge D i)
  exact LinearMap.congr_fun he x

universe u

/-- For a split compatible subgroup action, either two independent actual
weight-two states are fixed or an order-three element has only nonintegral
ordinary twisted weights, all congruent to `1/9` modulo `1/3`. -/
theorem p48q_split_action_obstruction
    (realization : Additive ExtremalC48.SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hIsometry : ∀ s : Additive ExtremalC48.SL47, ∀ a b,
      bilinear lattice (realization s a) (realization s b) = bilinear lattice a b)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    (H : Subgroup ExtremalC48.SL47)
    (U : H →* (Carrier lattice ≃ₗ[ℂ] Carrier lattice)) (phase : H → Charge lattice → ℂˣ)
    (hMode : ∀ h, PreservesModes lattice (U h))
    (hGround : ∀ h a, U h (ground lattice a) =
      (phase h a : ℂ) • ground lattice (realization (Additive.ofMul (h : ExtremalC48.SL47)) a)) :
    (∃ q : Fin 2 → Carrier lattice, (∀ i, q i ∈ grade lattice 2) ∧
      (∀ h i, U h (q i) = q i) ∧ LinearIndependent ℂ q) ∨
    (∃ h : H, orderOf h = 3 ∧
      ∀ (W : Type u) [AddCommGroup W] [Module ℂ W]
        (Ytw : Carrier lattice →ₗ[ℂ] VertexOperator ℂ W), CubicTwistedModuleLaw (U h) Ytw →
        ∀ lower : ℝ,
          (∀ (r : ℂ) (v : W), v ≠ 0 → conformalZeroMode Ytw v = r • v → lower ≤ r.re) →
          (∀ r : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (conformalZeroMode Ytw) r)) →
          ∀ (r : ℂ) (v : W), v ≠ 0 → conformalZeroMode Ytw v = r • v →
            (∃ n : ℕ, r = 16 / 9 + (n : ℂ) / 3) ∧
            (∃ m : ℤ, 9 * r = (m : ℂ) ∧ m % 3 = 1) ∧ ∀ z : ℤ, r ≠ (z : ℂ)) := by
  let chargeAction := realization.toMultiplicativeRight.comp H.subtype
  have hChargeInj : Function.Injective chargeAction :=
    Multiplicative.ofAdd.injective.comp (hFaithful.comp
      (Additive.ofMul.injective.comp Subtype.val_injective))
  by_cases hDiv : 3 ∣ Nat.card H
  · letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 hDiv
    have hOrder : addOrderOf (realization (Additive.ofMul (h : ExtremalC48.SL47))) = 3 :=
      (orderOf_injective chargeAction hChargeInj h).trans hh
    have hCube : U h ^ (3 : ℕ) = 1 := by
      rw [← map_pow, ← hh, pow_orderOf_eq_one, map_one]
    right
    refine ⟨h, hh, ?_⟩
    intro W _ _ Ytw hY lower hLower hFinite r v hv hr
    exact P48qOrderThreeSpectrumTransport.actual_twisted_spectrum_of_order_three_isometry
      realization hFaithful hIsometry hExhaustive _ (hIsometry _) hOrder (U h) (phase h)
      (hGround h) (hMode h) hCube Ytw hY lower hLower hFinite r v hv hr
  · let ρ : Representation ℚ H (RationalCartan lattice) := (rationalAction lattice).comp chargeAction
    let A : Representation ℂ H (Carrier lattice) :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp U
    exact Or.inl (P48qInvariantQuadratics.p48q_prime_to_three_fixed_weight_two H hDiv ρ
      ((rationalAction_injective lattice).comp hChargeInj) A
      (fun h => rationalExtension_preserves_gram lattice _ (hIsometry (Additive.ofMul h.val)))
      (fun h => rationalCurrent_lift lattice _ (hIsometry (Additive.ofMul h.val))
        (U h) (phase h) (hMode h) (hGround h))
      (fun h a n b => hMode h a b n))

run_cmd do
  let name := ``p48q_split_action_obstruction
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
    throwError "Unexpected axiom closure for {name}: {axioms}"
  Lean.logInfo m!"{name} depends on axioms: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction

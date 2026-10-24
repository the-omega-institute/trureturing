/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.allCorrectedCoefficientsChargeFinite; result=D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.result; claim=D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.allCorrectedCoefficientsChargeFinite
   digest: Fixed vacuum inputs detect infinitely many actual doubled isotropic charges. -/

import D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.Set.Finite.Basic

/-! The original corrected field detects infinitely many doubled norm-zero charges
with one fixed pair of actual vacuum tensors. Charge support is distinct from
energy restricted-dual support. The all-charge dual equivalence is reused. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockChargedResidue
open TwistedGround.InvariantPairing SignedOscillatorWick ActualChargedAdjoint

/-- Intrinsic sector support: every oscillator in an excluded charge vanishes. -/
def ChargeFinite (D : LatticeData) (ell : Module.Dual ℂ (Carrier D)) : Prop :=
  ∃ S : Finset (Charge D), ∀ q : Charge D, q ∉ S →
    ∀ p : Oscillator D, ell (Finsupp.single q p) = 0

/-- Explicit representation premise. sigma=id is diagonal charge orthogonality;
sigma=Neg.neg is opposite-charge orthogonality. No source form is assumed to exist. -/
def ChargeOrthogonal (D : LatticeData) (sigma : Charge D → Charge D)
    (P : LinearMap.BilinForm ℂ (Carrier D)) : Prop :=
  ∀ q r : Charge D, r ≠ sigma q → ∀ p s : Oscillator D,
    P (Finsupp.single q p) (Finsupp.single r s) = 0

/-- The exact existing coefficient, transported by the standard direct-sum/dual
equivalence. This is a product of FULL oscillator duals at all charges. -/
def completedCorrectedCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) :
    Charge D → Module.Dual ℂ (Oscillator D) :=
  (Finsupp.lsum ℂ).symm (correctedDualCoefficient D hu e x y)

/- Consumed support helpers; no new equivalence is proved. -/
private theorem finite_family_gives_charge_finite (D : LatticeData)
    (F : Charge D →₀ Module.Dual ℂ (Oscillator D)) :
    ChargeFinite D (Finsupp.lsum ℂ (fun q => F q)) := by
  classical
  refine ⟨F.support, ?_⟩
  intro q hq p
  rw [Finsupp.lsum_single, Finsupp.notMem_support_iff.mp hq]
  rfl

private theorem represented_charge_finite (D : LatticeData)
    (sigma : Charge D → Charge D) (P : LinearMap.BilinForm ℂ (Carrier D))
    (hP : ChargeOrthogonal D sigma P) (a : Carrier D) :
    ChargeFinite D (P a) := by
  classical
  refine ⟨a.support.image sigma, ?_⟩
  intro q hq p
  rw [← Finsupp.sum_single a]
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro r hr
  apply hP r q
  intro same
  exact hq (Finset.mem_image.mpr ⟨r, hr, same.symm⟩)

/- Crucial actual quotient calculation: no periodicity is postulated. -/
private theorem doubled_ground_lift (D : LatticeData) (a : Charge D) :
    groundLift D (a + a) = 1 := by
  apply (quotientEquiv D).injective
  rw [map_one]
  change reduction D (⟨0, a + a⟩ : Extension D) = 1
  apply SignExtension.ext
  · rfl
  · ext i
    change reduceCharge D (a + a) i = 0
    simp [reduceCharge, CharTwo.add_self_eq_zero]

private theorem even_isotropic_vacuum_action (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D)
    (ha : chargeNorm D (a + a) = 0) (u : ActualGround D hu) :
    chargedCoefficient D hu (a + a) 0 ((1 : Oscillator D) ⊗ₜ[ℂ] u) =
      (1 : Oscillator D) ⊗ₜ[ℂ] u := by
  rw [charged_vacuum_coefficient]
  rw [show chargeScalar D (a + a) = 1 by simp [chargeScalar, ha]]
  simp only [one_smul, ha, add_zero, creation_zero]
  rw [groundAction, doubled_ground_lift, map_one]
  rfl

/-- An infinite actual even-isotropic charge family forces an actual fixed-input
coefficient into the all-charge product. Both inputs have vacuum oscillators.
The family hypotheses concern only integral charges and their original norms;
they do not assume any coefficient-support conclusion.

The source representation obstruction quantifies over separately supplied
charge-orthogonal forms and retains their orientation P(a,b)=ell(b).
-/
theorem actual_even_isotropic_completion_boundary (D : LatticeData)
    (hu : IsUnit D.G.det) (c : ℕ → Charge D)
    (hi : Function.Injective (fun n => c n + c n))
    (hz : ∀ n : ℕ, chargeNorm D (c n + c n) = 0) :
    ∃ u v : ActualGround D hu,
      let x : ActualTensor D hu := (1 : Oscillator D) ⊗ₜ[ℂ] u
      let y : ActualTensor D hu := (1 : Oscillator D) ⊗ₜ[ℂ] v
      let ell := correctedDualCoefficient D hu 0 x y
      let K := completedCorrectedCoefficient D hu 0 x y
      actualForm D hu x y ≠ 0 ∧
      (∀ n : ℕ, ell (Finsupp.single (c n + c n) (1 : Oscillator D)) =
        actualForm D hu x y) ∧
      ¬ ChargeFinite D ell ∧
      (∀ sigma : Charge D → Charge D,
        ∀ P : LinearMap.BilinForm ℂ (Carrier D), ChargeOrthogonal D sigma P →
          ¬ ∃ a : Carrier D, P a = ell) ∧
      (¬ ∃ F : Charge D →₀ Module.Dual ℂ (Oscillator D),
        Finsupp.lsum ℂ (fun q => F q) = ell) ∧
      ¬ Function.HasFiniteSupport K ∧
      (Finsupp.lsum ℂ K = ell) ∧
      (∀ a : Carrier D, ell a = ∑ q ∈ a.support, K q (a q)) := by
  classical
  -- This is definitionally the SAME choice used by actualForm, not a new form.
  let G : GroundPairing D hu := Classical.choice (actual_ground_pairing D hu)
  let u : ActualGround D hu := fun _ => 1
  have hu0 : u ≠ 0 := by
    intro h
    have at_zero := congrFun h (0 : Half (groundRank D hu))
    norm_num [u] at at_zero
  have detects : ∃ v : ActualGround D hu, G.form u v ≠ 0 := by
    by_contra absent
    push_neg at absent
    exact hu0 (G.nondegenerate.1 u absent)
  obtain ⟨v, hv⟩ := detects
  let x : ActualTensor D hu := (1 : Oscillator D) ⊗ₜ[ℂ] u
  let y : ActualTensor D hu := (1 : Oscillator D) ⊗ₜ[ℂ] v
  let ell := correctedDualCoefficient D hu 0 x y
  let K := completedCorrectedCoefficient D hu 0 x y
  have wick_one : wick D (1 : Oscillator D) 1 = 1 := by
    simpa using (wick_constant_left D (1 : ℂ) (1 : Oscillator D))
  have nonzero : actualForm D hu x y ≠ 0 := by
    change G.form u v * wick D (1 : Oscillator D) 1 ≠ 0
    rw [wick_one, mul_one]
    exact hv
  have values (n : ℕ) :
      ell (Finsupp.single (c n + c n) (1 : Oscillator D)) =
        actualForm D hu x y := by
    change actualForm D hu
      ((correctedField D hu (Finsupp.single (c n + c n)
        (1 : Oscillator D))).coeff 0 x) y = _
    rw [corrected_singleton_coeff_charged]
    simp only [chargedField, HVertexOperator.coeff_of_coeff]
    change actualForm D hu
      (chargedCoefficient D hu (c n + c n) 0
        ((1 : Oscillator D) ⊗ₜ[ℂ] u)) y = _
    rw [even_isotropic_vacuum_action D hu (c n) (hz n) u]
  have infinite_support : ¬ ChargeFinite D ell := by
    rintro ⟨S, hS⟩
    apply (Set.infinite_range_of_injective hi)
    apply S.finite_toSet.subset
    rintro q ⟨n, rfl⟩
    change c n + c n ∈ S
    by_contra outside
    exact nonzero ((values n).symm.trans (hS _ outside 1))
  have no_representative : ∀ sigma : Charge D → Charge D,
      ∀ P : LinearMap.BilinForm ℂ (Carrier D), ChargeOrthogonal D sigma P →
        ¬ ∃ a : Carrier D, P a = ell := by
    intro sigma P hP hrep
    obtain ⟨a, ha⟩ := hrep
    apply infinite_support
    rw [← ha]
    exact represented_charge_finite D sigma P hP a
  have no_finite_family : ¬ ∃ F : Charge D →₀ Module.Dual ℂ (Oscillator D),
      Finsupp.lsum ℂ (fun q => F q) = ell := by
    rintro ⟨F, hF⟩
    apply infinite_support
    rw [← hF]
    exact finite_family_gives_charge_finite D F
  have product_infinite : ¬ Function.HasFiniteSupport K := by
    intro hK
    apply infinite_support
    refine ⟨hK.toFinset, ?_⟩
    intro q hq p
    have zero_coordinate : K q = 0 := by
      by_contra hn
      exact hq ((Set.Finite.mem_toFinset hK).mpr hn)
    change K q p = 0
    rw [zero_coordinate]
    rfl
  have reconstruct : Finsupp.lsum ℂ K = ell :=
    (Finsupp.lsum ℂ).apply_symm_apply ell
  refine ⟨u, v, nonzero, values, infinite_support, no_representative,
    no_finite_family, product_infinite, reconstruct, ?_⟩
  intro a
  change ell a = ∑ q ∈ a.support, K q (a q)
  rw [← reconstruct]
  rfl

/-- The explicit even unimodular hyperbolic plane. Used only in the refutation. -/
abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![(0 : ℤ), 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  even_diagonal := by intro i; fin_cases i <;> norm_num

private theorem hyperbolic_unimodular : IsUnit hyperbolic.G.det := by
  have determinant : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [determinant]
  exact isUnit_neg_one

/-- c(n)=(n,0), so the actual family in the theorem is q(n)=(2n,0). -/
private def hyperbolicLine (n : ℕ) : Charge hyperbolic :=
  fun i => if i = 0 then (n : ℤ) else 0

private theorem hyperbolic_family_injective :
    Function.Injective (fun n => hyperbolicLine n + hyperbolicLine n) := by
  intro m n same
  have at_zero := congrFun same (0 : Fin 2)
  change (m : ℤ) + (m : ℤ) = (n : ℤ) + (n : ℤ) at at_zero
  omega

private theorem hyperbolic_family_isotropic (n : ℕ) :
    chargeNorm hyperbolic (hyperbolicLine n + hyperbolicLine n) = 0 := by
  simp [chargeNorm, bilinear, hyperbolic, hyperbolicLine, Fin.sum_univ_two]

/-- The universal claim refuted by the original corrected field itself. -/
def allCorrectedCoefficientsChargeFinite : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu), ChargeFinite D (correctedDualCoefficient D hu e x y)

/-- No scope weakening: a counterexample to the universal finite-charge premise.
The preceding boundary theorem supplies the consumed completion obstruction. -/
theorem result : ¬ allCorrectedCoefficientsChargeFinite := by
  intro all_finite
  obtain ⟨u, v, h⟩ := actual_even_isotropic_completion_boundary hyperbolic
    hyperbolic_unimodular hyperbolicLine hyperbolic_family_injective
      hyperbolic_family_isotropic
  exact h.2.2.1 (all_finite hyperbolic hyperbolic_unimodular 0
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] u)
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] v))

#print axioms actual_even_isotropic_completion_boundary
#print axioms result

end D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion

/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuSourceSupport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuSourceSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal charged right-support relation. -/
/-
Dong--Li--Mason, DOI 10.1006/jabr.1997.7112, Theorem 3.4 and Remark 2.11.
These source equalities take place modulo the original literal circle span.
The finite tied-minimum transition span remains a separate source obligation.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuCurrentRelations

/-! Groundwork for finite source transitions and their sharp dimension bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuSourceSupport
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticePositiveEnergy
open ActualZhuFinite ActualZhuAlgebra ActualZhuGroundCurrent
open ActualZhuCurrentNormalForm ActualZhuCurrentRelations
open scoped BigOperators
noncomputable section

variable (D : LatticeData) [hD : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]
local instance : Ring (Q D) := quotientRing D hD.out
local instance : Algebra ℂ (Q D) := quotientAlgebra D hD.out

private theorem ground_chargePolynomial (δ α : Charge D) :
    (zhuO D).mkQ (Finsupp.single δ (chargePolynomial D α)) = E D δ * Hcharge D α := by
  classical
  simp only [chargePolynomial, Finsupp.single_finsetSum, ← Finsupp.smul_single,
    map_sum, map_smul, Hcharge, Finset.mul_sum, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he := oscillator_right_current D δ i 1
  change E D δ * H D i = _ at he
  rw [mul_one] at he
  rw [he]

/-- The right charged support relation on the original full source quotient. -/
theorem ground_right_support (δ : Charge D) :
    E D δ * (Hcharge D δ + ((chargeEnergy D δ).toNat : Q D)) = 0 := by
  let k := (chargeEnergy D δ).toNat
  have hz : (zhuO D).mkQ (translation D (Finsupp.single δ 1) +
      (k : ℂ) • Finsupp.single δ 1) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr
      (translation_weight_mem_zhuO D hD.out (ground_grade D δ hD.out))
  simp only [translation_single, Derivation.map_one_eq_zero, zero_add, mul_one,
    map_add, map_smul, ground_chargePolynomial D] at hz
  change E D δ * Hcharge D δ + (k : ℂ) • E D δ = 0 at hz
  rw [mul_add]
  have hs : E D δ * (k : Q D) = (k : ℂ) • E D δ := by
    rw [← (Nat.cast_commute k (E D δ)).eq, Algebra.smul_def, map_natCast]
  rw [hs]
  exact hz

#print axioms ground_right_support
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuSourceSupport

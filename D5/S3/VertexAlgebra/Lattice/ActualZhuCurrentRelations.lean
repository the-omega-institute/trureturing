/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-alpha opposite-charge circle relations in the literal Zhu quotient. -/
/-
Dong--Li--Mason, Certain associative algebras similar to U(sl2) and Zhu's
algebra A(V_L), DOI 10.1006/jabr.1997.7112, Theorem 3.4 and Remark 2.11.
Original native creation_derivation and ground_product are reused without
reproving their oscillator or field identities. Mathlib supplies binomial
ring coefficients and Chu--Vandermonde, with its original Apache-2.0 attribution.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuCurrentNormalForm
import D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
import Mathlib.RingTheory.Binomial

/-! Neutral creation recurrence and the full all-charge current polynomial. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuCurrentRelations
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualConformalState LatticePositiveEnergy
open ActualZhuProduct ActualZhuFinite ActualZhuAlgebra ActualZhuGroundCurrent
open ActualZhuOscillator ActualZhuCurrentNormalForm
open scoped BigOperators VertexOperator
open private creation_derivation from D5.S3.VertexAlgebra.LatticeSugawaraConformal
open private ground ground_product from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
noncomputable section
attribute [local instance] BinomialRing.toHasUniqueDiv

variable (D : LatticeData)

/-- Weighted oscillator homogeneity gives the exact original energy grade. -/
theorem single_weighted_grade (δ : Charge D) (p : Oscillator D) (n : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (oscillatorWeight D) p n) :
    Finsupp.single δ p ∈ grade D (chargeEnergy D δ + n) := by
  classical
  rw [mem_grade_iff]
  intro a ha
  by_cases he : δ = a.1
  · rw [Finsupp.single_apply, ite_eq_left he]
    by_contra hn
    have hw := hp hn
    have hd : oscillatorEnergy a.2 = n := hw
    apply ha
    simp [energy, ← he, hd]
  · simp [Finsupp.single_apply, he]

variable [hD : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]
local instance : Ring (Q D) := quotientRing D hD.out
local instance : Algebra ℂ (Q D) := quotientAlgebra D hD.out
local instance : Module ℚ≥0 (Q D) := Module.compHom (Q D) (NNRat.castHom ℂ)

/-- The charge-linear neutral current; no basis or rank assumption is added. -/
def Hcharge (α : Charge D) : Q D := ∑ i : Fin D.rank, (α i : ℂ) • H D i

private theorem chargePolynomial_mul_class (α : Charge D) (p : Oscillator D) :
    (zhuO D).mkQ (Finsupp.single 0 (chargePolynomial D α * p)) =
      Hcharge D α * (zhuO D).mkQ (Finsupp.single 0 p) := by
  classical
  simp only [chargePolynomial, Finset.sum_mul, smul_mul_assoc,
    Finsupp.single_finsetSum, ← Finsupp.smul_single, map_sum, map_smul,
    oscillator_left_current D, bilinear, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    Int.cast_zero, zero_smul, sub_zero, Hcharge, Finset.sum_mul, smul_mul_assoc]

/-- Quotient recurrence retains both the translation and energy contributions. -/
theorem creation_class_recurrence (α : Charge D) (n : ℕ) :
    ((n+1 : ℕ) : ℂ) • (zhuO D).mkQ (Finsupp.single 0 (creationCoeff D α (n+1))) =
      (Hcharge D α - (n : Q D)) *
        (zhuO D).mkQ (Finsupp.single 0 (creationCoeff D α n)) := by
  have hg := single_weighted_grade D 0 (creationCoeff D α n) n
    ((actual_creation_coefficient_transport D 0 α).1 n)
  simp only [chargeEnergy_zero, zero_add] at hg
  have hz : (zhuO D).mkQ (translation D (Finsupp.single 0 (creationCoeff D α n)) +
      (n : ℂ) • Finsupp.single 0 (creationCoeff D α n)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (translation_weight_mem_zhuO D hD.out hg)
  rw [translation_single, creation_derivation] at hz
  have hc0 : chargePolynomial D 0 = 0 := by simp [chargePolynomial]
  simp only [hc0, zero_mul, add_zero, Finsupp.single_sub,
    ← Finsupp.smul_single, map_add, map_sub, map_smul] at hz
  rw [chargePolynomial_mul_class D α] at hz
  rw [sub_mul]
  have hs (q : Q D) : (n : Q D) * q = (n : ℂ) • q := by
    rw [Algebra.smul_def, map_natCast]
  rw [hs]
  have hn : ((n : ℤ) + 1 : ℂ) = ((n+1 : ℕ) : ℂ) := by push_cast; ring
  rw [hn] at hz
  have he := congrArg (fun q : Q D => q + Hcharge D α *
    (zhuO D).mkQ (Finsupp.single 0 (creationCoeff D α n)) -
    (n : ℂ) • (zhuO D).mkQ (Finsupp.single 0 (creationCoeff D α n))) hz
  convert he using 1 <;> abel

private theorem choose_commutes (x : Q D) (n : ℕ) : Commute (Ring.choose x n) x := by
  have hc := Polynomial.smeval_commute_left ℤ (descPochhammer ℤ n)
    (Commute.refl x)
  rw [Ring.descPochhammer_eq_factorial_smul_choose] at hc
  change (n.factorial • Ring.choose x n) * x = x * (n.factorial • Ring.choose x n) at hc
  simp only [smul_mul_assoc, mul_smul_comm] at hc
  exact (nsmul_right_inj (Nat.factorial_ne_zero n)).mp hc

/-- Neutral creation coefficients are the falling-factorial binomial coefficients. -/
theorem creation_class_choose (α : Charge D) (n : ℕ) :
    (zhuO D).mkQ (Finsupp.single 0 (creationCoeff D α n)) = Ring.choose (Hcharge D α) n := by
  induction n with
  | zero =>
    change (zhuO D).mkQ (Finsupp.single 0 (creationCoeff D α 0)) = _
    rw [Ring.choose_zero_right]
    simp only [creationCoeff, show ¬(0 : ℤ) < 0 by omega, ↓reduceDIte,
      Int.toNat_zero, exponential_constant]
    rfl
  | succ n ih =>
    apply (nsmul_right_inj (Nat.succ_ne_zero n)).mp
    have hr := creation_class_recurrence D α n
    rw [ih, Nat.cast_smul_eq_nsmul] at hr
    have hb := Ring.choose_smul_choose (Hcharge D α) (n := n+1) (k := n) (by omega)
    simp only [Nat.choose_succ_self_right, show n+1-n = 1 by omega,
      Ring.choose_one_right] at hb
    simp only [Nat.cast_add, Nat.cast_one] at hr ⊢
    rw [hr, hb]
    exact ((choose_commutes D (Hcharge D α) n).sub_right
      (Nat.cast_commute n (Ring.choose (Hcharge D α) n)).symm).symm.eq

/-- The original opposite-charge circle, with all of its binomial terms retained. -/
theorem opposite_circle_sum (α : Charge D) :
    let k := (chargeEnergy D α).toNat
    (∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) •
      Ring.choose (Hcharge D α) (2*k+1-j)) = 0 := by
  classical
  let k := (chargeEnergy D α).toNat
  have hk : (k : ℤ) = chargeEnergy D α := Int.toNat_of_nonneg
    (chargeEnergy_nonneg D hD.out α)
  have hcircle : (zhuO D).mkQ
      (NormFourZhuFinite.circle D k (ground D α) (ground D (-α))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.subset_span ⟨k, ground D α, ground D (-α), ground_grade D α hD.out, rfl⟩)
  have he : (zhuO D).mkQ
      (NormFourZhuFinite.circle D k (ground D α) (ground D (-α))) =
      epsilon D α (-α) • (∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) •
        Ring.choose (Hcharge D α) (2*k+1-j)) := by
    unfold NormFourZhuFinite.circle
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul, ground_product, map_smul, add_neg_cancel]
    have hj' := Finset.mem_range.mp hj
    have hn : -((j : ℤ)-2)-1-bilinear D α (-α) = ((2*k+1-j : ℕ) : ℤ) := by
      rw [bilinear_neg_right, ← two_chargeEnergy, ← hk]
      omega
    rw [hn, creation_class_choose D α (2*k+1-j), smul_comm]
  rw [he] at hcircle
  have heps : epsilon D α (-α) ≠ 0 := by
    unfold epsilon paritySign
    split <;> norm_num
  exact (smul_eq_zero.mp hcircle).resolve_left heps

/-- Chu--Vandermonde converts the literal circle into the current's integer-root relation. -/
theorem current_choose_relation (α : Charge D) :
    let k := (chargeEnergy D α).toNat
    Ring.choose ((k : Q D) + Hcharge D α) (2*k+1) = 0 := by
  classical
  let k := (chargeEnergy D α).toNat
  change Ring.choose ((k : Q D) + Hcharge D α) (2*k+1) = 0
  rw [Ring.add_choose_eq (2*k+1) (Nat.cast_commute k (Hcharge D α)),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have he : (∑ j ∈ Finset.range (2*k+1+1),
      Ring.choose (k : Q D) j * Ring.choose (Hcharge D α) (2*k+1-j)) =
      ∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) •
        Ring.choose (Hcharge D α) (2*k+1-j) := by
    rw [← Finset.sum_subset (Finset.range_mono (by omega : k+1 ≤ 2*k+1+1))]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Ring.choose_natCast]
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    · intro j _ hj
      rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by
        have hj' : ¬ j < k+1 := by simpa only [Finset.mem_range] using hj
        omega), Nat.cast_zero, zero_mul]
  rw [he]
  exact opposite_circle_sum D α

private theorem choose_factorial_product (x : Q D) (n : ℕ) :
    n.factorial • Ring.choose x n =
      ((List.range n).map fun j : ℕ => x - (j : Q D)).prod := by
  induction n with
  | zero => simp [Ring.choose_zero_right]
  | succ n ih =>
    have hb := Ring.choose_smul_choose x (n := n+1) (k := n) (by omega)
    simp only [Nat.choose_succ_self_right, show n+1-n = 1 by omega,
      Ring.choose_one_right] at hb
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_singleton, List.prod_singleton]
    rw [Nat.factorial_succ, mul_nsmul, hb, ← smul_mul_assoc, ih]

/-- All-alpha squarefree current polynomial on the original full quotient,
with roots -k,-k+1,...,k; zero charge and rank zero are included. -/
theorem all_alpha_current_relation (α : Charge D) :
    let k := (chargeEnergy D α).toNat
    ((List.range (2*k+1)).map fun j : ℕ => Hcharge D α + (k : Q D) - (j : Q D)).prod = 0 := by
  let k := (chargeEnergy D α).toNat
  change ((List.range (2*k+1)).map fun j : ℕ =>
    Hcharge D α + (k : Q D) - (j : Q D)).prod = 0
  have hz := congrArg (fun x : Q D => (2*k+1).factorial • x)
    (current_choose_relation D α)
  rw [choose_factorial_product D, smul_zero] at hz
  change ((List.range (2*k+1)).map fun j : ℕ =>
    (k : Q D) + Hcharge D α - (j : Q D)).prod = 0 at hz
  simpa only [add_comm (k : Q D) (Hcharge D α)] using hz

#print axioms creation_class_recurrence
#print axioms creation_class_choose
#print axioms all_alpha_current_relation
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuCurrentRelations

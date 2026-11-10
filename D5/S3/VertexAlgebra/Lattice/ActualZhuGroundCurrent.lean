/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native mixed-commutator right-current law on the literal Zhu quotient. -/
/-
The lattice Zhu current relations follow Dong--Li--Mason,
Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L),
DOI 10.1006/jabr.1997.7112, Theorem 3.4 and Remark 2.11.
The direct mixed-commutator proof uses the original lattice fields.
These are consumed groundwork for the source oscillator normal form.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuAlgebra
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualMixedLocality
import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra

/-! Literal mixed-current relations for source-side normal forms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualZhuGroundCurrent
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualConformalState LatticeActualVertexAlgebra LatticePositiveEnergy
open ActualZhuProduct ActualZhuFinite ActualZhuAlgebra ActualZhuLeftIdeal
open scoped BigOperators VertexOperator
open private star_vacuum_right
  from D5.S3.VertexAlgebra.Lattice.ActualZhuAlgebra
noncomputable section

variable (D : LatticeData) (δ : Charge D) (i : Fin D.rank)
local notation "e" => (Finsupp.single δ (1 : Oscillator D))
local notation "h" => (currentState D i)
local notation "lam" => (bilinear D (unitCharge D i) δ : ℂ)

private theorem ground_current_coeff (n : ℤ) :
    mu D e n h = neutralMode D i (-1) (mu D e n (vacuum D)) -
      lam • mu D e (n-1) (vacuum D) := by
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A (vacuum D))
    (LatticeActualMixedLocality.neutral_actual_commutator D i δ (-1) n)
  simp only [FieldNormalProductLocality.commutator, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, current_state_creation] at hc
  rw [neutralField_ncoeff] at hc
  simp only [← stateField_ground D δ,
    show (-1 : ℤ)+n = n-1 by omega] at hc
  change neutralMode D i (-1) (mu D e n (vacuum D)) - mu D e n h =
    lam • mu D e (n-1) (vacuum D) at hc
  rw [← hc]
  abel

private theorem ground_current_modes :
    mu D e (-1) h = neutralMode D i (-1) e - lam • translation D e ∧
    mu D e 0 h = -(lam • e) ∧
    ∀ n : ℤ, 1 ≤ n → mu D e n h = 0 := by
  have hm1 : mu D e (-1) (vacuum D) = e := stateField_creation D e
  have hm2 : mu D e (-2) (vacuum D) = translation D e :=
    (translation_as_mode D e).symm
  have hz (n : ℤ) (hn : 0 ≤ n) : mu D e n (vacuum D) = 0 :=
    stateField_creativity D e n hn
  refine ⟨?_, ?_, ?_⟩
  · rw [ground_current_coeff, hm1,
      show (-1 : ℤ)-1 = -2 by omega, hm2]
  · rw [ground_current_coeff, hz 0 (by omega), map_zero,
      show (0 : ℤ)-1 = -1 by omega, hm1, zero_sub]
  · intro n hn
    rw [ground_current_coeff, hz n (by omega), hz (n-1) (by omega),
      map_zero, smul_zero, sub_zero]

private theorem ground_star_current (K : ℕ) (he : e ∈ grade D (K : ℤ)) :
    star D e h = neutralMode D i (-1) e -
      lam • (translation D e + (K : ℂ) • e) := by
  classical
  obtain ⟨hm1, h0, hpos⟩ := ground_current_modes D δ i
  cases K with
  | zero =>
      rw [star_homogeneous D 0 e h he]
      simpa using hm1
  | succ k =>
      rw [star_homogeneous D (k+1) e h he,
        Finset.sum_range_succ', Finset.sum_range_succ']
      have hz : (∑ j ∈ Finset.range k,
          ((k+1).choose (j+1+1) : ℂ) •
            mu D e (((j+1+1 : ℕ) : ℤ)-1) h) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hpos _ (by omega), smul_zero]
      rw [hz]
      simp only [Nat.cast_zero, Nat.cast_one, zero_sub, Nat.choose_zero_right,
        one_smul, hm1, Nat.cast_add, sub_self, Nat.choose_one_right,
        h0, zero_add]
      module

theorem ground_grade
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    e ∈ grade D ((chargeEnergy D δ).toNat : ℤ) := by
  rw [Int.toNat_of_nonneg (chargeEnergy_nonneg D hD δ), grade_eq_span]
  have hb : carrierBasis D (δ, 0) ∈
      Submodule.span ℂ
        (carrierBasis D '' {a : Label D | energy D a = chargeEnergy D δ}) := by
    apply Submodule.subset_span
    exact ⟨(δ, 0), by simp [energy, oscillatorEnergy], rfl⟩
  simpa [carrierBasis_apply] using hb

theorem translation_weight_mem_zhuO
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {K : ℕ} {a : Carrier D} (ha : a ∈ grade D (K : ℤ)) :
    translation D a + (K : ℂ) • a ∈ zhuO D := by
  have hc := translation_star_circle D hD ha (vacuum D)
  rw [star_vacuum_right D hD] at hc
  rw [hc]
  exact Submodule.subset_span ⟨K, a, vacuum D, ha, rfl⟩

theorem ground_right_current
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    quotientProduct D hD ((zhuO D).mkQ e) ((zhuO D).mkQ h) =
      (zhuO D).mkQ (neutralMode D i (-1) e) := by
  let K := (chargeEnergy D δ).toNat
  have he : e ∈ grade D (K : ℤ) := ground_grade D δ hD
  have hO := translation_weight_mem_zhuO D hD he
  have hz : (zhuO D).mkQ (translation D e + (K : ℂ) • e) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hO
  rw [quotientProduct_mk, ground_star_current D δ i K he,
    map_sub, map_smul, hz, smul_zero, sub_zero]

theorem current_grade : h ∈ grade D (1 : ℤ) := by
  rw [grade_eq_span]
  have hb : carrierBasis D (0, Finsupp.single (i, 0) 1) ∈
      Submodule.span ℂ (carrierBasis D '' {a : Label D | energy D a = 1}) := by
    apply Submodule.subset_span
    exact ⟨(0, Finsupp.single (i, 0) 1),
      by simp [energy, oscillatorEnergy, Finsupp.weight_single], rfl⟩
  simpa [carrierBasis_apply, currentState, MvPolynomial.X] using hb

theorem current_star_single (p : Oscillator D) :
    star D h (Finsupp.single δ p) =
      neutralMode D i (-1) (Finsupp.single δ p) + lam • Finsupp.single δ p := by
  classical
  rw [star_homogeneous D 1 h _ (current_grade D i)]
  simp [Finset.sum_range_succ, mu, current_state_field, neutralField_ncoeff,
    neutralMode_single, neutralPolynomialMode, Finsupp.smul_single]

#print axioms ground_right_current
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuGroundCurrent

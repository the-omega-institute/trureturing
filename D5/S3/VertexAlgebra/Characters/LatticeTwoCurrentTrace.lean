/- GID: D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact two-current traces on finite full-energy grades of positive integral lattices. -/

import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Nat.Dist

/-! Ordinary monomial currents on the original all-charge energy grades.
The current normalization is the lattice construction of Bakalov--Kac,
math/0402315v1, section 4.1. Finite marked occupations are counted by
removing and restoring particles at a fixed positive frequency.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators VertexOperator
open MvPolynomial

namespace D5.S3.VertexAlgebra.LatticeTwoCurrentTrace
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeThetaCharacter

/-- The block of the original current field between two actual full grades. -/
def actualCurrentBlock (D : LatticeData) (i : Fin D.rank) (n m : ℕ) :
    grade D (m : ℤ) →ₗ[ℂ] grade D (n : ℤ) :=
  (((gradeProjection D (n : ℤ)).comp
    ((Y D (currentState D i))[[ (m : ℤ) - (n : ℤ) ]])).domRestrict
      (grade D (m : ℤ))).codRestrict (grade D (n : ℤ))
        (fun v => gradeProjection_mem D (n : ℤ) _)

/-- The trace of the literal finite current cycle, with no ambient trace. -/
def actualCurrentCycleTrace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (n m : ℕ) : ℂ := by
  letI := grade_finiteDimensional D hD (n : ℤ)
  exact LinearMap.trace ℂ (grade D (n : ℤ))
    ((actualCurrentBlock D i n m).comp (actualCurrentBlock D j m n))

/-- Ordinary, unweighted monomial multiplicity. -/
def occupationMultiplicity (D : LatticeData) (a : ℕ) : ℂ :=
  Nat.card (IntegerFiber D a)

private theorem energy_add (D : LatticeData) (d e : Exponent D) :
    oscillatorEnergy (d + e) = oscillatorEnergy d + oscillatorEnergy e := by
  exact map_add (Finsupp.weight (fun x : Index D => x.2 + 1)) d e

private theorem energy_single (D : LatticeData) (x : Index D) (k : ℕ) :
    oscillatorEnergy (Finsupp.single x k : Exponent D) = (x.2 + 1) * k := by
  simp [oscillatorEnergy, Finsupp.weight_single, smul_eq_mul, mul_comm]

private theorem remove_energy (D : LatticeData) (d : Exponent D) (x : Index D)
    (k : ℕ) (hk : k ≤ d x) :
    oscillatorEnergy (d - Finsupp.single x k) + (x.2 + 1) * k = oscillatorEnergy d := by
  rw [← energy_single D x k, ← energy_add]
  congr 1
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hk)

private theorem marked_bound (D : LatticeData) (d : Exponent D) (x : Index D)
    (k : ℕ) (hk : k ≤ d x) : (x.2 + 1) * k ≤ oscillatorEnergy d := by
  have h := remove_energy D d x k hk
  omega

/-- Removing a chosen number of marked particles preserves precisely the residual energy. -/
private def markedEquiv (D : LatticeData) (a : ℕ) (x : Index D) :
    (Σ w : IntegerFiber D a, Fin (w.1 x + 1)) ≃
      (Σ k : Fin (a / (x.2 + 1) + 1), IntegerFiber D (a - k.1 * (x.2 + 1))) where
  toFun z := by
    have hk : z.2.1 ≤ z.1.1 x := by have := z.2.2; omega
    have hb := marked_bound D z.1.1 x z.2.1 hk
    have ha := z.1.2
    have hdiv : z.2.1 ≤ a / (x.2 + 1) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      simpa [mul_comm, ha] using hb
    refine ⟨⟨z.2.1, by omega⟩, ⟨z.1.1 - Finsupp.single x z.2.1, ?_⟩⟩
    have h := remove_energy D z.1.1 x z.2.1 hk
    rw [ha] at h
    change oscillatorEnergy (z.1.1 - Finsupp.single x z.2.1) = a - z.2.1 * (x.2 + 1)
    rw [Nat.mul_comm] at h
    omega
  invFun z := by
    have hk : z.1.1 * (x.2 + 1) ≤ a := by
      apply (Nat.le_div_iff_mul_le (by omega)).mp
      have := z.1.2
      omega
    refine ⟨⟨z.2.1 + Finsupp.single x z.1.1, ?_⟩, ⟨z.1.1, ?_⟩⟩
    · rw [energy_add, energy_single, z.2.2, Nat.mul_comm (x.2 + 1)]
      exact Nat.sub_add_cancel hk
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
  left_inv z := by
    classical
    have hk : z.2.1 ≤ z.1.1 x := by have := z.2.2; omega
    have he : z.1.1 - Finsupp.single x z.2.1 + Finsupp.single x z.2.1 = z.1.1 :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hk)
    apply Sigma.ext (Subtype.ext he)
    exact (Fin.heq_ext_iff (congrArg (fun d : Exponent D => d x + 1) he)).mpr rfl
  right_inv z := by
    classical
    apply Sigma.ext
    · apply Fin.ext; rfl
    · apply heq_of_eq
      exact Subtype.ext (add_tsub_cancel_right _ _)

private theorem marked_count (D : LatticeData) (a : ℕ) (x : Index D) :
    (∑ w : IntegerFiber D a, (w.1 x + 1 : ℕ)) =
      ∑ k ∈ Finset.range (a / (x.2 + 1) + 1),
        Nat.card (IntegerFiber D (a - k * (x.2 + 1))) := by
  classical
  have h := Fintype.card_congr (markedEquiv D a x)
  simp only [Fintype.card_sigma, Fintype.card_fin] at h
  simp only [Nat.card_eq_fintype_card]
  calc
    _ = ∑ k : Fin (a / (x.2 + 1) + 1),
        Fintype.card (IntegerFiber D (a - k.1 * (x.2 + 1))) := h
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun k => Fintype.card (IntegerFiber D (a - k * (x.2 + 1))))
      (a / (x.2 + 1) + 1)

private theorem projection_basis (D : LatticeData) (n : ℤ) (a : Label D)
    (ha : energy D a = n) : gradeProjection D n (carrierBasis D a) = carrierBasis D a := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext b
  rw [gradeProjection_coeff]
  change (if energy D b = n then Finsupp.single a (1 : ℂ) b else 0) =
    Finsupp.single a (1 : ℂ) b
  by_cases h : a = b
  · subst b; simp [ha]
  · simp [Finsupp.single_apply, h]

private theorem grade_repr (D : LatticeData) (n : ℤ)
    (v : grade D n) (a : EnergyFiber D n) :
    (gradeBasis D n).repr v a = carrierCoeffEquiv D v.1 a.1 := rfl

private theorem basis_value (D : LatticeData) (n : ℤ) (a : EnergyFiber D n) :
    (gradeBasis D n a : Carrier D) = carrierBasis D a.1 := by
  run_tac
    let supplier := (Lean.Name.num
      `_private.D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades 0).append
      `D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades.gradeBasis_coe
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($(Lean.mkIdent supplier)) _ _ _))

private theorem returning_coefficient (D : LatticeData) (i j : Fin D.rank)
    (β : Charge D) (d : Exponent D) (r : ℕ) :
    (neutralPolynomialMode D i β ((r : ℤ) + 1)
      (X (j,r) * monomial d 1)).coeff d =
        (r + 1 : ℂ) * (D.G i j : ℂ) * (d (j,r) + 1 : ℕ) := by
  classical
  rw [neutralPolynomialMode_positive]
  simp only [LinearMap.smul_apply, coeff_smul, weightedPartial,
    LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    coeff_sum, coeff_smul, smul_eq_mul, coeff_pderiv]
  have hc (c : Fin D.rank) :
      (X (j,r) * monomial d (1 : ℂ)).coeff (d + Finsupp.single (c,r) 1) =
        if c = j then 1 else 0 := by
    rw [X, monomial_mul_monomial]
    simp only [one_mul, coeff_monomial]
    have he : Finsupp.single (j,r) 1 + d = d + Finsupp.single (c,r) 1 ↔ c = j := by
      rw [add_comm, add_left_cancel_iff]
      constructor
      · intro h
        have hz := congrArg (fun f : Exponent D => f (j,r)) h
        by_contra hne
        simp [Finsupp.single_apply, hne, Ne.symm hne] at hz
      · rintro rfl; rfl
    simp [he]
  simp_rw [hc]
  simp [mul_assoc]

private theorem cycle_diag_upper (D : LatticeData) (i j : Fin D.rank)
    (n r : ℕ) (a : EnergyFiber D (n : ℤ)) :
    (gradeBasis D (n : ℤ)).repr
      ((actualCurrentBlock D i n (n + (r + 1))).comp
        (actualCurrentBlock D j (n + (r + 1)) n) (gradeBasis D (n : ℤ) a)) a =
      (r + 1 : ℂ) * (D.G i j : ℂ) * (a.1.2 (j,r) + 1 : ℕ) := by
  classical
  have he : energy D (a.1.1, Finsupp.single (j,r) 1 + a.1.2) =
      ((n + (r + 1) : ℕ) : ℤ) := by
    have ha := a.2
    simp only [energy] at ha ⊢
    rw [energy_add, energy_single]
    push_cast
    omega
  have hb : ((Y D (currentState D j))[[ (n : ℤ) - (n + (r + 1) : ℕ) ]])
      (carrierBasis D a.1) =
      carrierBasis D (a.1.1, Finsupp.single (j,r) 1 + a.1.2) := by
    rw [current_state_field, neutralField_ncoeff, carrierBasis_apply, neutralMode_single]
    rw [show (n : ℤ) - (n + (r + 1) : ℕ) = -(r : ℤ) - 1 by omega,
      neutralPolynomialMode_negative, LinearMap.mulLeft_apply, X,
      monomial_mul_monomial, one_mul, carrierBasis_apply]
  rw [grade_repr]
  change carrierCoeffEquiv D
    (gradeProjection D (n : ℤ)
      (((Y D (currentState D i))[[ ((n + (r + 1) : ℕ) : ℤ) - (n : ℤ) ]])
        (gradeProjection D ((n + (r + 1) : ℕ) : ℤ)
          (((Y D (currentState D j))[[ (n : ℤ) - ((n + (r + 1) : ℕ) : ℤ) ]])
            (gradeBasis D (n : ℤ) a))))) a.1 = _
  rw [basis_value, hb, projection_basis D _ _ he, gradeProjection_coeff, if_pos a.2,
    current_state_field, neutralField_ncoeff, carrierBasis_apply, neutralMode_single]
  change ((Finsupp.single a.1.1
    (neutralPolynomialMode D i a.1.1 (((n + (r + 1) : ℕ) : ℤ) - (n : ℤ))
      (monomial (Finsupp.single (j,r) 1 + a.1.2) 1))) a.1.1).coeff a.1.2 = _
  rw [Finsupp.single_eq_same]
  rw [show ((n + (r + 1) : ℕ) : ℤ) - (n : ℤ) = (r : ℤ) + 1 by omega]
  have hm : monomial (Finsupp.single (j,r) 1 + a.1.2) (1 : ℂ) =
      X (j,r) * monomial a.1.2 1 := by simp [X, monomial_mul_monomial]
  rw [hm]
  exact returning_coefficient D i j a.1.1 a.1.2 r

private def fullFiberEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℕ) :
    EnergyFiber D (n : ℤ) ≃
      (Σ β : positiveChargeCutoff D hD (n : ℤ),
        IntegerFiber D (n - (chargeEnergy D β.1).toNat)) where
  toFun a := by
    have ha := a.2
    have hq := chargeEnergy_nonneg D hD a.1.1
    simp only [energy] at ha
    refine ⟨⟨a.1.1, ?_⟩, ⟨a.1.2, ?_⟩⟩
    · simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
        Int.toNat_natCast]
      omega
    · change oscillatorEnergy a.1.2 = n - (chargeEnergy D a.1.1).toNat
      omega
  invFun a := by
    have hb := a.1.2
    simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      Int.toNat_natCast] at hb
    have hq := chargeEnergy_nonneg D hD a.1.1
    refine ⟨(a.1.1, a.2.1), ?_⟩
    simp only [energy]
    have ha := a.2.2
    omega
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by
    apply Sigma.ext (Subtype.ext rfl)
    apply heq_of_eq
    rfl

private theorem sum_fullFiber (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℕ)
    (f : Charge D → Exponent D → ℂ) :
    letI := energyFiber_finite D hD (n : ℤ)
    letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
    (∑ a : EnergyFiber D (n : ℤ), f a.1.1 a.1.2) =
      ∑ β ∈ positiveChargeCutoff D hD (n : ℤ),
        ∑ w : IntegerFiber D (n - (chargeEnergy D β).toNat), f β w.1 := by
  classical
  letI := energyFiber_finite D hD (n : ℤ)
  letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
  calc
    _ = ∑ a : (Σ β : positiveChargeCutoff D hD (n : ℤ),
        IntegerFiber D (n - (chargeEnergy D β.1).toNat)), f a.1.1 a.2.1 :=
      Fintype.sum_equiv (fullFiberEquiv D hD n) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      exact Finset.sum_coe_sort (positiveChargeCutoff D hD (n : ℤ))
        (fun β : Charge D => ∑ w : IntegerFiber D (n - (chargeEnergy D β).toNat), f β w.1)

private theorem trace_upper (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (n r : ℕ) :
    actualCurrentCycleTrace D hD i j n (n + (r + 1)) =
      (r + 1 : ℂ) * (D.G i j : ℂ) *
        ∑ β ∈ positiveChargeCutoff D hD (n : ℤ),
          ∑ k ∈ Finset.range ((n - (chargeEnergy D β).toNat) / (r + 1) + 1),
            occupationMultiplicity D (n - (chargeEnergy D β).toNat - k * (r + 1)) := by
  classical
  letI := grade_finiteDimensional D hD (n : ℤ)
  letI := energyFiber_finite D hD (n : ℤ)
  letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
  rw [actualCurrentCycleTrace, LinearMap.trace_eq_matrix_trace ℂ (gradeBasis D (n : ℤ))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, cycle_diag_upper]
  simp_rw [← Finset.mul_sum]
  rw [sum_fullFiber D hD n (fun _ d => ((d (j,r) + 1 : ℕ) : ℂ))]
  congr 1
  apply Finset.sum_congr rfl
  intro β hβ
  have hc := marked_count D (n - (chargeEnergy D β).toNat) (j,r)
  dsimp only at hc
  simp only [occupationMultiplicity]
  exact_mod_cast hc

private theorem block_zero_basis (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (a : EnergyFiber D (n : ℤ)) :
    actualCurrentBlock D i n n (gradeBasis D (n : ℤ) a) =
      (bilinear D (unitCharge D i) a.1.1 : ℂ) • gradeBasis D (n : ℤ) a := by
  apply Subtype.ext
  change gradeProjection D (n : ℤ) (((Y D (currentState D i))[[ (n : ℤ) - n ]])
    (gradeBasis D (n : ℤ) a)) = _
  rw [basis_value, current_state_field, neutralField_ncoeff, sub_self,
    carrierBasis_apply, neutralMode_single]
  simp only [neutralPolynomialMode, lt_self_iff_false, ↓reduceIte,
    LinearMap.smul_apply, LinearMap.id_apply, ← Finsupp.smul_single, map_smul]
  rw [← carrierBasis_apply, projection_basis D _ _ a.2]
  rw [Submodule.coe_smul, basis_value]

private theorem cycle_diag_equal (D : LatticeData) (i j : Fin D.rank)
    (n : ℕ) (a : EnergyFiber D (n : ℤ)) :
    (gradeBasis D (n : ℤ)).repr
      ((actualCurrentBlock D i n n).comp (actualCurrentBlock D j n n)
        (gradeBasis D (n : ℤ) a)) a =
      (bilinear D (unitCharge D i) a.1.1 : ℂ) *
        (bilinear D (unitCharge D j) a.1.1 : ℂ) := by
  classical
  simp [LinearMap.comp_apply, block_zero_basis, map_smul, smul_eq_mul, mul_comm]

private theorem trace_equal (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (n : ℕ) :
    actualCurrentCycleTrace D hD i j n n =
      ∑ β ∈ positiveChargeCutoff D hD (n : ℤ),
        (bilinear D (unitCharge D i) β : ℂ) *
          (bilinear D (unitCharge D j) β : ℂ) *
            occupationMultiplicity D (n - (chargeEnergy D β).toNat) := by
  classical
  letI := grade_finiteDimensional D hD (n : ℤ)
  letI := energyFiber_finite D hD (n : ℤ)
  letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
  rw [actualCurrentCycleTrace, LinearMap.trace_eq_matrix_trace ℂ (gradeBasis D (n : ℤ))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, cycle_diag_equal]
  rw [sum_fullFiber D hD n (fun β _ =>
    (bilinear D (unitCharge D i) β : ℂ) * (bilinear D (unitCharge D j) β : ℂ))]
  simp [occupationMultiplicity, Nat.card_eq_fintype_card, mul_comm]

private theorem trace_exchange (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (n m : ℕ) :
    actualCurrentCycleTrace D hD i j n m = actualCurrentCycleTrace D hD j i m n := by
  letI := grade_finiteDimensional D hD (n : ℤ)
  letI := grade_finiteDimensional D hD (m : ℤ)
  exact LinearMap.trace_comp_comm' (actualCurrentBlock D j m n) (actualCurrentBlock D i n m)

/-- The exact ordinary two-current trace for every pair of finite full-energy grades.
The off-diagonal coefficient counts marked particles in the lower grade. -/
theorem actual_two_current_grade_trace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (n m : ℕ) :
    actualCurrentCycleTrace D hD i j n m =
      if n = m then
        ∑ β ∈ positiveChargeCutoff D hD (n : ℤ),
          (bilinear D (unitCharge D i) β : ℂ) *
            (bilinear D (unitCharge D j) β : ℂ) *
              occupationMultiplicity D (n - (chargeEnergy D β).toNat)
      else
        (Nat.dist n m : ℂ) * (D.G i j : ℂ) *
          ∑ β ∈ positiveChargeCutoff D hD ((min n m : ℕ) : ℤ),
            ∑ k ∈ Finset.range ((min n m - (chargeEnergy D β).toNat) / Nat.dist n m + 1),
              occupationMultiplicity D (min n m - (chargeEnergy D β).toNat - k * Nat.dist n m) := by
  classical
  by_cases he : n = m
  · subst m
    rw [if_pos rfl]
    exact trace_equal D hD i j n
  · rw [if_neg he]
    rcases lt_or_gt_of_ne he with h | h
    · let r := m - n - 1
      have hm : m = n + (r + 1) := by dsimp [r]; omega
      have hd : Nat.dist n m = r + 1 := by rw [Nat.dist_eq_sub_of_le h.le]; omega
      rw [Nat.min_eq_left h.le, hd, hm]
      simpa only [Nat.cast_add, Nat.cast_one] using trace_upper D hD i j n r
    · let r := n - m - 1
      have hn : n = m + (r + 1) := by dsimp [r]; omega
      have hd : Nat.dist n m = r + 1 := by rw [Nat.dist_eq_sub_of_le_right h.le]; omega
      rw [Nat.min_eq_right h.le, hd, trace_exchange, hn, ← D.symmetric j i]
      simpa only [Nat.cast_add, Nat.cast_one] using trace_upper D hD j i m r

#print axioms actual_two_current_grade_trace

end D5.S3.VertexAlgebra.LatticeTwoCurrentTrace

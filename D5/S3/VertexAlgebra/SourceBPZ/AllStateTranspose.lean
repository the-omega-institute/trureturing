/- GID: D5/S3/VertexAlgebra/SourceBPZ/AllStateTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/AllStateTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Basic]
   utility: none
   digest: Original-source all-state BPZ with the actual finite Sugawara flow. -/

import D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner

/-!
The standard invariant bilinear form identity for the original lattice fields
is proved by finite oscillator insertion. The actual polynomial Möbius flow
collects both insertion and charge-zero-mode deletion terms. Its existing
factorial coefficient theorem identifies the result with the inverse-Gram
Sugawara operator. Charge energy may be negative and rank may be zero.
The lattice-field conventions are those of Bakalov--Kac, math/0402315v1,
section 4.1; no literature novelty is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualProductKernel LatticeActualGeneratorLocality
open LatticeSugawaraCurrents LatticeAllStateField
open LatticePositiveEnergy SourceMobius OriginalSourcePairing MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open private multiplication_recursion from
  D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule

private def leftPair (D : LatticeData) (m : ℤ) (u v : Carrier D) :
    Carrier D →ₗ[ℂ] ℂ where
  toFun a := sourcePairing D (((Y D a)[[m]]) u) v
  map_add' a b := by simp
  map_smul' c a := by simp

private def rightPair (D : LatticeData) (m : ℤ) (u v : Carrier D) :
    Carrier D →ₗ[ℂ] ℂ where
  toFun a := sourcePairing D u (((Y D a)[[m]]) v)
  map_add' a b := by simp
  map_smul' c a := by simp

private def modePair (D : LatticeData) (α : Charge D) (k : ℤ) (u v : Carrier D) :
    Oscillator D →ₗ[ℂ] ℂ := (rightPair D k u v).comp (Finsupp.lsingle α)

private def polynomialPair (D : LatticeData) (α : Charge D) (K : ℤ)
    (u v : Carrier D) : Polynomial (Oscillator D) →ₗ[ℂ] ℂ where
  toFun P := P.sum (fun j q => modePair D α (K-j) u v q)
  map_add' P Q := Polynomial.sum_add_index _ _ _
    (fun _ => map_zero _) (fun _ _ _ => map_add _ _ _)
  map_smul' c P := by
    rw [Polynomial.sum_smul_index' _ _ _ (fun _ => map_zero _)]
    simp only [map_smul, Polynomial.sum, Finset.smul_sum, RingHom.id_apply]

private theorem polynomialPair_monomial (D : LatticeData) (α : Charge D)
    (K : ℤ) (u v : Carrier D) (j : ℕ) (q : Oscillator D) :
    polynomialPair D α K u v (Polynomial.monomial j q) =
      modePair D α (K-j) u v q := by
  exact Polynomial.sum_monomial_index _ _ (map_zero _)

private theorem flow_X_polynomial (D : LatticeData) (α : Charge D)
    (i : Fin D.rank) (p : ℕ) :
    flowPolynomial D α (X (i,p)) =
      (∑ s ∈ Finset.range (p+1), Polynomial.monomial (p-s)
        (((p+1).choose (s+1) : ℂ) • (X (i,s) : Oscillator D))) +
      Polynomial.monomial (p+1) (C (bilinear D (unitCharge D i) α : ℂ)) := by
  classical
  have bound : ((sectorL1 D α).toLinearMap ^ ((p+1)+1)) (X (i,p)) = 0 := by
    have h := sectorL1_monomial_bound D α (Finsupp.single (i,p) 1) 1
    simpa [Finsupp.weight_single, sourceWeight, MvPolynomial.X] using h
  rw [flowPolynomial_eq_sum D α _ (p+1) bound, Finset.sum_range_succ,
    variable_power_charge, smul_smul, inv_mul_cancel₀
      (by exact_mod_cast Nat.factorial_ne_zero (p+1) : ((p+1).factorial : ℂ) ≠ 0),
    one_smul]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range (p+1), Polynomial.monomial n
        (((p+1).choose n : ℂ) • (X (i,p-n) : Oscillator D)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [variable_power D α i p n (by simpa using Finset.mem_range.mp hn),
        smul_smul, Nat.descFactorial_eq_factorial_mul_choose]
      congr 2
      push_cast
      rw [inv_mul_cancel_left₀ (by exact_mod_cast Nat.factorial_ne_zero n)]
    _ = _ := by
      rw [← Finset.sum_range_reflect (fun n => Polynomial.monomial n
        (((p+1).choose n : ℂ) • (X (i,p-n) : Oscillator D))) (p+1)]
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ≤ p := by simpa using Finset.mem_range.mp hs
      have chosen : (p+1).choose (p-s) = (p+1).choose (s+1) := by
        apply Nat.choose_symm_of_eq_add
        omega
      simp only [Nat.add_sub_cancel, show p-(p-s) = s by omega, chosen]

private theorem polynomialPair_insertion (D : LatticeData) (α : Charge D)
    (i : Fin D.rank) (p : ℕ) (P : Polynomial (Oscillator D))
    (K : ℤ) (u v : Carrier D) :
    polynomialPair D α K u v (flowPolynomial D α (X (i,p)) * P) =
      ∑ l ∈ P.support,
        ((∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) *
          modePair D α (K-l-p+s) u v (X (i,s) * P.coeff l)) +
          (bilinear D (unitCharge D i) α : ℂ) *
            modePair D α (K-l-p-1) u v (P.coeff l)) := by
  classical
  conv_lhs => arg 2; rw [← P.sum_monomial_eq]
  simp only [Polynomial.sum, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [flow_X_polynomial, add_mul, Finset.sum_mul, map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro s hs
    have hs' : s ≤ p := by simpa using Finset.mem_range.mp hs
    rw [Polynomial.monomial_mul_monomial, polynomialPair_monomial,
      smul_mul_assoc, map_smul, smul_eq_mul]
    rw [show K-((p-s+l : ℕ) : ℤ) = K-l-p+s by
      rw [Nat.cast_add, Int.natCast_sub hs']; omega]
  · rw [Polynomial.monomial_mul_monomial, polynomialPair_monomial,
      ← smul_eq_C_mul, map_smul, smul_eq_mul]
    rw [show K-((p+1+l : ℕ) : ℤ) = K-l-p-1 by push_cast; omega]

private theorem zero_mode_covariance (D : LatticeData) (α : Charge D)
    (i : Fin D.rank) (q : Oscillator D) (t : ℤ) (x : Carrier D) :
    neutralMode D i 0 (((Y D (Finsupp.single α q))[[t]]) x) =
      ((Y D (Finsupp.single α q))[[t]]) (neutralMode D i 0 x) +
        (bilinear D (unitCharge D i) α : ℂ) •
          ((Y D (Finsupp.single α q))[[t]]) x := by
  have scalar (β : Charge D) (r : Oscillator D) :
      neutralMode D i 0 (Finsupp.single β r) =
        (bilinear D (unitCharge D i) β : ℂ) • Finsupp.single β r := by
    simp [neutralMode_single, neutralPolynomialMode, Finsupp.smul_single]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | single β r =>
    have h := LatticeSectorIntertwiner.charge_homogeneity D α β q r t
    calc
      _ = (bilinear D (unitCharge D i) (α+β) : ℂ) •
          ((Y D (Finsupp.single α q))[[t]]) (Finsupp.single β r) := by
        conv_lhs => arg 2; rw [h]
        rw [scalar, ← h]
      _ = _ := by
        rw [scalar, map_smul, bilinear_add_right, Int.cast_add, add_smul]
        exact add_comm _ _

private theorem ground_transpose (D : LatticeData) (α : Charge D)
    (m : ℤ) (u v : Carrier D) :
    leftPair D m u v (Finsupp.single α 1) =
      (-1 : ℂ)^(chargeEnergy D α) *
        polynomialPair D α (2*chargeEnergy D α-m-2) u v
          (flowPolynomial D α 1) := by
  rw [map_one]
  change leftPair D m u v (Finsupp.single α 1) =
    (-1 : ℂ)^(chargeEnergy D α) * polynomialPair D α _ u v (Polynomial.monomial 0 1)
  rw [polynomialPair_monomial]
  change sourcePairing D (((Y D (Finsupp.single α 1))[[m]]) u) v =
    (-1 : ℂ)^(chargeEnergy D α) *
      sourcePairing D u (((Y D (Finsupp.single α 1))[[2*chargeEnergy D α-m-2-0]]) v)
  rw [sub_zero, stateField_ground, actual_modes, actual_modes,
    ChargedRawTranspose.sourcePairing_rawCoeff]
  rw [show paritySign (bilinear D α α / 2) = (-1 : ℂ)^(chargeEnergy D α) by
    rw [chargeEnergy, paritySign, neg_one_zpow_eq_ite] ]
  rw [show -(-m-1)-bilinear D α α = -(2*chargeEnergy D α-m-2)-1 by
    have h := two_chargeEnergy D α
    omega]

set_option maxHeartbeats 400000 in
-- The finite normal-product expression retains the original field constructors.
private theorem word_transpose (D : LatticeData) (α : Charge D)
    (w : List (Index D)) (m : ℤ) (u v : Carrier D) :
    leftPair D m u v (Finsupp.single α ((w.map (fun x => (X x : Oscillator D))).prod)) =
      (-1 : ℂ)^(chargeEnergy D α + ((w.map (sourceWeight D)).sum : ℕ)) *
        polynomialPair D α
          (2*(chargeEnergy D α+((w.map (sourceWeight D)).sum : ℕ))-m-2) u v
          (flowPolynomial D α ((w.map (fun x => (X x : Oscillator D))).prod)) := by
  classical
  induction w generalizing m u v with
  | nil => simpa using ground_transpose D α m u v
  | cons x w ih =>
    rcases x with ⟨i,p⟩
    let q : Oscillator D := (w.map (fun x => (X x : Oscillator D))).prod
    let P := flowPolynomial D α q
    let d₀ : ℤ := chargeEnergy D α + ((w.map (sourceWeight D)).sum : ℕ)
    have htail (t : ℤ) (x y : Carrier D) :
        sourcePairing D (((Y D (Finsupp.single α q))[[t]]) x) y =
          ∑ l ∈ P.support, (-1 : ℂ)^d₀ *
            sourcePairing D x
              (((Y D (Finsupp.single α (P.coeff l)))[[2*d₀-l-2-t]]) y) := by
      have h := ih t x y
      change _ = (-1 : ℂ)^d₀ * polynomialPair D α (2*d₀-t-2) x y P at h
      change leftPair D t x y (Finsupp.single α q) = _
      rw [h]
      simp only [polynomialPair, LinearMap.coe_mk, AddHom.coe_mk,
        Polynomial.sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [show 2*d₀-t-2-(l : ℤ) = 2*d₀-l-2-t by omega]
      rfl
    have step := consumed_normal_product_form D (sourcePairing D) i
      (SourcePairingLaws.sourcePairing_neutralMode D i) p
      (Y D (Finsupp.single α q)) P.support
      (fun l => Y D (Finsupp.single α (P.coeff l)))
      (fun _ => (-1 : ℂ)^d₀) (fun l => 2*d₀-l-2)
      (bilinear D (unitCharge D i) α : ℂ) htail
      (fun _ _ => zero_mode_covariance D α i _) m u v
    have insert_field (s : ℕ) (r : Oscillator D) :
        insertion D i s (Y D (Finsupp.single α r)) =
          Y D (Finsupp.single α (X (i,s)*r)) :=
      (multiplication_recursion D (i,s) α r).symm
    simp only [insert_field] at step
    have sign : (-1 : ℂ)^(p+1) * (-1 : ℂ)^d₀ =
        (-1 : ℂ)^(d₀+((p+1 : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      congr 1
      omega
    have degree : chargeEnergy D α +
        (((((i,p) :: w).map (sourceWeight D)).sum : ℕ) : ℤ) =
          d₀+((p+1 : ℕ) : ℤ) := by
      simp only [List.map_cons, List.sum_cons, sourceWeight, Nat.cast_add,
        Nat.cast_one, d₀]
      omega
    rw [degree]
    simp only [List.map_cons, List.prod_cons]
    change leftPair D m u v (Finsupp.single α (X (i,p)*q)) =
      (-1 : ℂ)^(d₀+((p+1 : ℕ) : ℤ)) *
        polynomialPair D α (2*(d₀+((p+1 : ℕ) : ℤ))-m-2) u v
          (flowPolynomial D α (X (i,p)*q))
    rw [map_mul, polynomialPair_insertion, ← sign]
    rw [← Finset.mul_sum, ← mul_assoc] at step
    simp only [leftPair, LinearMap.coe_mk, AddHom.coe_mk]
    rw [step]
    simp only [modePair, LinearMap.comp_apply, Finsupp.lsingle_apply,
      rightPair, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    · apply Finset.sum_congr rfl
      intro s hs
      rw [show 2*d₀-(l : ℤ)-2+p+s+2-m =
          2*(d₀+((p+1 : ℕ) : ℤ))-m-2-l-p+s by push_cast; omega]
    · rw [show 2*d₀-(l : ℤ)-2+p+1-m =
          2*(d₀+((p+1 : ℕ) : ℤ))-m-2-l-p-1 by push_cast; omega]

private theorem occurrences_weight (D : LatticeData) (e : Index D →₀ ℕ) :
    ((occurrences D e).map (sourceWeight D)).sum = e.weight (sourceWeight D) := by
  rw [occurrences, Multiset.sum_map_toList]
  induction e using Finsupp.induction with
  | zero => simp
  | single_add x n tail absent nonzero ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add,
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.sum_nsmul,
      Multiset.map_singleton, Multiset.sum_singleton, ih,
      map_add, Finsupp.weight_single]

set_option maxHeartbeats 2000000 in
-- The sector-to-original-carrier identification unfolds linear-map powers.
private theorem monomial_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (α : Charge D) (e : Index D →₀ ℕ) (R : ℕ)
    (hR : e.weight (sourceWeight D) ≤ R) (m : ℤ) (u v : Carrier D) :
    leftPair D m u v (Finsupp.single α (monomial e 1)) =
      (-1 : ℂ)^(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ)) *
        ∑ j ∈ Finset.range (R+1), (j.factorial : ℂ)⁻¹ *
          rightPair D (2*(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ))-j-m-2) u v
            ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j)
              (Finsupp.single α (monomial e 1))) := by
  have h := word_transpose D α (occurrences D e) m u v
  rw [occurrences_product, occurrences_weight] at h
  have killed : ((sectorL1 D α).toLinearMap ^ (R+1)) (monomial e 1) = 0 :=
    Module.End.pow_map_zero_of_le (Nat.add_le_add_right hR 1)
      (sectorL1_monomial_bound D α e 1)
  rw [flowPolynomial_eq_sum D α _ R killed, map_sum] at h
  simp only [polynomialPair_monomial, map_smul, smul_eq_mul] at h
  rw [h]
  apply congrArg (fun z : ℂ =>
    (-1 : ℂ)^(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ)) * z)
  apply Finset.sum_congr rfl
  intro j hj
  rw [sugawara_pow_single D _ (Matrix.nonsing_inv_mul _ (gram_det_unit D hu))
    (Matrix.mul_nonsing_inv _ (gram_det_unit D hu))]
  rw [show 2*(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ))-m-2-j =
      2*(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ))-j-m-2 by omega]
  rfl

/-
proof_shape: sourcePairing_allState: content
admission_basis: escape-witness
escape_witness: word_transpose consumes the finite normal insertion law and
collects its insertion/deletion terms as the actual flowPolynomial product.
The induction uses only the remaining word; no transpose for a flow
coefficient is assumed. The original charge/monomial coefficient support
then supplies the common signed energy and the exact actual-support cutoff.
The other private helpers are consumed by this derivation.
-/
set_option maxHeartbeats 2000000 in
-- Both finite supports and the family of Sugawara powers are collected linearly.
/-- The canonical all-state original-source BPZ theorem, including rank zero
and indefinite determinant-unit lattice data. -/
theorem sourcePairing_allState (D : LatticeData) (hu : IsUnit D.G.det)
    (d m : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (u v : Carrier D) :
    sourcePairing D (((Y D a)[[m]]) u) v =
      (-1 : ℂ)^d * ∑ j ∈ Finset.range (a.support.sup
        (fun α => weightedTotalDegree (sourceWeight D) (a α)) + 1),
        (j.factorial : ℂ)⁻¹ * sourcePairing D u
          (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j) a))
            [[2*d-(j : ℤ)-m-2]]) v) := by
  classical
  let R := a.support.sup (fun α => weightedTotalDegree (sourceWeight D) (a α))
  let T : Carrier D →ₗ[ℂ] ℂ := ∑ j ∈ Finset.range (R+1),
    (j.factorial : ℂ)⁻¹ •
      (rightPair D (2*d-j-m-2) u v).comp (sugawaraMode D (gramComplex D)⁻¹ 1 ^ j)
  have applyT (b : Carrier D) : T b = ∑ j ∈ Finset.range (R+1),
      (j.factorial : ℂ)⁻¹ * rightPair D (2*d-j-m-2) u v
        ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j) b) := by
    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, smul_eq_mul]
  change leftPair D m u v a = (-1 : ℂ)^d * ∑ j ∈ Finset.range (R+1),
    (j.factorial : ℂ)⁻¹ * rightPair D (2*d-j-m-2) u v
      ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j) a)
  rw [← applyT]
  have basis (α : Charge D) (hα : α ∈ a.support) (e : Index D →₀ ℕ)
      (he : e ∈ (a α).support) :
      leftPair D m u v (Finsupp.single α (monomial e 1)) =
        (-1 : ℂ)^d * T (Finsupp.single α (monomial e 1)) := by
    have energy_eq : energy D (α,e) = d := by
      by_contra hn
      exact (MvPolynomial.mem_support_iff.mp he) ((mem_grade_iff D d a).mp ha (α,e) hn)
    have degree : chargeEnergy D α+(e.weight (sourceWeight D) : ℤ) = d := energy_eq
    have hR : e.weight (sourceWeight D) ≤ R :=
      (le_weightedTotalDegree (sourceWeight D) he).trans
        (Finset.le_sup (f := fun α => weightedTotalDegree (sourceWeight D) (a α)) hα)
    have h := monomial_transpose D hu α e R hR m u v
    rw [degree] at h
    simpa only [T, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      smul_eq_mul] using h
  have expansion : a = ∑ α ∈ a.support, ∑ e ∈ (a α).support,
      (a α).coeff e • Finsupp.single α (monomial e 1) := by
    calc
      a = ∑ α ∈ a.support, Finsupp.single α (a α) := (Finsupp.sum_single a).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro α hα
        conv_lhs => arg 2; rw [(a α).as_sum]
        rw [Finsupp.single_finsetSum]
        apply Finset.sum_congr rfl
        intro e he
        simp only [Finsupp.smul_single, smul_monomial, smul_eq_mul, mul_one]
  rw [expansion]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro e he
  rw [basis α hα e he]
  ring

#print axioms sourcePairing_allState

end D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

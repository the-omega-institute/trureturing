/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCovariance
   mirror-E: none(waiver:original-number-covariance)
   anchors: []
   utility: none
   digest: Native number covariance through actual sorted ghost words and tensor coefficients. -/

/- The original occupation-word state-field map is used, without a new BV
record or an assumed mode grading. Attribution to the original ghost authors,
Scott Carnahan's signed residue calculus, and Mathlib is retained.
proof_shape: ghost_number_field, number_mode, number_one_parity: content
admission_basis: escape-witness
escape_witness: Normal products add the original signed occupation weights;
pointwise finite tensor convolution proves covariance for every actual mode.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyGhostGrading
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeMatterGhostNumberCovariance

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostCharge (ghostNumber charge siteSign)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeMatterGhostDegree (tensorNumber)
open LatticeBRSTCohomologyField (originalMode originalMode_apply)
open FieldNormalProduct (dividedDerivative identityField)
open private signedNormalMinusOne forward_finite reverse_finite wordField Y_ket
  derivative_modes generatingField generatingMode from
  D5.S3.Quantum.Fermionic.BcGhostStateField
open private number_ket charge_sum from D5.S3.Quantum.Fermionic.BcGhostCharge
open private term term_tmul term_finite Y_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private N_b N_original_coefficient from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology
open private fullBasis_apply from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section

private theorem normal_number (s a b : ℂ) (A B : VertexOperator ℂ Fock)
    (hA : ∀ n : ℤ, ghostNumber * (A[[n]]) - (A[[n]]) * ghostNumber = a • (A[[n]]))
    (hB : ∀ n : ℤ, ghostNumber * (B[[n]]) - (B[[n]]) * ghostNumber = b • (B[[n]]))
    (n : ℤ) :
    ghostNumber * ((signedNormalMinusOne s A B).1[[n]]) -
        ((signedNormalMinusOne s A B).1[[n]]) * ghostNumber =
      (a + b) • ((signedNormalMinusOne s A B).1[[n]]) := by
  have actA (k : ℤ) (v : Fock) :
      ghostNumber ((A[[k]]) v) = a • (A[[k]]) v + (A[[k]]) (ghostNumber v) :=
    sub_eq_iff_eq_add.mp (LinearMap.congr_fun (hA k) v)
  have actB (k : ℤ) (v : Fock) :
      ghostNumber ((B[[k]]) v) = b • (B[[k]]) v + (B[[k]]) (ghostNumber v) :=
    sub_eq_iff_eq_add.mp (LinearMap.congr_fun (hB k) v)
  have pair (k l : ℤ) (v : Fock) :
      ghostNumber ((A[[k]]) ((B[[l]]) v)) =
        (a+b) • (A[[k]]) ((B[[l]]) v) + (A[[k]]) ((B[[l]]) (ghostNumber v)) := by
    rw [actA, actB, map_add, map_smul]
    module
  have back (k l : ℤ) (v : Fock) :
      ghostNumber ((B[[k]]) ((A[[l]]) v)) =
        (a+b) • (B[[k]]) ((A[[l]]) v) + (B[[k]]) ((A[[l]]) (ghostNumber v)) := by
    rw [actB, actA, map_add, map_smul]
    module
  apply LinearMap.ext
  intro v
  let F : Fock → ℕ → Fock := fun w i => (A[[-(i:ℤ)-1]]) ((B[[n+i]]) w)
  let R : Fock → ℕ → Fock := fun w i => (B[[n-i-1]]) ((A[[i]]) w)
  have hf (w : Fock) : Function.HasFiniteSupport (F w) := by
    simpa only [F, show ∀ i : ℕ, (-1:ℤ)-i = -(i:ℤ)-1 by intro i; omega] using
      forward_finite A B (-1) n w
  have hr (w : Fock) : Function.HasFiniteSupport (R w) := by
    simpa only [R, show ∀ i : ℕ, n-1-i = n-i-1 by intro i; omega] using
      reverse_finite B A (n-1) w
  have fsum : ghostNumber (∑ᶠ i, F v i) =
      (a+b) • (∑ᶠ i, F v i) + ∑ᶠ i, F (ghostNumber v) i := by
    rw [map_finsum ghostNumber (hf v)]
    calc
      _ = ∑ᶠ i, ((a+b) • F v i + F (ghostNumber v) i) :=
        finsum_congr (fun i => pair _ _ v)
      _ = (∑ᶠ i, (a+b) • F v i) + ∑ᶠ i, F (ghostNumber v) i := by
        simpa only [Pi.smul_apply'] using
          (finsum_add_distrib ((hf v).smul_right (fun _ => a+b)) (hf (ghostNumber v)))
      _ = _ := by rw [← smul_finsum' (a+b) (hf v)]
  have rsum : ghostNumber (∑ᶠ i, R v i) =
      (a+b) • (∑ᶠ i, R v i) + ∑ᶠ i, R (ghostNumber v) i := by
    rw [map_finsum ghostNumber (hr v)]
    calc
      _ = ∑ᶠ i, ((a+b) • R v i + R (ghostNumber v) i) :=
        finsum_congr (fun i => back _ _ v)
      _ = (∑ᶠ i, (a+b) • R v i) + ∑ᶠ i, R (ghostNumber v) i := by
        simpa only [Pi.smul_apply'] using
          (finsum_add_distrib ((hr v).smul_right (fun _ => a+b)) (hr (ghostNumber v)))
      _ = _ := by rw [← smul_finsum' (a+b) (hr v)]
  change ghostNumber (((signedNormalMinusOne s A B).1[[n]]) v) -
      ((signedNormalMinusOne s A B).1[[n]]) (ghostNumber v) =
        (a+b) • ((signedNormalMinusOne s A B).1[[n]]) v
  simp only [(signedNormalMinusOne s A B).2, map_add, map_smul]
  change ghostNumber (∑ᶠ i, F v i) + s • ghostNumber (∑ᶠ i, R v i) -
      ((∑ᶠ i, F (ghostNumber v) i) + s • (∑ᶠ i, R (ghostNumber v) i)) =
        (a+b) • ((∑ᶠ i, F v i) + s • (∑ᶠ i, R v i))
  rw [fsum, rsum]
  module

private theorem derivative_number (j : ℕ) (n : ℤ) :
    ghostNumber * ((dividedDerivative (j/2) (generatingField (j%2 == 1)))[[n]]) -
      ((dividedDerivative (j/2) (generatingField (j%2 == 1)))[[n]]) * ghostNumber =
        (siteSign j : ℂ) •
          ((dividedDerivative (j/2) (generatingField (j%2 == 1)))[[n]]) := by
  have generator (k : ℤ) : ghostNumber * generatingMode (j%2 == 1) k -
      generatingMode (j%2 == 1) k * ghostNumber =
        (siteSign j : ℂ) • generatingMode (j%2 == 1) k := by
    by_cases he : j%2 = 0
    · have ho : j%2 ≠ 1 := by omega
      simpa [generatingMode, siteSign, he, ho] using
        BcGhostCharge.ghost_number_relations.2.1 (k-1)
    · have ho : j%2 = 1 := by omega
      simpa [generatingMode, siteSign, he, ho] using
        BcGhostCharge.ghost_number_relations.2.2 (k+2)
  rw [derivative_modes]
  calc
    _ = ((Ring.choose (-n-1+((j/2:ℕ):ℤ)) (j/2) : ℤ) : ℂ) •
        (ghostNumber * generatingMode (j%2 == 1) (n-((j/2:ℕ):ℤ)) -
          generatingMode (j%2 == 1) (n-((j/2:ℕ):ℤ)) * ghostNumber) := by
      simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = _ := by rw [generator, smul_comm]

private theorem word_number (w : List ℕ) (n : ℤ) :
    ghostNumber * ((wordField w)[[n]]) - ((wordField w)[[n]]) * ghostNumber =
      (((w.map siteSign).sum : ℤ) : ℂ) • ((wordField w)[[n]]) := by
  induction w generalizing n with
  | nil =>
    have identityModes (k : ℤ) : (identityField : VertexOperator ℂ Fock)[[k]] =
        if k = -1 then LinearMap.id else 0 := by
      rw [identityField, VertexOperator.ncoeff_of_coeff]
      simp only [show -k-1 = 0 ↔ k = -1 by omega]
    simp only [wordField, identityModes, List.map_nil, List.sum_nil, Int.cast_zero, zero_smul]
    split_ifs <;> ext v <;> simp [Module.End.mul_apply]
  | cons j tail ih =>
    have h := normal_number ((-1:ℂ)^tail.length) (siteSign j : ℂ)
      (((tail.map siteSign).sum : ℤ) : ℂ)
      (dividedDerivative (j/2) (generatingField (j%2 == 1)))
      (wordField tail) (derivative_number j) ih n
    simpa only [wordField, List.map_cons, List.sum_cons, Int.cast_add] using h

/-- All original ghost fields obey the native number derivation law. -/
theorem ghost_number_field (a : Fock) (n : ℤ) :
    ghostNumber * ((BcGhostStateField.Y a)[[n]]) -
      ((BcGhostStateField.Y a)[[n]]) * ghostNumber =
        ((BcGhostStateField.Y (ghostNumber a))[[n]]) := by
  classical
  have sorted (S : Finset ℕ) : (S.sort.map siteSign).sum = charge S := by
    rw [charge_sum]
    change (Multiset.map siteSign (↑S.sort : Multiset ℕ)).sum = _
    rw [Finset.sort_eq]
    rfl
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, mul_add, add_mul]
    rw [show ∀ A B C E : Module.End ℂ Fock,
      A+B-(C+E) = (A-C)+(B-E) by intros; abel, ha, hb]
  | single S z =>
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    simp only [hs, map_smul, Pi.smul_apply, number_ket,
      mul_smul_comm, smul_mul_assoc, ← smul_sub, Y_ket, word_number, sorted]

private theorem term_number (D : LatticeData) (s : State D) (n k : ℤ) :
    tensorNumber D * term D n k s - term D n k s * tensorNumber D =
      term D n k (tensorNumber D s) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    apply TensorProduct.ext'
    intro v b
    have h := LinearMap.congr_fun (ghost_number_field a (n-1-k)) b
    simpa only [tensorNumber, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
      term_tmul, Module.End.mul_apply, LinearMap.sub_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, ← TensorProduct.tmul_sub] using
      congrArg (fun w => ((LatticeAllStateField.Y D u)[[k]]) v ⊗ₜ[ℂ] w) h
  | add s t hs ht =>
    simp only [map_add, mul_add, add_mul]
    rw [show ∀ A B C E : Module.End ℂ (State D),
      A+B-(C+E) = (A-C)+(B-E) by intros; abel, hs, ht]

/-- Original all-state, all-integer mode covariance. No homogeneous input is assumed. -/
theorem number_mode (D : LatticeData) (x y : State D) (n : ℤ) :
    tensorNumber D (originalMode D n x y) =
      originalMode D n (tensorNumber D x) y + originalMode D n x (tensorNumber D y) := by
  have h : tensorNumber D (originalMode D n x y) -
      originalMode D n x (tensorNumber D y) = originalMode D n (tensorNumber D x) y := by
    simp only [originalMode_apply, Y_modes]
    rw [map_finsum (tensorNumber D) (term_finite D x y n),
      ← finsum_sub_distrib ((term_finite D x y n).fun_comp (map_zero (tensorNumber D)))
        (term_finite D x (tensorNumber D y) n)]
    exact finsum_congr (fun k => LinearMap.congr_fun (term_number D x n k) y)
  exact sub_eq_iff_eq_add.mp h

/-- The exact native lowering relation is reused, rather than reproved. -/
theorem number_b_apply (D : LatticeData) (m : ℤ) (x : State D) :
    tensorNumber D (ghostB D m x) = ghostB D m (tensorNumber D x) - ghostB D m x := by
  have h := LinearMap.congr_fun (N_b (D := D) m) x
  change tensorNumber D (ghostB D m x) - ghostB D m (tensorNumber D x) = -ghostB D m x at h
  exact (sub_eq_iff_eq_add.mp h).trans (by abel)

/-- Native integer degree of the literal unsigned descent current. -/
theorem current_number (D : LatticeData) (x y : State D) (p q : ℤ)
    (hx : tensorNumber D x = (p:ℂ) • x)
    (hy : tensorNumber D y = (q:ℂ) • y) :
    tensorNumber D (LatticeBRSTCohomologyBVSecondOrder.descentCurrent D x y) =
      ((p+q-1:ℤ):ℂ) • LatticeBRSTCohomologyBVSecondOrder.descentCurrent D x y := by
  change tensorNumber D (originalMode D 0 (ghostB D (-1) x) y) =
    ((p+q-1:ℤ):ℂ) • originalMode D 0 (ghostB D (-1) x) y
  rw [number_mode, number_b_apply, hx, hy, map_smul]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Int.cast_sub, Int.cast_add, Int.cast_one]
  module

private theorem charge_one_sign (S : Finset ℕ) (hS : charge S = 1) :
    (-1:ℂ)^S.card = -1 := by
  have split := S.card_filter_add_card_filter_not (fun j => j%2 = 0)
  have odd : S.filter (fun j => ¬j%2 = 0) = S.filter (fun j => j%2 = 1) := by
    apply Finset.ext
    intro j
    have hj : j % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases he : j % 2 = 0
    · simp [he]
    · have ho : j % 2 = 1 := by omega
      simp [he, ho]
  rw [odd] at split
  have hc := hS
  unfold charge at hc
  have card : S.card = 2 * (S.filter (fun j => j%2 = 0)).card + 1 := by omega
  rw [card, pow_add, pow_mul]
  norm_num

/-- Degree ONE for the original N forces actual odd parity, including mixed matter states. -/
theorem number_one_parity (D : LatticeData) (x : State D)
    (hx : tensorNumber D x = x) : LatticeMatterGhostStateField.parity D x = -x := by
  classical
  let B := LatticeBRSTZeroEnergyReduction.fullBasis D
  have pb (i : LatticeBRSTZeroEnergyReduction.FullLabel D) :
      LatticeMatterGhostStateField.parity D (B i) = (-1:ℂ)^i.2.card • B i := by
    simp [B, fullBasis_apply, LatticeMatterGhostStateField.parity,
      TensorProduct.map_tmul, parity_ket, TensorProduct.tmul_smul]
  have expand : x = ∑ i ∈ (B.repr x).support, (B.repr x i) • B i := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (B.linearCombination_repr x).symm
  conv_lhs => rw [expand]
  rw [map_sum]
  conv_rhs => rw [expand]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have nz : B.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have coeff : (charge i.2 : ℂ) * B.repr x i = B.repr x i := by
    have coordinates (v : State D) : LatticeRelativeMassShell.coeff D v i = B.repr v i := rfl
    have hn := N_original_coefficient (D := D) x i
    rw [coordinates, coordinates] at hn
    exact hn.symm.trans (congrArg (fun z => B.repr z i) hx)
  have eq1 : (charge i.2 : ℂ) = 1 := by
    exact (mul_right_cancel₀ nz (coeff.trans (one_mul _).symm))
  have ci : charge i.2 = 1 := by exact_mod_cast eq1
  rw [map_smul, pb, charge_one_sign i.2 ci, neg_one_smul, smul_neg]

end
end D5.S3.VertexAlgebra.LatticeMatterGhostNumberCovariance

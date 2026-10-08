/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIITransvectionSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIITransvectionSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA1RootSupply
import Lean.Elab.Term
set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! PartII p260, the actual untwisted single-root arithmetic in arbitrary
SL rank. This module is consumed by the nonabelian A2 orbital reconstruction;
no finite-simple classification or group coverage input is assumed. -/
open Lean Elab Term in
elab "rootFieldKernel%" id:ident : term => do
  let env ← getEnv
  let suffix := ".NikolovSegal.PartIIA1RootSupply." ++ id.getId.toString
  let candidates := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some idx => env.header.moduleNames[idx.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.PartIIA1RootSupply"
  match candidates with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique proved field kernel {id} not found"
namespace NikolovSegal.PartIITransvectionSupply
open PartIIFieldMaps Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u v
variable {F : Type u} [Field F] {I : Type v} [Fintype I] [DecidableEq I]

private theorem diag2n_inverse {i j : I} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    (diag2n hij a ha)⁻¹ = diag2n hij a⁻¹ (inv_ne_zero ha) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = (1 : Matrix I I F)
  rw [Matrix.diagonal_mul_diagonal]
  ext k l
  by_cases hki : k = i
  · subst k
    simp_all [Matrix.one_apply,Matrix.diagonal_apply,ha]
  · by_cases hkj : k = j
    · subst k
      simp_all [Matrix.one_apply,Matrix.diagonal_apply,hij.symm,ha]
    · simp_all [Matrix.one_apply,Matrix.diagonal_apply,hki,hkj]

private theorem diag2n_root {i j : I} (hij : i ≠ j) (a : F) (ha : a ≠ 0) (t : F) :
    MulAut.conj (diag2n hij a ha) (transvection hij t) = transvection hij (a^2*t) := by
  simp only [MulAut.conj_apply,diag2n_inverse]
  apply Subtype.ext
  change (diag2n hij a ha).val * (transvection hij t).val *
      (diag2n hij a⁻¹ (inv_ne_zero ha)).val = (transvection hij (a^2*t)).val
  ext k l
  simp only [diag2n_coe,transvection_coe,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · subst l
      simp_all [hij,hij.symm,ha,pow_two,mul_assoc,mul_comm,mul_left_comm]
    · by_cases hli : l = i
      · subst l
        simp_all [hij,hij.symm,ha]
      · simp_all [hli,hlj,hij,ha,eq_comm]
  · by_cases hkj : k = j
    · subst k
      by_cases hlj : l = j
      · subst l
        simp_all [hij,hij.symm,ha]
      · simp_all [hij,hij.symm,hlj,ha,eq_comm]
    · by_cases hkl : k = l
      · subst l
        simp_all [hki,hkj,eq_comm]
      · simp_all [hki,hkj,hkl,eq_comm]

private theorem actual_root_power {i j : I} (hij : i ≠ j)
    (phi : RingAut F) (chi a : F) (ha : a ≠ 0)
    (beta : MulAut (Matrix.SpecialLinearGroup I F))
    (hbeta : ∀ t, beta (transvection hij t) = transvection hij (chi*phi t))
    (n : ℕ) (t : F) :
    ((MulAut.conj (diag2n hij a ha)*beta)^n) (transvection hij t) =
      transvection hij (orbitProduct phi n chi * (orbitProduct phi n a)^2 * (phi^n) t) := by
  have hmain : ∀ n : ℕ, ((MulAut.conj (diag2n hij a ha)*beta)^n) (transvection hij t) =
      transvection hij (orbitProduct phi n (chi*a^2)*(phi^n) t) := by
    intro n
    induction n with
    | zero => simp [orbitProduct]
    | succ n ih =>
      rw [pow_succ',MulAut.mul_apply,ih,MulAut.mul_apply,hbeta,diag2n_root,
        (rootFieldKernel% orbitProduct_succ)]
      simp only [map_mul,pow_succ',RingAut.mul_apply]
      congr 1
      ring
  simpa only [(rootFieldKernel% orbitProduct_mul),mul_assoc] using hmain n

private theorem ordered_root {i j : I} (hij : i ≠ j) {M : ℕ} (v : Fin M → F) :
    orderedProduct (fun k => transvection hij (v k)) = transvection hij (∑ k, v k) := by
  induction M with
  | zero => simp [orderedProduct,transvection_coeff_zero]
  | succ M ih =>
    simp only [orderedProduct,List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ]
    rw [← orderedProduct,ih,← transvection_add]

/-- Genuine scalar VALUE coverage of every actual SLn transvection subgroup,
with diagonal determinant-one corrections chosen before every target. The
length and finite-field cutoff are independent of the matrix rank. -/
theorem actual_transvection_scalar_product [Fintype F] [DecidableEq F]
    {i j : I} (hij : i ≠ j) {q M : ℕ} (hq : 0 < q)
    (hM : q*(2*q+1) < M) (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin M → MulAut (Matrix.SpecialLinearGroup I F)) (phi : Fin M → RingAut F)
    (chi : Fin M → F) (hchi : ∀ k, chi k ≠ 0)
    (d : Fin M → ℕ) (hd : ∀ k, 0 < d k ∧ d k ∣ q)
    (hbeta : ∀ k t, beta k (transvection hij t) = transvection hij (chi k*phi k t)) :
    ∃ y : Fin M → Matrix.SpecialLinearGroup I F, ∀ target : F, ∃ t : Fin M → F,
      orderedProduct (fun k => (transvection hij (t k))⁻¹ *
        (((beta k*MulAut.conj (y k)⁻¹)^d k) (transvection hij (t k)))) = transvection hij target := by
  classical
  let mu := fun k => orbitProduct (phi k) (d k) (chi k)
  obtain ⟨lambda,hlambda,hcover⟩ := PartIIFieldMaps.lemma7_1 hq hM hF phi mu d (fun _ => 2)
    (fun k => (rootFieldKernel% orbitProduct_ne_zero) (phi k) (chi k) (hchi k) (d k))
    hd (by intro k; simp)
  let H := fun k => diag2n hij (lambda k) (hlambda k)
  let y := fun k => (beta k).symm ((H k)⁻¹)
  have hy : ∀ k, beta k*MulAut.conj (y k)⁻¹ = MulAut.conj (H k)*beta k := by
    intro k
    ext z
    simp only [MulAut.mul_apply,MulAut.conj_inv_apply,MulAut.conj_apply,map_mul,map_inv,y,
      MulEquiv.apply_symm_apply,inv_inv]
  refine ⟨y,?_⟩
  intro target
  obtain ⟨t,ht⟩ := hcover target
  refine ⟨t,?_⟩
  have hvalues : ∀ k, (transvection hij (t k))⁻¹ *
      (((beta k*MulAut.conj (y k)⁻¹)^d k) (transvection hij (t k))) =
      transvection hij (fieldValue (phi k) (mu k) (d k) 2 (lambda k) (t k)) := by
    intro k
    rw [hy,actual_root_power hij (phi k) (chi k) (lambda k) (hlambda k) (beta k) (hbeta k),
      transvection_inv,← transvection_add]
    congr 1
    simp only [fieldValue,mu]
    ring
  simp only [hvalues]
  rw [ordered_root]
  exact congrArg (transvection hij) ht
end NikolovSegal.PartIITransvectionSupply

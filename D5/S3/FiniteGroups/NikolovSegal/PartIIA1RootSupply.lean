/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA1RootSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA1RootSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual A1 root scalar products from finite-field maps with torus weight two. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIFieldMaps
import D5.S3.FiniteGroups.NikolovSegal.CosetPowerBridge
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

set_option autoImplicit false
/-! Actual A1 root-group consumption of PartII Lemma7.1(a), with the
SL2 diagonal torus weight TWO, genuine q_i divisors and scalar commutator
VALUES. This is the A1 orbital step of PartII pp259--261, not full simple
scalar PRODUCT existence or automorphism classification. -/
namespace NikolovSegal.PartIIA1RootSupply
open PartIIFieldMaps Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement
universe u
variable {F : Type u} [Field F]

/-- The actual positive A1 root subgroup parametrization in SL2(F). -/
def upper (t : F) : SL(2,F) := Matrix.SpecialLinearGroup.transvection zero_ne_one t

private theorem upper_add (t s : F) : upper (t+s) = upper t * upper s :=
  transvection_add zero_ne_one t s

private theorem upper_inv (t : F) : (upper t)⁻¹ = upper (-t) := transvection_inv zero_ne_one t

private theorem diag_upper (a : F) (ha : a ≠ 0) (t : F) :
    MulAut.conj (diag2 a ha) (upper t) = upper (a^2*t) := by
  have hc := Matrix.commutator_diag2_transvection a ha t (t*(a^2-1)) rfl
  calc
    _ = ⁅diag2 a ha,upper t⁆ * upper t := by
      simp only [MulAut.conj_apply,commutatorElement_def]
      group
    _ = upper (t*(a^2-1)) * upper t := congrArg (fun g => g*upper t) hc
    _ = upper (t*(a^2-1)+t) := (upper_add _ _).symm
    _ = upper (a^2*t) := by congr 1; ring

private theorem orbitProduct_succ (phi : RingAut F) (a : F) (n : ℕ) :
    orbitProduct phi (n+1) a = a*phi (orbitProduct phi n a) := by
  simp only [orbitProduct,Finset.prod_range_succ',map_prod,pow_zero,RingAut.one_apply]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [pow_succ',RingAut.mul_apply]

private theorem orbitProduct_mul (phi : RingAut F) (a b : F) (n : ℕ) :
    orbitProduct phi n (a*b^2) = orbitProduct phi n a*(orbitProduct phi n b)^2 := by
  simp only [orbitProduct,map_mul,map_pow,Finset.prod_mul_distrib,Finset.prod_pow]

private theorem actual_root_action_power (phi : RingAut F) (chi a : F) (ha : a ≠ 0)
    (beta : MulAut SL(2,F)) (hbeta : ∀ t, beta (upper t) = upper (chi*phi t))
    (n : ℕ) (t : F) :
    ((MulAut.conj (diag2 a ha)*beta)^n) (upper t) =
      upper (orbitProduct phi n chi * (orbitProduct phi n a)^2 * (phi^n) t) := by
  have hmain : ∀ n : ℕ, ((MulAut.conj (diag2 a ha)*beta)^n) (upper t) =
      upper (orbitProduct phi n (chi*a^2)*(phi^n) t) := by
    intro n
    induction n with
    | zero => simp [orbitProduct]
    | succ n ih =>
      rw [pow_succ',MulAut.mul_apply,ih,MulAut.mul_apply,hbeta,diag_upper,orbitProduct_succ]
      simp only [map_mul,pow_succ',RingAut.mul_apply]
      congr 1
      ring
  simpa only [orbitProduct_mul,mul_assoc] using hmain n

private theorem orbitProduct_ne_zero (phi : RingAut F) (a : F) (ha : a ≠ 0) (d : ℕ) :
    orbitProduct phi d a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (map_ne_zero (phi^i)).mpr ha

private theorem ordered_upper {M : ℕ} (v : Fin M → F) :
    orderedProduct (fun j => upper (v j)) = upper (∑ j, v j) := by
  induction M with
  | zero => simp [orderedProduct,upper,transvection_coeff_zero]
  | succ M ih =>
    simp only [orderedProduct,List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ]
    rw [← orderedProduct,ih,← upper_add]

/-- Genuine ordered scalar commutator VALUE coverage of the actual SL2
positive root subgroup. Lemma7.1 supplies lambda; y is one actual group tuple
chosen BEFORE every root target. No root/whole-group coverage premise occurs.
The beta tuple must satisfy its genuine prescribed semilinear root law.
Obtaining this law from arbitrary finite-simple automorphisms is a separate
remaining classification/orbital-subgroup obligation. -/
theorem actual_A1_root_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin M → MulAut SL(2,F)) (phi : Fin M → RingAut F)
    (chi : Fin M → F) (hchi : ∀ j, chi j ≠ 0)
    (d : Fin M → ℕ) (hd : ∀ j, 0 < d j ∧ d j ∣ q)
    (hbeta : ∀ j t, beta j (upper t) = upper (chi j * phi j t)) :
    ∃ y : Fin M → SL(2,F), ∀ target : F, ∃ t : Fin M → F,
      orderedProduct (fun j => (upper (t j))⁻¹ *
        (((beta j * MulAut.conj (y j)⁻¹)^d j) (upper (t j)))) = upper target := by
  classical
  let mu := fun j => orbitProduct (phi j) (d j) (chi j)
  obtain ⟨lambda,hlambda,hcover⟩ := PartIIFieldMaps.lemma7_1 hq hM hF phi mu d (fun _ => 2)
    (fun j => orbitProduct_ne_zero (phi j) (chi j) (hchi j) (d j)) hd (by intro j; simp)
  let H := fun j => diag2 (lambda j) (hlambda j)
  let y := fun j => (beta j).symm ((H j)⁻¹)
  have hy : ∀ j, beta j * MulAut.conj (y j)⁻¹ = MulAut.conj (H j)*beta j := by
    intro j
    ext z
    simp only [MulAut.mul_apply,MulAut.conj_inv_apply,MulAut.conj_apply,map_mul,map_inv,y,
      MulEquiv.apply_symm_apply,inv_inv]
  refine ⟨y,?_⟩
  intro target
  obtain ⟨t,ht⟩ := hcover target
  refine ⟨t,?_⟩
  have hvalues : ∀ j, (upper (t j))⁻¹ *
      (((beta j * MulAut.conj (y j)⁻¹)^d j) (upper (t j))) =
      upper (fieldValue (phi j) (mu j) (d j) 2 (lambda j) (t j)) := by
    intro j
    rw [hy,actual_root_action_power (phi j) (chi j) (lambda j) (hlambda j) (beta j) (hbeta j),upper_inv,← upper_add]
    congr 1
    simp only [fieldValue,mu]
    ring
  simp only [hvalues]
  rw [ordered_upper]
  exact congrArg upper ht

end NikolovSegal.PartIIA1RootSupply

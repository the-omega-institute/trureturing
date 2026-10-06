/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2GraphSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2ExponentDescent
import D5.S3.FiniteGroups.NikolovSegal.PartIIA2GraphTorus
set_option autoImplicit false
open Lean Elab Term in
elab "a2Kernel%" id:ident : term => do
  let env ← getEnv
  let moduleName := if id.getId == `diag2n_root || id.getId == `diag2n_inverse then "PartIITransvectionSupply" else "PartIIA2Orbital"
  let kernelNamespace :=  if moduleName == "PartIITransvectionSupply" then "PartIITransvectionSupply" else "PartIIA2Orbital"
  let suffix := ".NikolovSegal." ++ kernelNamespace ++ "." ++ id.getId.toString
  let candidates := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some idx => env.header.moduleNames[idx.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal." ++ moduleName
  match candidates with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique proved A2 kernel {id} from {moduleName} not found"
namespace NikolovSegal.PartIIA2GraphSupply
open PartIIFieldMaps Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem orbitProduct_mul_pow (phi : RingAut F) (a lambda : F) (c n : ℕ) :
    orbitProduct phi n (a*lambda^c) = orbitProduct phi n a*(orbitProduct phi n lambda)^c := by
  simp only [orbitProduct,map_mul,map_pow,Finset.prod_mul_distrib,Finset.prod_pow]

private theorem scalar_action_power {i j : Fin 3} (hij : i ≠ j)
    (gamma : MulAut SL(3,F)) (phi : RingAut F) (a : F)
    (hgamma : ∀ t, gamma (transvection hij t) = transvection hij (a*phi t)) (n : ℕ) (t : F) :
    (gamma^n) (transvection hij t) = transvection hij (orbitProduct phi n a*(phi^n) t) := by
  induction n with
  | zero => simp [orbitProduct]
  | succ n ih =>
    rw [pow_succ',MulAut.mul_apply,ih,hgamma,(rootFieldKernel% orbitProduct_succ)]
    simp only [map_mul,pow_succ',RingAut.mul_apply,mul_assoc]

private theorem ordered_root {i j : Fin 3} (hij : i ≠ j) {M : ℕ} : ∀ v : Fin M → F,
      orderedProduct (fun k => transvection hij (v k)) = transvection hij (∑ k,v k) := by
  intro v
  induction M with
  | zero => simp [orderedProduct,transvection_coeff_zero]
  | succ M ih =>
    simp only [orderedProduct,List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ]
    rw [← orderedProduct,ih,← transvection_add]

-- Intended to be retained ONLY with the actual graph/torus instantiation.
-- hcycle is an explicit action formula, never a coverage premise.
private theorem actual_root_cycle_product [Fintype F] [DecidableEq F]
    {i j : Fin 3} (hij : i ≠ j) {q M : ℕ} (hq : 0 < q)
    (hM : q*(4*q+1) < M) (hF : 4*(4*q+1)^q < Fintype.card F)
    (beta : Fin M → MulAut SL(3,F))
    (H : Fin M → (lambda : F) → lambda ≠ 0 → SL(3,F))
    (b c : Fin M → ℕ) (hc : ∀ k, 0 < c k ∧ c k ≤ 4)
    (phi : Fin M → RingAut F) (chi : Fin M → F) (hchi : ∀ k, chi k ≠ 0)
    (e : Fin M → ℕ) (he : ∀ k, 0 < e k ∧ e k ∣ q)
    (hcycle : ∀ k lambda hlambda t,
      ((MulAut.conj (H k lambda hlambda)*beta k)^b k) (transvection hij t) =
        transvection hij (chi k*lambda^c k*phi k t)) :
    ∃ lambda : Fin M → F, ∃ hlambda : ∀ k, lambda k ≠ 0,
      ∃ y : Fin M → SL(3,F),
      (∀ k, beta k*MulAut.conj (y k)⁻¹ = MulAut.conj (H k (lambda k) (hlambda k))*beta k) ∧
      ∀ target : F, ∃ t : Fin M → F,
      orderedProduct (fun k => (transvection hij (t k))⁻¹*
        (((beta k*MulAut.conj (y k)⁻¹)^(b k*(q/e k))) (transvection hij (t k)))) =
        transvection hij target := by
  classical
  let d := fun k => q/e k
  have hd : ∀ k, 0 < d k ∧ d k ∣ q := by
    intro k
    exact ⟨Nat.div_pos (Nat.le_of_dvd hq (he k).2) (he k).1,Nat.div_dvd_of_dvd (he k).2⟩
  let mu := fun k => orbitProduct (phi k) (d k) (chi k)
  obtain ⟨lambda,hlambda,hcover⟩ := PartIIFieldMaps.lemma7_1 hq hM hF phi mu d c
    (fun k => (rootFieldKernel% orbitProduct_ne_zero) (phi k) (chi k) (hchi k) (d k)) hd hc
  let y := fun k => (beta k).symm ((H k (lambda k) (hlambda k))⁻¹)
  have hy : ∀ k, beta k*MulAut.conj (y k)⁻¹ = MulAut.conj (H k (lambda k) (hlambda k))*beta k := by
    intro k
    ext z
    simp only [y,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,MulEquiv.apply_symm_apply,inv_inv]
  refine ⟨lambda,hlambda,y,hy,?_⟩
  intro target
  obtain ⟨t,ht⟩ := hcover target
  have hvalues : ∀ k,
      (transvection hij (t k))⁻¹*
        (((beta k*MulAut.conj (y k)⁻¹)^(b k*(q/e k))) (transvection hij (t k))) =
      transvection hij (fieldValue (phi k) (mu k) (d k) (c k) (lambda k) (t k)) := by
    intro k
    rw [hy,pow_mul]
    rw [scalar_action_power hij _ (phi k) (chi k*(lambda k)^c k)
      (hcycle k (lambda k) (hlambda k)) (d k) (t k)]
    rw [orbitProduct_mul_pow,transvection_inv,← transvection_add]
    congr 1
    simp only [fieldValue,mu]
    ring
  refine ⟨t,?_⟩
  simp only [hvalues]
  rw [ordered_root]
  exact congrArg (transvection hij) ht

/-- Actual prescribed positive A2 diagonal/field/graph action. -/
def diagonalFieldGraphAut (a : Fin 3 → Fˣ) (phi : RingAut F) (eps : Bool) : MulAut SL(3,F) :=
  PartIIA2Orbital.diagonalFieldAut a phi * (if eps then PartIIA2GraphTorus.tau else 1)

private def rootScale (a : Fin 3 → Fˣ) (i j : Fin 3) : F := (a i:F)*(↑(a j)⁻¹:F)
private theorem rootScale_ne (a : Fin 3 → Fˣ) (i j : Fin 3) : rootScale a i j ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)

private theorem diagonal_field_root (a : Fin 3 → Fˣ) (phi : RingAut F)
    {i j : Fin 3} (hij : i ≠ j) (t : F) :
    PartIIA2Orbital.diagonalFieldAut a phi (transvection hij t) =
      transvection hij (rootScale a i j*phi t) := by
  rw [PartIIA2Orbital.diagonalFieldAut,MulAut.mul_apply,
    (a2Kernel% field_root),(a2Kernel% diagonal_root)]
  rfl

private theorem graph_root01 (a : Fin 3 → Fˣ) (phi : RingAut F) (t : F) :
    diagonalFieldGraphAut a phi true (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
      transvection (show (1:Fin 3) ≠ 2 by decide) (-rootScale a 1 2*phi t) := by
  rw [diagonalFieldGraphAut,MulAut.mul_apply,if_pos rfl,PartIIA2GraphTorus.tau_T01,
    diagonal_field_root,map_neg]
  congr 1
  ring

private theorem graph_root12 (a : Fin 3 → Fˣ) (phi : RingAut F) (t : F) :
    diagonalFieldGraphAut a phi true (transvection (show (1:Fin 3) ≠ 2 by decide) t) =
      transvection (show (0:Fin 3) ≠ 1 by decide) (-rootScale a 0 1*phi t) := by
  rw [diagonalFieldGraphAut,MulAut.mul_apply,if_pos rfl,PartIIA2GraphTorus.tau_T12,
    diagonal_field_root,map_neg]
  congr 1
  ring

/-- Genuine mixed graph-orbit root product, not an assumed component law.
Every matrix/field/graph tuple is allowed. The actual torus and actual graph
laws prove the return identity; PartII Lemma7.1 then chooses lambda and y
BEFORE all root targets. The graph orbit span1/2 is kept separate from q/e.
The selected correction identity is retained for the later U reconstruction. -/
theorem actual_mixed_graph_root01_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (a : Fin M → Fin 3 → Fˣ) (phi : Fin M → RingAut F) (eps : Fin M → Bool)
    (e : Fin M → ℕ) (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ lambda : Fin M → F, ∃ hlambda : ∀ j, lambda j ≠ 0,
      ∃ y : Fin M → SL(3,F),
      (∀ j, diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹ =
        MulAut.conj (if eps j then PartIIA2GraphTorus.H (lambda j) (hlambda j)
          else diag2n (show (0:Fin 3) ≠ 1 by decide) (lambda j) (hlambda j))*
          diagonalFieldGraphAut (a j) (phi j) (eps j)) ∧
      ∀ target : F, ∃ t : Fin M → F,
        orderedProduct (fun j => (transvection (show (0:Fin 3) ≠ 1 by decide) (t j))⁻¹*
          (((diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹)^
            ((if eps j then 2 else 1)*(q/e j)))
            (transvection (show (0:Fin 3) ≠ 1 by decide) (t j)))) =
          transvection (show (0:Fin 3) ≠ 1 by decide) target := by
  let beta := fun j => diagonalFieldGraphAut (a j) (phi j) (eps j)
  let H : Fin M → (lambda : F) → lambda ≠ 0 → SL(3,F) := fun j lambda hlambda =>
    if eps j then PartIIA2GraphTorus.H lambda hlambda else diag2n (show (0:Fin 3) ≠ 1 by decide) lambda hlambda
  let b := fun j => if eps j then 2 else 1
  let c := fun j => if eps j then 3 else 2
  let psi := fun j => if eps j then (phi j)^2 else phi j
  let chi := fun j => if eps j then (-rootScale (a j) 0 1)*phi j (-rootScale (a j) 1 2)
      else rootScale (a j) 0 1
  have hc : ∀ j, 0 < c j ∧ c j ≤ 4 := by intro j; dsimp [c]; split_ifs <;> omega
  have hchi : ∀ j, chi j ≠ 0 := by
    intro j
    dsimp [chi]
    split_ifs
    · exact mul_ne_zero (neg_ne_zero.mpr (rootScale_ne _ _ _))
        ((map_ne_zero (phi j)).mpr (neg_ne_zero.mpr (rootScale_ne _ _ _)))
    · exact rootScale_ne _ _ _
  have hcycle : ∀ j lambda hlambda t,
      ((MulAut.conj (H j lambda hlambda)*beta j)^b j) (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
        transvection (show (0:Fin 3) ≠ 1 by decide) (chi j*lambda^c j*psi j t) := by
    intro j lambda hlambda t
    cases hs : eps j
    · simp only [H,b,c,psi,chi,beta,hs,Bool.false_eq_true,ite_false,pow_one,
        diagonalFieldGraphAut,mul_one]
      rw [MulAut.mul_apply,diagonal_field_root,(a2Kernel% diag2n_root)]
      congr 1
      ring
    · have hh := PartIIA2GraphTorus.isolating_graph_square lambda hlambda
        (diagonalFieldGraphAut (a j) (phi j) true)
        (-rootScale (a j) 1 2) (-rootScale (a j) 0 1) (phi j)
        (graph_root01 (a j) (phi j)) (graph_root12 (a j) (phi j)) t
      simpa only [H,b,c,psi,chi,beta,hs,ite_true,mul_assoc,mul_comm,mul_left_comm] using hh
  exact actual_root_cycle_product (show (0:Fin 3) ≠ 1 by decide) hq hM hF beta H b c hc psi chi hchi e he hcycle

private theorem mirrored_H_root01 (lambda : F) (hlambda : lambda ≠ 0) (t : F) :
    MulAut.conj (PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda))
      (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
        transvection (show (0:Fin 3) ≠ 1 by decide) t := by
  calc
    _ = PartIIA2GraphTorus.tau (MulAut.conj (PartIIA2GraphTorus.H lambda hlambda)
        (transvection (show (1:Fin 3) ≠ 2 by decide) (-t))) := by
      simp only [MulAut.conj_apply,map_mul,map_inv,PartIIA2GraphTorus.tau_T12,neg_neg]
    _ = _ := by rw [PartIIA2GraphTorus.H_conj_T12,PartIIA2GraphTorus.tau_T12,neg_neg]

private theorem mirrored_H_root12 (lambda : F) (hlambda : lambda ≠ 0) (t : F) :
    MulAut.conj (PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda))
      (transvection (show (1:Fin 3) ≠ 2 by decide) t) =
        transvection (show (1:Fin 3) ≠ 2 by decide) (lambda^3*t) := by
  calc
    _ = PartIIA2GraphTorus.tau (MulAut.conj (PartIIA2GraphTorus.H lambda hlambda)
        (transvection (show (0:Fin 3) ≠ 1 by decide) (-t))) := by
      simp only [MulAut.conj_apply,map_mul,map_inv,PartIIA2GraphTorus.tau_T01,neg_neg]
    _ = _ := by
      rw [PartIIA2GraphTorus.H_conj_T01,PartIIA2GraphTorus.tau_T01]
      congr 1
      ring

private theorem mirrored_graph_square (lambda : F) (hlambda : lambda ≠ 0)
    (a : Fin 3 → Fˣ) (phi : RingAut F) (t : F) :
    ((MulAut.conj (PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda))*
      diagonalFieldGraphAut a phi true)^2)
        (transvection (show (1:Fin 3) ≠ 2 by decide) t) =
      transvection (show (1:Fin 3) ≠ 2 by decide)
        (lambda^3*(-rootScale a 1 2)*phi (-rootScale a 0 1)*(phi^2) t) := by
  change MulAut.conj (PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda))
    (diagonalFieldGraphAut a phi true
      (MulAut.conj (PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda))
        (diagonalFieldGraphAut a phi true (transvection (show (1:Fin 3) ≠ 2 by decide) t)))) = _
  rw [graph_root12,mirrored_H_root01,graph_root01,mirrored_H_root12,map_mul]
  congr 1
  change lambda^3*((-rootScale a 1 2)*(phi (-rootScale a 0 1)*phi (phi t))) = _
  simp only [RingAut.mul_apply,pow_two,mul_assoc]

/-- Genuine mixed graph-orbit root product, not an assumed component law.
Every matrix/field/graph tuple is allowed. The actual torus and actual graph
laws prove the return identity; PartII Lemma7.1 then chooses lambda and y
BEFORE all root targets. The graph orbit span1/2 is kept separate from q/e.
The selected correction identity is retained for the later U reconstruction. -/
theorem actual_mixed_graph_root12_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (a : Fin M → Fin 3 → Fˣ) (phi : Fin M → RingAut F) (eps : Fin M → Bool)
    (e : Fin M → ℕ) (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ lambda : Fin M → F, ∃ hlambda : ∀ j, lambda j ≠ 0,
      ∃ y : Fin M → SL(3,F),
      (∀ j, diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹ =
        MulAut.conj (if eps j then PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H (lambda j) (hlambda j))
          else diag2n (show (1:Fin 3) ≠ 2 by decide) (lambda j) (hlambda j))*
          diagonalFieldGraphAut (a j) (phi j) (eps j)) ∧
      ∀ target : F, ∃ t : Fin M → F,
        orderedProduct (fun j => (transvection (show (1:Fin 3) ≠ 2 by decide) (t j))⁻¹*
          (((diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹)^
            ((if eps j then 2 else 1)*(q/e j)))
            (transvection (show (1:Fin 3) ≠ 2 by decide) (t j)))) =
          transvection (show (1:Fin 3) ≠ 2 by decide) target := by
  let beta := fun j => diagonalFieldGraphAut (a j) (phi j) (eps j)
  let H : Fin M → (lambda : F) → lambda ≠ 0 → SL(3,F) := fun j lambda hlambda =>
    if eps j then PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda) else diag2n (show (1:Fin 3) ≠ 2 by decide) lambda hlambda
  let b := fun j => if eps j then 2 else 1
  let c := fun j => if eps j then 3 else 2
  let psi := fun j => if eps j then (phi j)^2 else phi j
  let chi := fun j => if eps j then (-rootScale (a j) 1 2)*phi j (-rootScale (a j) 0 1)
      else rootScale (a j) 1 2
  have hc : ∀ j, 0 < c j ∧ c j ≤ 4 := by intro j; dsimp [c]; split_ifs <;> omega
  have hchi : ∀ j, chi j ≠ 0 := by
    intro j
    dsimp [chi]
    split_ifs
    · exact mul_ne_zero (neg_ne_zero.mpr (rootScale_ne _ _ _))
        ((map_ne_zero (phi j)).mpr (neg_ne_zero.mpr (rootScale_ne _ _ _)))
    · exact rootScale_ne _ _ _
  have hcycle : ∀ j lambda hlambda t,
      ((MulAut.conj (H j lambda hlambda)*beta j)^b j) (transvection (show (1:Fin 3) ≠ 2 by decide) t) =
        transvection (show (1:Fin 3) ≠ 2 by decide) (chi j*lambda^c j*psi j t) := by
    intro j lambda hlambda t
    cases hs : eps j
    · simp only [H,b,c,psi,chi,beta,hs,Bool.false_eq_true,ite_false,pow_one,
        diagonalFieldGraphAut,mul_one]
      rw [MulAut.mul_apply,diagonal_field_root,(a2Kernel% diag2n_root)]
      congr 1
      ring
    · have hh := mirrored_graph_square lambda hlambda (a j) (phi j) t
      simpa only [H,b,c,psi,chi,beta,hs,ite_true,mul_assoc,mul_comm,mul_left_comm] using hh
  exact actual_root_cycle_product (show (1:Fin 3) ≠ 2 by decide) hq hM hF beta H b c hc psi chi hchi e he hcycle

/-- The actual central root branch for every diagonal/field/graph tuple.
Its graph sign is computed from tau_T02, and the scalar q/e power is unchanged.
The field theorem supplies corrections before every central target. -/
theorem actual_mixed_graph_central_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (a : Fin M → Fin 3 → Fˣ) (phi : Fin M → RingAut F) (eps : Fin M → Bool)
    (e : Fin M → ℕ) (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin M → SL(3,F), ∀ target : F, ∃ t : Fin M → F,
      orderedProduct (fun j => (transvection (show (0:Fin 3) ≠ 2 by decide) (t j))⁻¹*
        (((diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹)^(q/e j))
          (transvection (show (0:Fin 3) ≠ 2 by decide) (t j)))) =
        transvection (show (0:Fin 3) ≠ 2 by decide) target := by
  let beta := fun j => diagonalFieldGraphAut (a j) (phi j) (eps j)
  let chi := fun j => if eps j then -rootScale (a j) 0 2 else rootScale (a j) 0 2
  let d := fun j => q/e j
  have hchi : ∀ j, chi j ≠ 0 := by
    intro j
    dsimp [chi]
    split_ifs
    · exact neg_ne_zero.mpr (rootScale_ne _ _ _)
    · exact rootScale_ne _ _ _
  have hbeta : ∀ j t, beta j (transvection (show (0:Fin 3) ≠ 2 by decide) t) =
      transvection (show (0:Fin 3) ≠ 2 by decide) (chi j*phi j t) := by
    intro j t
    cases hs : eps j
    · simp only [beta,chi,hs,Bool.false_eq_true,ite_false,diagonalFieldGraphAut,mul_one]
      exact diagonal_field_root _ _ _ _
    · simp only [beta,chi,hs,ite_true,diagonalFieldGraphAut,MulAut.mul_apply]
      rw [PartIIA2GraphTorus.tau_T02,diagonal_field_root,map_neg]
      congr 1
      ring
  have hd : ∀ j, 0 < d j ∧ d j ∣ q := by
    intro j
    exact ⟨Nat.div_pos (Nat.le_of_dvd hq (he j).2) (he j).1,Nat.div_dvd_of_dvd (he j).2⟩
  have hM2 : q*(2*q+1) < M := (Nat.mul_le_mul_left q (by omega)).trans_lt hM
  have hF2 : 2*(2*q+1)^q < Fintype.card F :=
    (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) q)).trans_lt hF
  exact PartIITransvectionSupply.actual_transvection_scalar_product
    (show (0:Fin 3) ≠ 2 by decide) hq hM2 hF2 beta phi chi hchi d hd hbeta
end NikolovSegal.PartIIA2GraphSupply

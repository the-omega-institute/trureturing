/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2Orbital
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2Orbital
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIITransvectionSupply
import D5.S3.FiniteGroups.NikolovSegal.TransitiveCoordinates
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
set_option autoImplicit false
set_option maxHeartbeats 1500000
/-! The actual nonabelian untwisted A2 orbital subgroup in SL3, PartII
p260. Ordered root products include the central a*b term. The field and
root arithmetic is proved and consumed; arbitrary graph/aut classification
and full higher-rank simple coverage are separate unfinished obligations. -/
namespace NikolovSegal.PartIIA2Orbital
open Matrix.SpecialLinearGroup PartIITransvectionSupply
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private def glAction (A : Matrix.GeneralLinearGroup (Fin 3) F) (g : SL(3,F)) : SL(3,F) :=
  ⟨(↑A : Matrix (Fin 3) (Fin 3) F) * g.val * ((↑A⁻¹ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),by
    rw [Matrix.det_mul,Matrix.det_mul,g.property,mul_one,← Matrix.det_mul,A.mul_inv,Matrix.det_one]⟩

/-- Actual conjugation by an arbitrary invertible 3x3 matrix, restricted to SL2. -/
def generalLinearAut (A : Matrix.GeneralLinearGroup (Fin 3) F) : MulAut SL(3,F) where
  toFun := glAction A
  invFun := glAction A⁻¹
  left_inv g := by
    apply Subtype.ext
    change ((↑A⁻¹ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((↑A : Matrix (Fin 3) (Fin 3) F)*g.val*(↑A⁻¹ : Matrix (Fin 3) (Fin 3) F)) * (↑(A⁻¹)⁻¹ : Matrix (Fin 3) (Fin 3) F) = g.val
    rw [inv_inv]
    simp only [← mul_assoc,A.inv_mul,one_mul]
    rw [mul_assoc,A.inv_mul,mul_one]
  right_inv g := by
    apply Subtype.ext
    change (↑A : Matrix (Fin 3) (Fin 3) F) *
      (((↑A⁻¹ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)*g.val*(↑(A⁻¹)⁻¹ : Matrix (Fin 3) (Fin 3) F)) * (↑A⁻¹ : Matrix (Fin 3) (Fin 3) F) = g.val
    rw [inv_inv]
    simp only [← mul_assoc,A.mul_inv,one_mul]
    rw [mul_assoc,A.mul_inv,mul_one]
  map_mul' g h := by
    apply Subtype.ext
    change (↑A : Matrix (Fin 3) (Fin 3) F)*(g.val*h.val)*(↑A⁻¹ : Matrix (Fin 3) (Fin 3) F) =
      ((↑A : Matrix (Fin 3) (Fin 3) F)*g.val*(↑A⁻¹ : Matrix (Fin 3) (Fin 3) F))*((↑A : Matrix (Fin 3) (Fin 3) F)*h.val*(↑A⁻¹ : Matrix (Fin 3) (Fin 3) F))
    simp only [mul_assoc]
    rw [← mul_assoc (↑A⁻¹ : Matrix (Fin 3) (Fin 3) F) (↑A : Matrix (Fin 3) (Fin 3) F),A.inv_mul,one_mul]


def fieldAut (phi : RingAut F) : MulAut SL(3,F) where
  toFun := Matrix.SpecialLinearGroup.map phi.toRingHom
  invFun := Matrix.SpecialLinearGroup.map phi.symm.toRingHom
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply]
  map_mul' := (Matrix.SpecialLinearGroup.map phi.toRingHom).map_mul


private def diagonalGL (a : Fin 3 → Fˣ) : Matrix.GeneralLinearGroup (Fin 3) F where
  val := Matrix.diagonal (fun i => (a i:F))
  inv := Matrix.diagonal (fun i => (↑(a i)⁻¹:F))
  val_inv := by simp [Matrix.diagonal_mul_diagonal,Matrix.diagonal_eq_one]
  inv_val := by simp [Matrix.diagonal_mul_diagonal,Matrix.diagonal_eq_one]

/-- The genuine A2 diagonal/field action on determinant-one matrices. -/
def diagonalFieldAut (a : Fin 3 → Fˣ) (phi : RingAut F) : MulAut SL(3,F) :=
  generalLinearAut (diagonalGL a)*fieldAut phi

private theorem field_root (phi : RingAut F) {i j : Fin 3} (hij : i ≠ j) (t : F) :
    fieldAut phi (transvection hij t) = transvection hij (phi t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  simp [fieldAut,Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,
    transvection_coe,Matrix.one_apply,Matrix.single_apply]
  split_ifs <;> simp

private theorem diagonal_root (a : Fin 3 → Fˣ) {i j : Fin 3} (hij : i ≠ j) (t : F) :
    generalLinearAut (diagonalGL a) (transvection hij t) =
      transvection hij ((a i:F)*(↑(a j)⁻¹:F)*t) := by
  apply Subtype.ext
  change Matrix.diagonal (fun k => (a k:F))*(transvection hij t).val*
    Matrix.diagonal (fun k => (↑(a k)⁻¹:F)) = (transvection hij ((a i:F)*(↑(a j)⁻¹:F)*t)).val
  ext k l
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,transvection_coe,
    Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]
  by_cases hki : k = i <;> by_cases hlj : l = j <;> by_cases hkl : k = l
  all_goals simp_all [mul_assoc,mul_comm,mul_left_comm]

/-- Actual Heisenberg coordinate chart of the positive A2 orbital group. -/
def upper3 (a b c : F) : SL(3,F) :=
  ⟨!![1,a,c;0,1,b;0,0,1],by simp [Matrix.det_fin_three]⟩

private theorem upper3_zero : upper3 (0:F) 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper3,Matrix.one_apply]

private theorem upper3_mul (a b c A B C : F) :
    upper3 a b c*upper3 A B C = upper3 (a+A) (b+B) (c+C+a*B) := by
  apply Subtype.ext
  change (upper3 a b c).val*(upper3 A B C).val = (upper3 (a+A) (b+B) (c+C+a*B)).val
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper3,Matrix.mul_apply,Fin.sum_univ_succ]
  all_goals ring

private theorem upper3_inv (a b c : F) : (upper3 a b c)⁻¹ = upper3 (-a) (-b) (a*b-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [upper3_mul]
  convert upper3_zero (F := F) using 1 <;> congr 1 <;> ring

/-- The ACTUAL nonabelian upper unipotent subgroup of SL3. -/
def upperUnipotent : Subgroup SL(3,F) where
  carrier := {g | ∃ a b c : F, upper3 a b c = g}
  one_mem' := ⟨0,0,0,upper3_zero⟩
  mul_mem' := by
    rintro x z ⟨a,b,c,rfl⟩ ⟨A,B,C,rfl⟩
    exact ⟨a+A,b+B,c+C+a*B,(upper3_mul _ _ _ _ _ _).symm⟩
  inv_mem' := by
    rintro x ⟨a,b,c,rfl⟩
    exact ⟨-a,-b,a*b-c,(upper3_inv _ _ _).symm⟩

private def rootI : Fin 3 → Fin 3 := ![0,1,0]
private def rootJ : Fin 3 → Fin 3 := ![1,2,2]
private theorem root_ne (a : Fin 3) : rootI a ≠ rootJ a := by
  fin_cases a <;> decide
private def root (a : Fin 3) (t : F) : SL(3,F) := transvection (root_ne a) t

private theorem root_mem (a : Fin 3) (t : F) : root a t ∈ upperUnipotent := by
  have h0 : root (0:Fin 3) t = upper3 t 0 0 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [root,rootI,rootJ,upper3,transvection_coe]
  have h1 : root (1:Fin 3) t = upper3 0 t 0 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [root,rootI,rootJ,upper3,transvection_coe]
  have h2 : root (2:Fin 3) t = upper3 0 0 t := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [root,rootI,rootJ,upper3,transvection_coe]
  fin_cases a
  · exact ⟨t,0,0,h0.symm⟩
  · exact ⟨0,t,0,h1.symm⟩
  · exact ⟨0,0,t,h2.symm⟩

private theorem three_root_product (a b c : F) :
    root 0 a*root 1 b*root 2 (c-a*b) = upper3 a b c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [root,rootI,rootJ,upper3,transvection_coe,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]
  all_goals ring

private def blockIndex {M : ℕ} (a : Fin 3) (j : Fin M) : Fin (3*M) := finProdFinEquiv (a,j)
private theorem ordered_blocks {M : ℕ} (f : Fin (3*M) → SL(3,F)) :
    orderedProduct f = orderedProduct (fun a : Fin 3 => orderedProduct (fun j : Fin M => f (blockIndex a j))) := by
  simp only [orderedProduct,List.ofFn_mul,List.prod_flatten,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext a
  dsimp only [Function.comp_apply]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  simp only [blockIndex,finProdFinEquiv]
  ac_rfl

/-- A genuine PartII A2 orbital scalar PRODUCT for every prescribed actual
D/Phi action, with only quantitative field/exponent hypotheses. No root-law
or coverage premise. The SAME y is fixed before ALL unipotent targets.
Witnesses stay in the actual allowed orbital subgroup, and the a*b central
term is reconstructed in its true noncommutative increasing order. -/
theorem actual_A2_diagonal_field_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (a : Fin (3*M) → Fin 3 → Fˣ) (phi : Fin (3*M) → RingAut F)
    (e : Fin (3*M) → ℕ) (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin (3*M) → SL(3,F), ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin (3*M) → SL(3,F), (∀ j, c j ∈ upperUnipotent) ∧
      orderedProduct (fun j => (c j)⁻¹ *
        (((diagonalFieldAut (a j) (phi j)*MulAut.conj (y j)⁻¹)^(q/e j)) (c j))) = target := by
  classical
  let beta := fun j => diagonalFieldAut (a j) (phi j)
  let d := fun j => q/e j
  have hd : ∀ j, 0 < d j ∧ d j ∣ q := by
    intro j
    refine ⟨Nat.div_pos (Nat.le_of_dvd hq (he j).2) (he j).1,?_⟩
    exact Nat.div_dvd_of_dvd (he j).2
  have hb : ∀ r j t, beta (blockIndex r j) (root r t) =
      root r ((a (blockIndex r j) (rootI r):F)*
        (↑(a (blockIndex r j) (rootJ r))⁻¹:F)*phi (blockIndex r j) t) := by
    intro r j t
    dsimp only [beta,diagonalFieldAut,root]
    rw [MulAut.mul_apply,field_root,diagonal_root]
  choose y hy using fun r : Fin 3 => actual_transvection_scalar_product (root_ne r) hq hM hF
    (fun j => beta (blockIndex r j)) (fun j => phi (blockIndex r j))
    (fun j => (a (blockIndex r j) (rootI r):F)*(↑(a (blockIndex r j) (rootJ r))⁻¹:F))
    (fun j => mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    (fun j => d (blockIndex r j)) (fun j => hd (blockIndex r j))
    (fun j t => hb r j t)
  let yall := fun k : Fin (3*M) => y ((finProdFinEquiv.symm k).1) ((finProdFinEquiv.symm k).2)
  have hyall : ∀ r j, yall (blockIndex r j) = y r j := by
    intro r j
    simp only [yall,blockIndex,Equiv.symm_apply_apply]
  refine ⟨yall,?_⟩
  intro target ht
  obtain ⟨A,B,C,rfl⟩ := ht
  let w : Fin 3 → F := ![A,B,C-A*B]
  choose t ht using fun r : Fin 3 => hy r (w r)
  let c := fun k : Fin (3*M) => root ((finProdFinEquiv.symm k).1)
      (t ((finProdFinEquiv.symm k).1) ((finProdFinEquiv.symm k).2))
  have hc : ∀ r j, c (blockIndex r j) = root r (t r j) := by
    intro r j
    simp only [c,blockIndex,Equiv.symm_apply_apply]
  refine ⟨c,fun j => root_mem _ _,?_⟩
  rw [ordered_blocks]
  have hblocks : ∀ r, orderedProduct (fun j : Fin M => (c (blockIndex r j))⁻¹ *
      (((diagonalFieldAut (a (blockIndex r j)) (phi (blockIndex r j))*
        MulAut.conj (yall (blockIndex r j))⁻¹)^(q/e (blockIndex r j))) (c (blockIndex r j)))) = root r (w r) := by
    intro r
    simpa only [hc,hyall,root,beta,d] using ht r
  calc
    _ = orderedProduct (fun r : Fin 3 => root r (w r)) := congrArg orderedProduct (funext hblocks)
    _ = upper3 A B C := by
      simpa [orderedProduct,List.ofFn_succ,List.ofFn_zero,w,mul_assoc] using three_root_product A B C
end NikolovSegal.PartIIA2Orbital

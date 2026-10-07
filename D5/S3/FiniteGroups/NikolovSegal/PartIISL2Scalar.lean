/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL2Scalar
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL2Scalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered four-root reconstruction and normalized SL2 scalar products. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA1RootSupply
import D5.S3.FiniteGroups.NikolovSegal.TransitiveCoordinates
set_option autoImplicit false
/-! PartII rank-one scalar PRODUCT assembly for actual SL2 automorphisms
with prescribed semilinear positive/negative root laws. The field theorem
and FOUR-root decomposition are proved and consumed. This does not assert
normalization/classification of arbitrary finite-simple automorphisms. -/
namespace NikolovSegal.PartIIA1RootSupply
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
def lower (t : F) : SL(2,F) := Matrix.SpecialLinearGroup.transvection one_ne_zero t

private theorem four_root_matrix (x y z w : F) :
    (upper x * lower y * upper z * lower w).val =
      !![1+x*y+((1+x*y)*z+x)*w, (1+x*y)*z+x;
         y+(y*z+1)*w, y*z+1] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper,lower,transvection_coe,Matrix.mul_apply,Fin.sum_univ_two]

-- Uniform exact FOUR-root decomposition, with ordered multiplication.
private theorem exists_four_roots (g : SL(2,F)) :
    ∃ x y z w : F, upper x * lower y * upper z * lower w = g := by
  apply Matrix.SpecialLinearGroup.fin_two_induction _ ?_ g
  intro a b c d hdet
  by_cases hd : d = 0
  · have hb : b ≠ 0 := by intro hb; simp [hd,hb] at hdet
    subst d
    refine ⟨0,-1/b,b,(a-1)/b,?_⟩
    apply Subtype.ext
    rw [four_root_matrix]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals dsimp
    all_goals field_simp
    all_goals try ring
    all_goals linear_combination hdet
  · refine ⟨(b-(d-1))/d,1,d-1,(c-1)/d,?_⟩
    apply Subtype.ext
    rw [four_root_matrix]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals dsimp
    all_goals field_simp
    all_goals try ring
    all_goals linear_combination -d*hdet
private def weyl : SL(2,F) := ⟨!![0,-1;1,0],by simp⟩
private theorem weyl_upper (t : F) : MulAut.conj (weyl : SL(2,F)) (upper t) = lower (-t) := by
  simp only [MulAut.conj_apply]
  apply Subtype.ext
  change (weyl : SL(2,F)).val * (upper t).val * Matrix.adjugate (weyl : SL(2,F)).val = (lower (-t)).val
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [weyl,upper,lower,transvection_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

private theorem actual_lower_root_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin M → MulAut SL(2,F)) (phi : Fin M → RingAut F)
    (chi : Fin M → F) (hchi : ∀ j, chi j ≠ 0)
    (d : Fin M → ℕ) (hd : ∀ j, 0 < d j ∧ d j ∣ q)
    (hbeta : ∀ j t, beta j (lower t) = lower (chi j * phi j t)) :
    ∃ y : Fin M → SL(2,F), ∀ target : F, ∃ t : Fin M → F,
      orderedProduct (fun j => (lower (t j))⁻¹ *
        (((beta j * MulAut.conj (y j)⁻¹)^d j) (lower (t j)))) = lower target := by
  let T := MulAut.conj (weyl : SL(2,F))
  have hTu : ∀ t : F, T (upper t) = lower (-t) := weyl_upper
  have hTl : ∀ t : F, T⁻¹ (lower t) = upper (-t) := by
    intro t
    apply T.injective
    simp only [MulAut.apply_inv_self,hTu,neg_neg]
  let beta' := fun j => T⁻¹ * beta j * T
  have hb' : ∀ j t, beta' j (upper t) = upper (chi j*phi j t) := by
    intro j t
    simp only [beta',MulAut.mul_apply,hTu,hbeta,hTl,map_neg]
    congr 1
    ring
  obtain ⟨y,hy⟩ := actual_A1_root_scalar_product hq hM hF beta' phi chi hchi d hd hb'
  have hstep : ∀ j z, (beta j*MulAut.conj (T (y j))⁻¹) (T z) =
      T ((beta' j*MulAut.conj (y j)⁻¹) z) := by
    intro j z
    simp only [beta',MulAut.mul_apply,MulAut.conj_inv_apply,map_mul,map_inv,
      MulAut.apply_inv_self]
  have hpow : ∀ j n z, ((beta j*MulAut.conj (T (y j))⁻¹)^n) (T z) =
      T (((beta' j*MulAut.conj (y j)⁻¹)^n) z) := by
    intro j n z
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',MulAut.mul_apply,ih,hstep]
      exact congrArg T (by rw [pow_succ']; rfl)
  refine ⟨fun j => T (y j),?_⟩
  intro target
  obtain ⟨t,ht⟩ := hy (-target)
  refine ⟨fun j => -t j,?_⟩
  have hm : ∀ f : Fin M → SL(2,F), T (orderedProduct f) = orderedProduct (fun j => T (f j)) := by
    intro f
    simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def]
  have hval : ∀ j, T ((upper (t j))⁻¹ *
      (((beta' j*MulAut.conj (y j)⁻¹)^d j) (upper (t j)))) =
      (lower (-t j))⁻¹ * (((beta j*MulAut.conj (T (y j))⁻¹)^d j) (lower (-t j))) := by
    intro j
    rw [map_mul,map_inv,← hpow,hTu]
  have hh := congrArg T ht
  rw [hm,hTu,neg_neg] at hh
  simpa only [hval] using hh

private def blockIndex {M : ℕ} (a : Fin 4) (j : Fin M) : Fin (4*M) := finProdFinEquiv (a,j)

private theorem ordered_blocks {G : Type*} [Group G] {M : ℕ} (f : Fin (4*M) → G) :
    orderedProduct f = orderedProduct (fun a : Fin 4 => orderedProduct (fun j : Fin M => f (blockIndex a j))) := by
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

/-- Actual full SL2 scalar PRODUCT coverage for normalized automorphisms with
Genuine prescribed semilinear positive AND negative root laws. Four consecutive
blocks use the two actual root suppliers, then exact ULUL matrix reconstruction.
The output is the UNCHANGED scalar interface, with q/e divisors, actual inner
y and ordered witnesses. Quantitative normalization of arbitrary finite-simple
automorphisms, other Lie types and other families remain separate gaps. -/
theorem actual_normalized_SL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut SL(2,F)) (e : Fin (4*M) → ℕ)
    (phiu phil : Fin (4*M) → RingAut F) (chiu chil : Fin (4*M) → F)
    (hchiu : ∀ j, chiu j ≠ 0) (hchil : ∀ j, chil j ≠ 0)
    (hbetau : ∀ j t, beta j (upper t) = upper (chiu j * phiu j t))
    (hbetal : ∀ j t, beta j (lower t) = lower (chil j * phil j t)) :
    PartIIScalarProductInput q (4*M) beta e := by
  intro he
  let d := fun j => q/e j
  have hd : ∀ j, 0 < d j ∧ d j ∣ q := by
    intro j
    refine ⟨Nat.div_pos (Nat.le_of_dvd hq (he j).2) (he j).1,?_⟩
    exact ⟨e j,(Nat.div_mul_cancel (he j).2).symm⟩
  obtain ⟨y0,hy0⟩ := actual_A1_root_scalar_product hq hM hF
    (fun j => beta (blockIndex 0 j)) (fun j => phiu (blockIndex 0 j))
    (fun j => chiu (blockIndex 0 j)) (fun j => hchiu _) (fun j => d (blockIndex 0 j))
    (fun j => hd _) (fun j t => hbetau _ t)
  obtain ⟨y1,hy1⟩ := actual_lower_root_scalar_product hq hM hF
    (fun j => beta (blockIndex 1 j)) (fun j => phil (blockIndex 1 j))
    (fun j => chil (blockIndex 1 j)) (fun j => hchil _) (fun j => d (blockIndex 1 j))
    (fun j => hd _) (fun j t => hbetal _ t)
  obtain ⟨y2,hy2⟩ := actual_A1_root_scalar_product hq hM hF
    (fun j => beta (blockIndex 2 j)) (fun j => phiu (blockIndex 2 j))
    (fun j => chiu (blockIndex 2 j)) (fun j => hchiu _) (fun j => d (blockIndex 2 j))
    (fun j => hd _) (fun j t => hbetau _ t)
  obtain ⟨y3,hy3⟩ := actual_lower_root_scalar_product hq hM hF
    (fun j => beta (blockIndex 3 j)) (fun j => phil (blockIndex 3 j))
    (fun j => chil (blockIndex 3 j)) (fun j => hchil _) (fun j => d (blockIndex 3 j))
    (fun j => hd _) (fun j t => hbetal _ t)
  let ys : Fin 4 → Fin M → SL(2,F) := ![y0,y1,y2,y3]
  let Y : Fin (4*M) → SL(2,F) := fun i => ys (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hY : ∀ a j, Y (blockIndex a j) = ys a j := by
    intro a j
    dsimp only [Y,blockIndex]
    rw [Equiv.symm_apply_apply]
  refine ⟨Y,?_⟩
  intro target
  obtain ⟨x0,x1,x2,x3,hroot⟩ := exists_four_roots target
  obtain ⟨t0,ht0⟩ := hy0 x0
  obtain ⟨t1,ht1⟩ := hy1 x1
  obtain ⟨t2,ht2⟩ := hy2 x2
  obtain ⟨t3,ht3⟩ := hy3 x3
  let cs : Fin 4 → Fin M → SL(2,F) := ![fun j => upper (t0 j),fun j => lower (t1 j),
    fun j => upper (t2 j),fun j => lower (t3 j)]
  let c : Fin (4*M) → SL(2,F) := fun i => cs (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hc : ∀ a j, c (blockIndex a j) = cs a j := by
    intro a j
    dsimp only [c,blockIndex]
    rw [Equiv.symm_apply_apply]
  refine ⟨c,?_⟩
  change orderedProduct (fun j => (c j)⁻¹ * ((beta j * MulAut.conj (Y j)⁻¹)^d j) (c j)) = target
  rw [ordered_blocks]
  simp only [hc,hY]
  have hout : ∀ f : Fin 4 → SL(2,F), orderedProduct f = f 0*f 1*f 2*f 3 := by
    intro f
    simp [orderedProduct,List.ofFn_succ,mul_assoc]
  rw [hout]
  change orderedProduct (fun j => (upper (t0 j))⁻¹ *
      ((beta (blockIndex 0 j)*MulAut.conj (y0 j)⁻¹)^d (blockIndex 0 j)) (upper (t0 j))) *
    orderedProduct (fun j => (lower (t1 j))⁻¹ *
      ((beta (blockIndex 1 j)*MulAut.conj (y1 j)⁻¹)^d (blockIndex 1 j)) (lower (t1 j))) *
    orderedProduct (fun j => (upper (t2 j))⁻¹ *
      ((beta (blockIndex 2 j)*MulAut.conj (y2 j)⁻¹)^d (blockIndex 2 j)) (upper (t2 j))) *
    orderedProduct (fun j => (lower (t3 j))⁻¹ *
      ((beta (blockIndex 3 j)*MulAut.conj (y3 j)⁻¹)^d (blockIndex 3 j)) (lower (t3 j))) = target
  rw [ht0,ht1,ht2,ht3]
  exact hroot

end NikolovSegal.PartIIA1RootSupply

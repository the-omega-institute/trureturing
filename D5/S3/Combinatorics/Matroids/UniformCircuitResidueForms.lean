/- GID: D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/UniformCircuitResidueForms
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Alternating form reduction of the uniform circuit and boundary equations. -/

module

public import D5.S3.HomologicalAlgebra.OrderedFaceSign
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! The effect of a distinguished coordinate on a pair of exterior operations. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms

open AlternatingMap
set_option autoImplicit false

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] {n : ℕ}

/-- Multiplication by a covector on alternating forms. -/
def covectorWedge (a : M →ₗ[R] R) (f : M [⋀^Fin n]→ₗ[R] N) :
    M [⋀^Fin (n + 1)]→ₗ[R] N :=
  alternatizeUncurryFin (a.smulRight f)

/-- Inserting a vector into a covector product gives a scalar term and a product
of the insertion into the original form. -/
theorem curry_covectorWedge (a : M →ₗ[R] R) (x : M) (f : M [⋀^Fin (n + 1)]→ₗ[R] N) :
    (covectorWedge a f).curryLeft x = a x • f - covectorWedge a (f.curryLeft x) := by
  ext v
  rw [curryLeft_apply_apply, covectorWedge, alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  simp only [curryLeft_apply_apply, covectorWedge, alternatizeUncurryFin_apply,
    Matrix.vecCons, Fin.val_zero, pow_zero, one_smul,
    Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons, smul_apply, sub_apply,
    LinearMap.smulRight_apply]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hr : i.succ.removeNth (Fin.cons x v : Fin (n + 2) → M) =
      (Fin.cons x (i.removeNth v) : Fin (n + 1) → M) :=
    Fin.cons_comp_succ_succAbove x v i
  rw [Fin.cons_succ, hr, Fin.val_succ, pow_succ, mul_smul, neg_one_smul, smul_neg]

private lemma covectorWedge_zero (a : M →ₗ[R] R) :
    covectorWedge a (0 : M [⋀^Fin n]→ₗ[R] N) = 0 := by
  ext v
  simp [covectorWedge, alternatizeUncurryFin_apply]

private lemma covectorWedge_sq (a : M →ₗ[R] R) (f : M [⋀^Fin n]→ₗ[R] N) :
    covectorWedge a (covectorWedge a f) = 0 := by
  let b := a.smulRight (a.smulRight f)
  have hb : a.smulRight (covectorWedge a f) = alternatizeUncurryFinLM ∘ₗ b := by
    apply LinearMap.ext
    intro x
    simp [b, covectorWedge]
  rw [covectorWedge, hb]
  apply alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
  intro x y
  simp only [b, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]
  rw [mul_comm]

private lemma curry_curry_swap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (x y : M) :
    (f.curryLeft x).curryLeft y = -(f.curryLeft y).curryLeft x := by
  ext v
  have h := f.map_insertNth (Fin.succ 0) y (Fin.cons x v)
  rw [Fin.insertNth_succ_cons, Fin.insertNth_zero'] at h
  simpa [curryLeft_apply_apply, Matrix.vecCons] using h

/-- A pivot on which the covector takes the value one splits the simultaneous
kernel of covector multiplication and insertion. -/
theorem closed_horizontal_iff (a : M →ₗ[R] R) (x y : M) (hx : a x = 1)
    (f : M [⋀^Fin (n + 2)]→ₗ[R] N) :
    covectorWedge a f = 0 ∧ f.curryLeft y = 0 ↔
      ∃ g : M [⋀^Fin (n + 1)]→ₗ[R] N, g.curryLeft x = 0 ∧
        f = covectorWedge a g ∧ a y • g = 0 ∧ g.curryLeft y = 0 := by
  constructor
  · rintro ⟨hclosed, hhorizontal⟩
    let g := f.curryLeft x
    have hgy : g.curryLeft y = 0 := by
      change (f.curryLeft x).curryLeft y = 0
      rw [curry_curry_swap, hhorizontal, curryLeft_zero, LinearMap.zero_apply, neg_zero]
    have heq := curry_covectorWedge a x f
    rw [hclosed, curryLeft_zero, LinearMap.zero_apply, hx, one_smul] at heq
    have hf : f = covectorWedge a g := sub_eq_zero.mp heq.symm
    refine ⟨g, curryLeft_same f x, hf, ?_, hgy⟩
    rw [hf, curry_covectorWedge, hgy] at hhorizontal
    simpa only [covectorWedge_zero, sub_zero] using hhorizontal
  · rintro ⟨g, _, rfl, hweighted, hgy⟩
    refine ⟨covectorWedge_sq a g, ?_⟩
    rw [curry_covectorWedge, hweighted, hgy]
    rw [covectorWedge_zero, sub_zero]

/-- Covector multiplication as a linear map on forms. -/
def covectorWedgeLinear (a : M →ₗ[R] R) :
    (M [⋀^Fin n]→ₗ[R] N) →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N :=
  alternatizeUncurryFinLM.comp (LinearMap.smulRightₗ a)

/-- Insertion of a fixed vector as a linear map on forms. -/
def insertVector (x : M) :
    (M [⋀^Fin (n + 1)]→ₗ[R] N) →ₗ[R] M [⋀^Fin n]→ₗ[R] N :=
  curryLeftLinearMap.flip x

/-- Inserting the pivot and multiplying by the covector are inverse maps
between the two specified submodules of forms. -/
def pivotFormEquiv (a : M →ₗ[R] R) (x y : M) (hx : a x = 1) :
    ↥((covectorWedgeLinear (N := N) (n := n + 2) a).ker ⊓ (insertVector y).ker) ≃ₗ[R]
      ↥(((insertVector (N := N) (n := n) x).ker ⊓ (insertVector y).ker) ⊓
        Submodule.torsionBy R (M [⋀^Fin (n + 1)]→ₗ[R] N) (a y)) where
  toFun f := ⟨f.val.curryLeft x, by
    have hclosed : covectorWedge a f.val = 0 := f.prop.1
    have hhorizontal : f.val.curryLeft y = 0 := f.prop.2
    obtain ⟨g, hgx, hg, hweight, hgy⟩ :=
      (closed_horizontal_iff a x y hx f.val).mp ⟨hclosed, hhorizontal⟩
    have hfg : f.val.curryLeft x = g := by
      rw [hg, curry_covectorWedge, hx, hgx, covectorWedge_zero, sub_zero, one_smul]
    change ((f.val.curryLeft x).curryLeft x = 0 ∧
      (f.val.curryLeft x).curryLeft y = 0) ∧ a y • f.val.curryLeft x = 0
    rw [hfg]
    exact ⟨⟨hgx, hgy⟩, hweight⟩⟩
  invFun g := ⟨covectorWedge a g.val, by
    exact (closed_horizontal_iff a x y hx _).mpr
      ⟨g.val, g.prop.1.1, rfl, g.prop.2, g.prop.1.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    change covectorWedge a (f.val.curryLeft x) = f.val
    have hclosed : covectorWedge a f.val = 0 := f.prop.1
    have h := curry_covectorWedge a x f.val
    rw [hclosed, curryLeft_zero, LinearMap.zero_apply, hx, one_smul] at h
    exact sub_eq_zero.mp h.symm |>.symm
  right_inv g := by
    apply Subtype.ext
    change (covectorWedge a g.val).curryLeft x = g.val
    have hgx : g.val.curryLeft x = 0 := g.prop.1.1
    rw [curry_covectorWedge, hx, hgx, covectorWedge_zero, sub_zero, one_smul]
  map_add' f g := Subtype.ext (by
    change (f.val + g.val).curryLeft x = f.val.curryLeft x + g.val.curryLeft x
    rw [curryLeft_add, LinearMap.add_apply])
  map_smul' t f := Subtype.ext (by
    change (t • f.val).curryLeft x = t • f.val.curryLeft x
    rw [curryLeft_smul, LinearMap.smul_apply])

/-- A form is determined by its values on increasing tuples of distinct basis vectors. -/
noncomputable def basisFormEquiv {I : Type*} [LinearOrder I] (b : Module.Basis I R M) :
    (Set.powersetCard I n → N) ≃ₗ[R] M [⋀^Fin n]→ₗ[R] N :=
  ((b.exteriorPower n).constr R).trans exteriorPower.alternatingMapLinearEquiv.symm

/-- Read the coordinate of an alternating form on an increasing basis tuple. -/
theorem basisFormEquiv_symm_apply {I : Type*} [LinearOrder I] (b : Module.Basis I R M)
    (f : M [⋀^Fin n]→ₗ[R] N) (s : Set.powersetCard I n) :
    (basisFormEquiv b).symm f s = f (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
  change ((b.exteriorPower n).constr R).symm (exteriorPower.alternatingMapLinearEquiv f) s = _
  rw [Module.Basis.constr_symm_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

open Finset Set.powersetCard
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

private lemma face_embedding_erase {I : Type*} [LinearOrder I]
    (e : Fin (n + 1) ↪o I) (i : Fin (n + 1)) :
    (ofFinEmbEquiv ((Fin.succAboveOrderEmb i).trans e)).val =
      (ofFinEmbEquiv e).val.erase (e i) := by
  ext x
  change x ∈ ofFinEmbEquiv ((Fin.succAboveOrderEmb i).trans e) ↔
    x ∈ (ofFinEmbEquiv e).val.erase (e i)
  rw [mem_ofFinEmbEquiv_iff_mem_range, mem_erase]
  change (∃ j, e (i.succAbove j) = x) ↔ x ≠ e i ∧ x ∈ ofFinEmbEquiv e
  rw [mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne i j (e.injective h), ⟨_, rfl⟩⟩
  · rintro ⟨hne, j, rfl⟩
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg e h))
    exact ⟨k, rfl⟩

private lemma insertionSign_erase_embedding {I : Type*} [LinearOrder I]
    (e : Fin (n + 1) ↪o I) (i : Fin (n + 1)) :
    insertionSign ((ofFinEmbEquiv e).val.erase (e i)) (e i) = (-1 : ℤ) ^ i.val := by
  have hfilter : ((ofFinEmbEquiv e).val.erase (e i)).filter (· < e i) =
      (Iio i).map e.toEmbedding := by
    ext x
    rw [mem_filter, mem_erase, mem_map]
    change (x ≠ e i ∧ x ∈ ofFinEmbEquiv e) ∧ x < e i ↔ _
    rw [mem_ofFinEmbEquiv_iff_mem_range]
    constructor
    · rintro ⟨⟨_, j, rfl⟩, hlt⟩
      exact ⟨j, mem_Iio.mpr ((e.lt_iff_lt).mp hlt), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hlt := e.strictMono (mem_Iio.mp hj)
      exact ⟨⟨hlt.ne, ⟨j, rfl⟩⟩, hlt⟩
  rw [insertionSign, hfilter, card_map, Fin.card_Iio]

/-- The finite ordered deletion sum is the coefficient of covector
multiplication on the corresponding basis tuple. -/
theorem basis_covectorWedge_apply {I : Type*} [LinearOrder I] (b : Module.Basis I ℤ M)
    (a : M →ₗ[ℤ] ℤ) (f : M [⋀^Fin n]→ₗ[ℤ] N)
    (e : Fin (n + 1) ↪o I) :
    covectorWedge a f (b ∘ e) =
      ∑ i : Fin (n + 1), insertionSign ((ofFinEmbEquiv e).val.erase (e i)) (e i) •
        a (b (e i)) •
          (basisFormEquiv b).symm f (ofFinEmbEquiv ((Fin.succAboveOrderEmb i).trans e)) := by
  rw [covectorWedge, alternatizeUncurryFin_apply]
  apply Fintype.sum_congr
  intro i
  rw [insertionSign_erase_embedding, LinearMap.smulRight_apply, basisFormEquiv_symm_apply,
    Equiv.symm_apply_apply]
  rfl

private lemma curryLeft_basis_repeat {I : Type*} [LinearOrder I] (b : Module.Basis I ℤ M)
    (f : M [⋀^Fin (n + 1)]→ₗ[ℤ] N) (k : I) (e : Fin n ↪o I)
    (hk : k ∈ ofFinEmbEquiv e) : f.curryLeft (b k) (b ∘ e) = 0 := by
  obtain ⟨j, rfl⟩ := (mem_ofFinEmbEquiv_iff_mem_range e k).mp hk
  rw [curryLeft_apply_apply]
  exact f.map_eq_zero_of_eq _ (i := 0) (j := j.succ) (by simp [Matrix.vecCons])
    (Fin.succ_ne_zero j).symm

/-- Inserting a new basis vector into a basis tuple gives the corresponding
coordinate with the ordered incidence sign. -/
theorem curryLeft_basis_insert {I : Type*} [LinearOrder I] (b : Module.Basis I ℤ M)
    (f : M [⋀^Fin (n + 1)]→ₗ[ℤ] N) (k : I) (e : Fin n ↪o I)
    (hk : k ∉ ofFinEmbEquiv e) :
    f.curryLeft (b k) (b ∘ e) =
      insertionSign (ofFinEmbEquiv e).val k •
        (basisFormEquiv b).symm f
          ⟨insert k (ofFinEmbEquiv e).val, by simp [card_insert_of_notMem hk]⟩ := by
  let S : Set.powersetCard I (n + 1) :=
    ⟨insert k (ofFinEmbEquiv e).val, by simp [card_insert_of_notMem hk]⟩
  let E := ofFinEmbEquiv.symm S
  have hkS : k ∈ S := mem_insert_self _ _
  obtain ⟨i, hi⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem S k).mpr hkS
  change E i = k at hi
  have hS : ofFinEmbEquiv E = S := Equiv.apply_symm_apply _ _
  have herase : (ofFinEmbEquiv E).val.erase (E i) = (ofFinEmbEquiv e).val := by
    rw [hS, hi]
    exact erase_insert hk
  have he : (Fin.succAboveOrderEmb i).trans E = e := by
    apply ofFinEmbEquiv.injective
    apply Subtype.ext
    exact (face_embedding_erase E i).trans herase
  have htuple : (i.insertNth (b k) (b ∘ e) : Fin (n + 1) → M) = b ∘ E := by
    funext j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp [hi]
    · simp only [Fin.insertNth_apply_succAbove, Function.comp_apply]
      exact congrArg b (congrArg (fun g : Fin n ↪o I => g l) he.symm)
  have hsign := insertionSign_erase_embedding E i
  rw [herase, hi] at hsign
  change f.curryLeft (b k) (b ∘ e) =
    insertionSign (ofFinEmbEquiv e).val k • (basisFormEquiv b).symm f S
  rw [hsign, basisFormEquiv_symm_apply, ← htuple, neg_one_pow_smul_map_insertNth]
  rfl

/-- Extend the basis coordinates of a form by zero on subsets of the wrong size. -/
noncomputable def formCoordinates {I : Type*} [LinearOrder I] (b : Module.Basis I ℤ M)
    (f : M [⋀^Fin n]→ₗ[ℤ] N) (S : Finset I) : N :=
  if h : S.card = n then (basisFormEquiv b).symm f ⟨S, h⟩ else 0

/-- Inserting a weighted sum of basis vectors reads out the signed weighted
boundary at the given ordered face. -/
theorem curryLeft_weighted_basis {I : Type*} [Fintype I] [LinearOrder I]
    (b : Module.Basis I ℤ M) (f : M [⋀^Fin (n + 1)]→ₗ[ℤ] N)
    (w : I → ℕ) (e : Fin n ↪o I) :
    f.curryLeft (∑ i, w i • b i) (b ∘ e) =
      ∑ i ∈ univ \ (ofFinEmbEquiv e).val, insertionSign (ofFinEmbEquiv e).val i •
        (w i • formCoordinates b f (insert i (ofFinEmbEquiv e).val)) := by
  classical
  let eval : (M [⋀^Fin n]→ₗ[ℤ] N) →ₗ[ℤ] N :=
    { toFun := fun g => g (b ∘ e)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change eval (f.curryLeft (∑ i, w i • b i)) = _
  simp only [map_sum, map_nsmul]
  change (∑ i, w i • f.curryLeft (b i) (b ∘ e)) = _
  rw [← sum_subset (sdiff_subset (s := univ) (t := (ofFinEmbEquiv e).val))]
  · apply sum_congr rfl
    intro i hi
    have hout : i ∉ ofFinEmbEquiv e := (mem_sdiff.mp hi).2
    have hcard : (insert i (ofFinEmbEquiv e).val).card = n + 1 :=
      (card_insert_of_notMem hout).trans (congrArg (· + 1) (ofFinEmbEquiv e).prop)
    rw [curryLeft_basis_insert b f i e hout, formCoordinates, dite_eq_left hcard]
    exact smul_comm _ _ _
  · intro i _ hi
    have hin : i ∈ ofFinEmbEquiv e := by
      change i ∈ (ofFinEmbEquiv e).val
      simpa only [mem_sdiff, mem_univ, true_and, not_not] using hi
    rw [curryLeft_basis_repeat b f i e hin, nsmul_zero]

/-- Insertion of a multiple of a basis vector is zero precisely when that
multiple kills the coefficients indexed by subsets containing the vector. -/
theorem curryLeft_smul_basis_eq_zero_iff {I : Type*} [LinearOrder I]
    (b : Module.Basis I ℤ M) (f : M [⋀^Fin (n + 1)]→ₗ[ℤ] N) (d : ℤ) (k : I) :
    f.curryLeft (d • b k) = 0 ↔
      ∀ S : Set.powersetCard I (n + 1), k ∈ S → d • (basisFormEquiv b).symm f S = 0 := by
  constructor
  · intro hz S hk
    let T : Set.powersetCard I n :=
      ⟨S.val.erase k, by
        change (S.val.erase k).card = n
        have hs : S.val.card = n + 1 := S.prop
        rw [card_erase_of_mem hk, hs, Nat.add_sub_cancel]⟩
    let e := ofFinEmbEquiv.symm T
    have hEq : ofFinEmbEquiv e = T := Equiv.apply_symm_apply _ _
    have hnot : k ∉ ofFinEmbEquiv e := by
      rw [hEq]
      exact notMem_erase _ _
    have hvalue := congrArg (fun h : M [⋀^Fin n]→ₗ[ℤ] N => h (b ∘ e)) hz
    simp only [map_zsmul, smul_apply, zero_apply] at hvalue
    rw [curryLeft_basis_insert b f k e hnot] at hvalue
    have hS (hc : insert k (ofFinEmbEquiv e).val ∈ Set.powersetCard I (n + 1)) :
        (⟨insert k (ofFinEmbEquiv e).val, hc⟩ : Set.powersetCard I (n + 1)) = S := by
      apply Subtype.ext
      change insert k (ofFinEmbEquiv e).val = S.val
      rw [hEq]
      exact insert_erase hk
    rw [hS, smul_comm d] at hvalue
    have hval := congrArg (insertionSign (ofFinEmbEquiv e).val k • ·) hvalue
    have hsq : insertionSign (ofFinEmbEquiv e).val k *
        insertionSign (ofFinEmbEquiv e).val k = 1 := by
      rw [insertionSign, ← pow_add]
      exact Even.neg_one_pow ⟨_, rfl⟩
    simpa only [smul_smul, ← mul_assoc, hsq, one_mul, smul_zero] using hval
  · intro h
    apply (basisFormEquiv b).symm.injective
    rw [_root_.map_zero]
    funext T
    rw [basisFormEquiv_symm_apply, map_zsmul, smul_apply]
    let e := ofFinEmbEquiv.symm T
    by_cases hk : k ∈ ofFinEmbEquiv e
    · rw [curryLeft_basis_repeat b f k e hk, smul_zero]
      rfl
    · rw [curryLeft_basis_insert b f k e hk, smul_comm d]
      rw [h _ (mem_insert_self _ _), smul_zero]
      rfl

end D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms

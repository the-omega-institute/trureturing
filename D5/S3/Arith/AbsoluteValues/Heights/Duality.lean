/- GID: D5/S3/Arith/AbsoluteValues/Heights/Duality
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/Duality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Arakelov height of a subspace agrees with that of its dual annihilator. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasis
public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasisMetrics
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.NumberTheory.Height.MvPolynomial
import all Mathlib.NumberTheory.Height.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection

-- Used only inside proofs: the complement of a subspace and the basis it produces, the dual
-- basis, the dimension of an annihilator, and the two-sided inverse of a square matrix.

public section

open Module

namespace Set.powersetCard

end Set.powersetCard

namespace Projectivization

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι]

end Projectivization

namespace Submodule

open exteriorPower

section Degenerate

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {V : Submodule K (ι → K)}

end Degenerate

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}

section Relative

variable [Height.AdmissibleAbsValues K]

/-- **The multiplicative height of a linear subspace of `ι → K`**: the projective height of its
Plücker point, following Schmidt. The rank is read off `V` rather than supplied, so this is a
total function of `V`. -/
noncomputable def mulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.mulHeight (V.pluckerPoint rfl)

/-- **The logarithmic height of a linear subspace of `ι → K`.** -/
noncomputable def logHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.logHeight (V.pluckerPoint rfl)

end Relative

section Arakelov

variable [NumberField K]

/-- **The multiplicative Arakelov height of a linear subspace of `ι → K`**, `H_Ar(V)` of
Bombieri–Gubler 2.8.11. -/
@[expose] noncomputable def arakelovMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.projectiveArakelovMulHeight (V.pluckerPoint rfl)

/-- **The logarithmic Arakelov height of a linear subspace of `ι → K`.** -/
noncomputable def arakelovLogHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.arakelovLogHeight (V.pluckerPoint rfl)

end Arakelov

section Absolute

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- **The absolute multiplicative height of a linear subspace of `ι → K`**, `h(V)` of
Bombieri–Gubler 2.8.4. -/
noncomputable def absMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.absMulHeight (V.pluckerPoint rfl)

/-- **The absolute logarithmic height of a linear subspace of `ι → K`.** -/
noncomputable def absLogHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.absLogHeight (V.pluckerPoint rfl)

end Absolute

end Submodule

section Examples

open Submodule

end Examples

end

public section

open Finset Function Height AdmissibleAbsValues Real

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α ι κ : Type*}

end Height

namespace Matrix

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {m n p m' n' : Type*}

/-- **The height of a matrix** is the height of the tuple of its **entries** (Bombieri–Gubler
2.9.8). The height of its row space — the height of the tuple of maximal minors, `H(A)` in
Bombieri–Vaaler — is a height on a Grassmannian and is never called the height of `A` here. -/
@[expose] noncomputable def mulHeight (A : Matrix m n K) : ℝ :=
  Height.mulHeight fun q : m × n ↦ A q.1 q.2

/-- The logarithmic height of a matrix. As everywhere in this development, the logarithmic height
is *defined* as the logarithm of the multiplicative one and never independently. -/
@[expose] noncomputable def logHeight (A : Matrix m n K) : ℝ := log (mulHeight A)

/-- **The affine height of a matrix**: the height of the tuple of its entries with a coordinate
`1` appended, `Height.mulHeightAff` of the entries. Unlike `Matrix.mulHeight` it is not invariant
under scaling, which is exactly what a bound on the determinant needs. -/
@[expose] noncomputable def mulHeightAff (A : Matrix m n K) : ℝ :=
  Height.mulHeightAff fun q : m × n ↦ A q.1 q.2

/-- The logarithmic affine height of a matrix. -/
@[expose] noncomputable def logHeightAff (A : Matrix m n K) : ℝ := log (mulHeightAff A)

section Basic

variable [Finite m] [Finite n]

end Basic

section Mul

variable [Finite m] [Fintype n] [Finite p]

end Mul

section Det

variable [Fintype n] [DecidableEq n]

end Det

end Matrix

namespace Matrix

variable {K : Type*} [Field K] [NumberField K] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- **The Arakelov height of a matrix**: the Arakelov height of the tuple of its entries, so the
Frobenius norm at each infinite place and the sup norm at each finite one. -/
@[expose] noncomputable def arakelovMulHeight (A : Matrix m n K) : ℝ :=
  NumberField.arakelovMulHeight fun q : m × n ↦ A q.1 q.2

/-- The logarithmic Arakelov height of a matrix. -/
@[expose] noncomputable def arakelovLogHeight (A : Matrix m n K) : ℝ := log (arakelovMulHeight A)

end Matrix

section Examples

open Height NumberField

end Examples

end

public section

open Finset Module Set.powersetCard exteriorPower

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*}

end Height

namespace NumberField

variable {K : Type*} [Field K] {ι : Type*}

section Arakelov

variable [NumberField K] [Fintype ι]

end Arakelov

section Absolute

variable [CharZero K] [Finite ι]

end Absolute

end NumberField

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {k l : ℕ}

variable [LinearOrder ι]

/-- The enumeration of `ι` that lists the elements of `s` in increasing order and then those of
its complement. This is the index identification the complementary-minor identity runs on; the
determinant of a matrix read through it depends on `s` only up to a sign. -/
private noncomputable def enumEquiv {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l) :
    Fin k ⊕ Fin l ≃ ι :=
  (Equiv.sumCongr (s.orderIsoOfFin hs).toEquiv
    ((sᶜ.orderIsoOfFin hsc).toEquiv.trans
      (Equiv.subtypeEquivRight fun _ ↦ Finset.mem_compl))).trans (Equiv.sumCompl (· ∈ s))

/-- **The complementary-minor identity.** If the rows of `C` and the rows of `D` are dual to one
another for the standard bilinear form, then the maximal minor of the first block of `C` on the
columns `s` is the complementary minor of the second block of `D` times the determinant of `C`
read through the enumeration attached to `s`. This is the whole content of duality: the
`s`-dependence of the factor is a sign, by `Matrix.det_permute'`. -/
private theorem det_submatrix_inl_eq_mul (C D : Matrix (Fin k ⊕ Fin l) ι R) (hCD : C * Dᵀ = 1)
    {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l) :
    ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)).det
      = (C.submatrix id (enumEquiv hs hsc)).det *
          ((D.submatrix Sum.inr id).submatrix id (sᶜ.orderEmbOfFin hsc)).det := by
  classical
  have hdual (r c : Fin k ⊕ Fin l) :
      ∑ i, C r i * D c i = (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) R) r c := by
    rw [← hCD, Matrix.mul_apply]
    rfl
  set E : Matrix ι (Fin k ⊕ Fin l) R :=
    Matrix.of fun i r ↦ Sum.elim (fun a ↦ if i = s.orderEmbOfFin hs a then 1 else 0)
      (fun b ↦ D (Sum.inr b) i) r with hE
  have hCE : C * E = Matrix.fromBlocks
      ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)) 0
      ((C.submatrix Sum.inr id).submatrix id (s.orderEmbOfFin hs)) 1 := by
    ext r c
    rcases c with a | b
    · rcases r with a' | b' <;>
        simp [Matrix.mul_apply, hE, mul_ite, Finset.sum_ite_eq' Finset.univ]
    · rcases r with a' | b' <;>
        simp [Matrix.mul_apply, hE, hdual _ (Sum.inr b), Matrix.one_apply]
  have hEσ : E.submatrix (enumEquiv hs hsc) id = Matrix.fromBlocks 1
      (Matrix.of fun a' b ↦ D (Sum.inr b) (s.orderEmbOfFin hs a')) 0
      ((D.submatrix Sum.inr id).submatrix id (sᶜ.orderEmbOfFin hsc))ᵀ := by
    ext r c
    rcases r with a' | b' <;> rcases c with a | b
    · simp only [Matrix.submatrix_apply, id_eq, enumEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Equiv.subtypeEquivRight_apply, OrderIso.coe_toEquiv, Finset.coe_orderIsoOfFin_apply,
        hE, Matrix.of_apply, Sum.elim_inl,
        Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      exact if_congr ⟨fun h ↦ (s.orderEmbOfFin hs).injective h, fun h ↦ by rw [h]⟩ rfl rfl
    · simp [hE, enumEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Equiv.subtypeEquivRight_apply, Finset.coe_orderIsoOfFin_apply]
    · have hne : sᶜ.orderEmbOfFin hsc b' ≠ s.orderEmbOfFin hs a := by
        intro hcon
        have h1 : sᶜ.orderEmbOfFin hsc b' ∈ sᶜ := sᶜ.orderEmbOfFin_mem hsc b'
        rw [hcon, Finset.mem_compl] at h1
        exact h1 (s.orderEmbOfFin_mem hs a)
      simp [hE, enumEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Equiv.subtypeEquivRight_apply, Finset.coe_orderIsoOfFin_apply, hne]
    · simp [hE, enumEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Equiv.subtypeEquivRight_apply, Finset.coe_orderIsoOfFin_apply, Matrix.transpose_apply]
  have hdet : (C * E).det = ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)).det := by
    rw [hCE, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  rw [← hdet, ← Matrix.submatrix_id_id (C * E),
    ← Matrix.submatrix_mul_equiv C E id (enumEquiv hs hsc) id, Matrix.det_mul, hEσ,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_transpose]

end Matrix

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {r : Type*} [Fintype r] [DecidableEq r]




end Matrix

namespace Submodule

open Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {k l : ℕ}


variable [LinearOrder ι]


/-- **Plücker duality in coordinates** (W. M. Schmidt 1967, §1, equations (2) and (4)). A
subspace and its annihilator have bases whose Plücker coordinates agree at complementary indices,
up to a sign at each index and one common nonzero factor — the involution Schmidt calls `τ`.
Every height in this development is invariant under exactly that much. -/
theorem exists_plucker_eq_plucker_compl (V : Submodule K (ι → K)) (hk : finrank K V = k)
    (hlk : l + k = Fintype.card ι) :
    ∃ (v : Fin k → (ι → K)) (w : Fin l → (ι → K)) (c : K), c ≠ 0 ∧
      LinearIndependent K v ∧ LinearIndependent K w ∧
      span K (Set.range v) = V ∧
      span K (Set.range w) = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ∧
      ∀ s : Set.powersetCard ι k,
        exteriorPower.plucker k v s
            = c * exteriorPower.plucker l w (Set.powersetCard.compl hlk s) ∨
          exteriorPower.plucker k v s
            = -(c * exteriorPower.plucker l w (Set.powersetCard.compl hlk s)) := by
  let nativeSource18 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) => (show exteriorPower.plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det from by
    classical
    rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp)))
  let nativeSource19 := (open Module Submodule exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι R) (s : Set.powersetCard ι m) => (show exteriorPower.plucker m A.row s =
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det from by
    classical
    rw [nativeSource18, Set.powersetCard.ofFinEmbEquiv_symm_apply]
    rfl)))
  classical
  obtain ⟨C, D, hCD, hV⟩ := (open scoped Classical NumberField in (open Height Module Matrix Set Submodule in (fun {K : Type _} [instK : Field K] {ι : Type _} [instI : Fintype ι] {k l : ℕ} (V : Submodule K (ι → K)) (hk : finrank K V = k)
        (hlk : l + k = Fintype.card ι) => (show ∃ C D : Matrix (Fin k ⊕ Fin l) ι K, C * Dᵀ = 1 ∧
          span K (Set.range (C.submatrix Sum.inl id).row) = V from by
      classical
      obtain ⟨W, hW⟩ := V.exists_isCompl
      have hWrank : finrank K W = l := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq V W
        rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, hk, Module.finrank_pi] at h
        omega
      let bV := Module.finBasisOfFinrankEq K V hk
      let bW := Module.finBasisOfFinrankEq K W hWrank
      let c : Module.Basis (Fin k ⊕ Fin l) K (ι → K) :=
        (bV.prod bW).map (V.prodEquivOfIsCompl W hW)
      have hcl (a : Fin k) : c (Sum.inl a) = (bV a : ι → K) := by
        simp only [c, Module.Basis.map_apply]
        rw [show (bV.prod bW) (Sum.inl a) = ((bV a : V), (0 : W)) from
          Prod.ext (bV.prod_apply_inl_fst bW a) (bV.prod_apply_inl_snd bW a)]
        simp [V.coe_prodEquivOfIsCompl' W hW ((bV a : V), (0 : W))]
      refine ⟨Matrix.of fun r ↦ (c r), Matrix.of fun s i ↦ c.coord s (Pi.basisFun K ι i), ?_, ?_⟩
      · ext r s
        rw [Matrix.mul_apply, Matrix.one_apply]
        have : ∑ i, c r i * c.coord s (Pi.basisFun K ι i) = c.coord s (c r) := by
          conv_rhs => rw [← (Pi.basisFun K ι).sum_repr (c r)]
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by
            rw [map_smul, smul_eq_mul, Pi.basisFun_repr]
        simp only [Matrix.transpose_apply, Matrix.of_apply]
        rw [this, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      · have hrange : Set.range ((Matrix.of fun r ↦ (c r) : Matrix (Fin k ⊕ Fin l) ι K).submatrix
            Sum.inl id).row = V.subtype '' (Set.range bV) := by
          rw [← Set.range_comp]
          exact congrArg Set.range (_root_.funext fun a ↦ hcl a)
        rw [hrange, Submodule.span_image, bV.span_eq, Submodule.map_top,
          Submodule.range_subtype])))) V hk hlk
  have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card ι := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨e₀⟩ := Fintype.truncEquivOfCardEq hcard
  have hDC : D * Cᵀ = 1 := by
    have h := congrArg Matrix.transpose hCD
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  refine ⟨(C.submatrix Sum.inl id).row, (D.submatrix Sum.inr id).row, (C.submatrix id e₀).det,
    (IsUnit.of_mul_eq_one ((Dᵀ).submatrix e₀ id).det (by
      rw [← Matrix.det_mul, Matrix.submatrix_mul_equiv C Dᵀ id e₀ id,
        Matrix.submatrix_id_id, hCD, Matrix.det_one])).ne_zero,
    ((open scoped Classical NumberField in (open Height Module Matrix Set Matrix in (fun {K : Type _} [instK : Field K] {ι : Type _} [instI : Fintype ι] {r : Type _} [instR : Fintype r] [instD : DecidableEq r] {C D : Matrix r ι K}
          (hCD : C * Dᵀ = 1) => (show LinearIndependent K C.row from by
        refine linearIndependent_iff'.2 fun t g hg i hi ↦ ?_
        have h := congrArg (· ⬝ᵥ D.row i) hg
        simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at h
        rw [Finset.sum_congr rfl fun j _ ↦ by
          rw [show C.row j ⬝ᵥ D.row i = (C * Dᵀ) j i from rfl, hCD]] at h
        simpa [Matrix.one_apply, Finset.sum_ite_eq' t, hi] using h)))) hCD).comp _ Sum.inl_injective,
    ((open scoped Classical NumberField in (open Height Module Matrix Set Matrix in (fun {K : Type _} [instK : Field K] {ι : Type _} [instI : Fintype ι] {r : Type _} [instR : Fintype r] [instD : DecidableEq r] {C D : Matrix r ι K}
          (hCD : C * Dᵀ = 1) => (show LinearIndependent K C.row from by
        refine linearIndependent_iff'.2 fun t g hg i hi ↦ ?_
        have h := congrArg (· ⬝ᵥ D.row i) hg
        simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at h
        rw [Finset.sum_congr rfl fun j _ ↦ by
          rw [show C.row j ⬝ᵥ D.row i = (C * Dᵀ) j i from rfl, hCD]] at h
        simpa [Matrix.one_apply, Finset.sum_ite_eq' t, hi] using h)))) hDC).comp _ Sum.inr_injective,
    hV, (open scoped Classical NumberField in (open Height Module Matrix Set Submodule in (fun {K : Type _} [instK : Field K] {ι : Type _} [instI : Fintype ι] {k l : ℕ} {V : Submodule K (ι → K)} {C D : Matrix (Fin k ⊕ Fin l) ι K}
          (hCD : C * Dᵀ = 1) (hlk : l + k = Fintype.card ι)
          (hV : span K (Set.range (C.submatrix Sum.inl id).row) = V) => (show span K (Set.range (D.submatrix Sum.inr id).row)
            = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap from by
        have hdual (r t : Fin k ⊕ Fin l) :
            C.row r ⬝ᵥ D.row t = (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) K) r t := by
          rw [← hCD]
          rfl
        have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card ι := by
          simp only [Fintype.card_sum, Fintype.card_fin]
          omega
        refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ ?_
        · rintro _ ⟨b, rfl⟩
          rw [SetLike.mem_coe, (fun {V : Submodule K (ι → K)} {x : ι → K} => (show x ∈ V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ↔ ∀ v ∈ V, v ⬝ᵥ x = 0 from by
        simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
        refine forall₂_congr fun v _ ↦ ?_
        rw [show ((Module.piEquiv ι K K).toLinearMap x) v = Module.piEquiv ι K K x v from rfl,
          Module.piEquiv_apply_apply]
        simp [dotProduct]))]
          intro v hv
          rw [← hV] at hv
          have hker := (fun {s : Set (ι → K)} {x : ι → K} (h : ∀ v ∈ s, v ⬝ᵥ x = 0) => (show span K s ≤ LinearMap.ker (Module.piEquiv ι K K x) from by
        rw [Submodule.span_le]
        intro v hv
        simpa only [SetLike.mem_coe, LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul,
          dotProduct] using h v hv)) (s := Set.range (C.submatrix Sum.inl id).row)
            (x := (D.submatrix Sum.inr id).row b) (fun y hy ↦ ?_) hv
          · simpa only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul, dotProduct]
              using hker
          · obtain ⟨a, rfl⟩ := hy
            rw [show (C.submatrix Sum.inl id).row a ⬝ᵥ (D.submatrix Sum.inr id).row b
              = C.row (Sum.inl a) ⬝ᵥ D.row (Sum.inr b) from rfl, hdual]
            simp
        · rw [(fun {V : Submodule K (ι → K)} {x : ι → K} => (show x ∈ V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ↔ ∀ v ∈ V, v ⬝ᵥ x = 0 from by
        simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
        refine forall₂_congr fun v _ ↦ ?_
        rw [show ((Module.piEquiv ι K K).toLinearMap x) v = Module.piEquiv ι K K x v from rfl,
          Module.piEquiv_apply_apply]
        simp [dotProduct]))] at hx
          have hzero (a : Fin k) : C.row (Sum.inl a) ⬝ᵥ x = 0 :=
            hx _ (hV ▸ Submodule.subset_span ⟨a, rfl⟩)
          have hmem : (∑ j, (C.row j ⬝ᵥ x) • D.row j)
              ∈ span K (Set.range (D.submatrix Sum.inr id).row) := by
            rw [Fintype.sum_sum_type]
            simp only [hzero, zero_smul, Finset.sum_const_zero, zero_add]
            exact Submodule.sum_mem _ fun b _ ↦
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
          rwa [← (open scoped Classical NumberField in (open Height Module Matrix Set Matrix in (fun {K : Type _} [instK : Field K] {ι : Type _} [instI : Fintype ι] {r : Type _} [instR : Fintype r] [instD : DecidableEq r] {C D : Matrix r ι K} (hCD : C * Dᵀ = 1)
                (hcard : Fintype.card r = Fintype.card ι) (x : ι → K) => (show x = ∑ j, (C.row j ⬝ᵥ x) • D.row j from by
              classical
              obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard
              have hsq : (Dᵀ.submatrix e id) * (C.submatrix id e) = 1 := by
                refine mul_eq_one_comm.1 ?_
                rw [Matrix.submatrix_mul_equiv C Dᵀ id e id, Matrix.submatrix_id_id, hCD]
              have hDC : Dᵀ * C = 1 := by
                have hsub : (Dᵀ * C).submatrix e e = (Dᵀ.submatrix e id) * (C.submatrix id e) := by
                  ext a b
                  simp [Matrix.mul_apply]
                have h : (Dᵀ * C).submatrix e e = (1 : Matrix ι ι K).submatrix e e := by
                  rw [hsub, hsq, Matrix.submatrix_one_equiv]
                have h2 := congrArg (fun M ↦ M.submatrix e.symm e.symm) h
                simpa [Matrix.submatrix_submatrix] using h2
              funext i
              have hx : x i = ∑ a, (Dᵀ * C) i a * x a := by
                rw [hDC]
                simp [Matrix.one_apply, Finset.sum_ite_eq]
              rw [hx, Finset.sum_apply]
              simp only [Matrix.mul_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, dotProduct,
                Matrix.row, Finset.sum_mul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring)))) hCD hcard x] at hmem)))) hCD hlk hV, fun s ↦ ?_⟩
  have hs : (s : Finset ι).card = k := Set.powersetCard.card_eq s
  have hsc : ((s : Finset ι))ᶜ.card = l := by
    rw [Finset.card_compl, hs]
    omega
  rw [nativeSource19, nativeSource19,
    Matrix.det_submatrix_inl_eq_mul C D hCD hs hsc]
  rcases (open scoped Classical NumberField in (open Height Module Matrix Set Matrix in (fun {K : Type _} [instK : Field K] {ι : Type _} [instI : Fintype ι] {r : Type _} [instR : Fintype r] [instD : DecidableEq r] (X : Matrix r ι K) (e₁ e₂ : r ≃ ι) => (show (X.submatrix id e₁).det = (X.submatrix id e₂).det ∨
          (X.submatrix id e₁).det = -(X.submatrix id e₂).det from by
      have h : X.submatrix id e₁ = (X.submatrix id e₂).submatrix id (e₁.trans e₂.symm) := by
        ext i j
        simp
      rw [h, Matrix.det_permute']
      rcases Int.units_eq_one_or (Equiv.Perm.sign (e₁.trans e₂.symm)) with hs | hs <;> rw [hs] <;> simp)))) C (Matrix.enumEquiv hs hsc) e₀ with hsign | hsign
  · refine Or.inl ?_
    rw [hsign]
    rfl
  · refine Or.inr ?_
    rw [hsign, neg_mul]
    rfl

end Submodule

namespace Submodule

open Matrix exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]


section Relative

variable [Height.AdmissibleAbsValues K]

end Relative

section Arakelov

variable [NumberField K]

/-- **The duality theorem in the Arakelov normalization** (Bombieri–Gubler, Proposition 2.8.10).
Schmidt's mechanism gives both normalizations at once: the two coordinate tuples differ by a
signed reindexing and a scalar, and no height in Layer 0 sees either. -/
theorem arakelovMulHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).arakelovMulHeight =
      V.arakelovMulHeight := by
  let nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite :
        (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace K) :
        (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
          = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
      have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
      have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
        rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
          ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
        congr 1
        push_cast
        ring
      rw [hsum, Real.mul_rpow (by positivity) (by positivity),
        hPower]
    rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
    simp only [harch, Finset.prod_mul_distrib]
    rw [mul_right_comm, hFinite, mul_comm])))
  let nativeSource20 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (c : R) (v w : Fin k → (ι → R)) => (show exteriorPower.plucker k v = c • exteriorPower.plucker k w ↔ exteriorPower.ιMulti R k v = c • exteriorPower.ιMulti R k w from by
    classical
    rw [exteriorPower.plucker, exteriorPower.plucker, ← map_smul]
    exact (LinearEquiv.injective _).eq_iff)))
  let nativeSource21 := (open Module in (fun {k : ℕ} (s : Set.powersetCard (Fin k) k) => (show ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) from by
    classical
    have hs : (s : Finset (Fin k)) = Finset.univ := Finset.eq_univ_of_card _ (by simp)
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique _ (fun x ↦ hs ▸ Finset.mem_univ x) strictMono_id).symm)))
  let nativeSource22 := (open Module in (fun {K : Type _} {E : Type _} [instSource1 : Field K] [instSource2 : AddCommGroup E] [instSource3 : Module K E] {k : ℕ} {v : Fin k → E} (hv : LinearIndependent K v) => (show exteriorPower.ιMulti K k v ≠ 0 from by
    classical
    have h := (exteriorPower.ιMulti_family_linearIndependent_field k hv).ne_zero
      (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
    rwa [exteriorPower.ιMulti_family, nativeSource21, Function.comp_id] at h)))
  let nativeSource23 := (open Module exteriorPower in (fun {K : Type _} [instSource1 : Field K] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {k : ℕ} {V : Submodule K (ι → K)} (hV : Module.finrank K V = k) (b b' : Module.Basis (Fin k) K V) => (show ∃ c : K, exteriorPower.plucker k (fun i ↦ ((b' i : ι → K))) = c • exteriorPower.plucker k fun i ↦ ((b i : ι → K)) from by
    classical
    have h1 : Module.finrank K (⋀[K]^k V) = 1 := by rw [exteriorPower.finrank_eq, hV, Nat.choose_self]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (exteriorPower.ιMulti K k ⇑b)
      (nativeSource22 b.linearIndependent)).1 h1 (exteriorPower.ιMulti K k ⇑b')
    refine ⟨c, (nativeSource20 ..).2 ?_⟩
    have := congrArg (exteriorPower.map k V.subtype) hc
    rwa [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, eq_comm] at this)))
  let nativeSource24 := (open Module exteriorPower in (fun {K : Type _} [instSource1 : Field K] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {k : ℕ} {V : Submodule K (ι → K)} (hV : Module.finrank K V = k) (b : Module.Basis (Fin k) K V)
      (hb : exteriorPower.plucker k (fun i ↦ ((b i : ι → K))) ≠ 0) => (show Submodule.pluckerPoint V hV = Projectivization.mk K (exteriorPower.plucker k fun i ↦ ((b i : ι → K))) hb from by
    classical
    obtain ⟨c, hc⟩ := nativeSource23 hV b (Module.finBasisOfFinrankEq K V hV)
    refine ((Projectivization.mk_eq_mk_iff' K _ _ _ hb).2 ⟨c, hc.symm⟩))))
  let nativeSource27 := (open Module in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show exteriorPower.plucker k v ≠ 0 from by
    classical
    change (((Pi.basisFun K ι).exteriorPower k).equivFun) (exteriorPower.ιMulti K k v) ≠ 0
    exact (((Pi.basisFun K ι).exteriorPower k).equivFun).map_ne_zero_iff.mpr
      (nativeSource22 hv))))
  let nativeSource28 := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v)
      (hV : Module.finrank K (Submodule.span K (Set.range v)) = k) => (show Submodule.pluckerPoint (Submodule.span K (Set.range v)) hV =
        Projectivization.mk K (exteriorPower.plucker k v) (nativeSource27 hv) from by
    classical
    have hfun : (fun i ↦ ((Module.Basis.span hv i : ι → K))) = v :=
      funext fun i ↦ congrArg Subtype.val (Module.Basis.span_apply hv i)
    rw [nativeSource24 hV (Module.Basis.span hv) (by rw [hfun]; exact nativeSource27 hv)]
    simp only [hfun])))
  let nativeSource29 := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show (span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (exteriorPower.plucker k v) from by
    classical
    have hV : finrank K (span K (Set.range v)) = k :=
      (finrank_span_eq_card hv).trans (Fintype.card_fin k)
    rw [(show (span K (Set.range v)).arakelovMulHeight =
        Projectivization.projectiveArakelovMulHeight ((span K (Set.range v)).pluckerPoint hV) from by
          exact Eq.rec (motive := fun (r : ℕ) (hr : finrank K (span K (Set.range v)) = r) ↦
            (span K (Set.range v)).arakelovMulHeight = Projectivization.projectiveArakelovMulHeight ((span K (Set.range v)).pluckerPoint hr))
            rfl hV), nativeSource28 hv hV]
    rfl)))
  obtain ⟨k, l, hlk, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ := (open scoped Classical NumberField in (open Height Module Matrix Set Submodule in (fun {K : Type _} [instK : Field K] {ι : Type _} [instI : Fintype ι] [instL : LinearOrder ι] (V : Submodule K (ι → K)) => (show ∃ (k l : ℕ) (hlk : l + k = Fintype.card ι) (v : Fin k → (ι → K)) (w : Fin l → (ι → K))
          (c : K), c ≠ 0 ∧ LinearIndependent K v ∧ LinearIndependent K w ∧
          span K (Set.range v) = V ∧
          span K (Set.range w) = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ∧
          ∀ s : Set.powersetCard ι k,
            plucker k v s = c * plucker l w (Set.powersetCard.compl hlk s) ∨
              plucker k v s = -(c * plucker l w (Set.powersetCard.compl hlk s)) from by
      have hle : Module.finrank K V ≤ Fintype.card ι := by
        have h := V.finrank_le (R := K)
        rwa [Module.finrank_pi] at h
      obtain ⟨v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ :=
        exists_plucker_eq_plucker_compl V (l := Fintype.card ι - Module.finrank K V) rfl (by omega)
      exact ⟨_, _, _, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩)))) V
  let nativeSource101 := (open Finset Function Height Real in (fun (e : Set.powersetCard ι k ≃ Set.powersetCard ι l) (x : Set.powersetCard ι l → K) => (show NumberField.arakelovMulHeight (x ∘ e) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · simp [NumberField.arakelovMulHeight]
    have hx' : x ∘ e ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
      exact ne_iff.mpr ⟨e.symm i, by simpa using hi⟩
    have hsum (v : NumberField.InfinitePlace K) : ∑ i, v (x (e i)) ^ 2 = ∑ i, v (x i) ^ 2 :=
      e.sum_comp fun i ↦ v (x i) ^ 2
    have hsup (v : NumberField.FinitePlace K) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) :=
      e.iSup_congr (congrFun rfl)
    rw [NumberField.arakelovMulHeight, if_neg hx', NumberField.arakelovMulHeight, if_neg hx]
    simp only [Function.comp_apply, hsum, hsup])))
  rw [← hWw, ← hVv, nativeSource29 hv, nativeSource29 hw,
    (fun {x y : Set.powersetCard ι k → K}
    (h : ∀ i, y i = x i ∨ y i = -x i) => (show NumberField.arakelovMulHeight y = NumberField.arakelovMulHeight x from by
  have hinf (v : NumberField.InfinitePlace K) (i : Set.powersetCard ι k) : v (y i) = v (x i) := by
    rcases h i with hi | hi
    · rw [hi]
    · rw [hi]; exact v.1.map_neg _
  have hfin (v : NumberField.FinitePlace K) (i : Set.powersetCard ι k) : v (y i) = v (x i) := by
    rcases h i with hi | hi
    · rw [hi]
    · rw [hi]; simp
  have hzero : y = 0 ↔ x = 0 := by
    simp only [funext_iff, Pi.zero_apply]
    refine ⟨fun h0 i ↦ ?_, fun h0 i ↦ ?_⟩ <;> rcases h i with hi | hi
    · rw [← hi]; exact h0 i
    · have := h0 i; rw [hi, neg_eq_zero] at this; exact this
    · rw [hi, h0 i]
    · rw [hi, h0 i, neg_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hzero.2 rfl]
  · have hy : y ≠ 0 := fun h0 ↦ hx (hzero.1 h0)
    simp only [NumberField.arakelovMulHeight, if_neg hx, if_neg hy]
    congr 1
    · exact Finset.prod_congr rfl fun v _ ↦ by
        rw [Finset.sum_congr rfl fun i _ ↦ by rw [hinf v i]]
    · exact finprod_congr fun v ↦ iSup_congr (hfin v))) hpl,
    show (fun s ↦ c * plucker l w (Set.powersetCard.compl hlk s))
      = c • (plucker l w ∘ (Set.powersetCard.compl hlk)) from rfl,
    nativeSource12 _ hc, nativeSource101]

end Arakelov

section Absolute

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

end Absolute

end Submodule

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

end Submodule

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : Type*}

section Relative

variable [Height.AdmissibleAbsValues K]

end Relative

section Arakelov

variable [NumberField K]


end Arakelov

section Absolute

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

end Absolute

end Matrix

section Examples

open Matrix Submodule

end Examples

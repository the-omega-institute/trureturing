/- GID: D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartnerAlgebra
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartnerAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.LinearAlgebra.PartnerAlgebra. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/LinearAlgebra/PartnerAlgebra.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Topology.LocalDefs
import D5.S3.Zeros.GRH.Lib.Adelic.Witt.SpaceOperations
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Tower property: constant term of a theta lift along an isotropic line (known result; see
Lib.SiegelWeil.Tower.LargeSideConstantTerm).

This file: Primitive matrices extend to bases; partner data and their laws under integral
matrices. -/

noncomputable section


open Matrix Function MatMul
variable {R a b n : Type} [CommRing R] [Fintype b] [Fintype n] (O : Subring R)
  {y : Matrix n b R} (e : b ⊕ a ≃ n) (k : GL n R)

/-- For k in GL_n(R) and the indices split as b ⊔ a, the rows of k⁻¹ indexed by a. -/
abbrev invLastRows := k⁻¹.1.submatrix (e ∘ .inr) id

/-- For k in GL_n(R) and the indices split as b ⊔ a, the columns of k indexed by b. -/
abbrev firstCols := k.1.submatrix id (e ∘ .inl)

/-- Φ vanishes off the matrices x_k, Ψ off the y_k (k in GL_n(O); `invLastRows`, `firstCols`), and
Φ(x_k) = χ(det k)Ψ(y_k) for all such k. -/
structure IsPartner (χ : MulChar R ℂ) (Φ Ψ : _ → ℂ) where
  supp_left x : Φ x ≠ 0 → ∃ k ∈ intGL n O, x = invLastRows e k
  supp_right y : Ψ y ≠ 0 → ∃ k ∈ intGL n O, y = firstCols e k
  apply_eq : ∀ k ∈ intGL n O, Φ (invLastRows e k) = χ k.1.det * Ψ (firstCols e k)

variable {O}
attribute [local simp ←] submatrix_mul ext_iff map_inv
attribute [local simp] mem_intGL liftIntegralFn extend

/-- For an invertible matrix k and a splitting of the indices into two blocks, the rows of k⁻¹
indexed by the first block. -/
abbrev invFirstRows := k⁻¹.1.submatrix (e ∘ .inl) id

omit [Fintype b] in
lemma invFirstRows_mul_firstCols : invFirstRows e k * firstCols e k = 1 := by simp

omit [Fintype b] in
lemma hasLeftInv_invLastRows_transpose : HasLeftInv (invLastRows e k)ᵀ :=
  ⟨_, invFirstRows_mul_firstCols (.trans (.sumComm ..) e) (invTransposeGL k)⟩

lemma IsPrimitiveMatrix.mul_iff {x : Matrix b a R} : IsPrimitiveMatrix O y →
  (IsPrimitiveMatrix O (y * x) ↔ IsPrimitiveMatrix O x) := by
  use fun ⟨i, s, r, _⟩ ↦ .and ⟨(cast ?_ <| r.mul ·), i.mul⟩ ⟨.imp' (· * y) ?_, .imp' (· * s)
    ?_⟩ <;> simp +contextual [← s.mul_assoc, IsIntMatrix.mul, *]

lemma isPrimitiveMatrix_iff_mem_intGL : IsPrimitiveMatrix O k.1 ↔
  k ∈ intGL n O := by simp [isPrimitiveMatrix_iff, Units.val_inj]

omit [Fintype b] in
lemma isPrimitiveMatrix_firstCols {k} (hk : k ∈ intGL n O) :
  IsPrimitiveMatrix O (firstCols e k) := by use ?_, invFirstRows e k <;> aesop_cat

omit [Fintype b] in
lemma exists_invLastRows_iff_transpose {x} : (∃ k ∈ intGL n O, x = invLastRows e k) ↔
  ∃ k ∈ intGL n O, xᵀ = firstCols (.trans (.sumComm ..) e) k :=
  invTransposeGL.exists_congr' (invTransposeGL_mem_intGL · |>.and transpose_inj)

lemma det_fromRows_invLastRows [Fintype a] s :
  ((fromRows s (invLastRows e k)).submatrix e.symm id).det * k.1.det = (s * firstCols e k).det := by
  rw [← det_mul, ← det_submatrix_equiv_self e]
  convert (s * firstCols e k).det_fromBlocks_one₂₂
    (s * k.1.submatrix id e).toCols₂ 0 <;> simp [mul_apply]
  simp [← mul_apply]

omit [Fintype b] in
lemma invLastRows_mul_firstCols : invLastRows e k * firstCols e k = 0 := by simp

variable [Fintype a]

lemma firstCols_mul_invFirstRows (h : invLastRows e k * y = 0) :
  firstCols e k * (invFirstRows e k * y) = y :=
  .trans (by simp_all [mul_apply, reindex_equiv e, -coe_units_inv]) (k.1.mul_invOf_cancel_left y)

lemma exists_firstCols_eq_mul O g (hg : g ∈ intGL b O) f (hf : f ∈ intGL a O) (hk : k ∈ intGL n O) :
  ∃ j ∈ intGL n O, firstCols e j = firstCols e k * g.1 ∧ invLastRows e j = f.1 * invLastRows e k ∧
  j.1.det * f.1.det = k.1.det * g.1.det := ⟨k * reindexGL e (blockGL (g, f⁻¹)), by simp_all
  [mul_mem, mul_apply, reindex_equiv e, mul_assoc, Ring.inverse_mul_cancel]⟩

namespace IsPartner

attribute [scoped grind] IsPartner Units.val_one det_one coe_units_inv isUnits_det_units one_mem
  invFirstRows_mul_firstCols firstCols_mul_invFirstRows invLastRows_mul_firstCols
  isPrimitiveMatrix_firstCols isPrimitiveMatrix_iff

attribute [scoped grind =_] det_fromRows_invLastRows isPrimitiveMatrix_iff_mem_intGL

/-- If the subring O of R satisfies `IsValuationPair`, an n × b matrix y is the block of b-columns
of an element of GL_n(O) exactly when y has entries in O and a left inverse over O. -/
lemma _root_.IsValuationPair.exists_firstCols_iff (val : IsValuationPair O) : (∃ k ∈ intGL n O, y =
  firstCols e k) ↔ IsPrimitiveMatrix O y := by grind [val.hermite ⟨e ∘ .inl, by aesop_cat⟩ y,
  Embedding.coeFn_mk, IsPrimitiveMatrix.mul_iff, exists_firstCols_eq_mul e (f := 1)]

variable {e χ Φ Ψ F} [CommRing F] (h : IsPartner O e χ Φ Ψ)

lemma lift_of_reduction {O : Subring F} (π : O →+* R) (_ : IsLocalHom π) (hπ : Surjective π) {χ'}
  (hχ : ∀ u, IsUnit u → χ' u = χ (π u)) (h : IsPartner ⊤ e χ Φ Ψ) :
  IsPartner O e χ' (liftIntegralFn π Φ) (liftIntegralFn π Ψ) :=
  have L {a b y} {e : b ⊕ a ≃ n} : (∃ k ∈ intGL n ⊤, map y π = firstCols e k) → ∃ m ∈ intGL n O,
    y.map (↑) = firstCols e m | ⟨k, _⟩ => ⟨_, ⟨(isUnit_of_mapMatrix π (M := of fun i ↦ extend
    (e ∘ .inl) (y i) (surjInv hπ ∘ k i))
    (by convert k.isUnit; aesop (add simp surjInv_eq))).unit, rfl⟩, by simp⟩
  ⟨by simpa [↓exists_invLastRows_iff_transpose] using! fun _ _ ↦
    L ∘ (exists_invLastRows_iff_transpose e).1 ∘ h.1 _, by simpa using! fun _ _ ↦ L ∘ h.2 _,
    fun | _, ⟨k, rfl⟩ => by
          simpa [hχ,
            ↓← GeneralLinearGroup.val_det_apply, k.map_det, -coe_units_inv] using! h.3 (k.map π)⟩

include h

/-- If Φ, Ψ are partners for χ, then χ(det g)·Φ(gx) = Φ(x) for all g in GL_a(O) and all a × n
matrices x. -/
lemma left_mul {g x} (m : g ∈ intGL a O) : χ g.1.det * Φ (g.1 * x) = Φ x := by grind +splitImp
  [inv_mem m, (exists_firstCols_eq_mul e · O 1), Matrix.mul_one, nonsing_inv_mul_cancel_left]

lemma right_mul g (m : g ∈ intGL b O) y : Ψ (y * g.1) * χ g.1.det = Ψ y := by grind +splitImp
  [χ.apply_ne_zero_iff, inv_mem m, exists_firstCols_eq_mul e (f := 1), Matrix.one_mul,
    mul_nonsing_inv_cancel_right]

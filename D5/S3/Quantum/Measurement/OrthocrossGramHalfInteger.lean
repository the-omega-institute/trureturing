/- GID: D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OrthocrossGramHalfInteger
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: 2 G^{-1} is integral for every orthocross MIC (conjecture of arXiv:1812.08762). -/

/-
proof_shape: gram_mul_invGram: content; four_zmat: content; result: content
escape_witness: form (1): the private propositions `gram_mul_invGram` (for every orthonormal
  basis, `G M = 1` with `M_{βγ} = tr(D_β Ω D_γ Ω)` for the explicit dual family `D`) and
  `four_zmat` (every entry of `4 Ω D_α Ω` lies in `(1 + i) ℤ[i]`), both on the live path of
  `result`
admission_basis: open-problem-resolution (issue #11385)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.OrthocrossGramHalfInteger

/-!
J. B. DeBrota, C. A. Fuchs and B. C. Stacey, *The varieties of minimal tomographically complete
measurements*, arXiv:1812.08762 (Int. J. Quantum Inf. 19 (2021) 2040005). For an orthonormal
basis `{|j⟩}` of `ℂ^d`, the orthocross MIC is built from the `d²` rank-one projectors `Π_α` onto
`|j⟩`, `(|j⟩ + |k⟩)/√2` and `(|j⟩ + i|k⟩)/√2` (`j < k`): with `Ω = Σ_α Π_α`, its elements are
`E_α = Ω^{-1/2} Π_α Ω^{-1/2}`, and its Gram matrix is `G_{αβ} = tr(E_α E_β)`. The paper
conjectures that the entries of `G⁻¹` are integers or half-integers. They are: `G⁻¹` is the
matrix `M_{αβ} = tr(D_α Ω D_β Ω)` of the dual family `tr(D_α Π_β) = δ_{αβ}`, and after scaling
by `1 - i` both `Ω` and every `D_α` have Gaussian-integer entries, so every entry of
`4 Ω D_β Ω` is divisible by `1 + i`; reading the entries of `M` off `Ω D_β Ω` gives `2M ∈ ℤ`.
-/

open Matrix Complex
open scoped MatrixOrder ComplexOrder

/-- Pairs `j < k` of basis indices. -/
abbrev Pair (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

/-- The index set: the `d` basis projectors, then the real and the imaginary cross projectors. -/
abbrev Idx (d : ℕ) := Fin d ⊕ Pair d ⊕ Pair d

/-- The vectors `e_j`, `e_j + e_k` and `e_j + i e_k`. -/
noncomputable def vec {d : ℕ} : Idx d → Fin d → ℂ
  | .inl j => Pi.single j 1
  | .inr (.inl p) => Pi.single p.1.1 1 + Pi.single p.1.2 1
  | .inr (.inr p) => Pi.single p.1.1 1 + Pi.single p.1.2 I

/-- `1` for a basis vector and `1/2` for a cross vector, whose squared norm is `2`. -/
noncomputable def weight {d : ℕ} : Idx d → ℂ
  | .inl _ => 1
  | .inr _ => 1 / 2

/-- The projector `Π_α` for the orthonormal basis given by the columns of `U`. -/
noncomputable def proj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (α : Idx d) :
    Matrix (Fin d) (Fin d) ℂ :=
  weight α • vecMulVec (U *ᵥ vec α) (star (U *ᵥ vec α))

/-- `Ω = Σ_α Π_α`. -/
noncomputable def frame {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ α, proj U α

/-- The orthocross MIC element `E_α = Ω^{-1/2} Π_α Ω^{-1/2}`. -/
noncomputable def mic {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (α : Idx d) :
    Matrix (Fin d) (Fin d) ℂ :=
  CFC.sqrt (frame U)⁻¹ * proj U α * CFC.sqrt (frame U)⁻¹

/-- The Gram matrix `G_{αβ} = tr(E_α E_β)`. -/
noncomputable def gram {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (Idx d) (Idx d) ℂ :=
  of fun α β => (mic U α * mic U β).trace

/-- The conjecture of arXiv:1812.08762: for every dimension and every orthonormal basis, the
Gram matrix of the orthocross MIC is invertible and `2 (G⁻¹)_{αβ}` is an integer. -/
def claim : Prop :=
  ∀ (d : ℕ) (U : unitaryGroup (Fin d) ℂ), IsUnit (gram (U : Matrix (Fin d) (Fin d) ℂ)).det ∧
    ∀ α β, ∃ z : ℤ, 2 * (gram (U : Matrix (Fin d) (Fin d) ℂ))⁻¹ α β = z

variable {d : ℕ}

/-- The off-diagonal part of `Ω`: `(1 - i)/2` above the diagonal and `(1 + i)/2` below it. -/
private noncomputable def cross (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  of fun p q => if p = q then 0 else if p < q then (1 - I) / 2 else (1 + I) / 2

/-- The two cross projectors of a pair `j < k`, added. -/
private noncomputable def pairMat (j k : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  of fun p q => (if p = j ∧ q = j then 1 else 0) + (if p = k ∧ q = k then 1 else 0) +
    (if p = j ∧ q = k then (1 - I) / 2 else 0) + (if p = k ∧ q = j then (1 + I) / 2 else 0)

/-- The dual family, `tr(dual α * Π_β) = δ_{αβ}`. -/
private noncomputable def dual : Idx d → Matrix (Fin d) (Fin d) ℂ
  | .inl j => of fun p q => (if p = j ∧ q = j then 1 else 0) - (if p = j then cross d j q else 0) -
      (if q = j then cross d p j else 0)
  | .inr (.inl x) => of fun p q => (if p = x.1.1 ∧ q = x.1.2 then 1 else 0) +
      (if p = x.1.2 ∧ q = x.1.1 then 1 else 0)
  | .inr (.inr x) => of fun p q => (if p = x.1.2 ∧ q = x.1.1 then I else 0) -
      (if p = x.1.1 ∧ q = x.1.2 then I else 0)

/-- `M_{βγ} = tr(D_β Ω D_γ Ω)`. -/
private noncomputable def invGram (d : ℕ) : Matrix (Idx d) (Idx d) ℂ :=
  of fun β γ => (dual β * frame 1 * dual γ * frame 1).trace

/-- `Z_α = Ω D_α Ω`. -/
private noncomputable def zmat (α : Idx d) : Matrix (Fin d) (Fin d) ℂ :=
  frame 1 * dual α * frame 1

/-- `Fin d × Fin d ≃ Idx d`: the diagonal, the pairs above it and the pairs below it. -/
private def idxEquiv : Fin d × Fin d ≃ Idx d where
  toFun p := if h : p.1 < p.2 then .inr (.inl ⟨p, h⟩) else
    if h' : p.2 < p.1 then .inr (.inr ⟨p.swap, h'⟩) else .inl p.1
  invFun
    | .inl j => (j, j)
    | .inr (.inl x) => x.1
    | .inr (.inr x) => x.1.swap
  left_inv p := by
    obtain ⟨a, b⟩ := p
    by_cases h : a < b
    · simp [h]
    · by_cases h' : b < a
      · simp [h, h']
      · have : a = b := le_antisymm (not_lt.mp h') (not_lt.mp h)
        subst this; simp
  right_inv α := by
    rcases α with j | ⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩
    · simp
    · simp [h]
    · dsimp only at h
      simp [not_lt.mpr h.le, h]

/-- The Gram matrix of every orthocross MIC has right inverse `M_{βγ} = tr(D_β Ω D_γ Ω)`. -/
private theorem gram_mul_invGram (U : unitaryGroup (Fin d) ℂ) :
    gram (U : Matrix (Fin d) (Fin d) ℂ) * invGram d = 1 := by
  -- Duality of `dual` and the standard-basis projectors: `tr(D_α Π_β) = δ_{αβ}`.
  have duality : ∀ α β : Idx d, (dual α * proj 1 β).trace = if α = β then 1 else 0 := by
    intro α β
    have trace_mul_proj : ∀ (D : Matrix (Fin d) (Fin d) ℂ) (β : Idx d),
        (D * proj 1 β).trace = weight β * (star (vec β) ⬝ᵥ (D *ᵥ vec β)) := by
      intro D β
      simp only [proj, one_mulVec, Matrix.mul_smul, trace_smul, mul_vecMulVec, smul_eq_mul]
      congr 1
      simp only [trace, diag, vecMulVec_apply, dotProduct, Pi.star_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have quad_single : ∀ (D : Matrix (Fin d) (Fin d) ℂ) (a : Fin d),
        star (Pi.single a (1 : ℂ)) ⬝ᵥ (D *ᵥ Pi.single a 1) = D a a := by
      intro D a
      simp [mulVec_single, dotProduct, Pi.single_apply]
    have quad_pair : ∀ (D : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) (c : ℂ), a ≠ b →
        star (Pi.single a (1 : ℂ) + Pi.single b c) ⬝ᵥ (D *ᵥ (Pi.single a 1 + Pi.single b c)) =
          D a a + c * D a b + star c * D b a + star c * c * D b b := by
      intro D a b c h
      simp only [star_add, Pi.star_single, star_one, RCLike.star_def, add_dotProduct,
        single_dotProduct, one_mul, mulVec_add, mulVec_single, Pi.add_apply, Pi.smul_apply,
        op_smul_eq_mul, col_apply]
      ring
    have cross_self : ∀ a : Fin d, cross d a a = 0 := by intro a; simp [cross]
    have cross_lt : ∀ {a b : Fin d}, a < b → cross d a b = (1 - I) / 2 := by
      intro a b h; simp [cross, h.ne, h]
    have cross_gt : ∀ {a b : Fin d}, a < b → cross d b a = (1 + I) / 2 := by
      intro a b h; simp [cross, h.ne', not_lt.mpr h.le]
    have dual_basis_apply : ∀ j p q : Fin d, dual (.inl j) p q =
        (if p = j ∧ q = j then 1 else 0) - (if p = j then cross d j q else 0) -
          (if q = j then cross d p j else 0) := fun _ _ _ => rfl
    have dual_real_apply : ∀ (x : Pair d) (p q : Fin d), dual (.inr (.inl x)) p q =
        (if p = x.1.1 ∧ q = x.1.2 then 1 else 0) + (if p = x.1.2 ∧ q = x.1.1 then 1 else 0) :=
      fun _ _ _ => rfl
    have dual_imag_apply : ∀ (x : Pair d) (p q : Fin d), dual (.inr (.inr x)) p q =
        (if p = x.1.2 ∧ q = x.1.1 then I else 0) - (if p = x.1.1 ∧ q = x.1.2 then I else 0) :=
      fun _ _ _ => rfl
    rcases α with j | x | x
    · rw [trace_mul_proj]
      rcases β with m | ⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩
      · simp only [vec, weight, quad_single, one_mul, dual_basis_apply, Sum.inl.injEq]
        by_cases h : m = j
        · subst h; simp [cross_self]
        · simp [h, Ne.symm h]
      all_goals
        dsimp only at hab
        simp only [vec, weight, reduceCtorEq, if_false]
        rw [quad_pair _ _ _ _ hab.ne]
        simp only [dual_basis_apply]
        by_cases hja : a = j
        · subst hja
          simp [hab.ne', cross_self, cross_lt hab, cross_gt hab]
          ring_nf
          try simp
          try norm_num
        by_cases hjb : b = j
        · subst hjb
          simp [hab.ne, cross_self, cross_lt hab, cross_gt hab]
          ring_nf
          try simp
          try norm_num
        simp [hja, hjb]
    all_goals
      have entries : ∀ {a b : Fin d}, a < b →
          (dual (.inr (.inl x)) a a = 0 ∧ dual (.inr (.inl x)) b b = 0 ∧
            dual (.inr (.inl x)) a b = (if x.1 = (a, b) then 1 else 0) ∧
            dual (.inr (.inl x)) b a = (if x.1 = (a, b) then 1 else 0)) ∧
          (dual (.inr (.inr x)) a a = 0 ∧ dual (.inr (.inr x)) b b = 0 ∧
            dual (.inr (.inr x)) a b = (if x.1 = (a, b) then -I else 0) ∧
            dual (.inr (.inr x)) b a = (if x.1 = (a, b) then I else 0)) := by
        intro a b hab
        obtain ⟨⟨a', b'⟩, h'⟩ := x
        dsimp only at h' ⊢
        simp only [dual_real_apply, dual_imag_apply, Prod.mk.injEq]
        have n1 : ¬(a = b' ∧ b = a') := by rintro ⟨rfl, rfl⟩; exact absurd hab (lt_asymm h')
        have na : ¬(a = a' ∧ a = b') := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ h'
        have na' : ¬(a = b' ∧ a = a') := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ h'
        have nb : ¬(b = a' ∧ b = b') := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ h'
        have nb' : ¬(b = b' ∧ b = a') := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ h'
        have n3 : ¬(b = a' ∧ a = b') := fun h => n1 ⟨h.2, h.1⟩
        by_cases h : a' = a ∧ b' = b
        · obtain ⟨rfl, rfl⟩ := h
          simp [h'.ne, h'.ne']
        · have e1 : ¬(a = a' ∧ b = b') := fun h2 => h ⟨h2.1.symm, h2.2.symm⟩
          have e2 : ¬(b = b' ∧ a = a') := fun h2 => h ⟨h2.2.symm, h2.1.symm⟩
          simp [na, na', nb, nb', n1, n3, e1, e2, h]
      have diag : ∀ m : Fin d, dual (.inr (.inl x)) m m = 0 ∧ dual (.inr (.inr x)) m m = 0 := by
        intro m
        obtain ⟨⟨a', b'⟩, h'⟩ := x
        dsimp only at h'
        have n1 : ¬(m = a' ∧ m = b') := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ h'
        have n2 : ¬(m = b' ∧ m = a') := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ h'
        simp [dual_real_apply, dual_imag_apply, n1, n2]
      have both : (dual (.inr (.inl x)) * proj 1 β).trace =
          (if .inr (.inl x) = β then 1 else 0) ∧
          (dual (.inr (.inr x)) * proj 1 β).trace = (if .inr (.inr x) = β then 1 else 0) := by
        rw [trace_mul_proj, trace_mul_proj]
        rcases β with m | ⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩
        · simp [vec, weight, (diag m).1, (diag m).2]
        all_goals
          dsimp only at hab
          obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ := entries hab
          simp only [vec, weight]
          rw [quad_pair _ _ _ _ hab.ne, quad_pair _ _ _ _ hab.ne, h1, h2, h3, h4, h5, h6, h7, h8]
          simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, Subtype.ext_iff, if_false]
          by_cases hx : x.1 = (a, b)
          · simp only [hx, if_true, star_one, Complex.star_def, Complex.conj_I]
            constructor <;> ring_nf <;> simp
          · simp [hx]
    · exact both.1
    · exact both.2
  have proj_eq : ∀ (V : Matrix (Fin d) (Fin d) ℂ) (α : Idx d),
      proj V α = V * proj 1 α * Vᴴ := by
    intro V α
    simp only [proj, one_mulVec, star_mulVec, ← vecMulVec_mul, mul_vecMulVec, Matrix.mul_smul,
      Matrix.smul_mul]
  have frame_eq : ∀ V : Matrix (Fin d) (Fin d) ℂ, frame V = V * frame 1 * Vᴴ := by
    intro V
    simp only [frame, proj_eq V, Finset.mul_sum, Finset.sum_mul]
  have posDef_one : (frame (1 : Matrix (Fin d) (Fin d) ℂ)).PosDef := by
    have hsum : ∑ j, proj (1 : Matrix (Fin d) (Fin d) ℂ) (.inl j) = 1 := by
      ext p q
      simp [Matrix.sum_apply, proj, vecMulVec_apply, vec, weight, one_apply]
    have hpsd : ∀ α : Idx d, (proj 1 α).PosSemidef := by
      intro α
      simp only [proj, one_mulVec]
      refine (posSemidef_vecMulVec_self_star _).smul ?_
      rcases α with j | x | x <;> simp [weight]
    rw [frame, Fintype.sum_sum_type, hsum]
    exact PosDef.one.add_posSemidef (posSemidef_sum _ fun _ _ => hpsd _)
  set W : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hVU : Wᴴ * W = 1 := UnitaryGroup.star_mul_self U
  have hUV : W * Wᴴ = 1 := mem_unitaryGroup_iff.mp U.2
  have posDef_W : (frame W).PosDef := by
    rw [frame_eq]
    refine posDef_one.mul_mul_conjTranspose_same ?_
    intro v w h
    have := congrArg (fun x => x ᵥ* Wᴴ) h
    simpa [vecMul_vecMul, hUV] using this
  have conj_mul_conj : ∀ {X Y : Matrix (Fin d) (Fin d) ℂ},
      W * X * Wᴴ * (W * Y * Wᴴ) = W * (X * Y) * Wᴴ := by
    intro X Y
    calc W * X * Wᴴ * (W * Y * Wᴴ) = W * X * (Wᴴ * W) * Y * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = W * (X * Y) * Wᴴ := by rw [hVU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have trace_conj : ∀ X : Matrix (Fin d) (Fin d) ℂ, (W * X * Wᴴ).trace = X.trace := by
    intro X
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hVU, Matrix.mul_one]
  set Ω := frame (1 : Matrix (Fin d) (Fin d) ℂ) with hΩ
  have hu : IsUnit Ω.det := (isUnit_iff_isUnit_det _).mp posDef_one.isUnit
  have h1 : Ω⁻¹ * Ω = 1 := nonsing_inv_mul _ hu
  have h2 : Ω * Ω⁻¹ = 1 := mul_nonsing_inv _ hu
  -- `G_{αβ} = tr(Π_α Ω⁻¹ Π_β Ω⁻¹)` for the standard basis.
  have gram_eq : ∀ α β, gram W α β = (proj 1 α * Ω⁻¹ * proj 1 β * Ω⁻¹).trace := by
    have hS : CFC.sqrt (frame W)⁻¹ * CFC.sqrt (frame W)⁻¹ = (frame W)⁻¹ :=
      CFC.sqrt_mul_sqrt_self _ posDef_W.inv.posSemidef.nonneg
    have hinv : (frame W)⁻¹ = W * Ω⁻¹ * Wᴴ := by
      refine inv_eq_left_inv ?_
      rw [frame_eq W, conj_mul_conj, h1, Matrix.mul_one, hUV]
    intro α β
    simp only [gram, mic, of_apply]
    set S := CFC.sqrt (frame W)⁻¹
    have hcyc : (S * proj W α * S * (S * proj W β * S)).trace =
        (proj W α * (S * S) * proj W β * (S * S)).trace := by
      rw [show S * proj W α * S * (S * proj W β * S) = S * (proj W α * S * (S * proj W β * S)) by
        simp only [Matrix.mul_assoc], trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [hcyc, hS, hinv, proj_eq W α, proj_eq W β, conj_mul_conj, conj_mul_conj, conj_mul_conj,
      trace_conj]
  have trace_sum_smul_mul : ∀ (c : Idx d → ℂ) (A : Idx d → Matrix (Fin d) (Fin d) ℂ)
      (B : Matrix (Fin d) (Fin d) ℂ),
      ((∑ β, c β • A β) * B).trace = ∑ β, c β * (A β * B).trace := by
    intro c A B
    rw [Finset.sum_mul, trace_sum]
    simp only [Matrix.smul_mul, trace_smul, smul_eq_mul]
  -- The dual family is a basis, so `Y = Σ_β tr(Y Π_β) D_β`.
  have completeness : ∀ Y : Matrix (Fin d) (Fin d) ℂ,
      ∑ β, (Y * proj 1 β).trace • dual β = Y := by
    have hli : LinearIndependent ℂ (dual (d := d)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg β
      have h := congrArg (fun M => (M * proj 1 β).trace) hg
      simp only [trace_sum_smul_mul, duality, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Matrix.zero_mul, trace_zero] at h
      exact h
    have hcard : Fintype.card (Idx d) = Module.finrank ℂ (Matrix (Fin d) (Fin d) ℂ) := by
      rw [← Fintype.card_congr idxEquiv, Module.finrank_matrix]
      simp
    set B := basisOfLinearIndependentOfCardEqFinrank' _ hli hcard
    have hB : ∀ β, B β = dual β := by intro β; simp [B]
    intro Y
    have hY := B.sum_repr Y
    have hc : ∀ γ, (Y * proj 1 γ).trace = B.repr Y γ := by
      intro γ
      conv_lhs => rw [← hY]
      simp only [hB, trace_sum_smul_mul, duality, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [hc]
    simpa only [hB] using hY
  have entry : ∀ α γ, ∑ β, (proj 1 α * Ω⁻¹ * proj 1 β * Ω⁻¹).trace *
      (dual β * Ω * dual γ * Ω).trace = if γ = α then 1 else 0 := by
    intro α γ
    have key : ∀ β, (proj 1 α * Ω⁻¹ * proj 1 β * Ω⁻¹).trace =
        (Ω⁻¹ * proj 1 α * Ω⁻¹ * proj 1 β).trace := by
      intro β
      rw [trace_mul_comm]
      simp only [Matrix.mul_assoc]
    simp only [key]
    have hsum : ∑ β, (Ω⁻¹ * proj 1 α * Ω⁻¹ * proj 1 β).trace * (dual β * Ω * dual γ * Ω).trace =
        ((∑ β, (Ω⁻¹ * proj 1 α * Ω⁻¹ * proj 1 β).trace • dual β) * (Ω * dual γ * Ω)).trace := by
      rw [trace_sum_smul_mul]
      simp only [Matrix.mul_assoc]
    rw [hsum, completeness]
    have hstep : Ω⁻¹ * proj 1 α * Ω⁻¹ * (Ω * dual γ * Ω) = Ω⁻¹ * (proj 1 α * dual γ * Ω) := by
      calc Ω⁻¹ * proj 1 α * Ω⁻¹ * (Ω * dual γ * Ω) = Ω⁻¹ * proj 1 α * (Ω⁻¹ * Ω) * dual γ * Ω := by
            simp only [Matrix.mul_assoc]
        _ = Ω⁻¹ * (proj 1 α * dual γ * Ω) := by
          rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hstep, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one,
      trace_mul_comm, duality]
  ext α γ
  rw [mul_apply, one_apply]
  simp only [gram_eq, invGram, of_apply]
  rw [entry]
  by_cases h : α = γ
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Every entry of `4 Ω D_α Ω` is `(1 + i)` times a Gaussian integer. -/
private theorem four_zmat (α : Idx d) (p q : Fin d) :
    ∃ a b : ℤ, 4 * zmat α p q = (1 + I) * (a + b * I) := by
  -- The closed form of `Ω` for the standard basis: `d` on the diagonal, `cross` off it.
  have frame_one : frame (1 : Matrix (Fin d) (Fin d) ℂ) = (d : ℂ) • 1 + cross d := by
    have proj_one_apply : ∀ (α : Idx d) (p q : Fin d),
        proj 1 α p q = weight α * vec α p * star (vec α q) := by
      intro α p q
      simp [proj, vecMulVec_apply, mul_assoc]
    have sum_pair : ∀ g : Fin d → Fin d → ℂ,
        ∑ x : Pair d, g x.1.1 x.1.2 = ∑ j, ∑ k, if j < k then g j k else 0 := by
      intro g
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : Fin d × Fin d => x.1 < x.2)
        (by simp) (fun x => g x.1 x.2), Finset.sum_filter, Fintype.sum_prod_type]
    have proj_pair : ∀ x : Pair d,
        proj 1 (.inr (.inl x)) + proj 1 (.inr (.inr x)) = pairMat x.1.1 x.1.2 := by
      intro x
      ext p q
      simp only [Matrix.add_apply, proj_one_apply, vec, weight, pairMat, of_apply, Pi.add_apply,
        Pi.single_apply, Complex.star_def]
      by_cases hpj : p = x.1.1 <;> by_cases hpk : p = x.1.2 <;> by_cases hqj : q = x.1.1 <;>
        by_cases hqk : q = x.1.2 <;> simp_all <;> ring_nf <;> simp [Complex.ext_iff] <;> norm_num
    have frame_one_eq : frame (1 : Matrix (Fin d) (Fin d) ℂ) =
        ∑ j, proj 1 (.inl j) + ∑ x : Pair d, pairMat x.1.1 x.1.2 := by
      simp only [frame, Fintype.sum_sum_type, ← proj_pair, Finset.sum_add_distrib]
    have count_eq : ∀ p : Fin d, (∑ k : Fin d, if p < k then (1 : ℂ) else 0) +
        (∑ k : Fin d, if k < p then (1 : ℂ) else 0) + 1 = d := by
      intro p
      have h1 : (1 : ℂ) = ∑ k : Fin d, if k = p then 1 else 0 := by simp
      rw [h1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      have h : ∀ k : Fin d, ((if p < k then (1 : ℂ) else 0) + (if k < p then 1 else 0) +
          if k = p then 1 else 0) = 1 := by
        intro k
        rcases lt_trichotomy k p with h | rfl | h
        · simp [h, h.ne, not_lt_of_gt h]
        · simp
        · simp [h, h.ne', not_lt_of_gt h]
      simp [h]
    ext p q
    rw [frame_one_eq, Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply,
      sum_pair (fun j k => pairMat j k p q)]
    simp only [proj_one_apply, vec, weight, Pi.single_apply, pairMat, of_apply, cross,
      Matrix.add_apply, Matrix.smul_apply, Complex.star_def]
    rcases lt_trichotomy p q with hpq | rfl | hpq
    · have hs : ∀ j k : Fin d, (if j < k then (((if p = j ∧ q = j then (1 : ℂ) else 0) +
          if p = k ∧ q = k then 1 else 0) + if p = j ∧ q = k then (1 - I) / 2 else 0) +
            if p = k ∧ q = j then (1 + I) / 2 else 0 else 0) =
            if p = j then (if q = k then (1 - I) / 2 else 0) else 0 := by
        intro j k
        simp only [Fin.ext_iff, Fin.lt_def] at hpq ⊢
        split_ifs <;> first | (exfalso; omega) | ring
      simp only [hs]
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq, hpq.ne, hpq, one_apply]
    · have hs : ∀ j k : Fin d, (if j < k then (((if p = j ∧ p = j then (1 : ℂ) else 0) +
          if p = k ∧ p = k then 1 else 0) + if p = j ∧ p = k then (1 - I) / 2 else 0) +
            if p = k ∧ p = j then (1 + I) / 2 else 0 else 0) =
            (if p = j then (if j < k then 1 else 0) else 0) +
              (if p = k then (if j < k then 1 else 0) else 0) := by
        intro j k
        simp only [Fin.ext_iff, Fin.lt_def]
        split_ifs <;> first | (exfalso; omega) | ring
      simp only [hs, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun j k => if p = j then (if j < k then (1 : ℂ) else 0) else 0)]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hc := count_eq p
      simp [one_apply] at hc ⊢
      linear_combination hc
    · have hs : ∀ j k : Fin d, (if j < k then (((if p = j ∧ q = j then (1 : ℂ) else 0) +
          if p = k ∧ q = k then 1 else 0) + if p = j ∧ q = k then (1 - I) / 2 else 0) +
            if p = k ∧ q = j then (1 + I) / 2 else 0 else 0) =
            if p = k then (if q = j then (1 + I) / 2 else 0) else 0 := by
        intro j k
        simp only [Fin.ext_iff, Fin.lt_def] at hpq ⊢
        split_ifs <;> first | (exfalso; omega) | ring
      simp only [hs]
      simp [Finset.sum_ite_eq, hpq.ne', one_apply, not_lt.mpr hpq.le]
  have mem_GI : ∀ {z : ℂ}, z ∈ GaussianInt.toComplex.range ↔ ∃ a b : ℤ, z = a + b * I := by
    intro z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.re, w.im, GaussianInt.toComplex_def w⟩
    · rintro ⟨a, b, rfl⟩
      exact ⟨⟨a, b⟩, GaussianInt.toComplex_def' a b⟩
  have I_mem : I ∈ GaussianInt.toComplex.range := mem_GI.mpr ⟨0, 1, by simp⟩
  have one_sub_I_mem : 1 - I ∈ GaussianInt.toComplex.range :=
    Subring.sub_mem _ (Subring.one_mem _) I_mem
  have mul_mem : ∀ {A B : Matrix (Fin d) (Fin d) ℂ},
      (∀ p q, A p q ∈ GaussianInt.toComplex.range) →
      (∀ p q, B p q ∈ GaussianInt.toComplex.range) →
      ∀ p q, (A * B) p q ∈ GaussianInt.toComplex.range := by
    intro A B hA hB p q
    rw [mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA p k) (hB k q)
  have gi_cross : ∀ p q : Fin d, (1 - I) * cross d p q ∈ GaussianInt.toComplex.range := by
    intro p q
    rw [mem_GI]
    simp only [cross, of_apply]
    split_ifs
    · exact ⟨0, 0, by simp⟩
    · exact ⟨0, -1, by push_cast; linear_combination (1 / 2 : ℂ) * Complex.I_sq⟩
    · exact ⟨1, 0, by push_cast; linear_combination (-1 / 2 : ℂ) * Complex.I_sq⟩
  have gi_ite_one : ∀ (c : Prop) [Decidable c],
      (if c then (1 : ℂ) else 0) ∈ GaussianInt.toComplex.range := by
    intro c _
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have gi_ite_I : ∀ (c : Prop) [Decidable c],
      (if c then I else 0) ∈ GaussianInt.toComplex.range := by
    intro c _
    split_ifs
    · exact I_mem
    · exact Subring.zero_mem _
  have gi_frame : ∀ p q : Fin d,
      ((1 - I) • frame (1 : Matrix (Fin d) (Fin d) ℂ)) p q ∈ GaussianInt.toComplex.range := by
    intro p q
    rw [frame_one, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, mul_add]
    refine Subring.add_mem _ (Subring.mul_mem _ one_sub_I_mem ?_) (gi_cross p q)
    rw [Matrix.smul_apply, one_apply, smul_eq_mul]
    exact Subring.mul_mem _ (natCast_mem _ d) (gi_ite_one _)
  have gi_dual : ∀ p q : Fin d, ((1 - I) • dual α) p q ∈ GaussianInt.toComplex.range := by
    intro p q
    rw [Matrix.smul_apply, smul_eq_mul]
    rcases α with j | x | x
    · change (1 - I) * ((if p = j ∧ q = j then 1 else 0) - (if p = j then cross d j q else 0) -
        (if q = j then cross d p j else 0)) ∈ _
      rw [mul_sub, mul_sub]
      refine Subring.sub_mem _ (Subring.sub_mem _ ?_ ?_) ?_
      · exact Subring.mul_mem _ one_sub_I_mem (gi_ite_one _)
      · split_ifs
        · exact gi_cross _ _
        · simp
      · split_ifs
        · exact gi_cross _ _
        · simp
    · exact Subring.mul_mem _ one_sub_I_mem (Subring.add_mem _ (gi_ite_one _) (gi_ite_one _))
    · exact Subring.mul_mem _ one_sub_I_mem (Subring.sub_mem _ (gi_ite_I _) (gi_ite_I _))
  set W := (1 - I) • frame (1 : Matrix (Fin d) (Fin d) ℂ)
  set Y := (1 - I) • dual α
  have hWYW : W * Y * W = (1 - I) ^ 3 • zmat α := by
    simp only [W, Y, zmat, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1; ring
  obtain ⟨a', b', hab⟩ := mem_GI.mp (mul_mem (mul_mem gi_frame gi_dual) gi_frame p q)
  refine ⟨-b', a', ?_⟩
  have h2 : (W * Y * W) p q = (1 - I) ^ 3 * zmat α p q := by
    rw [hWYW, Matrix.smul_apply, smul_eq_mul]
  rw [hab] at h2
  rw [show (4 : ℂ) = (1 + I) * I * (1 - I) ^ 3 by
    linear_combination (I ^ 3 - 2 * I ^ 2 - I + 4 : ℂ) * Complex.I_sq]
  push_cast
  linear_combination (-(1 + I) * I) * h2 + ((1 + I) * (b' : ℂ)) * Complex.I_sq

/-- The conjecture holds: `G` is invertible and `2 G⁻¹` has integer entries. -/
theorem result : claim := by
  intro d U
  have hGM := gram_mul_invGram (d := d) U
  refine ⟨isUnit_det_of_right_inverse hGM, fun α β => ?_⟩
  rw [inv_eq_right_inv hGM]
  have cross_self : ∀ a : Fin d, cross d a a = 0 := by intro a; simp [cross]
  have cross_lt : ∀ {a b : Fin d}, a < b → cross d a b = (1 - I) / 2 := by
    intro a b h; simp [cross, h.ne, h]
  have cross_gt : ∀ {a b : Fin d}, a < b → cross d b a = (1 + I) / 2 := by
    intro a b h; simp [cross, h.ne', not_lt.mpr h.le]
  have cross_conj : ∀ p q : Fin d, star (cross d p q) = cross d q p := by
    intro p q
    simp only [cross, of_apply]
    rcases lt_trichotomy p q with h | rfl | h
    · simp [h.ne, h.ne', h, not_lt.mpr h.le]
    · simp
    · simp [h.ne, h.ne', h, not_lt.mpr h.le, Complex.ext_iff]
  have dual_herm : ∀ γ : Idx d, (dual γ)ᴴ = dual γ := by
    intro γ
    ext p q
    rw [conjTranspose_apply]
    rcases γ with j | x | x
    · change star ((if q = j ∧ p = j then 1 else 0) - (if q = j then cross d j p else 0) -
        (if p = j then cross d q j else 0)) = (if p = j ∧ q = j then 1 else 0) -
        (if p = j then cross d j q else 0) - (if q = j then cross d p j else 0)
      simp only [star_sub, apply_ite star, star_one, star_zero, cross_conj]
      by_cases hp : p = j <;> by_cases hq : q = j <;> simp [hp, hq]
    · change star ((if q = x.1.1 ∧ p = x.1.2 then (1 : ℂ) else 0) +
        (if q = x.1.2 ∧ p = x.1.1 then 1 else 0)) = (if p = x.1.1 ∧ q = x.1.2 then 1 else 0) +
        (if p = x.1.2 ∧ q = x.1.1 then 1 else 0)
      simp only [star_add, apply_ite star, star_one, star_zero]
      rw [add_comm]; simp only [and_comm]
    · have hx : (↑x : Fin d × Fin d).1 ≠ (↑x : Fin d × Fin d).2 := x.2.ne
      change star ((if q = x.1.2 ∧ p = x.1.1 then I else 0) -
        (if q = x.1.1 ∧ p = x.1.2 then I else 0)) = (if p = x.1.2 ∧ q = x.1.1 then I else 0) -
        (if p = x.1.1 ∧ q = x.1.2 then I else 0)
      have e1 : (q = (↑x : Fin d × Fin d).2 ∧ p = (↑x : Fin d × Fin d).1) ↔
          (p = (↑x : Fin d × Fin d).1 ∧ q = (↑x : Fin d × Fin d).2) := and_comm
      have e2 : (q = (↑x : Fin d × Fin d).1 ∧ p = (↑x : Fin d × Fin d).2) ↔
          (p = (↑x : Fin d × Fin d).2 ∧ q = (↑x : Fin d × Fin d).1) := and_comm
      simp only [star_sub, apply_ite star, star_zero, Complex.star_def, Complex.conj_I, e1, e2]
      by_cases h1 : p = (↑x : Fin d × Fin d).1 ∧ q = (↑x : Fin d × Fin d).2 <;>
        by_cases h2 : p = (↑x : Fin d × Fin d).2 ∧ q = (↑x : Fin d × Fin d).1 <;>
        simp [h1, h2, hx, hx.symm]
  have frame_herm : (frame (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ = frame 1 := by
    have hpsd : ∀ γ : Idx d, (proj 1 γ).PosSemidef := by
      intro γ
      simp only [proj, one_mulVec]
      refine (posSemidef_vecMulVec_self_star _).smul ?_
      rcases γ with j | x | x <;> simp [weight]
    exact (posSemidef_sum Finset.univ fun γ _ => hpsd γ).isHermitian
  have zmat_herm : ∀ p q : Fin d, star (zmat β p q) = zmat β q p := by
    intro p q
    have h : (zmat β)ᴴ = zmat β := by
      simp only [zmat, conjTranspose_mul, frame_herm, dual_herm, Matrix.mul_assoc]
    rw [← conjTranspose_apply, h]
  have re_im_four : ∀ {z : ℂ} {a b : ℤ}, 4 * z = (1 + I) * (a + b * I) →
      4 * z.re = a - b ∧ 4 * z.im = a + b := by
    intro z a b h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    constructor <;> linarith
  have mem_ZC : ∀ {x : ℂ}, x ∈ (Int.castRingHom ℂ).range ↔ ∃ n : ℤ, x = n := by
    intro x
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨n, rfl⟩
  have hM : invGram d α β = (dual α * zmat β).trace := by
    simp only [invGram, of_apply, zmat, Matrix.mul_assoc]
  suffices h : 2 * (dual α * zmat β).trace ∈ (Int.castRingHom ℂ).range by
    obtain ⟨n, hn⟩ := mem_ZC.mp h
    exact ⟨n, by rw [hM, hn]⟩
  rcases α with j | x | x
  · -- `M_{X_j β} = Z_jj - Σ_q (cross_jq Z_qj + cross_qj Z_jq)`.
    have hread : (dual (.inl j) * zmat β).trace =
        zmat β j j - ∑ q, (cross d j q * zmat β q j + cross d q j * zmat β j q) := by
      simp only [trace, diag, mul_apply, dual, of_apply, sub_mul, ite_mul, one_mul, zero_mul,
        Finset.sum_sub_distrib, ite_and, Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']
      ring
    rw [hread, mul_sub, Finset.mul_sum]
    refine Subring.sub_mem _ ?_ (Subring.sum_mem _ fun q _ => ?_)
    · obtain ⟨a, b, h⟩ := four_zmat β j j
      obtain ⟨hr, hi⟩ := re_im_four h
      have him : (zmat β j j).im = 0 := by
        have := congrArg Complex.im (zmat_herm j j)
        simp at this
        linarith
      refine mem_ZC.mpr ⟨a, ?_⟩
      apply Complex.ext <;> simp <;> linarith
    · obtain ⟨a, b, h⟩ := four_zmat β j q
      obtain ⟨hr, hi⟩ := re_im_four h
      rw [← zmat_herm j q]
      rcases lt_trichotomy j q with hjq | rfl | hjq
      · rw [cross_lt hjq, cross_gt hjq]
        refine mem_ZC.mpr ⟨-b, ?_⟩
        apply Complex.ext <;> simp <;> linarith
      · rw [cross_self]
        exact mem_ZC.mpr ⟨0, by simp⟩
      · rw [cross_lt hjq, cross_gt hjq]
        refine mem_ZC.mpr ⟨a, ?_⟩
        apply Complex.ext <;> simp <;> linarith
  · -- `M_{T_x β} = Z_ba + Z_ab`.
    have hread : (dual (.inr (.inl x)) * zmat β).trace =
        zmat β x.1.2 x.1.1 + zmat β x.1.1 x.1.2 := by
      simp only [trace, diag, mul_apply, dual, of_apply, add_mul, ite_mul, one_mul, zero_mul,
        Finset.sum_add_distrib, ite_and]
      simp [Finset.sum_ite_eq']
    rw [hread, ← zmat_herm]
    obtain ⟨a, b, h⟩ := four_zmat β x.1.1 x.1.2
    obtain ⟨hr, _⟩ := re_im_four h
    refine mem_ZC.mpr ⟨a - b, ?_⟩
    apply Complex.ext
    · simp; linarith
    · simp
  · -- `M_{V_x β} = i Z_ab - i Z_ba`.
    have hread : (dual (.inr (.inr x)) * zmat β).trace =
        I * zmat β x.1.1 x.1.2 - I * zmat β x.1.2 x.1.1 := by
      simp only [trace, diag, mul_apply, dual, of_apply, sub_mul, ite_mul, zero_mul,
        Finset.sum_sub_distrib, ite_and]
      simp [Finset.sum_ite_eq']
    rw [hread, ← zmat_herm x.1.1 x.1.2]
    obtain ⟨a, b, h⟩ := four_zmat β x.1.1 x.1.2
    obtain ⟨_, hi⟩ := re_im_four h
    refine mem_ZC.mpr ⟨-(a + b), ?_⟩
    apply Complex.ext
    · simp; linarith
    · simp

end D5.S3.Quantum.Measurement.OrthocrossGramHalfInteger

/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner
   mirror-E: none(waiver:symbolic-arbitrary-dimension-construction)
   anchors: []
   utility: none
   digest: Arbitrary product-corner APPT compression through unitary transport. -/

/-
utility:none, declaration-by-declaration semantic scope (CLAUDE.md §3.3):
corner, corner_injective, Outside, outsideFintype, cornerEquiv, cornerEquiv_symm_corner:
  Symbolic product embeddings, complement types, finiteness and equivalences for all r,m,n; no bounded search or certified input is delivered.
conjugate_corner, selected_corner_psd:
  Universal matrix transport and an implication from literal APPT, with the permutation and unitary constructed for arbitrary dimensions; no checker or numerical-premise reduction is delivered.
All groups avoid bounded-enumeration, checker, numeric-reduction and
certified-instance as their primary delivered content. Utility semantics
remain subject to independent review; the header does not prove acceptance.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false

open Matrix
open scoped ComplexOrder BigOperators

namespace D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

/-- Partial transposition on the B factor, allowing unequal factor dimensions. -/
def partialTranspose {A B : Type*} (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose ρ

end D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment

def APPT {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix (A × B) (A × B) ℂ) : Prop :=
  D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.APPT M

end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open QutritPerturbationAttainment
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

noncomputable def extendUnitaryAlong {I J C : Type}
    [Fintype I] [Fintype J] [Fintype C]
    [DecidableEq I] [DecidableEq J] [DecidableEq C]
    (e : (J ⊕ C) ≃ I) (V : unitaryGroup J ℂ) : unitaryGroup I ℂ :=
  ⟨(fromBlocks (V : Matrix J J ℂ) 0 0 (1 : Matrix C C ℂ)).submatrix e.symm e.symm, by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_submatrix,
      submatrix_mul_equiv _ _ _ e.symm _]
    have hv : (V : Matrix J J ℂ) * (V : Matrix J J ℂ)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp V.property
    simp [fromBlocks_conjTranspose, fromBlocks_multiply, hv, fromBlocks_one]⟩

theorem extendUnitaryAlong_diagonal {I J C : Type}
    [Fintype I] [Fintype J] [Fintype C]
    [DecidableEq I] [DecidableEq J] [DecidableEq C]
    (e : (J ⊕ C) ≃ I) (V : unitaryGroup J ℂ) (x : J → ℂ) (y : C → ℂ) :
    (extendUnitaryAlong e V : Matrix I I ℂ) *
      diagonal (fun i => Sum.elim x y (e.symm i)) *
      (extendUnitaryAlong e V : Matrix I I ℂ)ᴴ =
    (fromBlocks ((V : Matrix J J ℂ) * diagonal x * (V : Matrix J J ℂ)ᴴ)
      0 0 (diagonal y)).submatrix e.symm e.symm := by
  change ((fromBlocks (V : Matrix J J ℂ) 0 0 (1 : Matrix C C ℂ)).submatrix e.symm e.symm) *
    diagonal (fun i => Sum.elim x y (e.symm i)) *
    ((fromBlocks (V : Matrix J J ℂ) 0 0 (1 : Matrix C C ℂ)).submatrix e.symm e.symm)ᴴ = _
  have hd : diagonal (fun i => Sum.elim x y (e.symm i)) =
      (diagonal (Sum.elim x y)).submatrix e.symm e.symm := by
    simpa only [Function.comp_def] using
      (Matrix.submatrix_diagonal_equiv (Sum.elim x y) e.symm).symm
  rw [hd, conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e.symm _,
    submatrix_mul_equiv _ _ _ e.symm _, ← fromBlocks_diagonal x y]
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one,
    conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, one_mul, mul_one]

noncomputable def permutationU {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) : unitaryGroup I ℂ := ⟨e.permMatrix ℂ, by
  rw [mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp⟩

theorem c_square : (Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)=2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [← mul_inv, h]
  norm_num

theorem c_star : star (Real.sqrt 2 : ℂ)⁻¹=(Real.sqrt 2 : ℂ)⁻¹ := by simp

theorem appt_conjugate {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {M : Matrix (A × B) (A × B) ℂ} (h : APPT M) (V : unitaryGroup (A × B) ℂ) :
    APPT ((V : Matrix (A × B) (A × B) ℂ)*M*(V : Matrix (A × B) (A × B) ℂ)ᴴ) := by
  intro U
  have hp := h (U*V)
  simpa only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hp

theorem real_psd_of_complex {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℝ) (h : (M.map Complex.ofReal).PosSemidef) : M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have he := congrFun (congrFun h.isHermitian i) j
    have hr := congrArg Complex.re he
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply] using hr
  · intro x
    have hp := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    have he : star (fun i => (x i : ℂ)) ⬝ᵥ ((M.map Complex.ofReal) *ᵥ (fun i => (x i : ℂ))) =
        ((star x ⬝ᵥ (M *ᵥ x) : ℝ) : ℂ) := by
      simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
        ← Complex.ofReal_sum, ← Complex.ofReal_mul]
    rw [he] at hp
    exact Complex.zero_le_real.mp hp

theorem permutation_conjugate {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) (M : Matrix I I ℂ) :
    (permutationU e : Matrix I I ℂ)*M*(permutationU e : Matrix I I ℂ)ᴴ=M.submatrix e e := by
  change e.permMatrix ℂ*M*(e.permMatrix ℂ)ᴴ=M.submatrix e e
  rw [Matrix.conjTranspose_permMatrix]
  change e.toPEquiv.toMatrix*M*(e⁻¹).toPEquiv.toMatrix=M.submatrix e e
  rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  rfl

end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtCorner
open QutritPerturbationAttainment QutritSpectralReduction
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

noncomputable section

def corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (p : Fin r × Fin r) : Fin m × Fin n :=
  (Fin.castLE hm p.1, Fin.castLE hn p.2)

theorem corner_injective {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) :
    Function.Injective (corner hm hn) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun z : Fin m × Fin n => z.1.val) h
  · exact congrArg (fun z : Fin m × Fin n => z.2.val) h

abbrev Outside {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) :=
  {p : Fin m × Fin n // p ∉ Set.range (corner hm hn)}

instance outsideFintype {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) :
    Fintype (Outside hm hn) := Fintype.ofFinite _

def cornerEquiv {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) :
    ((Fin r × Fin r) ⊕ Outside hm hn) ≃ (Fin m × Fin n) :=
  (Equiv.sumCongr (Equiv.ofInjective (corner hm hn) (corner_injective hm hn))
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (corner hm hn)))

@[simp] theorem cornerEquiv_symm_corner {r m n : ℕ}
    (hm : r ≤ m) (hn : r ≤ n) (p : Fin r × Fin r) :
    (cornerEquiv hm hn).symm (corner hm hn p) = Sum.inl p :=
  (cornerEquiv hm hn).symm_apply_apply (Sum.inl p)

theorem conjugate_corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (d : Fin m × Fin n → ℂ) (V : unitaryGroup (Fin r × Fin r) ℂ) :
    (((extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ) * diagonal d *
      (extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ)ᴴ).submatrix
        (corner hm hn) (corner hm hn)) =
    (V : Matrix _ _ ℂ) * diagonal (fun q => d (corner hm hn q)) *
      (V : Matrix _ _ ℂ)ᴴ := by
  have hd : diagonal d = diagonal (fun p =>
      Sum.elim (fun q => d (corner hm hn q))
        (fun q => d (cornerEquiv hm hn (Sum.inr q)))
        ((cornerEquiv hm hn).symm p)) := by
    congr 1
    funext p
    obtain ⟨q, rfl⟩ := (cornerEquiv hm hn).surjective p
    cases q <;> simp <;> rfl
  rw [hd, extendUnitaryAlong_diagonal]
  ext i j
  simp [Matrix.submatrix_apply]

/-- Literal APPT realizes ANY injectively labelled product corner after ANY
corner unitary. The complement permutation and identity unitary extension
are constructed here; there is no supplied assignment-PSD premise.
-/
theorem selected_corner_psd {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ)
    (label : Fin r × Fin r → Fin (m * n)) (hl : Function.Injective label)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ))))
    (V : unitaryGroup (Fin r × Fin r) ℂ) :
    (partialTranspose ((V : Matrix _ _ ℂ) *
      diagonal (fun q => (l (label q) : ℂ)) * (V : Matrix _ _ ℂ)ᴴ)).PosSemidef := by
  classical
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (corner hm hn) (fun q => e.symm (label q)) (corner_injective hm hn)
    (e.symm.injective.comp hl)
  let d : Fin m × Fin n → ℂ := fun q => (l (e (p q)) : ℂ)
  have hd : (permutationU p : Matrix _ _ ℂ) *
      diagonal (fun q => (l (e q) : ℂ)) *
      (permutationU p : Matrix _ _ ℂ)ᴴ = diagonal d := by
    rw [permutation_conjugate, Matrix.submatrix_diagonal_equiv]
    rfl
  have hdiag : APPT (diagonal d) := by
    rw [← hd]
    exact appt_conjugate h (permutationU p)
  let W := extendUnitaryAlong (cornerEquiv hm hn) V
  let M := (W : Matrix _ _ ℂ) * diagonal d * (W : Matrix _ _ ℂ)ᴴ
  have hpos : ((partialTranspose M).submatrix
      (corner hm hn) (corner hm hn)).PosSemidef :=
    (hdiag W).submatrix (corner hm hn)
  have hpt : (partialTranspose M).submatrix (corner hm hn) (corner hm hn) =
      partialTranspose (M.submatrix (corner hm hn) (corner hm hn)) := by
    rfl
  rw [hpt] at hpos
  have hlocal : M.submatrix (corner hm hn) (corner hm hn) =
      (V : Matrix _ _ ℂ) * diagonal (fun q => d (corner hm hn q)) *
        (V : Matrix _ _ ℂ)ᴴ := conjugate_corner hm hn d V
  rw [hlocal] at hpos
  have hlabels : (fun q => d (corner hm hn q)) =
      fun q => (l (label q) : ℂ) := by
    funext q
    simp [d, hp q]
  rwa [hlabels] at hpos


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtCorner

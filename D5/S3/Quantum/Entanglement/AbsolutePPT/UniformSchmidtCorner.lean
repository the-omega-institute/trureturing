/- Uncompiled source candidate at afc3608700b56b2459986135c9852f1d202ae040.
   Apply expose-product-pt.patch at the original owner before compiling.
   This file proves no final centered-variance theorem. See LiteralSchmidtBridge.md. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import D5.S3.Quantum.Matrix.PartialTransposeTrace
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false

open Matrix
open scoped ComplexOrder BigOperators

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

@[simp] theorem cornerEquiv_inl {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (p : Fin r × Fin r) : cornerEquiv hm hn (Sum.inl p) = corner hm hn p := rfl

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
    cases q <;> simp
  rw [hd, extendUnitaryAlong_diagonal]
  ext i j
  simp [Matrix.submatrix_apply]

/-- Literal APPT realizes ANY injectively labelled product corner after ANY
corner unitary. The complement permutation and identity unitary extension
are constructed here; there is no supplied assignment-PSD premise.
The Bell-specific instantiation is still to be translated from the content source. -/
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
    exact QuadbitQuintitMaximumPurity.product_partialTranspose
      (Fin.castLE hm) (Fin.castLE hn) M
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

/-- All real coefficients are allowed, including negative and zero ones. -/
def schmidt {r : ℕ} (x : Fin r → ℝ) : Fin r × Fin r → ℂ :=
  fun p => if p.1 = p.2 then (x p.1 : ℂ) else 0

def schmidtPT {r : ℕ} (x : Fin r → ℝ) :
    Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ :=
  partialTranspose (vecMulVec (schmidt x) (star (schmidt x)))

theorem schmidt_pt_entry {r : ℕ} (x : Fin r → ℝ)
    (p q : Fin r × Fin r) :
    schmidtPT x p q = if p = (q.2, q.1) then ((x q.1 * x q.2 : ℝ) : ℂ) else 0 := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  by_cases hil : i = l <;> by_cases hkj : k = j <;>
    simp_all [schmidtPT, partialTranspose, schmidt, vecMulVec_apply,
      Pi.star_apply, Prod.mk.injEq, mul_comm, eq_comm]

theorem schmidt_pt_single {r : ℕ} (x : Fin r → ℝ) (i j : Fin r) :
    schmidtPT x *ᵥ Pi.single (i, j) 1 =
      Pi.single (j, i) (((x i * x j : ℝ) : ℂ)) := by
  classical
  ext p
  simp [Matrix.mulVec_single_one, Matrix.col_apply, schmidt_pt_entry,
    Pi.single_apply]

theorem schmidt_pt_diagonal {r : ℕ} (x : Fin r → ℝ) (i : Fin r) :
    schmidtPT x *ᵥ Pi.single (i, i) 1 =
      (((x i ^ 2 : ℝ) : ℂ)) • (Pi.single (i, i) 1) := by
  rw [schmidt_pt_single]
  ext p
  simp [Pi.single_apply, pow_two, smul_eq_mul]

theorem schmidt_pt_symmetric {r : ℕ} (x : Fin r → ℝ) (i j : Fin r) :
    schmidtPT x *ᵥ (Pi.single (i, j) 1 + Pi.single (j, i) 1) =
      (((x i * x j : ℝ) : ℂ)) •
        (Pi.single (i, j) 1 + Pi.single (j, i) 1) := by
  rw [Matrix.mulVec_add, schmidt_pt_single, schmidt_pt_single]
  ext p
  simp [Pi.single_apply, smul_eq_mul, mul_comm]
  <;> split_ifs <;> ring

theorem schmidt_pt_antisymmetric {r : ℕ} (x : Fin r → ℝ) (i j : Fin r) :
    schmidtPT x *ᵥ (Pi.single (i, j) 1 - Pi.single (j, i) 1) =
      (((-(x i * x j) : ℝ) : ℂ)) •
        (Pi.single (i, j) 1 - Pi.single (j, i) 1) := by
  rw [Matrix.mulVec_sub, schmidt_pt_single, schmidt_pt_single]
  ext p
  simp [Pi.single_apply, smul_eq_mul, mul_comm]
  <;> split_ifs <;> ring

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtCorner

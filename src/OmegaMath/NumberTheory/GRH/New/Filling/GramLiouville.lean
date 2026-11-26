import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.LatticeComplement
import OmegaMath.NumberTheory.GRH.New.Filling.LatticeChart
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Discriminant of lattice points in a subspace; Liouville inequality for Gram
determinants. -/

open Module MatMul Matrix

namespace Filling

variable {E P σ τ m n k : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype P]
  [Field k] {y : Matrix P τ k} {A : Matrix σ P k} (M : Matrix m n E)

/-- For a matrix over E, the matrix over the finite adeles of E obtained by embedding each
entry. -/
noncomputable abbrev finAdeleMat := M.map ((↑) : E → 𝔸f E)

lemma finAdeleMat_conjTranspose : finAdeleMat Mᴴ = (finAdeleMat M)ᴴ := by aesop

lemma map_conjTranspose (φ : E →+* ℂ) : Mᴴ.map φ = (M.map φ)ᴴ := by aesop

omit [NumberField.IsCMField E] in
@[simp] lemma finAdeleMat_smul (a : E) : finAdeleMat (a • M) = (a :
  𝔸f E) • finAdeleMat M := by aesop

lemma mul_eq_zero_of_range_le_ker [Fintype τ] : colSpan y ≤ A.mulVecLin.ker →
  A * y = 0 := by simp [LE.le, ext_iff_mulVec]

/-- If A x is invertible and a subspace L contains the columns of x, there is a matrix y with
columns in L and A y = 0 such that the columns of x and y together form a basis of L. -/
lemma exists_basis_extend_ker [Fintype σ] {x} (h : (A * x).det ≠ 0) {L} (hL : colSpan x ≤ L) :
    ∃ s y, finrank k (SubmoduleElem (L ⊓ A.mulVecLin.ker)) = s ∧ HasLeftInv (x.fromCols y) ∧ colSpan
  (x.fromCols y) = L ∧ colSpan y ≤ L ∧ A * y = 0 ∧ ∀ t : Fin s → k, y *ᵥ t ∈ colSpan x → t = 0 :=
  ⟨_, (exists_basis_matrix _).imp fun y ⟨⟨l, _⟩, e⟩ ↦ let C := (A * x)⁻¹ * A
  have ⟨p, o⟩ := (le_inf_iff.1 e.le).imp id mul_eq_zero_of_range_le_ker; ⟨rfl, ⟨C.fromRows (l - l *
    x * C), by aesop⟩, le_antisymm (by simp [LE.le, add_mem, hL _, p _]) fun v w ↦ (e.ge ⟨sub_mem w
    (hL ⟨C *ᵥ v, rfl⟩), by simp [C, mulVec_sub, ← A.mul_assoc, h]⟩).imp' (C *ᵥ v ⊕ᵥ ·) (by aesop),
    p, o, fun _ ⟨_, k⟩ ↦ by simpa [C, *, -k] using congr((l - l * x * C) *ᵥ $k).symm⟩⟩

variable [Fintype σ]

variable [StablyUnram E] {L : Matrix σ P (𝔸f E)} {H : Matrix P σ (𝔸f E)} (u : L * H = 1)
  (V : Submodule E (σ → E)) {s D K} {x : Matrix σ (Fin s) E} (Y : Matrix τ P (𝔸f E))

/-- For left invertible H, a chosen matrix m = ya, with y a basis of V over E, a ∈ GL_s(𝔸_f) and
Hm primitive over Ô. -/
@[irreducible] noncomputable def sublatticeBasis (hs : finrank E V = s := by rfl) :
    {m // IsPrimitiveMatrix (Ô E) (H * m) ∧ ∃ᵉ (y : Matrix _ (Fin s) E) (a : GL (Fin s) (𝔸f E)),
  HasLeftInv y ∧ colSpan y = V ∧ m = finAdeleMat y * a.1} :=
  Nonempty.some ((hs ▸ exists_basis_matrix V).elim fun y ⟨i@⟨l, _⟩, e⟩ ↦
  (exists_preimageLattice_eq_colLattice ⟨finAdeleMat l * L, by simp [← L.mul_assoc, *,
  ← Matrix.map_mul]⟩).elim fun a ⟨_, h⟩ ↦ ⟨_, H.mul_assoc _ a.1 ▸ h, y, a, i, e, rfl⟩)

/-- The discriminant √[det mᴴm] of the lattice of adelic points of V that H makes integral, for
its basis m = `Filling.sublatticeBasis`, with [·] the generalised index `genIndex`. -/
noncomputable def sublatticeDisc := √(genIndex
  ((sublatticeBasis u V (s := finrank E V)).1ᴴ * (sublatticeBasis u V).1).det)

/-- Let n have dim V columns, adelic combinations of vectors of V, with Hn integral, D = [det
nᴴn] ≠ 0 and the columns of YHn in K. Let i be the index of K in the Ô-span of the columns of YHm,
m = `Filling.sublatticeBasis`, d = `Filling.sublatticeDisc`. Then (d·i)² ≤ D, d > 0 and i ≥ 1. -/
lemma sublatticeDisc_mul_index_sq_le (c : s = finrank E V) (e : colSpan x ≤
  V) (w : GL (Fin s) (𝔸f E)) (d : genIndex (finAdeleMat (xᴴ * x)).det * genIndex w.1.det ^ 2 =
  D) (h : D ≠ 0) : let n := H * (finAdeleMat x * w.1); IsIntMatrix (Ô E) n → (∀ j, (Y * n).col j ∈
    K) → let i := submoduleIndex K (colLattice (Ô E) (Y * (H * (sublatticeBasis u V).1)))
    (sublatticeDisc u V * i) ^ 2 ≤ D ∧ 0 < sublatticeDisc u V ∧ 1 ≤ i := by
  subst c d; rw [sublatticeDisc]; obtain ⟨b, ⟨-, l, j, o⟩, y, a, -, t, g⟩ := sublatticeBasis u V
  obtain ⟨B, rfl⟩ := exists_mul_eq_of_col_mem_range (t.ge <| e ⟨_, x.mulVec_single_one ·⟩)
  obtain ⟨A, f⟩ : ∃ A, finAdeleMat (y * B) * w.1 = b * A := ⟨a⁻¹ * finAdeleMat B * w, by simp [*]⟩
  rw [← genIndex_det_conj, show w.1ᴴ * _ * _ = Aᴴ * (bᴴ * b) *
    A by simpa [finAdeleMat_conjTranspose] using congr($fᴴ * $f), genIndex_det_conj, f] at *
  simp [← Matrix.mul_assoc]; intro i k
  obtain ⟨p, A, rfl⟩ := by simpa [genIndex.apply_eq_zero_iff, ← A.isUnit_iff_isUnit_det] using h
  rw [← submoduleIndex_colLattice_intVectors (by simpa [← Matrix.mul_assoc, o] using j.mul i)] at *
  obtain ⟨⟨z, w⟩⟩ := ne_zero_and_le_of_dvd (h <| by simp [·]) (submoduleIndex_dvd_of_le _ (K' :=
    colLattice ..) (colLattice_le k) le_sup_left), genIndex_pos p.unit
  use by grw [mul_pow, w, Real.sq_sqrt]; bound, by simpa, z.pos

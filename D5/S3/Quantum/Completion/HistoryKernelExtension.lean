/- GID: D5/S3/Quantum/Completion/HistoryKernelExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/HistoryKernelExtension
   mirror-E: none(waiver:universal-positive-extension)
   anchors: []
   utility: none
   digest: The fixed history-kernel extension law implies positivity on every finite ordered list. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

noncomputable section

open scoped ComplexOrder MatrixOrder
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.HistoryKernelExtension

/-- The table always reads the same primitive kernel, including repeated labels. -/
def finiteGram {X I : Type*} (K : X → X → ℂ) (L : I → X) : Matrix I I ℂ :=
  fun i j => K (L i) (L j)

/-- The full extension block retains both cross blocks and the square residual. -/
def residualExtension {I : Type*} [Fintype I] (G : Matrix I I ℂ)
    (c : Matrix I Unit ℂ) (r : ℂ) : Matrix (I ⊕ Unit) (I ⊕ Unit) ℂ :=
  Matrix.fromBlocks G (G * c) (cᴴ * G)
    (cᴴ * G * c + fun _ _ => star r * r)

/-- C129's universal law; there is no positivity or Hermitian premise. -/
def KernelExtensionLaw {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → X) (h : X),
    ∃ (c : Matrix (Fin n) Unit ℂ) (r : ℂ),
      finiteGram K (Sum.elim L (fun _ : Unit => h)) =
        residualExtension (finiteGram K L) c r

private def oldFactor {I : Type*} (A : Matrix I I ℂ) : Matrix (I ⊕ Unit) I ℂ :=
  Sum.elim A (fun _ _ => 0)

private def residualFactor {I : Type*} (r : ℂ) : Matrix (I ⊕ Unit) Unit ℂ :=
  Sum.elim (fun _ _ => 0) (fun _ _ => r)

private theorem residualExtension_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (G : Matrix I I ℂ) (c : Matrix I Unit ℂ) (r : ℂ) (hG : G.PosSemidef) :
    (residualExtension G c r).PosSemidef := by
  obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  have hA' : G = Aᴴ * A := by
    simpa only [Matrix.star_eq_conjTranspose] using hA
  have hGram := Matrix.fromBlocks_gram_posSemidef
    (X := residualFactor (I := I) r) (Y := oldFactor A)
  have hDiag : Matrix.fromBlocks G (0 : Matrix I Unit ℂ) 0
      (fun _ _ : Unit => star r * r) =
      Matrix.fromBlocks
        ((oldFactor A)ᴴ * oldFactor A)
        ((oldFactor A)ᴴ * residualFactor r)
        ((residualFactor (I := I) r)ᴴ * oldFactor A)
        ((residualFactor (I := I) r)ᴴ * residualFactor r) := by
    ext i j
    cases i <;> cases j <;>
      simp [oldFactor, residualFactor, Matrix.fromBlocks, Matrix.mul_apply, hA']
  rw [← hDiag] at hGram
  have hp := hGram.conjTranspose_mul_mul_same
    (Matrix.fromBlocks (1 : Matrix I I ℂ) c 0 (1 : Matrix Unit Unit ℂ))
  simpa [residualExtension, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.mul_assoc] using hp

/-- The universal same-entry law yields every finite table, without assuming
    Hermitian symmetry, a vector carrier, distinct labels, or nonzero residuals. -/
theorem extensionLaw_finiteGram_posSemidef {X : Type*} (K : X → X → ℂ)
    (hK : KernelExtensionLaw K) :
    ∀ (n : ℕ) (L : Fin n → X), (finiteGram K L).PosSemidef := by
  intro n
  induction n with
  | zero =>
      intro L
      have hz : finiteGram K L = 0 := by ext i; exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
  | succ n ih =>
      intro L
      let old : Fin n → X := fun i => L i.succ
      obtain ⟨c, r, heq⟩ := hK n old (L 0)
      have hp := residualExtension_posSemidef (finiteGram K old) c r (ih old)
      rw [← heq] at hp
      have hs := hp.submatrix (Fin.cases (Sum.inr ()) (fun i => Sum.inl i))
      convert hs using 1
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j <;> rfl

end D5.S3.Quantum.Completion.HistoryKernelExtension

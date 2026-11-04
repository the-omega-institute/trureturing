/- GID: D5/S3/Quantum/Completion/HistoryKernelExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/HistoryKernelExtension
   mirror-E: none(waiver:universal-positive-extension)
   anchors: []
   utility: none
   digest: Kernel extension implies positivity on every finite list. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

/-! Fixed-entry finite history tables and their universal extension law. -/

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
    (cᴴ * G * c + Matrix.of (fun _ _ : Unit => star r * r))

/-- C129's universal law; there is no positivity or Hermitian premise. -/
def KernelExtensionLaw {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → X) (h : X),
    ∃ (c : Matrix (Fin n) Unit ℂ) (r : ℂ),
      finiteGram K (Sum.elim L (fun _ : Unit => h)) =
        residualExtension (finiteGram K L) c r

private theorem residualExtension_posSemidef {I : Type*} [Fintype I]
    (G : Matrix I I ℂ) (c : Matrix I Unit ℂ) (r : ℂ) (hG : G.PosSemidef) :
    (residualExtension G c r).PosSemidef := by
  classical
  let D : Matrix Unit Unit ℂ := Matrix.of (fun _ _ => star r * r)
  have hD : D.PosSemidef := by
    convert Matrix.posSemidef_conjTranspose_mul_self
      (Matrix.of (fun _ _ : Unit => r)) using 1
    ext i j
    simp [D, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hd : (Matrix.fromBlocks G (0 : Matrix I Unit ℂ) 0 D).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hG.isHermitian.fromBlocks (by simp) hD.isHermitian) ?_
    intro x
    have hp := add_nonneg (hG.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
      (hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr))
    convert hp using 1
    simp [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
      Function.comp_def]
  have hp := hd.conjTranspose_mul_mul_same
    (Matrix.fromBlocks (1 : Matrix I I ℂ) c 0 (1 : Matrix Unit Unit ℂ))
  simpa [residualExtension, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.mul_assoc, D] using hp

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

/-- Finite positivity supplies the positive quadratic form on the free
    finitely supported formal span, the input needed for C129 Theorem 2.4. -/
theorem extensionLaw_kernel_posSemidef {X : Type*} (K : X → X → ℂ)
    (hK : KernelExtensionLaw K) : (Matrix.of K).PosSemidef := by
  classical
  have hfin := extensionLaw_finiteGram_posSemidef K hK
  refine ⟨?_, ?_⟩
  · ext x y
    have hh := (hfin 2 ![x, y]).isHermitian
    exact hh.apply 0 1
  · intro f
    let e := (Fintype.equivFin f.support).symm
    have hp := hfin (Fintype.card f.support) (fun i => (e i).val)
    have hs := hp.submatrix (fun i : f.support => e.symm i)
    have hs' : (Matrix.of (fun i j : f.support => K i.val j.val)).PosSemidef := by
      simpa [finiteGram, Matrix.submatrix] using hs
    have hq := hs'.dotProduct_mulVec_nonneg (fun i => f i.val)
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.of_apply,
      Pi.star_apply, ← mul_assoc] at hq
    change 0 ≤ ∑ i ∈ f.support, ∑ j ∈ f.support, star (f i) * K i j * f j
    have heq : (∑ i : f.support, ∑ j : f.support,
        star (f i.val) * K i.val j.val * f j.val) =
        ∑ i ∈ f.support, ∑ j ∈ f.support, star (f i) * K i j * f j := by
      calc
        _ = ∑ i : f.support, ∑ j ∈ f.support,
            star (f i.val) * K i.val j * f j := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_coe_sort f.support
            (fun j => star (f i.val) * K i.val j * f j)
        _ = _ := Finset.sum_coe_sort f.support
          (fun i => ∑ j ∈ f.support, star (f i) * K i j * f j)
    exact heq ▸ hq

end D5.S3.Quantum.Completion.HistoryKernelExtension

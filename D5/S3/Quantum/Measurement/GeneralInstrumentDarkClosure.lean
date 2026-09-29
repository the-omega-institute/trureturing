/- GID: D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/GeneralInstrumentDarkClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The dark layers of a general no-click instrument are kernels of the survival defects and close after dimension many steps. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

open Matrix
open scoped ComplexOrder

variable {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]

/-- The dual `𝒜(X) = ∑ₐ Q_aᴴ X Q_a` of the no-click map with Kraus operators `Q_a`. -/
def noClickDual (Q : α → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ a, (Q a)ᴴ * X * Q a

/-- The survival effect `S_n = 𝒜ⁿ(I)`. -/
def survival (Q : α → Matrix (Fin d) (Fin d) ℂ) : ℕ → Matrix (Fin d) (Fin d) ℂ
  | 0 => 1
  | n + 1 => noClickDual Q (survival Q n)

/-- The dark layers: `D₀ = ℂᵈ` and `D_{n+1}` is the set of vectors annihilated by every click
Kraus operator whose images under every unread no-click Kraus operator lie in `Dₙ`. -/
def darkLayer (Q : α → Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ) :
    ℕ → Submodule ℂ (Fin d → ℂ)
  | 0 => ⊤
  | n + 1 => (⨅ i, LinearMap.ker (L i).mulVecLin) ⊓
      ⨅ a, (darkLayer Q L n).comap (Q a).mulVecLin

/-- **Finite closure of the dark directions of a general instrument.** For no-click Kraus
operators `Q_a` and click Kraus operators `L_i` with `∑ₐ Q_aᴴ Q_a + ∑ᵢ L_iᴴ L_i = I`, every dark
layer is the kernel of the survival defect, `Dₙ = ker(I - Sₙ)`; the layers are constant from
`n = d` on; and `D_d` is the largest subspace that every `L_i` annihilates and every `Q_a` maps
into itself. -/
theorem darkLayer_closure (Q : α → Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1) :
    (∀ n, darkLayer Q L n = LinearMap.ker (1 - survival Q n).mulVecLin) ∧
      (∀ n, d ≤ n → darkLayer Q L n = darkLayer Q L d) ∧
      (∀ i, ∀ v ∈ darkLayer Q L d, (L i).mulVec v = 0) ∧
      (∀ a, ∀ v ∈ darkLayer Q L d, (Q a).mulVec v ∈ darkLayer Q L d) ∧
      ∀ V : Submodule ℂ (Fin d → ℂ), (∀ i, ∀ v ∈ V, (L i).mulVec v = 0) →
        (∀ a, ∀ v ∈ V, (Q a).mulVec v ∈ V) → V ≤ darkLayer Q L d := by
  classical
  -- the survival defect satisfies `I - S_{n+1} = ∑ᵢ L_iᴴ L_i + ∑ₐ Q_aᴴ (I - Sₙ) Q_a`
  have hclick : ∑ i, (L i)ᴴ * L i = 1 - ∑ a, (Q a)ᴴ * Q a := eq_sub_of_add_eq' hcomp
  have hstep : ∀ n, 1 - survival Q (n + 1) =
      ∑ i, (L i)ᴴ * L i + ∑ a, (Q a)ᴴ * (1 - survival Q n) * Q a := by
    intro n
    simp only [survival, noClickDual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Finset.sum_sub_distrib, hclick]
    abel
  -- every survival defect is positive semidefinite
  have hpsd : ∀ n, (1 - survival Q n).PosSemidef := by
    intro n
    induction n with
    | zero => simpa [survival] using (PosSemidef.zero : (0 : Matrix (Fin d) (Fin d) ℂ).PosSemidef)
    | succ n ih =>
        rw [hstep]
        exact (posSemidef_sum _ fun i _ => posSemidef_conjTranspose_mul_self (L i)).add
          (posSemidef_sum _ fun a _ => ih.conjTranspose_mul_mul_same (Q a))
  -- the quadratic form of a conjugated operator
  have hquad : ∀ (B P : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ),
      star v ⬝ᵥ ((Bᴴ * P * B) *ᵥ v) = star (B *ᵥ v) ⬝ᵥ (P *ᵥ (B *ᵥ v)) := by
    intro B P v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.star_mulVec]
  -- the kernel of the survival defect after one more step
  have hker : ∀ n (v : Fin d → ℂ), (1 - survival Q (n + 1)) *ᵥ v = 0 ↔
      (∀ i, (L i) *ᵥ v = 0) ∧ ∀ a, (1 - survival Q n) *ᵥ ((Q a) *ᵥ v) = 0 := by
    intro n v
    have hL : ∀ i, 0 ≤ star v ⬝ᵥ (((L i)ᴴ * L i) *ᵥ v) := fun i =>
      (posSemidef_conjTranspose_mul_self (L i)).dotProduct_mulVec_nonneg v
    have hQ : ∀ a, 0 ≤ star v ⬝ᵥ (((Q a)ᴴ * (1 - survival Q n) * Q a) *ᵥ v) := fun a =>
      ((hpsd n).conjTranspose_mul_mul_same (Q a)).dotProduct_mulVec_nonneg v
    rw [← (hpsd (n + 1)).dotProduct_mulVec_zero_iff, hstep, Matrix.add_mulVec,
      dotProduct_add, Matrix.sum_mulVec, Matrix.sum_mulVec, dotProduct_sum, dotProduct_sum,
      add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun i _ => hL i)
        (Finset.sum_nonneg fun a _ => hQ a),
      Finset.sum_eq_zero_iff_of_nonneg fun i _ => hL i,
      Finset.sum_eq_zero_iff_of_nonneg fun a _ => hQ a]
    refine and_congr (forall_congr' fun i => ?_) (forall_congr' fun a => ?_)
    · simp only [Finset.mem_univ, true_implies]
      rw [(posSemidef_conjTranspose_mul_self (L i)).dotProduct_mulVec_zero_iff,
        conjTranspose_mul_self_mulVec_eq_zero]
    · simp only [Finset.mem_univ, true_implies]
      rw [hquad, (hpsd n).dotProduct_mulVec_zero_iff]
  -- membership in the next layer
  have hmem : ∀ n (v : Fin d → ℂ), v ∈ darkLayer Q L (n + 1) ↔
      (∀ i, (L i) *ᵥ v = 0) ∧ ∀ a, (Q a) *ᵥ v ∈ darkLayer Q L n := by
    intro n v
    simp [darkLayer, Submodule.mem_iInf]
  -- (1) every layer is the kernel of the survival defect
  have hlayer : ∀ n, darkLayer Q L n = LinearMap.ker (1 - survival Q n).mulVecLin := by
    intro n
    induction n with
    | zero => ext v; simp [darkLayer, survival]
    | succ n ih =>
        ext v
        rw [hmem, LinearMap.mem_ker, Matrix.mulVecLin_apply, hker]
        simp only [ih, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  -- the layer map is monotone, so the layers decrease and one equality propagates
  have hmono : ∀ m n, darkLayer Q L m ≤ darkLayer Q L n →
      darkLayer Q L (m + 1) ≤ darkLayer Q L (n + 1) := by
    intro m n h v hv
    rw [hmem] at hv ⊢
    exact ⟨hv.1, fun a => h (hv.2 a)⟩
  have hanti : ∀ n, darkLayer Q L (n + 1) ≤ darkLayer Q L n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih => exact hmono _ _ ih
  have hprop : ∀ k, darkLayer Q L (k + 1) = darkLayer Q L k →
      ∀ m, darkLayer Q L (k + m) = darkLayer Q L k := by
    intro k hk m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [← add_assoc, le_antisymm (hmono _ _ ih.le) (hmono _ _ ih.ge), hk]
  -- a strict drop lowers the dimension, so some step among the first `d + 1` is an equality
  have hexists : ∃ k ≤ d, darkLayer Q L (k + 1) = darkLayer Q L k := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hdim : ∀ k ≤ d + 1, Module.finrank ℂ (darkLayer Q L k) + k ≤ d := by
      intro k hk
      induction k with
      | zero =>
          change Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) + 0 ≤ d
          rw [finrank_top, Module.finrank_fin_fun, add_zero]
      | succ k ih =>
          have hlt : darkLayer Q L (k + 1) < darkLayer Q L k :=
            lt_of_le_of_ne (hanti k) (hne k (by omega))
          have := Submodule.finrank_lt_finrank_of_lt hlt
          have := ih (by omega)
          omega
    have := hdim (d + 1) le_rfl
    omega
  obtain ⟨k, hkd, hk⟩ := hexists
  have hstable : ∀ n, d ≤ n → darkLayer Q L n = darkLayer Q L d := by
    intro n hn
    have h1 := hprop k hk (n - k)
    have h2 := hprop k hk (d - k)
    rw [Nat.add_sub_cancel' (by omega)] at h1 h2
    rw [h1, h2]
  have hfix : darkLayer Q L (d + 1) = darkLayer Q L d := hstable (d + 1) (by omega)
  refine ⟨hlayer, hstable, fun i v hv => ?_, fun a v hv => ?_, fun V hL hQ => ?_⟩
  · rw [← hfix, hmem] at hv
    exact hv.1 i
  · rw [← hfix, hmem] at hv
    exact hv.2 a
  · have hV : ∀ n, V ≤ darkLayer Q L n := by
      intro n
      induction n with
      | zero => exact le_top
      | succ n ih =>
          intro v hv
          rw [hmem]
          exact ⟨fun i => hL i v hv, fun a => ih (hQ a v hv)⟩
    exact hV d

#print axioms darkLayer_closure

end D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

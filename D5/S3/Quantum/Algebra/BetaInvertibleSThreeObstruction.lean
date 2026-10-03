/- GID: D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No beta-invertible S3 in the Z_N x Z_N SymTFT when 3 divides N (arXiv:2406.12151). -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the
  reduction of `ρ` modulo 3 (`hQ3`, `hβ3`), the alternating lemma `halt` with its consequence
  `hshape` (for `g ≠ 1`, `S_g = δ_g β_g⁻¹` has zero diagonal and is determined by its entry
  `S_g 0 1`), the injectivity lemma `hinj` (equal `S_g` force `β(h⁻¹ g) = 0`) and the count of
  the five non-identity permutations against the three elements of `ZMod 3`
admission_basis: open-problem-resolution (issue #11228)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.BetaInvertibleSThreeObstruction

open Matrix

/-!
D.-C. Lu, Z. Sun and Z. Zhang, *Exploring G-ality defects in 2-dim QFTs*, arXiv:2406.12151 (JHEP
11 (2025) 081). For `A = ℤ_N × ℤ_N` the anyons of the SymTFT are the pairs `(a, â)` with
self-statistics `exp(2πi a·â / N)`, and the anyon permutation symmetries are the invertible
matrices `U = (α β; γ δ)` over `ZMod N` preserving `Q(a, â) = a·â`. `U` is β-invertible when its
block `β : Â → A` is invertible. The paper proves that no `S₃` subgroup has all non-identity
elements β-invertible when `N` is even, and conjectures the same when `3 ∣ N`. Reducing modulo
3, each `g ≠ 1` maps the Lagrangian `{(0, x)}` to the graph of `S_g = δ_g β_g⁻¹`, which `Q`
forces to be alternating, hence one of three matrices; distinct `g` give distinct `S_g`, and
`S₃` has five non-identity elements.
-/

/-- `Q(a, â) = a · â` on `A ⊕ Â = (ZMod N)² ⊕ (ZMod N)²`; the left summand is `A`. -/
def Q {N : ℕ} (v : Fin 2 ⊕ Fin 2 → ZMod N) : ZMod N :=
  v (Sum.inl 0) * v (Sum.inr 0) + v (Sum.inl 1) * v (Sum.inr 1)

/-- The conjecture of Lu, Sun and Zhang for `3 ∣ N`: no homomorphism `ρ : S₃ → GL₄(ZMod N)`
preserves `Q` and has an invertible upper-right block `β` at every non-identity element. -/
def claim : Prop :=
  ∀ N : ℕ, 3 ∣ N → ¬ ∃ ρ : Equiv.Perm (Fin 3) →* GL (Fin 2 ⊕ Fin 2) (ZMod N),
    (∀ g v, Q ((ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod N)) *ᵥ v) = Q v) ∧
    ∀ g, g ≠ 1 →
      IsUnit (Matrix.toBlocks₁₂ (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod N))).det

/-- The conjecture holds: there is no β-invertible `S₃` symmetry when `3 ∣ N`. -/
theorem result : claim := by
  intro N h3 ⟨ρ, hQ, hβ⟩
  -- the block formula on vectors `(0, x)`
  have block : ∀ {R : Type} [CommRing R] (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
      (x : Fin 2 → R), M *ᵥ Sum.elim 0 x = Sum.elim (M.toBlocks₁₂ *ᵥ x) (M.toBlocks₂₂ *ᵥ x) := by
    intro R _ M x
    funext i
    rcases i with i | i <;> fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂]
  let φ : ZMod N →+* ZMod 3 := ZMod.castHom h3 (ZMod 3)
  let M : Equiv.Perm (Fin 3) → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
    fun g => (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod N)).map φ
  have hMmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    simp only [M, map_mul, Units.val_mul]
    exact Matrix.map_mul
  have hMone : M 1 = 1 := by
    simp only [M, map_one, Units.val_one]
    exact Matrix.map_one φ (map_zero φ) (map_one φ)
  have hQ3 : ∀ g (w : Fin 2 ⊕ Fin 2 → ZMod 3), Q (M g *ᵥ w) = Q w := by
    intro g w
    obtain ⟨v, rfl⟩ : ∃ v : Fin 2 ⊕ Fin 2 → ZMod N, (fun i => φ (v i)) = w :=
      ⟨fun i => (w i).val, funext fun i => by simp [φ]⟩
    have e : M g *ᵥ (fun i => φ (v i)) =
        fun i => φ (((ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod N)) *ᵥ v) i) := by
      funext i
      rw [RingHom.map_mulVec]
      rfl
    rw [e]
    have hq : ∀ u : Fin 2 ⊕ Fin 2 → ZMod N, Q (fun i => φ (u i)) = φ (Q u) := by
      intro u
      simp [Q]
    rw [hq, hq, hQ]
  have hβ3 : ∀ g, g ≠ 1 → IsUnit (M g).toBlocks₁₂.det := by
    intro g hg
    have : (M g).toBlocks₁₂ =
        (Matrix.toBlocks₁₂ (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod N))).map φ := rfl
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hβ g hg).map φ
  -- `S_g = δ_g β_g⁻¹`
  let S : Equiv.Perm (Fin 3) → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    fun g => (M g).toBlocks₂₂ * ((M g).toBlocks₁₂)⁻¹
  have halt : ∀ g, g ≠ 1 → ∀ y : Fin 2 → ZMod 3, y ⬝ᵥ (S g *ᵥ y) = 0 := by
    intro g hg y
    have hu := hβ3 g hg
    set x := ((M g).toBlocks₁₂)⁻¹ *ᵥ y
    have hq := hQ3 g (Sum.elim 0 x)
    rw [block] at hq
    have h1 : (M g).toBlocks₁₂ *ᵥ x = y := by
      simp only [x, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    have h2 : (M g).toBlocks₂₂ *ᵥ x = S g *ᵥ y := by
      simp only [x, S, Matrix.mulVec_mulVec]
    rw [h1, h2] at hq
    simpa [Q, dotProduct, Fin.sum_univ_two] using hq
  have hshape : ∀ g, g ≠ 1 → S g = !![0, S g 0 1; -(S g 0 1), 0] := by
    intro g hg
    have a0 := halt g hg ![1, 0]
    have a1 := halt g hg ![0, 1]
    have a2 := halt g hg ![1, 1]
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec] at a0 a1 a2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a0, a1]
    linear_combination a2 - a0 - a1
  have hinj : ∀ g h, g ≠ 1 → h ≠ 1 → S g 0 1 = S h 0 1 → g = h := by
    intro g h hg hh e
    by_contra hne
    have hSg : S g = S h := by rw [hshape g hg, hshape h hh, e]
    have hk : h⁻¹ * g ≠ 1 := by
      intro hk; exact hne (by rw [← mul_left_cancel_iff (a := h⁻¹), hk, inv_mul_cancel])
    have hug := hβ3 g hg
    have huh := hβ3 h hh
    have hzero : (M (h⁻¹ * g)).toBlocks₁₂ = 0 := by
      ext i j
      set x : Fin 2 → ZMod 3 := Pi.single j 1
      set z := ((M h).toBlocks₁₂)⁻¹ *ᵥ ((M g).toBlocks₁₂ *ᵥ x)
      have hgz : M g *ᵥ Sum.elim 0 x = M h *ᵥ Sum.elim 0 z := by
        rw [block, block]
        congr 1
        · simp only [z, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huh,
            Matrix.one_mul]
        · have : (M h).toBlocks₂₂ *ᵥ z = S h *ᵥ ((M g).toBlocks₁₂ *ᵥ x) := by
            simp only [z, S, Matrix.mulVec_mulVec, Matrix.mul_assoc]
          rw [this, ← hSg]
          simp only [S, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hug,
            Matrix.mul_one]
      have hinv : M h⁻¹ * M h = 1 := by rw [← hMmul, inv_mul_cancel, hMone]
      have hk' : M (h⁻¹ * g) *ᵥ Sum.elim 0 x = (Sum.elim 0 z : Fin 2 ⊕ Fin 2 → ZMod 3) := by
        rw [hMmul, ← Matrix.mulVec_mulVec, hgz, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      have := congrFun hk' (Sum.inl i)
      rw [block] at this
      simp only [Sum.elim_inl] at this
      simpa [x, Matrix.mulVec_single_one] using this
    have := hβ3 _ hk
    rw [hzero, Matrix.det_zero] at this
    exact not_isUnit_zero this
  have hcard := Fintype.card_le_of_injective
    (fun g : {g : Equiv.Perm (Fin 3) // g ≠ 1} => S g.1 0 1)
    (fun g h e => Subtype.ext (hinj g.1 h.1 g.2 h.2 e))
  rw [ZMod.card] at hcard
  have : Fintype.card {g : Equiv.Perm (Fin 3) // g ≠ 1} = 5 := by decide
  omega

end D5.S3.Quantum.Algebra.BetaInvertibleSThreeObstruction

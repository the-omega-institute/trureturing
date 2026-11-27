/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The P48q Gram dual and the projected integral charges in the fixed space. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate

/-!
The integral Gram inverse identifies the ambient P48q dual with the original lattice.
In the fixed space, pairing with integral norm images makes three times a dual
momentum integral. The norm image certificate then gives an integral charge whose
order-three average is that momentum.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual

open P48qFixedRankCertificate P48qGramCertificate P48qNormImageCertificate
open scoped Matrix

noncomputable section

local notation "c" => Int.castRingHom ℂ
local notation "embed" => (fun a : Fin 48 → ℤ => c ∘ a)
local notation "G" => (nebeGram.map c)
local notation "B" => Matrix.toBilin' G
local notation "A" => nebeOrderThree
local notation "T" => rowAction ℂ A
local notation "N" => (1 + A + A ^ 2 : Matrix (Fin 48) (Fin 48) ℤ)

private theorem gram_integral (a b : Fin 48 → ℤ) :
    B (embed a) (embed b) = c (nebeGram.toBilin' a b) := by
  simp only [Matrix.toBilin'_apply, Matrix.map_apply, Function.comp_apply,
    Int.coe_castRingHom, Int.cast_sum, Int.cast_mul]

/-- In the complexified row coordinates the Gram dual of P48q is P48q itself. -/
theorem gram_dual_iff (μ : Fin 48 → ℂ) :
    (∀ x : Fin 48 → ℤ, ∃ m : ℤ, B (embed x) μ = (m : ℂ)) ↔
      ∃ a : Fin 48 → ℤ, μ = embed a := by
  constructor
  · intro h
    have hCoordinate (i : Fin 48) : ∃ m : ℤ, (G *ᵥ μ) i = (m : ℂ) := by
      have he : embed (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℂ) := by
        funext j
        by_cases hij : j = i <;> simp [hij]
      simpa only [he, Matrix.toBilin'_apply', single_one_dotProduct] using
        h (Pi.single i 1)
    choose z hz using hCoordinate
    have hμ : G *ᵥ μ = embed z := funext hz
    have hInverse : nebeGramInverse.map c * G = 1 := by
      change (c).mapMatrix nebeGramInverse * (c).mapMatrix nebeGram = 1
      rw [← map_mul, gram_inverse_certificate, map_one]
    refine ⟨nebeGramInverse *ᵥ z, ?_⟩
    calc
      μ = nebeGramInverse.map c *ᵥ (G *ᵥ μ) := by
        rw [Matrix.mulVec_mulVec, hInverse, Matrix.one_mulVec]
      _ = embed (nebeGramInverse *ᵥ z) := by
        rw [hμ]
        exact funext fun i => ((c).map_mulVec nebeGramInverse z i).symm
  · rintro ⟨a, rfl⟩ x
    exact ⟨nebeGram.toBilin' x a, gram_integral x a⟩

private theorem action_embed (x : Fin 48 → ℤ) : T (embed x) = embed (x ᵥ* A) := by
  change Aᵀ.map c *ᵥ embed x = embed (x ᵥ* A)
  rw [← Matrix.mulVec_transpose]
  exact funext fun i => ((c).map_mulVec Aᵀ x i).symm

private theorem norm_embed (x : Fin 48 → ℤ) :
    embed (x ᵥ* N) = embed x + T (embed x) + T (T (embed x)) := by
  simp only [action_embed, pow_two, ← Matrix.vecMul_vecMul, Matrix.vecMul_add,
    Matrix.vecMul_one]
  exact funext fun i => by simp only [Function.comp_apply, Pi.add_apply, map_add]

private theorem gram_invariant (x y : Fin 48 → ℂ) : B (T x) (T y) = B x y := by
  have hGram : (Aᵀ.map c)ᵀ * G * Aᵀ.map c = G := by
    change (c).mapMatrix A * (c).mapMatrix nebeGram * (c).mapMatrix Aᵀ = (c).mapMatrix nebeGram
    rw [← map_mul, ← map_mul, gram_isometry_certificate]
  change ((B).comp (Aᵀ.map c).toLin' (Aᵀ.map c).toLin') x y = B x y
  rw [Matrix.toBilin'_comp, hGram]

private theorem norm_fixed (x : Fin 48 → ℤ) : (x ᵥ* N) ᵥ* A = x ᵥ* N := by
  have hNA : N * A = N := by
    calc
      N * A = A + A ^ 2 + 1 := by
        rw [add_mul, add_mul, one_mul, ← pow_two, ← pow_succ, nebeOrderThree_cube]
      _ = N := by abel
  rw [Matrix.vecMul_vecMul, hNA]

/-- The dual of the integral fixed lattice consists exactly of the projections
of integral charges, where the order-three projection is the norm divided by three. -/
theorem fixed_dual_iff_projected_charge (μ : Fin 48 → ℂ) :
    (T μ = μ ∧ ∀ x : Fin 48 → ℤ, x ᵥ* A = x → ∃ m : ℤ, B (embed x) μ = (m : ℂ)) ↔
      ∃ a : Fin 48 → ℤ, μ = (3 : ℂ)⁻¹ • embed (a ᵥ* N) := by
  constructor
  · rintro ⟨hFixed, hIntegral⟩
    have hStep (y : Fin 48 → ℂ) : B (T y) μ = B y μ := by
      simpa only [hFixed] using gram_invariant y μ
    have hTriple (x : Fin 48 → ℤ) :
        B (embed x) ((3 : ℂ) • μ) = B (embed (x ᵥ* N)) μ := by
      simp only [norm_embed, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_right, hStep]
      ring
    obtain ⟨v, hv⟩ := (gram_dual_iff ((3 : ℂ) • μ)).mp fun x => by
      rw [hTriple]
      exact hIntegral (x ᵥ* N) (norm_fixed x)
    have hvFixed : v ᵥ* A = v := by
      have hCast : embed (v ᵥ* A) = embed v := by
        rw [← action_embed, ← hv, map_smul, hFixed]
      exact funext fun i => Int.cast_injective (α := ℂ) (congrFun hCast i)
    obtain ⟨a, ha⟩ := nebeOrderThree_fixed_is_norm_image v hvFixed
    refine ⟨a, ?_⟩
    rw [ha, ← hv, smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]
  · rintro ⟨a, rfl⟩
    refine ⟨by rw [map_smul, action_embed, norm_fixed], ?_⟩
    intro x hx
    have hFixed : T (embed x) = embed x := by rw [action_embed, hx]
    have hStep (y : Fin 48 → ℂ) : B (embed x) (T y) = B (embed x) y := by
      simpa only [hFixed] using gram_invariant (embed x) y
    refine ⟨nebeGram.toBilin' x a, ?_⟩
    rw [LinearMap.BilinForm.smul_right, norm_embed]
    simp only [map_add, hStep]
    calc
      _ = B (embed x) (embed a) := by ring
      _ = _ := gram_integral x a

#print axioms gram_dual_iff
#print axioms fixed_dual_iff_projected_charge

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual

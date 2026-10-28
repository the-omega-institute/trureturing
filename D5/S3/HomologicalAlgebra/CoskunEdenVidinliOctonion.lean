/- GID: D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.claim; result=D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.result; claim=D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.claim
   digest: The exceptional Vidinli product has no real-linear octonion push-forward. -/

/-
proof_shape: result: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#20661; Refuted)
Direct frozen dependencies: none. The closed octonion owner has no frozen state record.
proof_shape: vidinliMul, claim, octLeft, kernelVectors: bind-only definitions.
proof_shape: vidinli_unit, oct_zero_mul, kernelVectors_injective,
  vidinli_kills_kernelVectors: bind-only; consumer: result; escape_witness: none.
proof_shape: oct_norm_zero_iff: bind-only; consumer: octLeft_injective; escape_witness: none.
proof_shape: octLeft_injective: bind-only; consumer: result; escape_witness: none.
Direct frozen dependencies for every declaration above: none.
The coordinate product and existential claim are the expressions of issue #20661.
The private linear maps package octonion left multiplication and the five kernel vectors.
The norm argument uses MonsterTwistedOctonionNorm.norm_mul; rank-nullity and the
injective-map finrank bound are supplied by pinned Mathlib.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm

/-! Binding conventions for O. Coşkun and A. Eden, "Structure of Vidinli Algebras: Simple Nonassociative Jordan–Lie
Algebras with Azumaya Properties", arXiv:2511.09395v1 (12 November 2025).

* Definition 5.1, coordinate expression: for a = ∑ aᵢeᵢ, b = ∑ bᵢeᵢ, "a ⊻₇ b = c₁e₁ + ∑_{i=2}^{7} cᵢeᵢ, where
  c₁ = a₁b₁ − ∑_{i=2}^{7} aᵢbᵢ + (a₂b₃ − a₃b₂) + (a₄b₅ − a₅b₄) + (a₆b₇ − a₇b₆), cᵢ = a₁bᵢ + b₁aᵢ for i = 2, …, 7".
  Here `V₇` is `Fin 7 → ℝ` and the coordinate `i : Fin 7` is aᵢ₊₁.
* Section 3.1 (4): "The multiplication ⊻ is a push-forward of quaternion multiplication via the linear maps
  π : H → V₃, ν : V₃ → H, … that is, we have a ⊻ b = π(ν(a)ν(b))."
* Remark 5.9: "Whether a similar push-forward description exists for the exceptional Vidinli algebra V₇ in terms of
  the octonions … remains an open question." The octonions are the closed source owner
  `MonsterTwistedOctonionNorm.Octonion` (`Fin 8 → ℝ`) with its signed Cayley–Dickson product `mul`, whose unit is the
  first coordinate and whose Euclidean norm is multiplicative (`MonsterTwistedOctonionNorm.norm_mul`). -/

namespace D5.S3.HomologicalAlgebra.CoskunEdenVidinliOctonion

open D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm (Octonion mul)

/-- Definition 5.1, coordinate expression: the product `a ⊻₇ b` of the exceptional Vidinli algebra `V₇`. -/
def vidinliMul (a b : Fin 7 → ℝ) : Fin 7 → ℝ := fun i =>
  if i = 0 then
    a 0 * b 0 - ∑ j ∈ Finset.Ioi (0 : Fin 7), a j * b j + (a 1 * b 2 - a 2 * b 1) + (a 3 * b 4 - a 4 * b 3) +
      (a 5 * b 6 - a 6 * b 5)
  else a 0 * b i + b 0 * a i

/-- Remark 5.9, octonion clause: `⊻₇` is a push-forward of octonion multiplication, `a ⊻₇ b = π(ν(a)ν(b))` for
real-linear maps `ν : V₇ → 𝕆` and `π : 𝕆 → V₇`. -/
def claim : Prop :=
  ∃ (ν : (Fin 7 → ℝ) →ₗ[ℝ] Octonion) (π : Octonion →ₗ[ℝ] (Fin 7 → ℝ)),
    ∀ a b, vidinliMul a b = π (mul (ν a) (ν b))

end D5.S3.HomologicalAlgebra.CoskunEdenVidinliOctonion

namespace D5.S3.HomologicalAlgebra.CoskunEdenVidinliOctonion
open D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm

private theorem vidinli_unit (a : Fin 7 → ℝ) : vidinliMul a (Pi.single 0 1) = a := by
  ext i
  fin_cases i <;> simp [vidinliMul, Pi.single_apply]

private theorem oct_zero_mul (q : Octonion) : mul 0 q = 0 := by
  ext i
  fin_cases i <;> simp [mul]

private theorem oct_norm_zero_iff (p : Octonion) : normSq p = 0 ↔ p = 0 := by
  simpa [normSq, funext_iff] using (Finset.sum_sq_eq_zero_iff Finset.univ p)

private def octLeft (p : Octonion) : Octonion →ₗ[ℝ] Octonion where
  toFun := mul p
  map_add' q r := by
    ext i
    fin_cases i <;> simp [mul] <;> ring
  map_smul' c q := by
    ext i
    fin_cases i <;> simp [mul] <;> ring

private theorem octLeft_injective (p : Octonion) (hp : p ≠ 0) :
    Function.Injective (octLeft p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hn : normSq p * normSq q = 0 := by
    rw [← norm_mul, show mul p q = 0 from hq]
    exact (oct_norm_zero_iff 0).mpr rfl
  exact (oct_norm_zero_iff q).mp ((mul_eq_zero.mp hn).resolve_left (by
    intro h
    exact hp ((oct_norm_zero_iff p).mp h)))

private def kernelVectors : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 7 → ℝ) :=
  LinearMap.pi ![(0 : (Fin 5 → ℝ) →ₗ[ℝ] ℝ), LinearMap.proj 0,
    LinearMap.proj 0, LinearMap.proj 1, LinearMap.proj 2,
    LinearMap.proj 3, LinearMap.proj 4]

private theorem kernelVectors_injective : Function.Injective kernelVectors := by
  intro x y h
  ext i
  fin_cases i
  · exact congrFun h 1
  · exact congrFun h 3
  · exact congrFun h 4
  · exact congrFun h 5
  · exact congrFun h 6

private theorem vidinli_kills_kernelVectors (x : Fin 5 → ℝ) :
    vidinliMul (Pi.single 1 1) (kernelVectors x) = 0 := by
  ext i
  fin_cases i <;> simp [vidinliMul, kernelVectors, Pi.single_apply]


theorem result : ¬ claim := by
  rintro ⟨ν, π, h⟩
  have hν : Function.Injective ν := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    calc
      a = vidinliMul a (Pi.single 0 1) := (vidinli_unit a).symm
      _ = π (mul (ν a) (ν (Pi.single 0 1))) := h _ _
      _ = 0 := by rw [ha, oct_zero_mul, map_zero]
  have hπ : Function.Surjective π := by
    intro a
    exact ⟨mul (ν a) (ν (Pi.single 0 1)), (h a _).symm.trans (vidinli_unit a)⟩
  have he₂ : ν (Pi.single 1 1) ≠ 0 := by
    exact (not_congr (ν.map_eq_zero_iff hν)).mpr
      (Pi.single_ne_zero_iff.mpr (one_ne_zero : (1 : ℝ) ≠ 0))
  let T := (octLeft (ν (Pi.single 1 1))).comp ν
  have hT : Function.Injective T := (octLeft_injective _ he₂).comp hν
  let F : (Fin 5 → ℝ) →ₗ[ℝ] LinearMap.ker π :=
    (T.comp kernelVectors).codRestrict (LinearMap.ker π) (fun x => by
      change π (mul (ν (Pi.single 1 1)) (ν (kernelVectors x))) = 0
      rw [← h, vidinli_kills_kernelVectors])
  have hF : Function.Injective F :=
    (LinearMap.injective_codRestrict_iff _).mpr (hT.comp kernelVectors_injective)
  have hdim := LinearMap.finrank_le_finrank_of_injective hF
  have hrank := π.finrank_range_add_finrank_ker
  have hrange : LinearMap.range π = ⊤ := LinearMap.range_eq_top.mpr hπ
  have hrange_dim : Module.finrank ℝ (LinearMap.range π) = 7 := by
    rw [hrange, finrank_top]
    exact Module.finrank_fin_fun ℝ
  have hoct_dim : Module.finrank ℝ Octonion = 8 := Module.finrank_fin_fun ℝ
  rw [hrange_dim, hoct_dim] at hrank
  simp only [Module.finrank_fin_fun] at hdim
  omega


end D5.S3.HomologicalAlgebra.CoskunEdenVidinliOctonion

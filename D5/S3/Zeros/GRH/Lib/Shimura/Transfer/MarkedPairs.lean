/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Transfer/MarkedPairs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Transfer/MarkedPairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Transfer.MarkedPairs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Transfer/MarkedPairs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Pseudocharacter.FibreSum
import D5.S3.Zeros.GRH.Lib.LocalGL.TraceFormula.ChangingSigns
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Transfer of eigensystems between inner forms of a unitary group differing at a real
place (known result; see Lib.Shimura.Transfer.PELDataExistence).

This file: Conjugation invariance of the count; reflections commuting with a regular matrix. -/

open Quotient ConjAct Finset Matrix MulAction NumberField Polynomial

variable {E n} [Field E] [CMBase E] [Fintype n] {x g : GL n (𝔸f E)} {ℓ ε} {𝔑 : 𝓞 E} {f :
  heckeAlgebra n ℂ 𝔑}

/-- For y, z in GL_n(E), Φ_{v₀}(z)·J_μ(y)·Φ_{v₀}(z)⁻¹ = J_μ(zyz⁻¹), where J_μ(y) is the matrix
`eigenReflection` ε y μ, a polynomial in Φ_{v₀}(y), with the same ε and root index μ on both
sides. -/
lemma ratConj_eigenReflection {ε μ} {y : GL n E} z : ratConj z (eigenReflection ε y μ) =
  eigenReflection ε (z * y * z⁻¹) μ := by
  simp [eigenReflection, ratConj, ← aeval_smul, units_smul_def, ← map_inv]

lemma isSignedFrame_mul_iff z (h : g ∈ GU E n) : IsSignedFrame (x * g) ℓ ↔
  IsSignedFrame (toFinGL z * x) (ratConj z ℓ) :=
  ⟨(by simpa [mul_assoc] using ·.mul z (inv_mem h)), (by simpa [ratConj] using ·.mul z⁻¹ h)⟩

lemma finsum_countTerm_eq_sum w (h : (countTerm ε f 1).support.Finite) : ∑ᶠ c, countTerm ε f w c =
  ∑ c ∈ h.toFinset, countTerm ε f 1 c * w c.out.2.1.1.charpoly c.out.2.2 := by
  convert finsum_eq_sum_of_support_subset .. <;> simp [countTerm] <;> grind

/-- Let P = det(X − y) be separable, J_ν = `eigenReflection` True y ν. For roots μ of Φ_{v₀}P, J_μ
is a reflection; each reflection J commuting with Φ_{v₀}(y) has a root μ: Φ_{v₀}(y)(J+1) = μ(J+1),
and J = J_ν iff ν = μ. -/
lemma isReflection_eigenReflection {y : GL n E} (hz : y.1.charpoly.Separable) :
  (∀ i, IsReflection (eigenReflection True y i)) ∧ ∀ J, IsReflection J → ratConj y J = J → ∃ i,
  y.1.map (Φ v₀) * (J + 1) = numberedRoots (Φ v₀) y.1.charpoly i • (J + 1) ∧ ∀ j, J =
  eigenReflection True y j ↔ i = j := ((isConj_diagonal_of_isRoot_charpoly
  (isRoot_numberedRoots hz _)).imp (·.mul_inv_eq_iff_eq_mul.2)).rec
  fun k (h : toConjAct k • diagonalAlgHom ℂ _ = y.1.map (Φ v₀)) ↦ by
  simp [eigenReflection, ← h, aeval_smul, aeval_algHom_apply,
    aeval_pi_apply, -Lagrange.interpolate_apply, eval_interpolate_univ_node, -diagonalAlgHom_apply]
  refine .symm ⟨fun J r c ↦ (r.conj k⁻¹).elim fun u ⟨w, a, e⟩ ↦ (exists_ne_zero_of_sum_ne_zero
    (a ▸ two_ne_zero)).imp fun i s ↦ ?_, fun i ↦ .conj k ⟨diagonal 1 i, diagonal 2 i, ?_⟩⟩
  obtain ⟨rfl, c⟩ := inv_smul_eq_iff (g := toConjAct k).1 e, (Units.mul_inv_eq_iff_eq_mul _).1 c
  simp [← h, ← smul_mul', smul_comm (_ : ℂ), ↓smul_left_cancel_iff, mul_sub, sub_mul, smul_sub] at *
  all_goals simp_all [← ext_iff, diagonal_apply, vecMulVec, mul_comm]
  repeat grind [dotProduct, sum_eq_single i]

lemma heckeAlgebra.heckeCosetFn_conj (h : x ∈ levelGU n 𝔑) : heckeCosetFn f (x⁻¹ * g * x) =
  heckeCosetFn f g := by simpa [h] using! congr($(f.2.2 single_one_mem_levelSpace ⟨x, h⟩).1 g)

lemma heckeAlgebra.mem_GUPlus_of_ne_zero : heckeCosetFn f g ≠ 0 → g ∈ GUPlus E n :=
    (spanOn.exists_mem_of_cosetFn_ne_zero f.2.1 · |>.rec fun _ ⟨d,
  e⟩ ↦ by simpa using mul_mem d (mem_GUPlus_of_mem_levelGU (QuotientGroup.eq.1 e)))

lemma countTerm_mk {μ w y} : countTerm ε f w ⟦(x, y, μ)⟧ =
  ite (IsSignedFrame x (eigenReflection ε y μ)) (heckeCosetFn f (γ y x) * w
  y.1.charpoly μ) 0 := (@mk_out _ (orbitRel _ (MarkedTriple _ n)) (⟦x⟧, y, μ)).rec fun z
  (e : (⟦_⟧, z * y * _, μ) = _) ↦ (QuotientGroup.mk_out_eq_mul _ (toFinGL z * x)).rec fun k h ↦ by
  rw [← heckeAlgebra.heckeCosetFn_conj k.2, countTerm, ← e]
  simp [h, γ, ← ratConj_eigenReflection, mul_assoc _ _ k.1,
    ← isSignedFrame_mul_iff z k⁻¹.2.1]; group

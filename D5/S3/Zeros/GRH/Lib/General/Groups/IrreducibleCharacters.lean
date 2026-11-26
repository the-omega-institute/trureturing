/- GID: D5/S3/Zeros/GRH/Lib/General/Groups/IrreducibleCharacters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Groups/IrreducibleCharacters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Groups.IrreducibleCharacters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Groups/IrreducibleCharacters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.CentralProjections
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of group theory (textbook or folklore).

This file: Recognising irreducible and virtual characters by pairings; when a character's projector
vanishes. -/


open MonoidAlgebra Finset LinearMap ComplexConjugate Fint Matrix Algebra Representation Calc
variable {G H V} [Group G] [Finite G] [Group H] {χ f : G → ℂ} [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] {ρ : Representation ℂ G V} (Z) [CommSemiring Z] [Algebra Z ℂ]
attribute [local simp] basis algebraMap_eq_smul_one div_eq_inv_mul finMean FDRep.character character
  asAlgebraHom_eq_sum GroupAlgebra.average trace_tensorProduct'

/-- Let f be a class function on a finite group G. (1) f is an irreducible character if ⟨f,f⟩ =
1, Re f(1) ≥ 0 and some class function I has ⟨I,f⟩ ≠ 0 and ⟨χ,f⟩ ∈ ℤ for each character χ
with ⟨χ,I⟩ ≠ 0 and χ(1)⟨χ,I(·y)⟩ = ⟨χ,I⟩χ(y) for all y. (2) f is a Z-combination of
characters if all ⟨χ,f⟩ come from Z. (3) a ∈ ℂ[G](∑f(g)g)a if a acts as zero on every
finite-dimensional representation on which ∑f(g)g does. -/
lemma irreducible_criteria_of_isClassFunction (h : IsClassFunction f) : (∀ I, IsClassFunction I →
  classInner I f ≠ 0 → classInner f f = 1 → 0 ≤ (f 1).re → (∀ χ, IsChar χ → classInner χ I ≠ 0 →
  (∀ y, χ 1 * classInner χ (I <| · * y) = classInner χ I * χ y) → ∃ m : ℤ, classInner χ f = m) →
  IsIrrChar f) ∧ ((∀ χ, IsChar χ → ∃ m, classInner χ f = algebraMap Z ℂ m) → f ∈ virtualChars Z G) ∧
  ∀ a, (∀ V : FDRep ℂ G, asAlgebraHom V.ρ (groupAlgElem f) = 0 → asAlgebraHom V.ρ a = 0) → ∃ u, a =
  u * groupAlgElem f * a := by
  have ⟨n, d, _, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ ℂ[G]
  let ρ i := (lift ..).symm (toLinAlgEquiv'.toAlgHom.comp ((Pi.evalAlgHom ℂ _ i).comp e.toAlgHom))
  choose χ c v using fun i ↦ (⟨_, ⟨.of (dual (ρ i)), rfl⟩, by simp [← trace_toLin'_eq]; tauto⟩ :
    ∃ χ, IsChar χ ∧ χ 1 = d i ∧ ∀ y, (e (single y 1) i).trace = χ y⁻¹)
  choose a t using fun {f} (h : IsClassFunction (groupAlgElem f).coeff) i ↦
    (IsCentral.mem_center_iff ℂ).1
    (Set.center_pi.le (MulEquivClass.apply_mem_center e (Subring.mem_center_iff.2 h.commute)) i ⟨⟩)
  have w f h i y := (by simpa [IsChar.apply_inv, *, ·, mul_comm (f _), Finsupp.sum_fintype]
    using congr(($((groupAlgElem f * .single y⁻¹ 1).lift_unique e.toAlgHom) i).trace).symm) (@t f h)
  have u := by simpa using (w · · · 1)
  have S {f} h : f = ∑ i, classInner (χ i) f • χ i := funext fun g ↦
    (fun _ _ ↦ by simp_all [classInner, t h, traceAux, Matrix.trace, stdBasis, mul_assoc,
    toMatrix_apply, ← mul_sum, Fintype.sum_prod_type, Fintype.sum_sigma,
    ← single_eq_of_single_single]) (u f h) congr($(traceAux_eq ℂ ((Pi.basis fun _ ↦
    stdBasis ..).map e.symm.toLinearEquiv) (basis ..)) (mulLeft ℂ (groupAlgElem f * .single g⁻¹ 1)))
  use fun I _ z k _ H ↦ ?_, by grind [S h, sum_mem, algebraMap_smul, IsChar.mem_virtualChars,
    Subalgebra.smul_mem], fun _ H ↦ ⟨e.symm ((a h)⁻¹ • 1), e.injective (by
    ext1 i; by_cases z : a h i = 0; simpa [ρ, asAlgebraHom, t h, z] using H (.of (ρ i))
    simp [t h, z])⟩
  rw [congr(classInner $(S ‹_›)), classInner] at *
  simp [sum_mul, finMean_sum, mul_assoc, ← classInner.eq_1, RCLike.conj_mul, -finMean] at z k
  specialize S h; norm_cast at k; have ⟨i, _, z⟩ := exists_ne_zero_of_sum_ne_zero z
  have ⟨m, U⟩ := H _ (c i) (by grind) (by simp [*, classInner, field])
  simp +contextual [sum_eq_single i, by simpa using (fun j l p ↦ (k ▸ single_lt_sum l ‹_›
    (mem_univ j) p (by simp)).not_ge (by simp [U] at *; norm_cast; grind) :), U] at S k
  cases k <;> simp_all [classInner, IsIrrChar]; grind

/-- Let G be finite, i : G → H a homomorphism, χ a character of H, s ∈ H, ρ a finite-dimensional
complex representation of G. If the average over G of χ(i(g))·tr ρ(g) vanishes, then ∑_g
χ(i(g)s)·ρ(g) = 0. -/
lemma IsChar.groupAlgElem_eq_zero {χ} (h : IsChar χ) (i : G →* H) s (z :
  finMean (χ ∘ i * ρ.character) = 0) : ρ.asAlgebraHom (groupAlgElem (χ <| i · * s)) = 0 := by
  obtain ⟨τ, rfl⟩ := h
  simpa using congr(TensorProduct.lift (lsmul .. ∘ₗ _ ∘ₗ mulRight _ (τ.ρ s)) $(((homTensorHomEquiv
    ..).injective (by simpa using (tprod (τ.ρ.comp i) ρ).isProj_averageMap.isIdempotentElem
    |>.eq_zero_of_trace_eq_zero (by simp_all)) : ∑ u, _ ⊗ₜ ρ u = 0)))

lemma IsChar.groupAlgElem_eq_zero_iff (h : IsChar χ) : ρ.asAlgebraHom (groupAlgElem (conj ∘ χ)) =
  0 ↔ classInner χ ρ.character = 0 := ⟨(by simpa [classInner] using congrArg (trace ℂ V) ·),
  (by simpa using h.star.groupAlgElem_eq_zero (.id _) 1 ·)⟩

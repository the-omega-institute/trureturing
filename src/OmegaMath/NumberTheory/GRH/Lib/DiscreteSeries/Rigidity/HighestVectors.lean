import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.CommonEigenvectors
import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Rigidity.CasimirBound
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Supporting lemmas (textbook or folklore).

Part of: Lowest K-type and Casimir value determine a discrete series coefficient; analytic vectors
(known result; see Lib.DiscreteSeries.Rigidity.CasimirGrowth).

This file: Highest weight vectors exist; filtration steps are spanned by lowering words,
finite-dimensional. -/


open Finset Pi Submodule Module GlModule LinearMap End
variable {n} [Fintype n] {H} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε} {l :
  HCParam ε} {ρ : GlModule n H} {ν x s g} (hx : l.IsKHighest ρ ν x) [hg : l.HasGap g]

/-- For a list of index pairs (a, b), the vector ν + Σ (e_a − e_b): the weight of the product of
the E_ab applied to a vector of weight ν. -/
noncomputable def wordWeight (ν : n → ℤ) :=
  List.foldr (fun (a, b) ↦ (· + (single a 1 - single b 1))) ν

attribute [local simp] word wordWeight map_single_mul_single add_smul HCParam.IsKHighest
  hasEigenvalue_iff Submodule.eq_bot_iff
local add_aesop_rules 1% (by rw [apply_apply_eq_swap_add_bracket])

lemma HCParam.exists_highest_vector (W : Submodule ℂ H) [Module.Finite ℂ W] (h0 : W ≠ ⊥) (hW : ∀ a
  b, ε a = ε b → W ∈ (ρ.E a b).invtSubmodule) : ∃ μ : n → ℂ, ∃ v ∈ W, v ≠ 0 ∧ (∀ a, ρ.E a a v = μ
  a • v) ∧ ρ.IsCompactPrimitive l v := ({μ | _}.exists_max_image ((↑) ∘ l ⬝ᵥ · |>.re) (.subset (.pi'
  (finite_hasEigenvalue <| restrict _ <| hW · _ rfl)) (by simp; bound))
  (.right (exists_eigenvector_of_commute _ (hW · _ rfl) (by aesop) (U := ⊥) (.symm (by aesop))))
  ).imp fun μ ⟨⟨v, h⟩, H⟩ ↦ ⟨v, by simpa [h] using fun a b e f ↦ not_imp_comm.1 (H (μ +
  (single a 1 - single b 1)) ⟨_, by tauto, ·, by aesop⟩) (by simpa)⟩

include hx

lemma HCParam.IsKHighest.E_word_eq_wordWeight_smul w a : ρ.E a a (ρ.word w x) =
  (wordWeight ν w a : ℂ) • ρ.word w x ∧
  |wordWeight ν w a - ν a| ≤ w.length := by
  induction w <;> constructor <;> [aesop; aesop; aesop; (simp_all; grind)]

include hg

/-- Let l have distinct entries and x be K-highest. A subspace that is stable under the compact
lowering operators and contains all words of length ≤ s in the E_ab applied to x contains
M_s, where M_0 = U(𝔨)x, M_{s+1} = M_s + 𝔤M_s. -/
lemma HCParam.IsKHighest.filtration_le_of_word_mem : let Q T := ∀ a b, ε a = ε b → l a < l b →
    T ∈ (ρ.E a b).invtSubmodule
  ∀ T, Q T → (∀ w, w.length ≤ s → ρ.word w x ∈ T) → ρ.filtration ε x s ≤ T := by
  intro Q T o g
  have k r {T} : Q T → Q ((pi (Prod.map ε ε ⁻¹' r) fun _ ↦ T).comap (.pi ρ.E.uncurry)) := by aesop
  induction' s with s i generalizing T
  apply sInf_le_of_le _ (sInf_le (s := {T | Q T ∧ x ∈ T}) (by simp_all))
  simpa using fun a b e y u T o t ↦ u _ (k (.diagonal _) o)
    (by simp_all; grind [smul_mem, zero_mem, HasGap]) (a, b) e
  simp! [map_le_iff_le_comap]
  use by grind, fun a b _ ↦ (i _ (k ⊤ o) (fun w e p _ ↦ g (w.cons p) (by simpa)) · (a, b) ⟨⟩)

lemma HCParam.IsKHighest.finite_filtration (h : IsUnitaryCasimirGe l ρ) s :
  Module.Finite ℂ (ρ.filtration ε x s) := s.rec (.of_fg ((fg_span ((((List.finite_length_le _
  (l ⬝ᵥ (ν + ν + l) + l.casimirKValue ν).toNat).image (ρ.word · x)).insert 0).subset (by
  rintro _ ⟨m, w, _, rfl⟩; by_contra
  obtain ⟨_, t⟩ := dotProduct_self_star_nonneg (l + wordWeight ν w), (sum_le_sum fun a _ ↦
    single_le_sum (a := a) (by aesop) (by simp)).trans congr($(casimirK_eq_smul_of_mem_filtration m
    hx.casimirK_eq_smul ▸ h.inner_casimir _).re).ge
  simp_all [star_trivial, hx.E_word_eq_wordWeight_smul, norm_smul, mul_pow, ← sum_mul,
    ← Complex.ofReal_pow, -word]
  simp_all [dotProduct]; norm_cast at t; grind : ↑(ρ.filtration ε x 0) ∩ (ρ.word · x) ''
  {w | w.length ≤ l ⬝ᵥ (ν - wordWeight ν w)} ⊆ _))).of_le (hx.filtration_le_of_word_mem _ (fun a b e
  c ↦ mapsTo_span fun _ ⟨t, w, _⟩ ↦ ⟨E_mem_filtration t e, w.cons (a, b), by simp_all; lia⟩)
  fun | [], _ => subset_span ⟨self_mem_filtration, [], by simp⟩))) fun _ _ ↦ finite_sup ..

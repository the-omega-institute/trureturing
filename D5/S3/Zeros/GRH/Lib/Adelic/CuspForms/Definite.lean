/- GID: D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/Definite
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/CuspForms/Definite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.CuspForms.Definite. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/CuspForms/Definite.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Reduction.Defs
import D5.S3.Zeros.GRH.Lib.Adelic.Transference.MassBasic
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

Continuous automorphic functions on definite groups are rapidly decreasing, by compactness. -/

open Function Space EuclideanSpace Matrix.Norms.L2Operator

/-- The shortest vector length, cut off at 1 (`Space.firstMinimum`), of the lattice of V ⊕ W at (g,
h) is at least the minimum of those of V at g and W at h. -/
lemma inf_le_firstMinimum_sum {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] {s s' g h} {V :
  Space E n s} {W : Space E n' s'} : (V.move g).firstMinimum ⊓ (W.move h).firstMinimum ≤
  ((V.sum W).move (.sum (g, h))).firstMinimum := by
  simp [↓le_firstMinimum_iff, ne_iff]
  use fun y a ↦ .imp ?_ ?_ <;> intro <;> grw [firstMinimum_le _ (ne_iff.2 ‹_›)] <;> simp_all
    [norm_eq, archCoords, baseLattice, ↓move_vecAtPoint, vecAtPoint, sum, comp_def, ← map_inv,
    Fintype.sum_prod_type, Matrix.fromBlocks_mulVec] <;> gcongr <;> simp <;> positivity

namespace Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] {s} {V : Space E n s} {F M B K}

lemma one_le_height g : 1 ≤ V.height g := by simp [height, one_le_inv₀, firstMinimum_pos]

@[simp] lemma height_pos g : 0 < V.height g := by grind [one_le_height]

attribute [local simp] le_of_lt mul_assoc

/-- For compact K ⊆ G there is C ≥ 1 with ht(k) ≤ C·ht(g) whenever g⁻¹γk ∈ K for some γ ∈ Γ. -/
lemma exists_height_le_mul (h : IsCompact K) :
    ∃ C ≥ 1, ∀ γ g k, g⁻¹ * V.ratEmbed γ * k ∈ K → V.height k ≤ C * V.height g := by
  obtain ⟨⟨c, hc, H⟩, R, hR⟩ := V.exists_smul_mulVec_mem_latticeBall (h.image_auto (·.2)),
    h.exists_bound_of_continuousOn (f := (·.1 · |>.1.1)) (by fun_prop)
  use 1 ⊔ c * R, by simp, fun γ g k m ↦ inv_le_of_inv_le₀ (by simp) ?_
  simp [le_firstMinimum_iff, height, field]
  use (H ⟨_, m, rfl⟩ (norm_le_pi_norm _) · · |>.elim fun p q b ↦ by grw [firstMinimum_le p (by
    simpa [*] using! (smul_ne_zero_iff_ne γ).2 b), q, hR _ m, ← le_max_right])

lemma exists_mul_height_pow_le (h : IsCompact K) C : ∃ D, ∀ᵉ (g) (γ ∈ V.Γ), γ * g ∈ K →
  C * V.height g ^ B ≤ D :=
  ⟨_, fun _ _ ⟨γ, _⟩ ↦ by grw [le_abs_self C, (exists_height_le_mul h).choose_spec.2 γ 1] <;> aesop⟩

lemma IsRapid.bounded : V.IsRapid F → ∃ C, ∀ g, ‖F g‖ ≤ C := (by simpa using · 0)

lemma IsRapid.mul : V.IsRapid F → V.IsModerate M → V.IsRapid (M * F) | h, ⟨C, _, b⟩, _ => ⟨_, (by simp; grw
          [b ·, le_abs_self C, mul_mul_mul_comm, ← pow_add, mul_assoc, (h _).choose_spec] <;> simp)⟩

lemma IsRapid.comp_mul_right (h : V.IsRapid F) {x} : V.IsRapid (F <| · * x) | B => ⟨_, (by
  grw [(exists_height_le_mul isCompact_singleton).choose_spec.2 1 _ ·, mul_pow, mul_left_comm,
    le_abs_self (_ ^ B), (h B).choose_spec] <;> aesop)⟩

lemma IsRapid.integrable : V.IsRapid F → Continuous F → MeasureTheory.Integrable F V.quotMeasure :=
  (IsBoundedMeasurable.of ·.bounded · |>.memLp_top.integrable le_top)

/-- The automorphic functions of rapid decay for the space V, as a subrepresentation of the
complex functions on G under right translation by G_f. -/
noncomputable def rapidFunctions : Subrepresentation (finRightRep E s) := ⟨.ofLinearComb {y |
  V.IsAutomorphic y ∧ V.IsRapid y} ⟨0, isAutomorphic_const .., (⟨·, by simp⟩)⟩ fun _ ⟨a, c⟩ _ ⟨b,
  d⟩ u v ↦ ⟨a.map₂ b
  (u * · + v * ·), fun _ ↦ ⟨_, (by simp; grw [norm_add_le, add_mul] <;> simp; grw [(c _).choose_spec
  ·, (d _).choose_spec])⟩⟩, fun _ _ ↦ .imp (·.comp_mul_right _) (·.comp_mul_right)⟩

end Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] {s} {V : Space E n s} {F}

lemma Space.isRapid_of_isCocompact : Continuous F → V.Γ.FixesLeft F → V.Γ.Cocpt → V.IsRapid F
  | c, h, ⟨_, K, H⟩, _ => ⟨_, (H · |>.elim fun γ _ ↦ by grw [← h γ, (K.exists_bound_of_continuousOn
    c.continuousOn).choose_spec,
    (exists_mul_height_pow_le K _).choose_spec _ γ] <;> simp_all [le_of_lt])⟩

lemma Space.IsAutomorphic.mem_rapidFunctions (h : V.IsAutomorphic F) (d : ∀ i j, s i =
  s j := by simp) :
  F ∈ V.rapidFunctions := ⟨h, isRapid_of_isCocompact h.1 h.2 (V.exists_isCompact_of_definite d)⟩

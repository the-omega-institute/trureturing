/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Main/HeckeOperatorOfFunction
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Main/HeckeOperatorOfFunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Main.HeckeOperatorOfFunction. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/HeckeOperatorOfFunction.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel.NeatLevel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local matching)
(known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Hecke polynomial coefficients, monic of degree n; jumps are distinct. Left translation;
operators attached to test functions and their products with Hecke operators. -/

open Polynomial Finset Set
variable {E n M : Type} [Field E] [CMType E] [Fintype n]

@[simp] lemma coeff_heckePoly {R} [CommRing R] q N t j : (@heckePoly R _ q N t).coeff j =
    (ite (j ≤ N) ((-1) ^ (N - j) * q ^ (N - j).choose 2) 0 : ℤ) * t (N - j) := by
  simp [heckePoly, -map_mul]; grind [sum_eq_single (N - j)]

lemma HasHeckePolyAt.isMonicOfDegree {f : Gf E n → M → ℂ} (hf : f ≠ 0) {w hw P} :
  HasHeckePolyAt f w hw P → P.IsMonicOfDegree (Fintype.card n) :=
  fun ⟨k, t, h, ht⟩ ↦ by simp_all [isMonicOfDegree_iff, heckeSplit, natDegree_le_iff_coeff_eq_zero,
  not_le.2, ← smul_left_inj hf, ← ht, heckeGL_zero, mem_sphericalAt_iff hw]

lemma Weight.nodup_jumps {E : Type} [Field E] [CMType E] (κ : Weight E) N σ : (jumps κ N σ).Nodup :=
  .map (.of_lt_imp_ne fun i j
  h ↦ by grind [sum_mono_set (κ.1 (.mk σ)) (Finset.Ioo_subset_Ioo h.le N.le_refl)]) List.nodup_range

variable {G G' W : Type _} [Group G] [Group G'] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ G W) (K : Subgroup G) {J : Subgroup G'} {f : G → ℂ} {F : G' → ℂ}
  (T : Module.End ℂ (levelSpace π K))

attribute [local simp] indicator mul_mem_cancel_left mul_assoc heckeFun_sum

/-- The left regular representation of G on functions G → ℂ: (g·F)(x) = F(g⁻¹x). -/
def leftTranslation : Representation ℂ G (G → ℂ) :=
  ⟨⟨fun g ↦ .funLeft _ _ (g⁻¹ * ·), by aesop⟩, by aesop⟩

/-- The function f is right K-invariant and nonzero on finitely many cosets gK, and T is the
operator Σ_{g ∈ G/K} f(g)π(g) on the K-fixed vectors. -/
def IsOperatorOf f := ∃ a, f = (cosetFn K a · : G → _) ∧ ∀ v, T v = π.asAlgebraHom a v

variable {π K T}

lemma indicator_subgroup_mul_left {k g} : k ∈ K → indicator K 1 (k * g) =
  (indicator K 1 g : ℂ) := by aesop

lemma IsOperatorOf.heckeFun_mul {φ a s} (hF : HasFiniteCosets J F) (e : φ =
  heckeFun (leftTranslation.comp a) J F f) : IsOperatorOf π K T f →
  IsOperatorOf π K ((heckeFun (π.comp a) J F).restrict s * T) φ := .imp' (∑ q ∈ hF.toFinset,
  .single (a q.out) (F q.out) * ·) (by simp_all [cosetFn, funext_iff, leftTranslation])

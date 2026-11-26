import OmegaMath.NumberTheory.GRH.Lib.Shimura.Uniformisation.Frames
import OmegaMath.NumberTheory.GRH.Lib.Weil.Unramified.SphericalHecke
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hecke algebra of a pair and its action by correspondences on the base of a tower (known
result; see Lib.Shimura.HeckeTower.WildType).

This file: spans in the group ring k[G]; elements sending K-fixed vectors to eigenvectors. -/

noncomputable section

open MonoidAlgebra Submodule QuotientGroup Representation


variable {G} (k) [Group G] [CommRing k] (K : Subgroup G)

/-- The submodule of the group ring k[G] spanned by the elements of the subset D. -/
def spanOn D := span k (of k G '' D)

variable {k} {a b W} [AddCommGroup W] [Module k W]

/-- For a representation π of G on a k-module W, an element a = ∑ a_g [g] of the group ring k[G]
acts as ∑ a_g π(g), summed over the support of a. -/
lemma asAlgebraHom_eq_sum_support (π : Representation k G W) :
    π.asAlgebraHom a = ∑ g ∈ a.coeff.support, a.coeff g • π g := rfl

/-- For a = ∑ a_g [g] in k[G], the finitely supported function on G ⧸ K whose value at a coset
is the sum of the a_g over g in it. -/
@[local simp] def cosetFn a := ((ofMulAction k G (G ⧸ K)).asAlgebraHom a (.single ⟦1⟧ 1)).coeff

/-- The a in k[G] that, in every representation π, send K-fixed vectors to χ-eigenvectors of the
subgroup J of H acting by π∘ι; by default J = ι⁻¹(K), χ = 1. -/
def fixedToEigen {H} [Group H] (ι : H →* G) (J := K.comap ι) (χ : J →* k := 1) : Submodule k
  k[G] := by use! {a | ∀ ⦃W⦄ [AddCommGroup.{0} W] [Module k W] ⦃π⦄ ⦃v : W⦄, v ∈ levelSpace π K →
  π.asAlgebraHom a v ∈ levelSpace (π.comp ι) J χ} <;> simp_all [smul_smul, mul_comm]

variable {K} {D D' D'' : Set G} (h : a ∈ spanOn k D)

/-- For ψ from G/K to a k-module W, the linear map sending a = ∑ a_g [g] in k[G] to ∑ a_g ψ(gK). -/
def Model.cosetSum (ψ : _ → W) a := (cosetFn K a).linearCombination k ψ

lemma single_one_mem_levelSpace : .single (mk 1) 1 ∈ levelSpace (ofMulAction k G (G ⧸ K)) K :=
  (by simp [← mk_mul_of_mem 1 ·.2])

include h

lemma spanOn.exists_mem_of_cosetFn_ne_zero {q} : _root_.cosetFn K a q ≠ 0 → ∃ d ∈ D, d = q :=
  Function.mtr (by induction h using span_induction <;> aesop)

lemma spanOn.mul (h' : b ∈ spanOn k D') (H : ∀ g ∈ D, ∀ g' ∈ D', g * g' ∈ D'') : a * b ∈ spanOn k
  D'' := span_mono (by rintro _ ⟨⟩; grind) ((span_mul_span ..).le (mul_mem_mul h h'))

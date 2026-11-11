/- GID: D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Coinvariants]
   utility: none
   digest: Trace one inverts the native norm; nonzero kernel order supplies a semilinear scalar. -/

import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Ring.Aut
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
The unnormalized norm on native R-coinvariants is inverted by a conjugation-trace-one
endomorphism. For a genuinely semilinear action, Dedekind independence on the finite
image and the kernel-fiber cardinality construct a trace-one scalar without dividing
by the image order. No coefficient-projectivity or dimension hypothesis is used.
This is the classical trace-one mechanism, not a literature novelty claim.
-/

set_option autoImplicit false

universe uR uG uV uK

namespace D5.S3.FiniteGroups.GroupAlgebra.SemilinearKernelNorm

open Representation

section TraceOne

variable {R : Type uR} {G : Type uG} {V : Type uV}
  [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- The canonical unnormalized norm on the native coinvariants `V / Coinvariants.ker ρ`. -/
noncomputable def coinvariantsNorm : ρ.Coinvariants →ₗ[R] ρ.invariants :=
  Coinvariants.lift ρ
    (LinearMap.codRestrict ρ.invariants ρ.norm fun v =>
      (mem_invariants ρ _).2 fun g => self_norm_apply ρ g v) fun g => by
    apply LinearMap.ext
    intro v
    exact Subtype.ext (norm_self_apply ρ g v)

@[simp] theorem coinvariantsNorm_mk (v : V) :
    (coinvariantsNorm ρ (Coinvariants.mk ρ v) : V) = ρ.norm v := rfl

/-- A supplied conjugation-trace-one endomorphism inverts the actual norm.
There is no projectivity, finite generation or dimension hypothesis on `V`. -/
noncomputable def traceOneNormEquiv (t : Module.End R V)
    (ht : (∑ g : G, (ρ g).comp (t.comp (ρ g⁻¹))) = LinearMap.id) :
    ρ.Coinvariants ≃ₗ[R] ρ.invariants := by
  classical
  have htrace (v : V) : (∑ g : G, ρ g (t (ρ g⁻¹ v))) = v := by
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun ht v
  let inv : ρ.invariants →ₗ[R] ρ.Coinvariants :=
    (Coinvariants.mk ρ).comp (t.domRestrict ρ.invariants)
  refine LinearEquiv.ofLinearMap (coinvariantsNorm ρ) inv ?_ ?_
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ.norm (t (v : V)) = (v : V)
    have hv := (mem_invariants ρ (v : V)).mp v.property
    simpa only [Representation.norm, LinearMap.sum_apply, hv] using htrace (v : V)
  · apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ q
    change Coinvariants.mk ρ (t (ρ.norm v)) = Coinvariants.mk ρ v
    have hnorm : ρ.norm v = ∑ g : G, ρ g⁻¹ v := by
      simp only [Representation.norm, LinearMap.sum_apply]
      refine Fintype.sum_bijective (fun g : G => g⁻¹) inv_bijective _ _ ?_
      intro g
      rw [inv_inv]
    calc
      _ = ∑ g : G, Coinvariants.mk ρ (t (ρ g⁻¹ v)) := by
        rw [hnorm]
        simp only [map_sum]
      _ = ∑ g : G, Coinvariants.mk ρ (ρ g (t (ρ g⁻¹ v))) := by
        simp only [Coinvariants.mk_self_apply]
      _ = Coinvariants.mk ρ v := by rw [← map_sum, htrace]

@[simp] theorem traceOneNormEquiv_mk (t : Module.End R V)
    (ht : (∑ g : G, (ρ g).comp (t.comp (ρ g⁻¹))) = LinearMap.id) (v : V) :
    (traceOneNormEquiv ρ t ht (Coinvariants.mk ρ v) : V) = ρ.norm v :=
  coinvariantsNorm_mk ρ v

@[simp] theorem traceOneNormEquiv_symm_apply (t : Module.End R V)
    (ht : (∑ g : G, (ρ g).comp (t.comp (ρ g⁻¹))) = LinearMap.id)
    (w : ρ.invariants) :
    (traceOneNormEquiv ρ t ht).symm w = Coinvariants.mk ρ (t (w : V)) := rfl

end TraceOne

section SemilinearScalar

variable {R : Type uR} {G : Type uG} {V : Type uV} {K : Type uK}
  [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V]
  [Field K] [Algebra R K] [Module K V] [IsScalarTower R K V]
  (ρ : Representation R G V) (γ : G →* (K ≃+* K))
  (hρ : ∀ (g : G) (a : K) (v : V), ρ g (a • v) = γ g a • ρ g v)

/-- Multiplication by `c` is K-linear, restricted here to the coefficient ring R. -/
def scalarTraceEnd (c : K) : Module.End R V :=
  (LinearMap.lsmul K V c).restrictScalars R

@[simp] theorem scalarTraceEnd_apply (c : K) (v : V) :
    scalarTraceEnd (R := R) c v = c • v := rfl

include hρ in
theorem scalar_conjugation_trace_one (c : K) (hc : (∑ g : G, γ g c) = 1) :
    (∑ g : G, (ρ g).comp
      ((scalarTraceEnd (R := R) (V := V) c).comp (ρ g⁻¹))) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, scalarTraceEnd_apply,
    hρ, self_inv_apply, LinearMap.id_apply]
  rw [← Finset.sum_smul, hc, one_smul]

/-- A scalar of trace one inverts the norm for an arbitrary semilinear action.
The action and norm are R-linear; coinvariants use the R-span, not the K-span.
No invertibility of the whole group order is imposed. -/
noncomputable def semilinearScalarNormEquiv (c : K) (hc : (∑ g : G, γ g c) = 1) :
    ρ.Coinvariants ≃ₗ[R] ρ.invariants :=
  traceOneNormEquiv ρ (scalarTraceEnd (R := R) c)
    (scalar_conjugation_trace_one ρ γ hρ c hc)

@[simp] theorem semilinearScalarNormEquiv_mk (c : K)
    (hc : (∑ g : G, γ g c) = 1) (v : V) :
    (semilinearScalarNormEquiv ρ γ hρ c hc (Coinvariants.mk ρ v) : V) = ρ.norm v :=
  traceOneNormEquiv_mk ρ _ _ v

@[simp] theorem semilinearScalarNormEquiv_symm_apply (c : K)
    (hc : (∑ g : G, γ g c) = 1) (w : ρ.invariants) :
    (semilinearScalarNormEquiv ρ γ hρ c hc).symm w =
      Coinvariants.mk ρ (c • (w : V)) :=
  traceOneNormEquiv_symm_apply ρ _ _ w

end SemilinearScalar


section SemilinearKernelScalar

variable {G : Type uG} {K : Type uK} [Group G] [Fintype G] [Field K]
  (γ : G →* (K ≃+* K))

/-- Sum over the faithful image; the field and its automorphism group need not be finite. -/
noncomputable def semilinearImageTrace (b : K) : K := by
  classical
  exact ∑ σ : γ.range, (σ : K ≃+* K) b

/-- Left translation in the image fixes the image trace, even in modular characteristic. -/
theorem semilinearImageTrace_fixed (σ : γ.range) (b : K) :
    (σ : K ≃+* K) (semilinearImageTrace γ b) = semilinearImageTrace γ b := by
  classical
  simp only [semilinearImageTrace, map_sum]
  change (∑ τ : γ.range, ((σ * τ : γ.range) : K ≃+* K) b) =
    ∑ τ : γ.range, (τ : K ≃+* K) b
  exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ fun _ => rfl

/-- Dedekind independence makes the image trace nonzero without dividing by the image order. -/
theorem exists_semilinearImageTrace_ne_zero :
    ∃ b : K, semilinearImageTrace γ b ≠ 0 := by
  classical
  let f : γ.range → (K →* K) := fun σ => (σ : K ≃+* K).toMonoidHom
  have hf : Function.Injective f := by
    intro σ τ hστ
    apply Subtype.ext
    apply RingEquiv.ext
    intro x
    exact DFunLike.congr_fun hστ x
  have hi : LinearIndependent K
      (fun σ : γ.range => fun x : K => (σ : K ≃+* K) x) :=
    (linearIndependent_monoidHom K K).comp f hf
  by_contra h
  have hz (b : K) : semilinearImageTrace γ b = 0 := by
    by_contra hb
    exact h ⟨b, hb⟩
  have hfun : (∑ σ : γ.range, (fun x : K => (σ : K ≃+* K) x)) =
      (0 : K → K) := by
    funext b
    simpa only [Finset.sum_apply, Pi.zero_apply, semilinearImageTrace] using hz b
  have hone : (1 : K) = 0 := by
    apply (Fintype.linearIndependent_iff.mp hi) (fun _ => (1 : K)) ?_ (1 : γ.range)
    simpa only [one_smul] using hfun
  exact one_ne_zero hone

/-- Each image element has exactly `Nat.card γ.ker` preimages. This identity does not
assume that cardinal is nonzero in K and does not assume G is commutative. -/
theorem semilinear_sum_eq_kernel_mul_imageTrace (b : K) :
    (∑ g : G, γ g b) = (Nat.card γ.ker : K) * semilinearImageTrace γ b := by
  classical
  have hcard (σ : γ.range) :
      Fintype.card {g : G // γ.rangeRestrict g = σ} = Nat.card γ.ker := by
    rw [← Nat.card_eq_fintype_card]
    calc
      _ = Nat.card γ.rangeRestrict.ker :=
        Nat.card_congr
          (MonoidHom.fiberEquivKerOfSurjective γ.rangeRestrict_surjective σ)
      _ = Nat.card γ.ker := by rw [MonoidHom.ker_rangeRestrict]
  calc
    (∑ g : G, γ g b) =
        ∑ σ : γ.range, ∑ _g : {g : G // γ.rangeRestrict g = σ},
          (σ : K ≃+* K) b :=
      (Fintype.sum_fiberwise' γ.rangeRestrict
        (fun σ : γ.range => (σ : K ≃+* K) b)).symm
    _ = ∑ σ : γ.range, (Nat.card γ.ker : K) * (σ : K ≃+* K) b := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard σ]
    _ = (Nat.card γ.ker : K) * semilinearImageTrace γ b := by
      rw [← Finset.mul_sum]
      rfl

/-- The sharp scalar criterion for an arbitrary action. Choose b with nonzero image
trace s and take `c = b / (|ker γ| * s)`. The image order need not be invertible. -/
theorem exists_semilinearScalarTraceOne_iff :
    (∃ c : K, (∑ g : G, γ g c) = 1) ↔ (Nat.card γ.ker : K) ≠ 0 := by
  classical
  constructor
  · rintro ⟨c, hc⟩ hker
    rw [semilinear_sum_eq_kernel_mul_imageTrace γ c, hker, zero_mul] at hc
    exact zero_ne_one hc
  intro hker
  obtain ⟨b, hb⟩ := exists_semilinearImageTrace_ne_zero γ
  have hfixed (g : G) : γ g (semilinearImageTrace γ b) = semilinearImageTrace γ b :=
    semilinearImageTrace_fixed γ (γ.rangeRestrict g) b
  refine ⟨b / ((Nat.card γ.ker : K) * semilinearImageTrace γ b), ?_⟩
  calc
    (∑ g : G, γ g (b / ((Nat.card γ.ker : K) * semilinearImageTrace γ b))) =
        (∑ g : G, γ g b) / ((Nat.card γ.ker : K) * semilinearImageTrace γ b) := by
      simp only [map_div₀, map_mul, map_natCast, hfixed, Finset.sum_div]
    _ = 1 := by
      rw [semilinear_sum_eq_kernel_mul_imageTrace γ b]
      exact div_self (mul_ne_zero hker hb)

end SemilinearKernelScalar

section SemilinearKernelNorm

variable {R : Type uR} {G : Type uG} {V : Type uV} {K : Type uK}
  [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V]
  [Field K] [Algebra R K] [Module K V] [IsScalarTower R K V]

/-- For any genuinely γ-semilinear R-linear action, construct the scalar and the actual
unnormalized norm isomorphism together. Coinvariants are the native R-coinvariants.
There is no dimension, projectivity, faithfulness, or whole-group-order hypothesis. -/
theorem exists_semilinearKernelNormEquiv
    (ρ : Representation R G V) (γ : G →* (K ≃+* K))
    (hρ : ∀ (g : G) (a : K) (v : V), ρ g (a • v) = γ g a • ρ g v)
    (hker : (Nat.card γ.ker : K) ≠ 0) :
    ∃ (c : K) (e : ρ.Coinvariants ≃ₗ[R] ρ.invariants),
      (∑ g : G, γ g c) = 1 ∧
      (∀ v : V, (e (Coinvariants.mk ρ v) : V) = ρ.norm v) ∧
      (∀ w : ρ.invariants, e.symm w = Coinvariants.mk ρ (c • (w : V))) := by
  classical
  obtain ⟨c, hc⟩ := (exists_semilinearScalarTraceOne_iff γ).mpr hker
  refine ⟨c, semilinearScalarNormEquiv ρ γ hρ c hc, hc, ?_, ?_⟩
  · intro v
    exact semilinearScalarNormEquiv_mk ρ γ hρ c hc v
  · intro w
    exact semilinearScalarNormEquiv_symm_apply ρ γ hρ c hc w

end SemilinearKernelNorm

end D5.S3.FiniteGroups.GroupAlgebra.SemilinearKernelNorm

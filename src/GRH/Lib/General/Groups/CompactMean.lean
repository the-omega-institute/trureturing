import GRH.Lib.Adelic.Hecke.ClassMean
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

This file: Smooth and unitary representations; averaging projector over a compact subgroup. -/

noncomputable section

open Subgroup Topology ComplexOrder DoubleCoset Module


variable {G V W} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ G V) (H : Subgroup G) {x} [TopologicalSpace G]

/-- The representation ρ is smooth: every vector is fixed by all g in some neighbourhood of 1. -/
class IsSmoothRep (ρ : Representation ℂ G V) where eventually_fixed x : ∀ᶠ g in 𝓝 1, ρ g x = x

/-- The sesquilinear form B is positive definite and invariant under ρ. -/
def IsUnitary (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) := (∀ x ≠ 0, 0 < B x x) ∧ ∀ a x y, B (ρ a x) (ρ a y) = B x y

local instance : Module ℚ V := .restrictScalars ℚ ℂ V

instance : Unique (@Quotient G _ {1} .univ) := ⟨⟨⟦1⟧⟩,
  (·.out_eq ▸ ((eq (H := ⊥) (K := ⊤)).2 (by simp)).symm)⟩

variable [IsTopologicalGroup G] [IsSmoothRep ρ] [CompactSpace H]

instance [h : CompactSpace G] :
  @HasFiniteType G _ ⊥ ⊤ _ := by constructor <;> simp [Fintype.finite, h.1]

@[local simp ↓] lemma orbit_mem_smoothInvariants x : (fun p : H × H ↦
  ρ (p.1⁻¹ * p.2) x) ∈ smoothInvariants ⊥ := ⟨by simp,
  isOpen_of_mem_nhds _ (by simpa using! (isCompact_univ.eventually_forall_of_forall_eventually
  fun _ _ ↦ by simpa [← ρ.inv_apply_eq_iff, ← End.mul_apply, ← map_mul] using!
  Continuous.tendsto' (by fun_prop) (1, _) _ (by simp) (IsSmoothRep.eventually_fixed x)))⟩

/-- For a smooth representation ρ and a compact subgroup H, the mean of ρ over H: it sends x to
the mean of ρ(a⁻¹b)x over (a, b) in H × H. -/
@[irreducible] def compactMean : End ℂ V := ⟨⟨(classIntegral ⊥ ⊤ fun p : H × H ↦ ρ (p.1⁻¹ * p.2) ·),
  by simp [↓← classIntegral_add, Pi.add_def]⟩,
  fun c _ ↦ map_classIntegral (DistribSMul.toAddMonoidHom V c) 1⟩

variable {ρ H B} (hB : IsUnitary ρ B) {K : Subgroup G} {σ : ℂ →+* ℂ} (φ : V →ₛₗ[σ] W)
unseal compactMean

@[simp] lemma apply_compactMean {h} (hh : h ∈ H) x : ρ h (compactMean ρ H x) = compactMean ρ H x :=
  .symm (map_classIntegral (ρ h).toAddMonoidHom (⟨h, hh⟩, 1))

@[simp] lemma compactMean_apply {h} (hh : h ∈ H) x : compactMean ρ H (ρ h x) = compactMean ρ H x :=
  map_classIntegral (.id _) (1, ⟨h, hh⟩)

lemma map_compactMean_of_const {c} (h : ∀ h ∈ H, φ (ρ h x) = c) : φ (compactMean ρ H x) = c := by
  erw [← map_classIntegral φ.toAddMonoidHom 1 (o := fun _ ↦ (h _ (by aesop)).symm)]
  simp [classIntegral_eq_classSum, classSum, eq_top_iff']

/-- Let ρ be smooth, H a compact subgroup, φ linear and invariant under a subgroup K. If each k
∈ H has some u with gug⁻¹ ∈ K and ρ(u⁻¹k)x = x, then φ(ρ(g)x') = φ(ρ(g)x) for x' the mean of
x over H. -/
lemma map_compactMean_of_factor {φ : V →ₗ[ℂ] W} {g} (hφ : ∀ k ∈ K, ∀ z, φ (ρ k z) = φ z) (h :
  ∀ k ∈ H, ∃ u, g * u * g⁻¹ ∈ K ∧ ρ (u⁻¹ * k) x = x) : φ (ρ g (compactMean ρ H x)) = φ (ρ g x) :=
  map_compactMean_of_const
  (φ ∘ₗ _) (h · · |>.elim fun _ ⟨p, q⟩ ↦ by simpa using (hφ _ p _).trans congr(φ (ρ g $q)))

lemma compactMean_mem_levelSpace x : compactMean ρ H x ∈ levelSpace ρ H := by simp

@[simp] lemma compactMean_eq_self x (h : x ∈ levelSpace ρ H 1) : compactMean ρ H x = x :=
  map_compactMean_of_const .id (by aesop)

include hB

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep ρ] in
/-- For an invariant scalar product B, the adjoint of ρ(g) is ρ(g⁻¹): B(ρ(g)x, y) = B(x,
ρ(g⁻¹)y). -/
lemma IsUnitary.adjoint_eq_inv g x y : B (ρ g x) y = B x (ρ g⁻¹ y) := by simp [← hB.2 g x]

/-- For ρ smooth with invariant scalar product B, the mean of ρ over a compact subgroup H
(`compactMean`) is self-adjoint for B. -/
lemma IsUnitary.compactMean_adjoint x y : B (compactMean ρ H x) y = B x (compactMean ρ H y) :=
  (map_compactMean_of_const _ fun _ m ↦ congr(B $(apply_compactMean m x) _).symm.trans
  (hB.2 ..)).symm.trans (map_compactMean_of_const (B.flip _) (by simp_all [adjoint_eq_inv]))

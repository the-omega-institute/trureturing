import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.Base
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Continuous cocycles, coboundaries, H² and functoriality for discrete modules. -/

noncomputable section


open Submodule DistribMulAction
variable {R G M H N} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M) [Group H] [TopologicalSpace
  H] [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N] {ρ' : Representation R
  H N} (φ : H →ₜ* G) (u : M →ₗ[R] N) (h : ∀ g m, u (ρ (φ g) m) = ρ' g (u m) := by bound)

instance (priority := 100) : ContinuousConstSMul R M := ⟨by fun_prop⟩

/-- The continuous 1-cocycles of ρ: the R-module of continuous f: G → M with f(gh) = f(g) +
ρ(g)f(h). -/
def Z1 := mk (R := R) ⟨⟨{f | Continuous f ∧ ∀ g h, f (g * h) = f g + ρ g (f h)},
  by simp_all [Continuous.add, add_add_add_comm]⟩, by continuity⟩ (by continuity)

/-- The R-linear map from M to functions G → M sending m to g ↦ ρ(g)m − m. -/
abbrev d0 := LinearMap.pi (ρ · - .id)

/-- The continuous 2-cocycles of ρ: continuous f: G × G → M with ρ(g)f(h,k) − f(gh,k) + f(g,hk)
− f(g,h) = 0. -/
def Z2 := ofLinearComb (R := R) {f | Continuous f ∧ ∀ g h k, f (g * h, k) = f (g, h * k) - f (g, h)
  + ρ g (f (h, k))} ⟨0, by continuity⟩ fun _ ⟨_, _⟩ _ ⟨_, _⟩ _ _ ↦
  ⟨by fun_prop, by intros; simp [*]; module⟩

/-- The 2-coboundaries of ρ: functions (g,h) ↦ ρ(g)c(h) − c(gh) + c(g) on G × G with c: G → M
continuous. -/
def B2 := ofLinearComb (R := R) {f : G × G → M | ∃ c, Continuous c ∧ ∀ g h, f (g, h) = ρ g (c h) -
  c (g * h) + c g} ⟨0, 0, by continuity⟩ fun _ ⟨c, _, _⟩ _ ⟨d, _, _⟩ a b ↦
  ⟨a • c + b • d, by fun_prop, by intros; simp [*]; module⟩

/-- Continuous cohomology H²(G,M): continuous 2-cocycles of ρ modulo coboundaries of continuous
1-cochains. -/
@[instance_reducible] def H2 := _ ⧸ (B2 ρ).comap (Z2 ρ).subtype deriving AddCommGroup, Module R

variable {ρ}

/-- For a continuous homomorphism φ: H → G and linear u: M → N with uρ(φg) = ρ'(g)u, the
additive map f ↦ u∘f∘φ from continuous 1-cocycles of ρ to those of ρ'. -/
abbrev pairMapZ1 : Z1 ρ →+ Z1 ρ' := ⟨⟨fun f ↦ ⟨(u <| f.1 <| φ.1 ·), f.2.imp (by continuity)
  (by aesop)⟩, by bound⟩, by bound⟩

/-- The linear map H²(G,M) → H²(H,N) induced by a compatible pair: continuous φ: H → G and
continuous φ-equivariant linear u: M → N. -/
def pairMapH2 : H2 ρ →ₗ[R] H2 ρ' := mapQ _ _ ⟨⟨fun f ↦ ⟨(u <| f.1 <| ·.map φ φ), f.2.imp (by
  fun_prop) (by aesop)⟩, by bound⟩, by bound⟩ fun f ⟨c, _, _⟩ ↦ ⟨u ∘ c ∘ φ, by fun_prop, by aesop⟩

variable (R) in
/-- The R-linear representation of a monoid G on M obtained from a homomorphism χ : G → S into a
monoid S acting R-linearly on M: g acts as χ(g). -/
abbrev actionRep M [AddCommMonoid M] [Module R M] {G S} [Monoid G] [Monoid S] [DistribMulAction S M]
  [SMulCommClass S R M] (χ : G →* S) : Representation R G M := (toModuleEnd ..).comp χ

/-- For an R-module M and a character χ: G → R^×, the representation of G on M in which g acts
as the scalar χ(g). -/
def charRep M [AddCommGroup M] [Module R M] (χ : G →* Rˣ) := actionRep R M ((Units.coeHom R).comp χ)

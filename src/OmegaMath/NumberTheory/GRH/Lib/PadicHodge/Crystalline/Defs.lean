import OmegaMath.NumberTheory.GRH.Lib.PadicHodge.PeriodRings.BdR
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius
(known result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Definitions: (potentially) crystalline, Hodge–Tate jumps, Weil pairs, linear Frobenius,
crystalline cocycles. -/

noncomputable section


open TensorProduct Module DistribSMul RingHomClass

/-- A group Γ together with a homomorphism j from Γ to G_p = Gal(Q̄_p over Q_p) whose image is
open. -/
class OverGp Γ (p : outParam ℕ) [Fact p.Prime] [Group Γ] where
  (toGp : Γ →* Gp p) isOpen_range : Fact (IsOpen (SetLike.coe toGp.range))

/-- A group G with a homomorphism j onto an open subgroup of G_p = Gal(Q̄_p over Q_p), bundled
as one object. -/
class GroupOverGp (p : outParam ℕ) [Fact p.Prime] where (G) [group : Group G] [overGp : OverGp G p]

attribute [instance_reducible] GroupOverGp.group GroupOverGp.overGp
attribute [instance] OverGp.isOpen_range GroupOverGp.group GroupOverGp.overGp

export OverGp (toGp)

variable {p} [ThePrime p] {Γ R T} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra
  ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [𝒥 : OverGp Γ p] (ρ : Representation R Γ T)
  (B) [CommRing B] [Algebra ℤ_[p] B] (γ : R →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ) (s m)

instance : CoeSort (GroupOverGp p) Type := ⟨(·.G)⟩

/-- For m acting on a ring B and an endomorphism f of T, the Z_p-linear endomorphism b⊗x ↦
(mb)⊗f(x) of B⊗T, the tensor product taken over Z_p. -/
def tensorAction {M} [Monoid M] [MulSemiringAction M B] [SMulCommClass M ℤ_[p] B] (m : M) (f :
  End R T) : End ℤ_[p] (B ⊗[ℤ_[p]] T) := map (toLinearMap _ _ m) f

/-- For a filter F on Γ, the set of elements of B⊗T (over Z_p) fixed by j(g)⊗ρ(g) for F-almost
all g. -/
def fixedPeriods [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B] F :=
  {x | ∀ᶠ g in F, tensorAction B (toGp g) (ρ g) x = x}

/-- For a representation T and a filter F on Γ, the property that elements of B⊗T fixed by
F-almost all g span B⊗T over B. -/
def IsAdmissible F := Submodule.span Bcris (fixedPeriods ρ Bcris F) = ⊤

/-- T is crystalline: the elements of B⊗T fixed by all of Γ span B⊗T over B. -/
abbrev IsCrystalline := IsAdmissible ρ ⊤

/-- Z_f(T), the R-module of maps c: Γ → T such that some y in B⊗T has 1⊗c(g) = gy − y for all g;
for T free over Z_p, the crystalline cocycles. -/
def crysCocycles : Submodule R (Γ → T) :=
  ⟨⟨⟨{c | ∃ y, ∀ g, 1 ⊗ₜ c g = tensorAction Bcris (toGp g) (ρ g) y - y}, fun ⟨y, _⟩ ↦
  .imp' (y + ·) (by simp [tmul_add]; grind)⟩, 0, by simp⟩, fun a _ ⟨y, e⟩ ↦ ⟨y.map 1 (a • .id),
  (congr(map 1 (a • .id) $(e ·)).trans (by simp [tensorAction, map_map, LinearMap.comp]))⟩⟩

/-- (s, m) is a Weil pair: s in G_p acts on the residue field of the integers of Q̄_p as x ↦
x^(1/p^m); m = 0 means inertia. -/
def IsWeilPair (s : Gp p) m := IsFrob (intQpBar p) (p ^ m) s⁻¹

/-- For s in G_p, (s, 0) is a Weil pair if and only if s lies in the inertia group of the
valuation ring of Q̄_p. -/
lemma isWeilPair_zero_iff {s} : IsWeilPair s 0 ↔ s ∈ inertiaGroup _ (intQpBar p) :=
  (inertiaGroup ..).inv_mem_iff

/-- The p-adic cyclotomic character of Γ: the cyclotomic character of G_p composed with j. -/
abbrev χ := cyclotomicGp.comp 𝒥.toGp

variable (Γ) in def nearOne := (nhds 1).comap 𝒥.toGp

variable (Γ) in lemma eventually_nearOne_apply_eq c : ∀ᶠ g in nearOne Γ, toGp g c = c :=
  ⟨_, (isLocallyConstant_smul c {c}).mem_nhds rfl, .rfl⟩

/-- D_pcris(T): the Z_p-submodule of B⊗T of elements fixed by j(g)⊗ρ(g) for all g with j(g) in
some neighbourhood of 1 in G_p. -/
abbrev Dpcris := fixedPeriods ρ Bcris (nearOne Γ)

/-- T is potentially crystalline: the elements of B⊗T fixed by all g with j(g) near 1 span B⊗T
over B. -/
abbrev IsPotCrys := IsAdmissible ρ (nearOne Γ)

/-- The element y of C_p⊗T (tensor product over Z_p) has Hodge–Tate weight u: (j(g)⊗ρ(g))y =
χ(j(g))^(−u)·y for all g in Γ, with χ the p-adic cyclotomic character. -/
def HasHodgeTateWeight y := ∀ g, tensorAction ℂ_[p] (toGp g) (ρ g) y =
  (cyclotomicGp (toGp g) ^ (-u)).1 • y

/-- For γ from R to C_p and integer u, the Q̄_p-space of γ-semilinear f: T→C_p with, for each x,
f(gx) = χ(g)^(−u)·g f(x) for g near 1. -/
def hodgeTateMaps : Submodule (PadicAlgCl p) (T →ₛₗ[toRingHom γ] ℂ_[p]) :=
  ⟨⟨⟨{f | ∀ x, ∀ᶠ g in _, f (ρ g x) = (χ g ^ (-u)).1 • toGp g • f x}, fun h k x ↦
  (h x).mp ((k x).mp (by simp_all))⟩, by simp⟩, fun c _ h x ↦ (h x).mp
  ((eventually_nearOne_apply_eq Γ c).mp (by simp_all [Algebra.smul_def c, ← PadicComplex.coe_eq]))⟩

/-- The multiplicity of the Hodge–Tate jump u at γ: the dimension over Q̄_p (zero if infinite)
of the space `hodgeTateMaps`. -/
def jump := finrank (PadicAlgCl p) (hodgeTateMaps ρ γ u)

/-- The property of a multiset J of integers that for every integer u the multiplicity of the
jump u of T at γ equals its count in J. -/
def HasJumps J := ∀ u, jump ρ γ u = Multiset.count u J

/-- β_{s,m}: a chosen B-linear endomorphism of B⊗T agreeing with φ^m j(s) ⊗ ρ(s) on D_pcris(T),
if one exists (arbitrary otherwise). -/
def linearFrob := Classical.epsilon fun β : End Bcris _ ↦ ∀ d ∈ Dpcris ρ,
  β d = tensorAction _ (⟨.ofAdd m, toGp s⟩ : FrobGal) (ρ s) d

variable (R T) in def coefEnd :=
  toRingHom ((End.baseChangeHom ℤ_[p] Bcris T).comp (Algebra.lsmul (A := R) ..))

/-- The polynomial P over R kills (s, m): T is potentially crystalline and P(β_{s,m}) = 0 on
B⊗T, the coefficients acting through T. -/
def IsKilledBy P := IsPotCrys ρ ∧ Polynomial.eval₂ (coefEnd R T) (linearFrob ρ s m) P = 0

/-- For a homomorphism r from Γ to GL_n(R), the representation on R^n in which g acts by
multiplying column vectors by r(g). -/
abbrev matrixRep {n} [Fintype n] (r : Γ →* GL n R) := actionRep R (n → R) ((Units.coeHom _).comp r)

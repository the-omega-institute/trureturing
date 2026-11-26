import OmegaMath.NumberTheory.GRH.Lib.General.Groups.RatModInt
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.ProfiniteGalois
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Module over Z/l^r with small l-torsion admits primitive relation with prescribed zeros.
Discrete modules with continuous action, restriction, exact sequences, functions on finite sets.
Counting in exact sequences; left exactness of continuous 1-cocycles. Trivialised cocycles:
extension from orbit representatives, corestriction, submultiplicative count in exact sequences.
Additive notation for the multiplicative group of the algebraic closure. -/

open Quotient AddMonoidHom AddSubgroup Classical Function MulAction QZ ZMod

variable {ℓ r k : ℕ} (R Γ : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ]

/-- Let ℓ be prime, r > 0, Y a finite abelian group, p: Y → (ℤ/ℓ^r)^ι additive, t: Fin k → ι,
and #Y[ℓ]·ℓ^{k+1} ≤ ℓ^{|ι|}. Then some vector n with a unit entry vanishes at all t(j) and
is orthogonal to p(Y). -/
lemma exists_primitive_relation {Y ι} [Fact ℓ.Prime] [AddCommGroup Y] [Fintype ι] (p : Y →+ ι →
  ZMod (ℓ ^ r)) (t :
  Fin k → ι) (hr : 0 < r) (h : .card (Submodule.torsionBy ℕ Y ℓ) * ℓ ^ (k + 1) ≤ ℓ ^ Fintype.card
  ι) : Finite Y → ∃ n, (∀ x, p x ⬝ᵥ n = 0) ∧ (∀ j, n (t j) = 0) ∧ ∃ i, IsUnit (n i) := by
  by_contra! ⟨_, H⟩
  have := (index_map_eq (.pi ⊤ fun _ ↦ range (ℓ • .id _)) (mk' (fun n ↦ (mk' (p · ⬝ᵥ n) (by simp), n
    ∘ t)) (by aesop)).rangeRestrict_surjective fun n e i _ ↦ ((@isUnit_natCast_iff_not_dvd_pow ℓ _
    (n i).val Fact.out hr).not_left.1 (by simp [H n (congr($e.1.1 ·))
    (congr($e.1.2 ·))])).natCast.imp (by aesop)).ge.trans ((index_antitone (by
    rintro _ ⟨⟨_, n, ⟨⟩⟩, ⟨⟩⟩; use ℓ • n, by tauto, map_nsmul ..)).trans (index_range (f := ℓ • .id
    _).trans_le (Nat.card_le_card_of_injective (fun x ↦
    ((ofZMod _).comp (QuotientAddGroup.lift (range (ℓ • .id _))
    x.1.1.1 (by simpa [LE.le] using (congr($(x.2).1.1 ·)))), fun j ↦ (⟨_, congr($(x.2).1.2 j)⟩ : ker
    (ℓ • .id _)))) fun x y e ↦ by ext z; exacts [ofZMod_injective congr($e.1 z), congr($e.2 z)])))
  erw [index_pi, index_range, Nat.card_prod, Nat.card_fun,
    IsAddCyclic.card_nsmulAddMonoidHom_ker] at *
  exact (h.trans (by simpa [Nat.gcd_eq_right, hr.ne', ← index_eq_card, index_range])).not_gt
    (mul_lt_mul_of_pos_left (Nat.pow_lt_pow_succ Fact.out) Nat.card_pos)

/-- A discrete Γ-module over R: an R-module with the discrete topology and a continuous R-linear
action of the topological group Γ. -/
structure DiscreteModule where of ::
  {V : Type}
  [addCommGroup : AddCommGroup V]
  [moduleR : Module R V]
  [topologicalSpace : TopologicalSpace V]
  [discrete : DiscreteTopology V]
  ρ : Representation R Γ V
  continuous : Continuous (ρ · ·).uncurry := by
    simp [continuous_prod_of_discrete_right, LinearMap.pi, LinearMap.restrict_apply]; fun_prop

variable {G} [Group G] {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] (M A :
  DiscreteModule R Γ)

/-- The inclusion of a subgroup U in G, as a continuous homomorphism. -/
def subgroupIncl [TopologicalSpace G] (U : Subgroup G) := ContinuousMonoidHom.mk U.subtype

attribute [instance] DiscreteModule.addCommGroup DiscreteModule.moduleR
  DiscreteModule.topologicalSpace DiscreteModule.discrete

attribute [fun_prop] DiscreteModule.continuous

namespace DiscreteModule

instance : CoeSort (DiscreteModule R Γ) Type := ⟨V⟩

/-- For discrete Γ-modules M and A over R, the R-linear maps M → A commuting with the action of
Γ. -/
abbrev Hom := M.ρ.IntertwiningMap A.ρ

/-- The linear map from a discrete Γ-module A to its continuous 1-cocycles sending m to g ↦ gm −
m. -/
abbrev coboundary := (d0 A.ρ).codRestrict (Z1 A.ρ) (by simp [Z1, LinearMap.pi]; fun_prop)

/-- The R-submodule of elements of a discrete Γ-module A fixed by all of Γ. -/
noncomputable abbrev H0 := A.ρ.invariants

/-- The continuous cohomology H²(Γ,A) of a discrete Γ-module A. -/
abbrev H2 := _root_.H2 A.ρ

/-- For a continuous homomorphism φ: G → Γ, the discrete Γ-module A viewed as a discrete
G-module through φ. -/
abbrev restrictAlong {G} [Group G] [TopologicalSpace G] (A : DiscreteModule R Γ) (φ : G →ₜ* Γ) :=
  of (A.ρ.comp φ.1)

variable (U : Subgroup Γ) {M N P : DiscreteModule R Γ}

/-- For a subgroup U of Γ, the discrete Γ-module A viewed as a discrete U-module. -/
abbrev restrictTo := A.restrictAlong (subgroupIncl U)

/-- For a subgroup U of Γ, the restriction map H²(Γ, A) → H²(U, A). -/
abbrev resH2 : A.H2 →ₗ[R] (A.restrictTo U).H2 := pairMapH2 (subgroupIncl U) .id

/-- The linear map H²(Γ,M) → H²(Γ,N) induced by composing cocycles with a Γ-equivariant linear
map M → N. -/
abbrev Hom.mapH2 (ι : M.Hom N) := pairMapH2 (.id Γ) _ ι.isIntertwining

/-- Property of equivariant maps ι: M → N, π: N → P: ι is injective, π is surjective, and the
kernel of π is the image of ι. -/
def IsShortExact (ι : M.Hom N) (π : N.Hom P) := (⇑ι).Injective ∧ (⇑ι).Exact π ∧ (⇑π).Surjective

lemma IsShortExact.restrictAlong {G} [Group G] [TopologicalSpace G] {ι : M.Hom N} {π : N.Hom P} (φ :
  G →ₜ* Γ) : IsShortExact ι π → (M.restrictAlong φ).IsShortExact (N := N.restrictAlong φ) (P :=
  P.restrictAlong φ) ⟨_, (ι.2 <| φ ·)⟩ ⟨_, (π.2 <| φ ·)⟩ := _root_.id

/-- A Γ-stable R-submodule W of a discrete Γ-module A, as a discrete Γ-module with the
restricted action. -/
abbrev submodule W h := of (A.ρ.subrepresentation W h)

lemma isShortExact_submodule W h : (A.submodule W h).IsShortExact (P := of (A.ρ.quotient W h)
  ((IsOpenQuotientMap.id.prodMap W.isOpenQuotientMap_mkQ).continuous_comp_iff.1
  (W.mkQL.2.comp A.continuous)) (discrete := ⟨A.discrete.1 ▸
  rfl⟩)) ⟨W.subtype, by aesop⟩ ⟨W.mkQ, by aesop⟩ := ⟨by simp, by aesop_cat, Quot.exists_rep⟩

variable [IsTopologicalGroup Γ] (U : Subgroup Γ) [Finite (Γ ⧸ U)] [DiscreteTopology (Γ ⧸ U)]

/-- For a subgroup U with Γ/U finite and discrete, the discrete Γ-module of functions f: Γ/U → A
with action (gf)(x) = g·f(g⁻¹x). -/
abbrev funModule := of ⟨⟨fun g ↦ .pi fun x : Γ ⧸ U ↦
  A.ρ g ∘ₗ .proj (g⁻¹ • x), by aesop⟩, by aesop (add simp mul_smul)⟩

/-- The Γ-equivariant linear map from A to the A-valued functions on Γ/U sending an element to
the constant function with that value. -/
def const : A.Hom (A.funModule U) := ⟨.const, by tauto⟩

open Fint in
/-- The Γ-equivariant linear map from the A-valued functions on the finite set Γ/U to A sending
f to the sum of its values. -/
noncomputable def sum : (A.funModule U).Hom A :=
    ⟨∑ x, .proj x, by simp [DFunLike.ext_iff, ← map_sum, (MulAction.bijective _).sum_comp]⟩

/-- For a morphism ι: M → N of Γ-modules, the map on continuous 1-cocycles Z¹(M) → Z¹(N) given
by composing with ι. -/
abbrev Hom.mapZ1 (ι : M.Hom N) := pairMapZ1 (.id Γ) _ ι.isIntertwining

lemma card_eq_mul_of_exact {A B C} [AddGroup A] [AddGroup B] [AddGroup C] (f : A →+ B) (g : B →+ C)
    (i : Injective f) (h : Exact f g) W : .card W = Nat.card (comap f W) * .card (map g W) := by
  erw [← relIndex_ker, ← card_map_of_injective i, map_comap_eq, h.addMonoidHom_ker_eq,
    ← addSubgroupOf_map_subtype, card_subtype, card_mul_index]

omit [IsTopologicalGroup Γ]

lemma IsShortExact.card_eq_mul {π : N.Hom P} {ι} (h : M.IsShortExact ι π) : Nat.card N =
  .card M * .card P := by simpa [h.2.2 _] using card_eq_mul_of_exact ι (π : N →+ P) h.1 h.2.1 ⊤

lemma Hom.card_eq_card_comap_mul_card_map (ι : M.Hom N) {π : N.Hom P} (h : Injective ι) (e :
  Exact ι π) W : .card W = Nat.card (comap ι.mapZ1 W) * .card (map π.mapZ1
  W) := by apply card_eq_mul_of_exact <;> simp [e _, skolem, Injective, Exact, funext_iff] <;>
  simp [Z1, Set.preimage, ι.isIntertwining, continuous_discrete_rng, ← h.eq_iff]; aesop

variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G] (X : Type) [MulAction G X]
  (I : Set G) (V : DiscreteModule R G) (k : ℕ) {A B : DiscreteModule R G} {C ι} {π :
  B.Hom C} {Ω} [Field Ω] {x y : DiscreteUnits Ω} (a : Ω)

/-- Trivialised cocycles: pairs of f : X → V and continuous z : G → V vanishing on I, with g
f(g⁻¹x) = f(x) + z(g) for all g, x. -/
def trivialisedCocycles := ofSub {p : (X → V) × _ | Continuous p.2 ∧ (∀ g x, V.ρ g (p.1 x) = p.1
  (g • x) + p.2 g) ∧ ∀ g ∈ I, p.2 g = 0} ⟨0, by continuity⟩ (by simp_all [Continuous.add]; grind)

/-- The group `DiscreteModule.trivialisedCocycles` of cocycles in V vanishing on I with
trivialisations at the points of X is finite, of order at most (#V)^k. -/
abbrev HasFewCocycles := .card (trivialisedCocycles X I V) ∈ Set.Ioc 0 (.card V ^ k)

/-- For an equivariant map u : A → B, the additive map between the groups
`DiscreteModule.trivialisedCocycles` of A and B that composes both components of a pair of functions
with u. -/
def trivialisedCocycles.map (u : A.Hom B) :
  A.trivialisedCocycles X I →+ B.trivialisedCocycles X I := .mk' (fun p ↦
  ⟨p.1.map (u ∘ ·) (u ∘ ·), p.2.imp (by fun_prop) (by simp_all [← u.isIntertwining])⟩) (by simp)

lemma trivialisedCocycles.card_eq_of_isShortExact (s : A.IsShortExact ι π) :
  Nat.card (B.trivialisedCocycles X I) = .card (A.trivialisedCocycles X I) * .card (map X I
  π).range := by rw [← card_top, card_eq_mul_of_exact (map X I ι) (map X I π)] <;> simp [Injective,
  Exact, map, s.2.1 _, funext_iff, skolem, Prod.ext_iff] <;> simp [ι.isIntertwining,
  trivialisedCocycles, ofSub, continuous_discrete_rng, Set.preimage, ← s.1.eq_iff] <;> aesop

variable {X I}

lemma trivialisedCocycles.snd_mem_Z1 [Nonempty X] {p} : p ∈ C.trivialisedCocycles X I → p.2 ∈ Z1
  C.ρ := .imp_right fun a g k ↦ by grind [a.1 (g * k) ofNonempty, mul_smul, Module.End.mul_apply]

/-- Let the x_i represent the G-orbits on X, z be a 1-cocycle vanishing on I, and z(g) = g m_i −
m_i on the stabiliser of x_i. Then some φ with φ(x_i) = m_i makes (φ, z) a trivialised
cocycle. -/
lemma trivialisedCocycles.exists_mem_of_orbit_reps {V : DiscreteModule R G} {κ x} (hx :
  Bijective (Quotient.mk (orbitRel G X) ∘ x)) {z} (hz : z ∈ Z1
  V.ρ) (hI : ∀ g ∈ I, z g = 0) (m : κ → V) (h : ∀ i g, g • x i = x i → z g = V.ρ g (m i) - m i) :
  ∃ f, (f, z) ∈ V.trivialisedCocycles X I ∧ ∀ i, f (x i) = m i := by
  have := (@hx.1 · · <| sound ⟨·, ·⟩)
  choose i s e using (hx.2 ⟦·⟧ |>.imp fun _ ↦ exact ∘ symm)
  use fun y ↦ V.ρ (s y) (m (i y)) - z (s y), ⟨hz.1, fun g y ↦ by grind [mul_inv_cancel_left
    (g * s y) (s _), hz.2, mul_smul, inv_smul_smul, Module.End.mul_apply], hI⟩, by grind

/-- Corestriction: let P be open of finite index, all conjugates of I in I ∩ P, and (f, c)
trivialised for P. Then y ↦ ∑_{s ∈ G/P} s f(s⁻¹y) trivialises some z, with z(g) = ∑ s
c(s⁻¹gs) when all conjugates of g lie in P. -/
lemma trivialisedCocycles.corestrict_mem [IsTopologicalGroup G] (P : OpenSubgroup G) [Fintype (G ⧸
  P.1)] (hI : ∀ g ∈ I, g ∈ P ∧ ∀ s, s⁻¹ * g * s ∈ I) {p} : p ∈ (C.restrictTo P).trivialisedCocycles
  X ((↑) ⁻¹' I) → (fun y ↦ ∑ x : G ⧸ P.1, C.ρ x.out (p.1 (x.out⁻¹ • y)), fun g ↦ ∑ x, C.ρ x.out
  (p.2 ⟨_, QuotientGroup.leftRel_apply.1 (mk_eq_iff_out.1 (Quotient.mk_smul_out _ g⁻¹ x))⟩)) ∈
  C.trivialisedCocycles X I := .imp (by fun_prop) (.imp
  (fun a g y ↦ by simpa [← Finset.sum_add_distrib] using
  Fintype.sum_equiv (toPerm g) _ _ fun x ↦ by simp [mul_smul, subgroupIncl, ← sub_eq_of_eq_add'
  (a _ (x.out⁻¹ • y)), -ContinuousMonoidHom.coe_toMonoidHom]) fun _ g _ ↦ by simp [show ∀ x :
  G ⧸ P.1, g⁻¹ • x = x by simp_all [QuotientGroup.forall_mk, QuotientGroup.eq], *])

/-- For 0 → A → B → C → 0 exact: if the trivialised cocycles `DiscreteModule.trivialisedCocycles` of
A and C are finite in number, at most (#A)^k and (#C)^k, likewise for B; equality for B forces
surjectivity onto those of C and equality for A. -/
lemma trivialisedCocycles.card_le_of_isShortExact {k} (s : A.IsShortExact ι π) (a :
  HasFewCocycles X I A k) (c : HasFewCocycles X I C k) : B.HasFewCocycles X I k ∧ (.card B ^ k ≤
  Nat.card (trivialisedCocycles X I B) → (map X I π).range = ⊤ ∧ Nat.card A ^ k ≤
  .card (trivialisedCocycles X I A)) := by
  obtain ⟨⟨⟩, ⟨⟩, ⟨⟩⟩ := Nat.card_pos_iff.1 c.1, a, c
  rw [HasFewCocycles, card_eq_of_isShortExact X I s, s.card_eq_mul, mul_pow]
  use ⟨mul_pos ‹_› Nat.card_pos, ?_⟩, fun h ↦ ⟨eq_top_of_le_card _ ?_, ?_⟩
  repeat nlinarith [(map X I π).range.card_le_card_addGroup]

@[ext] lemma _root_.DiscreteUnits.ext : x.toMul.1 = y.toMul.1 → x = y := Units.ext

/-- A non-zero element a of the field Ω, viewed as an element of the additively written
multiplicative group `DiscreteUnits` Ω. -/
def _root_.DiscreteUnits.ofNeZero : a ≠ 0 → DiscreteUnits Ω := .mk0 a

@[simp] lemma _root_.DiscreteUnits.val_ofNeZero h : (DiscreteUnits.ofNeZero a h).toMul.1 = a := rfl

variable (x) {Γ : Type*} [Group Γ] [MulSemiringAction Γ Ω] {K} [Field K] [Algebra K Ω]
  [SMulCommClass Γ K Ω]

@[simp] lemma _root_.DiscreteUnits.val_unitsRep (g : Γ) : (unitsRep g x).toMul.1 = g • x.toMul :=
  rfl

@[simp] lemma _root_.DiscreteUnits.val_ofBase a : (DiscreteUnits.ofBase Γ Ω a).1.toMul.1 =
  algebraMap K Ω a.toMul.1 := rfl

lemma _root_.DiscreteUnits.exists_nsmul [IsAlgClosed Ω] {n} (hn : n ≠ 0) : ∃ y, n • y = x :=
  (IsAlgClosed.exists_pow_nat_eq _ hn.pos).rec (⟨.ofPow _ · hn ·, DiscreteUnits.ext ‹_›⟩)

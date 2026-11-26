import GRH.Lib.ClassField.Global.Avatars
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Selmer cocycle groups, their finiteness, S-units, split primes, tame generators,
places. -/

noncomputable section


variable {G K R X : Type} [Group G] [TopologicalSpace G] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R] (m N : ℕ) [NeZero m] [MulAction G X] (I :
  Set G) {M : DiscreteModule R G} (x : Z1 M.ρ) (V : DiscreteModule R Gal(Ω/K)) {v : FinPlace K} {B :
  ClosurePlace} (U : OpenNormalSubgroup G)
open NeZero NumberField Pointwise MulSemiringAction Set QuotientGroup

/-- γ lies in inertia at A, and γy/y = `rootPowHom` 1 for some m-th root y of some uniformiser π of
K for A. -/
def IsTameGeneratorFor (A : ClosurePlace) γ := γ ∈ inertiaGroup G A ∧ ∃ π y, IsUniformiser A (π :
  Kˣ).1 ∧ m • y = ↑(DiscreteUnits.ofBase G Ω (.ofMul π)) ∧ unitsRep γ y - y = (rootPowHom Ω m).1 1

variable (G) in
/-- For B above a prime v of K, some γ in the inertia group of B multiplies an m-th root of some
uniformiser of K by the fixed primitive m-th root of unity given by `rootPowHom`. -/
lemma exists_isTameGeneratorFor (h : IsPlaceOver B v) : ∃ γ : G, IsTameGeneratorFor m B γ :=
  (h.exists_uniformiser G).rec fun π ⟨a, u⟩ ↦ ((DiscreteUnits.ofBase G Ω π).1.exists_nsmul out).rec
  fun y hy ↦ ((h.decompGroup_spec G).1.exists_inertia_smul_eq_of_pow_eq u (pos m) congr($hy.1) (y :=
  ((rootPowHom Ω m).1 1 + y).toMul) (mod_cast by simp [mul_pow,
  (isPrimitiveRoot_rootPowHom_one ..).1])).rec (⟨·, ·.1, π, y, h.isUniformiser_iff.2 a, by aesop⟩)

/-- The places of Ω above N and infinity: valuation subrings in which N has valuation below 1,
together with the infinite places. -/
def PlaceAboveS := {B : ClosurePlace // B N < 1} ⊕ InfinitePlace Ω deriving Nonempty

instance : MulAction G (PlaceAboveS N) := @Sum.instMulAction _ _ _ _ (SubMulAction.mk _ fun g ↦
  (by simpa using! (val_smul_lt_one g).2 ·)).mulAction (.compHom _ (toAlgAut G ℚ Ω))

instance (Q : Subgroup G) [Q.Normal] : MulAction (G ⧸ Q) (MulAction.orbitRel.Quotient Q X) := {
  smul := .map₂ (· • ·) fun a b e x y ⟨q, h⟩ ↦ ⟨⟨a * q * b⁻¹, by simp [← eq_one_iff, Quotient.sound
    e]⟩, by simp [← h, mul_smul, Q.smul_def]⟩, one_smul := Quot.ind (congr(⟦$(one_smul G ·)⟧)),
  mul_smul := by rintro ⟨⟩ ⟨⟩ ⟨⟩; exact congrArg _ (mul_smul ..) }

/-- A continuous 1-cocycle that vanishes on the inertia group and at a Frobenius element of a
place B above the prime v vanishes on the decomposition group of B. -/
lemma DiscreteModule.Z1.eq_zero_on_decompGroup {φ} (h : IsPlaceOver B v) (f : IsFrob B v.q φ) :
  (∀ g ∈ inertiaGroup G B, x.1 g = 0) → x.1 φ = 0 → ∀ g ∈ decompGroup G B, x.1 g = 0 :=
  h.decompGroup_le f (U := cocycleKer M.ρ x.2.2) (x.2.1.1 {0} (by simp))

/-- The continuous 1-cocycles of ρ restricting into L_v on Dec(A_v) for v in S, and vanishing on
complex conjugations and on inertia groups above primes outside S ∪ P. -/
def selmerZ1 S (A : _ → ClosurePlace) L P := Z1 V.ρ ⊓ .pi (inertiaAbove (S ∪ P)ᶜ) ⊥ ⊓ (.comap
  (.pi fun v ↦ .funLeft R V (decompGroup _ (A v)).subtype) (.pi S L) ⊓ .pi {c | IsComplexConj c} ⊥)

/-- For a finite discrete module V of the absolute Galois group of K and a finite set S of primes,
there are finitely many continuous 1-cocycles vanishing on all inertia groups above primes outside
S. -/
lemma selmerZ1.finite_unramified_cocycles [Finite V] {S} (hS : S.Finite := by toFinite_tac) :
    (Z1 V.ρ ⊓ .pi (inertiaAbove Sᶜ) ⊥).1.1.1.Finite := by
  cases' exists_openNormalSubgroup_apply_eq V.continuous with N
  let U := (N.1 ⊓ ⟨(cycCharMod Ω 3).ker, isOpen_ker_cycCharMod.1⟩).1
  obtain ⟨T, f : Finite T, _, -, e⟩ := exists_sup_idelesUnitOff_eq_top
    (tendsto_place_comap_cofinite (algebraMap K (fixedFieldOf U)) hS.compl_mem_cofinite)
  apply (finite_univ.prod (.pi' fun w : T ↦
    (w.1.isPlaceOver_placeOver.decompGroup_spec U).1.finite_Z1_local ((V.restrictTo _).restrictTo
    _))).of_injOn (f := AddMonoidHom.mk' (fun z ↦ ((z ·.out⁻¹ : _ ⧸ U → _), fun _ ↦ (z ·))) (by
    tauto)) fun _ ↦ (by use ⟨⟩, fun _ ↦ ·.1.imp (by fun_prop) (by tauto))
  exact (injOn_iff_map_eq_zero (F := _ →+ _) _ (Z1 V.ρ ⊓ .pi (inertiaAbove Sᶜ) ⊥)).2
    fun z ⟨c, n⟩ h ↦ funext ((cocycleKer V.ρ c.2
    ).mul_mem_cancel_left congr($h.1 ·) |>.1 (QZChar.eq_zero_of_unramified_off _ e ⟨(z ·),
    c.imp (by fun_prop) (by aesop)⟩ (Γ :=
    U) (nomatch ·.2.2 ▸ ·.cycCharMod_eq_neg_one) (congr($h.2 ⟨·, ·⟩ ⟨·, ·⟩)) (fun w _ ↦ (n · ⟨_, by
    tauto, _, w.isPlaceOver_placeOver.isPlaceOver_below, ·⟩)) ⟨_, by simp [← QuotientGroup.eq]⟩))


/-- The N-units of Ω: elements of Ω^× that are units in every valuation subring in which N does
not have valuation below 1. -/
def sUnits : Submodule ℤ (DiscreteUnits Ω) := .comap (.const ..) (.pi {B : ClosurePlace | B N = 1}
  (·.unitGroup.toAddSubgroup.toIntSubmodule))

/-- The N-units of the fixed field of U: the N-units of Ω that are fixed by U. -/
abbrev fixedSUnits := sUnits N ⊓ (unitsModule U.1.1).H0

/-- The N-units of the fixed field of the open normal subgroup U, as a module over the group
ring ℤ[G/U]. -/
abbrev fixedSUnitsRep : Representation ℤ (G ⧸ U.1.1) (fixedSUnits N U) :=
  lift _ (unitsRep.subrepresentation _ fun g _ ↦
  .imp (by simpa [isEquiv_comap.eq_one_iff_eq_one] using! · <| ·.comap (toRingHom G Ω g))
  (unitsRep.le_comap_invariants _ _ ·)) (LinearMap.ext fun x ↦ Subtype.ext <| x.2.2 ⟨·, ·⟩)

/-- Auxiliary primes: distinct v_i ∤ N with places and Frobenii in U; m ∣ N; U fixes μ_m and
contains all inertia off N; I is the inertia off N and the v_i; primes above N generate the
class groups of number fields in Ω^U over K. -/
structure SplitPlaces (ι : Type) where
  cyc_eq_one : ∀ g ∈ U, cycCharMod Ω m g = 1
  dvd_level : m ∣ N
  v : ι → FinPlace K
  v_injective : v.Injective
  level_notMem i : ↑N ∉ (v i).1
  valRing : ι → ClosurePlace
  isPlaceOver i : IsPlaceOver (valRing i) (v i)
  φ : ι → G
  isFrob i : IsFrob (valRing i) (v i).q (φ i) ∧ φ i ∈ U
  mem_inertia_iff g : g ∈ I ↔ ∃ w, ↑N ∉ w.1 ∧ w ∉ range v ∧ ∃ B : ClosurePlace, IsPlaceOver B w ∧
    g ∈ inertiaGroup G B
  inertiaGroup_le {v : FinPlace K} {B : ClosurePlace} : ↑N ∉ v.1 → IsPlaceOver B v →
    inertiaGroup G B ≤ U
  principal_sup_idelesUnitOff (F : IntermediateField K Ω) [NumberField F] : F ≤ fixedFieldOf U.1.1 →
    principalIdele (K := F).range ⊔ idelesUnitOff {w | ↑N ∈ w.1} = ⊤

variable {m N I U ι} (s : SplitPlaces m N I U ι)

lemma ofBase_mem_sUnits {x} : (DiscreteUnits.ofBase G Ω (.ofMul x)).1 ∈ sUnits N ↔
  x ∈ unit {w : FinPlace K | ↑N ∈ w.1} K :=
  ⟨fun h (w : FinPlace K) ↦ w.isPlaceOver_placeOver.valuationVia_eq_one_iff.1 ∘ h _ ∘
  w.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2, fun h B b ↦ by_cases id
  (exists_isPlaceOver_of_val_ne_one K (by simp) · |>.elim fun _ o ↦
  o.valuationVia_eq_one_iff.2 (h _ (o.valuation_natCast_eq_one_iff.1 b)))⟩

/-- Every y in Ω^× whose m-th power is an N-unit of the fixed field of U, and which all Frobenii
φ_i fix, is fixed by U. -/
abbrev SplitPlaces.FrobeniiDetectRoots := ∀ y, m • y ∈ fixedSUnits N U →
  (∀ i, unitsRep (s.φ i) y = y) → ∀ g ∈ U, unitsRep g y = y

lemma mem_sUnits_of_nsmul_mem {r} {y : fixedSUnits N U} (e : m • r = ↑y) : r ∈ sUnits N :=
  (by simpa [← e, ne] using y.2.1 · ·)

lemma SplitPlaces.decompGroup_le {i} (h : IsPlaceOver B (s.v i)) : decompGroup G B ≤ U :=
  h.decompGroup_le (((s.isPlaceOver i).exists_smul G h).choose_spec ▸ (s.isFrob i).1.conj _) U.1.2
  (s.inertiaGroup_le (s.level_notMem i) h) (U.2.1 _ (s.isFrob i).2 _)

/-- For open U ⊆ Q ⊴ B, Q fixing μ_m: the primes of the fixed field of B above s, with Frobenii
conjugated by coset representatives σ, as a family split for Q. -/
def SplitPlaces.liftToSubgroup (B : OpenSubgroup G) (Q : OpenNormalSubgroup B.1) (r : U.1.1 ≤
  B) (u : U.1.1.subgroupOf B ≤ Q) (c : ∀ g ∈ Q, cycCharMod Ω m g = 1) (σ : G ⧸ B.1 → G) (e : ∀ x,
  σ x = x) : SplitPlaces m N ((↑) ⁻¹' I) Q (ι × G ⧸ B.1) := by
  have o (θ : ι × _) := (s.isPlaceOver θ.1).smul (σ θ.2)⁻¹
  choose w W k using (o · |>.exists_above (L := fixedFieldOf B.1))
  refine ⟨c, s.dvd_level, w, fun ⟨_, a⟩ θ q ↦ ?_, (s.level_notMem ·.1 ∘ by simp [← k]), _, W,
    fun _ ↦ ⟨_, r (U.2.1 _ (s.isFrob _).2 _)⟩, fun θ ↦ ⟨(((o _).ramification_in_tower _ (W θ)).1
    ((s.decompGroup_le (o θ)).trans r)).1 ▸ (s.isFrob _).1.conj _, u (U.2.1 _ (s.isFrob _).2 _)⟩,
    (s.mem_inertia_iff · |>.trans ⟨fun ⟨v, a, b, C, c, d⟩ ↦ c.exists_above.imp fun
    _ ⟨e, rfl⟩ ↦ ⟨a ∘ by simp, fun ⟨θ, q⟩ ↦ b (by simp [← q, k]), C, e, d⟩, fun ⟨v, a, b, C, c⟩ ↦
    ⟨_, by simpa, fun ⟨i, q⟩ ↦ (c.1.isPlaceOver_below.exists_smul G (q ▸ s.isPlaceOver _)).rec fun g
    a ↦ b ⟨(i, g), (W _).unique (by simpa [smul_smul, ← a] using! c.1.smul (⟨_,
    QuotientGroup.eq.1 (e _)⟩ : B.1))⟩, C, c.imp_left .isPlaceOver_below⟩⟩), fun a b _ c ↦ u
    (s.inertiaGroup_le (by simpa) b.isPlaceOver_below c), fun F i e ↦ @s.principal_sup_idelesUnitOff
    (F.restrictScalars K) i fun _ a ⟨g, k⟩ ↦ e a ⟨⟨g, r k⟩, u k⟩⟩
  obtain ⟨rfl, t, k⟩ := s.v_injective (k _ ▸ q ▸ k _), (q ▸ W _).exists_smul B.1 (W _)
  exact congrArg _ (e a ▸ e θ.2 ▸ QuotientGroup.eq.2
    ((mul_mem_cancel_left t.2).1 (r (s.decompGroup_le (o θ) (by simpa [mul_smul])))))

include s

lemma SplitPlaces.mem_and_conj_mem g : g ∈ I → g ∈ U ∧ ∀ t, t⁻¹ * g * t ∈ I :=
  ext s.mem_inertia_iff ▸ fun ⟨w, a, b, _, c, d⟩ ↦
  ⟨s.inertiaGroup_le a c d, (⟨w, a, b, _, c.smul _, inv_inv · ▸ d.conj _⟩)⟩

import GRH.Lib.GaloisRep.Pseudocharacter.FibreSum
import GRH.Lib.ClassField.Global.NormTheorems
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Chebotarev's density theorem, existence form. Only existence is proved, namely
that Frobenius elements at primes of degree one outside a finite set are dense in the absolute
Galois group. No density value is given. Source: J. S. Milne, Class Field Theory, VIII 7.4
(Deuring's reduction); Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer
18 (1996).

Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Chebotarev, existence form: Frobenius elements at degree-one primes are dense. Filter of
most degree-one Frobenius elements; density and properness from Chebotarev. -/

open QZChar Filter QuotientGroup Subgroup Topology

/-- Chebotarev: for a non-empty open W ⊂ Γ = Gal(K̄/K) and a finite set S of primes, there is v
∉ S of prime norm with a place above it all of whose arithmetic Frobenius elements lie in W.

Known result: Chebotarev's density theorem, existence form. -/
lemma chebotarev {K : Type} [Field K] [NumberField K] [Algebra K Ω] {W : Set Gal(Ω/K)}
    (hW : IsOpen W) (h : W.Nonempty) {S} (hS : @Set.Finite (FinPlace K) S) : ∃ v ∉ S, v.q.Prime ∧
  ∃ A : ClosurePlace, IsPlaceOver A v ∧ ∃ σ ∈ W, IsFrob A v.q σ ∧ ∀ τ, IsFrob A v.q τ → τ ∈ W := by
  have ⟨⟨U, _⟩, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hW.preimage_of_continuous (f := (h.some * ·))) h.some_mem
  let H := (id ⟨zpowers h.some ⊔ U, isOpen_mono le_sup_right U.2⟩ : OpenSubgroup _).1
  obtain ⟨⟨χ, c⟩, a, ha⟩ := exists_ker_eq_of_isCyclic ⟨_, H.subgroupOf_isOpen _ U.2⟩
    ((quotientInfEquivProdNormalQuotient ..).isCyclic.1 (isCyclic_of_surjective _ (mk'_surjective
    _))), artinMap_surjective H ⟦⟨_, mem_sup_left (mem_zpowers _)⟩⟧
  have ⟨w, ⟨p, e⟩, r, s⟩ := (((second_inequality _ (continuous_iff_isOpen_ker.1 continuous_artinMap
    χ) (by simp_all [artinMap_principalIdele]) abelianLift_artinMap_adeleNorm).2.2
    a⁻¹).and_eventually (tendsto_place_comap_cofinite (algebraMap K _)
    ((finite_ramified U.2).and hS.compl_mem_cofinite))).exists
  have ⟨σ, hσ, F⟩ := w.isPlaceOver_placeOver.exists_frob_inv_eq_localArtin (Γ :=
    H) (v_uniformizer w)
  simp_all [w.isPlaceOver_placeOver.artinAt_eq_of_localArtin_eq F, inv_mul_eq_one,
    ← (w.below K).1.absNorm_pow_inertiaDeg, Nat.prime_iff]
  refine ⟨_, s, p.1, _, w.isPlaceOver_placeOver.isPlaceOver_below, σ, ?t _ hσ, hσ, ?t⟩
  simpa using fun _ h ↦ hU (div_mem (c.le ((toHom χ).eq_iff.1 e))
    (r _ w.isPlaceOver_placeOver.isPlaceOver_below (.inv_mul h hσ)))

/-- A finite place w of E of prime norm, a valuation subring A of Ω above w, and a geometric
Frobenius s in Gal(Ω/E) at A. -/
structure FrobeniusDatum (E : Type) [Field E] [EmbeddedNumberField E] where
  (w : FinPlace E) (valRing : ClosurePlace) (frob : Gal(Ω/E)) (prime_q : w.q.Prime) (isPlaceOver :
    IsPlaceOver valRing w) isFrob : IsFrob valRing w.q frob⁻¹

/-- The filter 'most Frobenii': each nonempty open set has a nonempty open part all of whose
geometric Frobenii (w, A, s), at almost all w of prime norm, lie in X. -/
def mostFrobenii (E : Type) [Field E] [EmbeddedNumberField E] : Filter (FrobeniusDatum E) :=
    ⟨{X | ∀ V, IsOpen V → V.Nonempty → ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧ ∀ᶠ w in cofinite, ∀ A s p o
    f, s ∈ O → ⟨w, A, s, p, o, f⟩ ∈ X}, by aesop, fun _ _ _ ↦ by grind [Eventually.mono], fun h k ↦
    (by choose O _ b c d using h · · ·; peel k O b c; grind [this.2.2.2.mp, d.mono])⟩

/-- The filter of most Frobenii tending to g: `mostFrobenii` on triples (w, A, s), refined by the
condition that s lies near g. -/
noncomputable abbrev mostFrobeniiAt (E : Type) [Field E] [EmbeddedNumberField E] g :=
  mostFrobenii E ⊓ (𝓝 g).comap (·.frob)

variable {E : Type} [Field E] [EmbeddedNumberField E]

lemma tendsto_mostFrobeniiAt {X g} [TopologicalSpace X] (f : _ → X) (h :
  Continuous f := by fun_prop) : Tendsto (f ·.frob) (mostFrobeniiAt E g) (𝓝 (f g)) :=
  (h.tendsto g).comp (by simp [tendsto_iff_comap])

lemma eventually_mostFrobenii {p q : _ → _} (h : cofinite.Eventually p) (H : ∀ x : FrobeniusDatum E,
  p x.w → q x := by exact fun _ ↦ id) : ∀ᶠ x in mostFrobenii E, q x := fun _ ↦ by grind [h.mono]

attribute [local simp] Set.Nonempty

lemma mostFrobenii_push {F} [Field F] [EmbeddedNumberField F] {φ} (hφ : IsOpenEmbedding φ) (π :
  FinPlace E → _) {X} (h : X ∈ mostFrobenii E) : ∀ᶠ y in mostFrobenii F, ∀ x, π x.w = y.w →
  φ x.frob = y.frob → x ∈ X := fun V o n ↦
  by_cases (let ⟨_, _, b, _, d⟩ := h _ (hφ.continuous.1 _ o) ·; ⟨_, by simpa, hφ.isOpenMap _
    b, by simpa, (d.image π).subset (by grind [hφ.1.2, FrobeniusDatum])⟩) (by simp_all; grind)

lemma dense_of_mostFrobenii {p} (h : ∀ᶠ x in mostFrobenii E, p x.frob) : Dense (Set.ofPred p) :=
  dense_iff_inter_open.2
  (let ⟨_, _, o, n, d⟩ := h · · ·; (chebotarev o.inv n.inv d).elim (by simp; tauto))

instance {g} : NeBot (mostFrobeniiAt E g) := neBot_inf_comap_iff_map.2
    (inf_neBot_iff.2 fun _ h _ ↦ (dense_of_mostFrobenii h).inter_nhds_nonempty)

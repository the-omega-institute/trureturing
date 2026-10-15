/- GID: D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/ConfigurationPathTransport
   mirror-E: none(waiver:implementation-owner-scope)
   anchors: []
   utility: none
   digest: Configuration ideal completion, finite-endpoint edge composition and graph transport. -/

import D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
import Mathlib.Order.Ideal
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity

universe u v
variable {E : Type u}

/-! ## Configurations and finite ideal completion -/

variable {E : Type u} [PartialOrder E]

def Configuration (compatible : Finset E → Prop) (C : Set E) : Prop :=
  IsLowerSet C ∧ ∀ s : Finset E, (↑s : Set E) ⊆ C → compatible s

def FiniteSubconfiguration (compatible : Finset E → Prop)
    (C K : Set E) : Prop :=
  K.Finite ∧ K ⊆ C ∧ Configuration compatible K

def FiniteDirected (F : Set (Set E)) : Prop :=
  ∀ s : Finset (Set E), (∀ C ∈ s, C ∈ F) →
    ∃ K ∈ F, ∀ C ∈ s, C ⊆ K

private theorem finite_upper_of_pairwise_directed
    {F : Set (Set E)} (hF : F.Nonempty)
    (hd : ∀ ⦃C D : Set E⦄, C ∈ F → D ∈ F →
      ∃ K ∈ F, C ⊆ K ∧ D ⊆ K) : FiniteDirected F := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      obtain ⟨K, hK⟩ := hF
      exact ⟨K, hK, by simp⟩
  | @insert C s hCs ih =>
      intro hs
      obtain ⟨L, hL, hLs⟩ := ih (fun D hD => hs D (Finset.mem_insert_of_mem hD))
      obtain ⟨K, hK, hCL, hLK⟩ := hd (hs C (Finset.mem_insert_self ..)) hL
      refine ⟨K, hK, ?_⟩
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hCL
      · exact (hLs D hD).trans hLK

private theorem configuration_union
    {compatible : Finset E → Prop} {F : Set (Set E)}
    (hcfg : ∀ C ∈ F, Configuration compatible C)
    (hdir : FiniteDirected F) :
    Configuration compatible (⋃₀ F) := by
  classical
  refine ⟨?_, ?_⟩
  · intro a b hab hb
    rcases Set.mem_sUnion.mp hb with ⟨C, hCF, hbC⟩
    exact Set.mem_sUnion.mpr ⟨C, hCF, (hcfg C hCF).1 hab hbC⟩
  · intro s hs
    let choose : ∀ e : {x // x ∈ s}, Set E := fun e =>
      Classical.choose (Set.mem_sUnion.mp (hs e.property))
    have hchoose : ∀ e : {x // x ∈ s}, choose e ∈ F ∧ e.1 ∈ choose e := by
      intro e
      exact Classical.choose_spec (Set.mem_sUnion.mp (hs e.property))
    let t : Finset (Set E) := s.attach.image choose
    have ht : ∀ C ∈ t, C ∈ F := by
      intro C hCt
      rcases Finset.mem_image.mp hCt with ⟨e, he, rfl⟩
      exact (hchoose e).1
    obtain ⟨K, hK, hKs⟩ := hdir t ht
    apply (hcfg K hK).2 s
    intro e he
    have heC := (hchoose ⟨e, he⟩).2
    exact hKs (choose ⟨e, he⟩)
      (Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_attach .., rfl⟩) heC

/-! ## Finite configuration ideals -/

abbrev Configurations (compatible : Finset E → Prop) :=
  {C : Set E // Configuration compatible C}

abbrev FiniteConfigurations (compatible : Finset E → Prop) :=
  {C : Set E // C.Finite ∧ Configuration compatible C}

noncomputable def finiteIdeal {compatible : Finset E → Prop}
    (hempty : compatible ∅) (C : Configurations compatible) :
    Order.Ideal (FiniteConfigurations compatible) where
  carrier := {K | K.1 ⊆ C.1}
  lower' := by
    intro K L h hK
    change K.1 ⊆ C.1 at hK
    change L.1 ⊆ K.1 at h
    exact fun e he => hK (h he)
  nonempty' := ⟨⟨∅, Set.finite_empty, by
    refine ⟨by simp [IsLowerSet], ?_⟩
    intro s hs
    have : s = ∅ := by simpa using hs
    simpa [this] using hempty⟩, Set.empty_subset _⟩
  directed' := by
    intro K hK L hL
    refine ⟨⟨K.1 ∪ L.1, K.2.1.union L.2.1, ?_⟩,
      Set.union_subset hK hL, Set.subset_union_left, Set.subset_union_right⟩
    exact ⟨K.2.2.1.union L.2.2.1,
      fun s hs => C.2.2 s (hs.trans (Set.union_subset hK hL))⟩

private theorem mem_finiteIdeal {compatible : Finset E → Prop}
    (hempty : compatible ∅) (C : Configurations compatible) (K : FiniteConfigurations compatible) :
    K ∈ finiteIdeal hempty C ↔ K.1 ⊆ C.1 := Iff.rfl

private theorem ideal_union_configuration {compatible : Finset E → Prop}
    (I : Order.Ideal (FiniteConfigurations compatible)) :
    Configuration compatible (⋃₀ (Subtype.val '' (I : Set (FiniteConfigurations compatible)))) := by
  apply configuration_union
  · rintro K ⟨k, hk, rfl⟩
    exact k.2.2
  · apply finite_upper_of_pairwise_directed
    · obtain ⟨k, hk⟩ := I.nonempty
      exact ⟨k.1, k, hk, rfl⟩
    · rintro C D ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      obtain ⟨k, hk, hck, hdk⟩ := I.directed c hc d hd
      exact ⟨k.1, ⟨k, hk, rfl⟩, hck, hdk⟩

private theorem finite_subset_ideal_union {compatible : Finset E → Prop}
    (I : Order.Ideal (FiniteConfigurations compatible))
    (K : FiniteConfigurations compatible)
    (hK : K.1 ⊆ ⋃₀ (Subtype.val '' (I : Set (FiniteConfigurations compatible)))) : K ∈ I := by
  classical
  have witness (e : K.1) : ∃ L : FiniteConfigurations compatible, L ∈ I ∧ e.1 ∈ L.1 := by
    rcases Set.mem_sUnion.mp (hK e.2) with ⟨L, ⟨k, hk, rfl⟩, he⟩
    exact ⟨k, hk, he⟩
  let pick (e : K.1) := Classical.choose (witness e)
  have hp (e : K.1) := Classical.choose_spec (witness e)
  letI : Fintype K.1 := K.2.1.fintype
  have upper : ∀ s : Finset (FiniteConfigurations compatible),
      (∀ k ∈ s, k ∈ I) → ∃ L ∈ I, ∀ k ∈ s, k ≤ L := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; obtain ⟨L, hL⟩ := I.nonempty; exact ⟨L, hL, by simp⟩
    | @insert k s hks ih =>
      intro hs
      obtain ⟨L, hL, hLs⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
      obtain ⟨M, hM, hkM, hLM⟩ := I.directed k (hs k (Finset.mem_insert_self ..)) L hL
      refine ⟨M, hM, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hkM
      · exact (hLs x hx).trans hLM
  obtain ⟨L, hL, hLs⟩ := upper (Finset.univ.image pick) (by
    intro k hk; rcases Finset.mem_image.mp hk with ⟨e, _, rfl⟩; exact (hp e).1)
  apply I.lower (a := L) (b := K) _ hL
  intro e he
  exact hLs (pick ⟨e, he⟩) (Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩)
    (hp ⟨e, he⟩).2

/-- All configurations, including infinite ones, are the ideal completion of their finite pieces. -/
noncomputable def configurationIdealIso {compatible : Finset E → Prop}
    (hempty : compatible ∅) (hpred : ∀ e : E, (Set.Iic e).Finite) :
    Configurations compatible ≃o Order.Ideal (FiniteConfigurations compatible) where
  toFun := finiteIdeal hempty
  invFun I := ⟨⋃₀ (Subtype.val '' (I : Set (FiniteConfigurations compatible))),
    ideal_union_configuration I⟩
  left_inv C := by
    apply Subtype.ext
    apply Set.Subset.antisymm
    · rintro e ⟨K, ⟨k, hk, rfl⟩, he⟩
      exact ((mem_finiteIdeal hempty C k).mp hk) he
    · intro e he
      have hI : Set.Iic e ⊆ C.1 := fun x hx => C.2.1 hx he
      let k : FiniteConfigurations compatible := ⟨Set.Iic e, hpred e,
        ⟨fun a b hab hb => hab.trans hb, fun s hs => C.2.2 s (hs.trans hI)⟩⟩
      exact Set.mem_sUnion.mpr ⟨k.1, ⟨k, ((mem_finiteIdeal hempty C k).mpr hI), rfl⟩, le_rfl⟩
  right_inv I := by
    apply Order.Ideal.ext
    ext K
    change (K.1 ⊆ ⋃₀ (Subtype.val '' (I : Set (FiniteConfigurations compatible)))) ↔ K ∈ I
    constructor
    · exact finite_subset_ideal_union I K
    · intro hK e he
      exact Set.mem_sUnion.mpr ⟨K.1, ⟨K, hK, rfl⟩, he⟩
  map_rel_iff' := by
    intro C D
    constructor
    · intro h e he
      change (↑(finiteIdeal hempty C) : Set (FiniteConfigurations compatible)) ⊆
          (↑(finiteIdeal hempty D) : Set (FiniteConfigurations compatible)) at h
      have hI : Set.Iic e ⊆ C.1 := fun x hx => C.2.1 hx he
      let k : FiniteConfigurations compatible := ⟨Set.Iic e, hpred e,
        ⟨fun a b hab hb => hab.trans hb, fun s hs => C.2.2 s (hs.trans hI)⟩⟩
      have hk : k ∈ finiteIdeal hempty D := h ((mem_finiteIdeal hempty C k).mpr hI)
      exact ((mem_finiteIdeal hempty D k).mp hk) le_rfl
    · intro h K hK
      exact (mem_finiteIdeal hempty D K).mpr (((mem_finiteIdeal hempty C K).mp hK).trans h)

/-! ## Finite endpoints in an arbitrary ambient poset -/

private theorem exec_data {I J : Set E} {l : List E} (hl : Exec I l J) :
    I ⊆ J ∧ l.Nodup ∧ (∀ e, e ∈ l ↔ e ∈ J ∧ e ∉ I) := by
  induction l generalizing I with
  | nil => cases hl; exact ⟨Set.Subset.rfl, by simp, by simp⟩
  | cons e l ih =>
    obtain ⟨he, ht⟩ := hl
    obtain ⟨hs, hn, hm⟩ := ih ht
    have heJ := hs (Set.mem_insert e I)
    have hel : e ∉ l := fun h => ((hm e).mp h).2 (Set.mem_insert e I)
    refine ⟨fun x hx => hs (Or.inr hx), List.nodup_cons.mpr ⟨hel, hn⟩, ?_⟩
    intro x
    simp only [List.mem_cons]
    constructor
    · rintro (rfl | hx)
      · exact ⟨heJ, he.1⟩
      · exact ⟨((hm x).mp hx).1, fun h => ((hm x).mp hx).2 (Or.inr h)⟩
    · rintro ⟨hxJ, hxI⟩
      by_cases hx : x = e
      · exact Or.inl hx
      · exact Or.inr ((hm x).mpr ⟨hxJ, by simpa using And.intro hx hxI⟩)

private theorem exec_subtype {J : Set E} (hJ : IsLowerSet J)
    (I K : Set E) (hI : I ⊆ J) (hK : K ⊆ J) (l : List J) :
    Exec (Subtype.val ⁻¹' I) l (Subtype.val ⁻¹' K) ↔ Exec I (l.map Subtype.val) K := by
  induction l generalizing I with
  | nil =>
    simp only [List.map_nil, Exec]
    constructor
    · intro h
      ext e
      constructor
      · intro he
        exact (congrArg (fun S : Set J => (⟨e, hI he⟩ : J) ∈ S) h).mp he
      · intro he
        exact (congrArg (fun S : Set J => (⟨e, hK he⟩ : J) ∈ S) h).mpr he
    · intro h; rw [h]
  | cons e l ih =>
    have hi : insert e.1 I ⊆ J := Set.insert_subset e.2 hI
    have eqinsert : Subtype.val ⁻¹' insert e.1 I = insert e (Subtype.val ⁻¹' I) := by
      ext x; simp [Subtype.ext_iff]
    have hen : Enabled (Subtype.val ⁻¹' I) e ↔ Enabled I e.1 := by
      constructor
      · rintro ⟨hf, hp⟩
        refine ⟨hf, fun d hd => hp ⟨d, hJ hd.le e.2⟩ hd⟩
      · rintro ⟨hf, hp⟩
        exact ⟨hf, fun d hd => hp d hd⟩
    simp only [List.map_cons, Exec]
    rw [hen, ← eqinsert, ih _ hi]

private theorem finite_exec_connectivity {I J : Set E} (hI : IsLowerSet I)
    (hJ : IsLowerSet J) (hIJ : I ⊆ J) (hfin : J.Finite) :
    (∃ l, Exec I l J) ∧
    (∀ l m, Exec I l J → Exec I m J →
      Relation.ReflTransGen (LegalSwap I J) l m) := by
  classical
  letI : Fintype J := hfin.fintype
  let I' : Set J := Subtype.val ⁻¹' I
  have hI' : IsLowerSet I' := fun a b hab hb => hI hab hb
  have lifted := result I' Set.univ hI' (by simp [IsLowerSet]) (Set.subset_univ _)
  have liftExec (l : List J) : Exec I' l Set.univ ↔ Exec I (l.map Subtype.val) J := by
    simpa [I'] using exec_subtype hJ I J hIJ Set.Subset.rfl l
  constructor
  · obtain ⟨l, hl⟩ := lifted.2.1
    exact ⟨l.map Subtype.val, (liftExec l).mp hl⟩
  · intro l m hl hm
    let l' : List J := l.attach.map (fun e : {e // e ∈ l} =>
      (⟨e.val, (((exec_data hl).2.2 e.val).mp e.property).1⟩ : J))
    let m' : List J := m.attach.map (fun e : {e // e ∈ m} =>
      (⟨e.val, (((exec_data hm).2.2 e.val).mp e.property).1⟩ : J))
    have hl' : l'.map Subtype.val = l := by simp [l']
    have hm' : m'.map Subtype.val = m := by simp [m']
    have chain := lifted.2.2 l' m' ((liftExec l').mpr (by simpa [hl'] using hl))
      ((liftExec m').mpr (by simpa [hm'] using hm))
    rw [← hl', ← hm']
    apply Relation.ReflTransGen.lift (List.map Subtype.val) _ _ _ chain
    intro a b hab
    obtain ⟨ha, hb, p, s, e, f, K, hea, heb, hp, hK, he, hf, hef, hfe⟩ := hab
    let K₀ : Set E := Subtype.val '' K
    have hK₀ : K₀ ⊆ J := fun x hx => by rcases hx with ⟨y, _, rfl⟩; exact y.2
    have hpre : Subtype.val ⁻¹' K₀ = K := by ext x; simp [K₀]
    have hIlower : IsLowerSet K₀ := by
      rintro x y hxy ⟨z, hz, rfl⟩
      exact ⟨⟨y, hJ hxy z.2⟩, hK hxy hz, rfl⟩
    have hp₀ : Exec I (p.map Subtype.val) K₀ :=
      (exec_subtype hJ I K₀ hIJ hK₀ p).mp (by simpa [I', hpre] using hp)
    have he₀ : Enabled K₀ e.1 := by
      refine ⟨fun hx => he.1 (by
        have hh : e ∈ Subtype.val ⁻¹' K₀ := hx
        rwa [hpre] at hh), ?_⟩
      intro d hd
      exact ⟨⟨d, hJ hd.le e.2⟩, he.2 _ hd, rfl⟩
    have hf₀ : Enabled K₀ f.1 := by
      refine ⟨fun hx => hf.1 (by
        have hh : f ∈ Subtype.val ⁻¹' K₀ := hx
        rwa [hpre] at hh), ?_⟩
      intro d hd
      exact ⟨⟨d, hJ hd.le f.2⟩, hf.2 _ hd, rfl⟩
    exact ⟨(liftExec a).mp ha, (liftExec b).mp hb,
      p.map Subtype.val, s.map Subtype.val, e.1, f.1, K₀,
      by simp [hea], by simp [heb], hp₀, hIlower, he₀, hf₀, hef, hfe⟩

/-- Finite endpoint configurations suffice; the event carrier need not be finite. -/
theorem exec_exists_iff_subset {I J : Set E}
    (hI : IsLowerSet I) (hJ : IsLowerSet J) (hfin : J.Finite) :
    (∃ l, Exec I l J) ↔ I ⊆ J :=
  ⟨fun ⟨_, h⟩ => (exec_data h).1, fun h => (finite_exec_connectivity hI hJ h hfin).1⟩

noncomputable def gapCard (I J : Finset E) : Nat := by
  classical
  exact (J \ I).card

private theorem exec_length_eq_gapCard {I J : Finset E} {l : List E}
    (hl : Exec (I : Set E) l J) : l.length = gapCard I J := by
  classical
  obtain ⟨_, hn, hm⟩ := exec_data hl
  have hset : l.toFinset = J \ I := by ext e; simp [hm e]
  rw [gapCard, ← hset, List.toFinset_card_of_nodup hn]

def pathWeight {R : Type v} [AddMonoid R] (weight : E → R) : List E → R
  | [] => 0
  | e :: l => weight e + pathWeight weight l

private theorem pathWeight_append {R : Type v} [AddMonoid R]
    (weight : E → R) (l m : List E) :
    pathWeight weight (l ++ m) = pathWeight weight l + pathWeight weight m := by
  induction l with
  | nil => simp [pathWeight]
  | cons e l ih => simp [pathWeight, ih, add_assoc]

noncomputable def clockFinite (observed : E → Prop) (weight : E → ℝ) (C : Finset E) : ℝ := by
  classical
  exact (C.filter observed).sum weight

/-- Subdivision preserves duration precisely when the piece weights sum to the original weight. -/
private theorem subdivision_iff (weight : E → ℝ) (e : E) (pieces tail : List E) :
    pathWeight weight (e :: tail) = pathWeight weight (pieces ++ tail) ↔
      weight e = pathWeight weight pieces := by
  simp [pathWeight, pathWeight_append]

/-- Strict observer-clock growth for finite configurations over an arbitrary carrier. -/
private theorem clockFinite_strict_of_new_observed {observed : E → Prop} {weight : E → ℝ}
    (hpos : ∀ e, observed e → 0 < weight e) {C D : Finset E}
    (hCD : C ⊆ D) {e : E} (heD : e ∈ D) (heC : e ∉ C) (heo : observed e) :
    clockFinite observed weight C < clockFinite observed weight D := by
  classical
  let A := C.filter observed
  let B := D.filter observed
  have hAB : A ⊆ B := Finset.filter_subset_filter observed hCD
  have heB : e ∈ B := by simp [B, heD, heo]
  have heA : e ∉ A := by simp [A, heC]
  have hdiff : 0 < Finset.sum (B \ A) weight := by
    apply Finset.sum_pos'
    · intro x hx
      exact (hpos x (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2).le
    · exact ⟨e, by simp [Finset.mem_sdiff, heB, heA], hpos e heo⟩
  have hsum := Finset.sum_sdiff hAB (f := weight)
  change Finset.sum A weight < Finset.sum B weight
  linarith

/-- Nested finite configurations have positive append-only histories with additive lengths,
monotone observer clocks, strict advance on each new counted event, and exact subdivision. -/
theorem finite_history_clocks (C D B : Finset E)
    (hC : IsLowerSet (C : Set E)) (hD : IsLowerSet (D : Set E))
    (hCD : C ⊆ D) (hDB : D ⊆ B) (observed : E → Prop) (weight : E → ℝ)
    (hpos : ∀ e, observed e → 0 < weight e) :
    ∃ l : List E, Exec (C : Set E) l D ∧ l.length = gapCard C D ∧
      (∀ m : List E, Exec (C : Set E) m D → m.length = gapCard C D) ∧
      gapCard C B = gapCard C D + gapCard D B ∧
      clockFinite observed weight C ≤ clockFinite observed weight D ∧
      ((∃ e ∈ D, e ∉ C ∧ observed e) →
        clockFinite observed weight C < clockFinite observed weight D) ∧
      (∀ m : List E, Exec (D : Set E) m C → l = []) ∧
      (∀ e pieces tail, pathWeight weight (e :: tail) = pathWeight weight (pieces ++ tail) ↔
        weight e = pathWeight weight pieces) := by
  classical
  obtain ⟨l,hl⟩ := (exec_exists_iff_subset hC hD D.finite_toSet).mpr hCD
  have hlen := exec_length_eq_gapCard hl
  refine ⟨l,hl,hlen,(fun _ hm => exec_length_eq_gapCard hm),?_,?_,?_,?_,subdivision_iff weight⟩
  · have hCB := hCD.trans hDB
    have ha := Finset.card_sdiff_add_card_eq_card hCD
    have hb := Finset.card_sdiff_add_card_eq_card hDB
    have hc := Finset.card_sdiff_add_card_eq_card hCB
    unfold gapCard
    omega
  · unfold clockFinite
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter observed hCD)
      (fun e he _ => (hpos e (Finset.mem_filter.mp he).2).le)
  · rintro ⟨e,heD,heC,heo⟩
    exact clockFinite_strict_of_new_observed hpos hCD heD heC heo
  · intro m hm
    have hDC : D ⊆ C := (exec_data hm).1
    have heq := Finset.Subset.antisymm hCD hDC
    have hz : l.length = 0 := by simpa [gapCard,heq] using hlen
    simpa only [List.length_eq_zero_iff] using hz

structure DependentReadout (E : Type u) [PartialOrder E] where
  fibre : Set E → Type v
  edge : ∀ {K : Set E} {e : E}, Enabled K e → fibre K → fibre (insert e K)

def pathMap (R : DependentReadout E) :
    ∀ {I J : Set E} (l : List E), Exec I l J → R.fibre I → R.fibre J
  | _, _, [], h, x => h ▸ x
  | _, _, e :: l, h, x => pathMap R l h.2 (R.edge h.1 x)

theorem exec_append {I K J : Set E} {p s : List E}
    (hp : Exec I p K) (hs : Exec K s J) : Exec I (p ++ s) J := by
  induction p generalizing I with
  | nil => cases hp; exact hs
  | cons e p ih => exact ⟨hp.1, ih hp.2⟩

theorem pathMap_append (R : DependentReadout E) {I K J : Set E}
    {p s : List E} (hp : Exec I p K) (hs : Exec K s J) (x : R.fibre I) :
    pathMap R (p ++ s) (exec_append hp hs) x = pathMap R s hs (pathMap R p hp x) := by
  induction p generalizing I with
  | nil => cases hp; rfl
  | cons e p ih => exact ih hp.2 (R.edge hp.1 x)

def PathIndependent (R : DependentReadout E) : Prop :=
  ∀ {I J : Set E}, IsLowerSet I → IsLowerSet J → J.Finite →
    ∀ (l m : List E) (hl : Exec I l J) (hm : Exec I m J) (x : R.fibre I),
      pathMap R l hl x = pathMap R m hm x

/-- The diamond contains only the two edge composites, with no surrounding path. -/
def DiamondCompatible (R : DependentReadout E) : Prop :=
  ∀ {K : Set E} {a b : E}, IsLowerSet K → K.Finite →
    ∀ (ha : Enabled K a) (hb : Enabled K b)
      (hab : Enabled (insert a K) b) (hba : Enabled (insert b K) a) (x : R.fibre K),
      pathMap R [a,b] (show Exec K [a,b] (insert b (insert a K)) from ⟨ha,hab,rfl⟩) x =
      pathMap R [b,a] (show Exec K [b,a] (insert b (insert a K)) from
        ⟨hb,hba,Set.insert_comm a b K⟩) x

/-- Local edge diamonds are equivalent to path independence on all finite-endpoint intervals. -/
theorem pathIndependent_iff_diamondCompatible (R : DependentReadout E) :
    PathIndependent R ↔ DiamondCompatible R := by
  constructor
  · intro hind K a b hK hf ha hb hab hba x
    have hlow (K : Set E) (a : E) (hK : IsLowerSet K) (ha : Enabled K a) :
        IsLowerSet (insert a K) := by
      intro y z hzy hy
      rcases hy with hy | hy
      · subst y
        by_cases hz : z = a
        · exact Or.inl hz
        · exact Or.inr (ha.2 z (lt_of_le_of_ne hzy hz))
      · exact Or.inr (hK hzy hy)
    have hcomm := Set.insert_comm b a K
    have hh := hind hK (hlow _ _ (hlow _ _ hK ha) hab) ((hf.insert a).insert b)
      [a,b] [b,a] ⟨ha, hab, rfl⟩ ⟨hb, hba, hcomm.symm⟩ x
    exact hh
  · intro hd I J hI hJ hfin l m hl hm x
    have chain := (finite_exec_connectivity hI hJ (exec_data hl).1 hfin).2 l m hl hm
    have swap : ∀ {l m}, LegalSwap I J l m →
        ∀ hl : Exec I l J, ∀ hm : Exec I m J,
          pathMap R l hl x = pathMap R m hm x := by
      intro l m h hl hm
      obtain ⟨_, _, p, s, a, b, K, rfl, rfl, hp, hK, ha, hb, hab, hba⟩ := h
      have haB : Enabled (insert b K) a :=
        ⟨by simp [ha.1, ne_of_not_le hab], fun d hd => Or.inr (ha.2 d hd)⟩
      have hbA : Enabled (insert a K) b :=
        ⟨by simp [hb.1, ne_of_not_le hba], fun d hd => Or.inr (hb.2 d hd)⟩
      have suffix : ∃ hs : Exec (insert b (insert a K)) s J, True := by
        have peel : ∀ {I K : Set E} {p t : List E}, Exec I p K →
            Exec I (p ++ t) J → Exec K t J := by
          intro I K p t hp ht
          induction p generalizing I with
          | nil => cases hp; exact ht
          | cons e p ih => exact ih hp.2 ht.2
        exact ⟨(peel hp hl).2.2, trivial⟩
      obtain ⟨hs, _⟩ := suffix
      have hKJ : K ⊆ J := fun e he => (exec_data hs).1 (Or.inr (Or.inr he))
      have hdiamond := hd hK (hfin.subset hKJ) ha hb hbA haB (pathMap R p hp x)
      have pairA : Exec K [a,b] (insert b (insert a K)) := ⟨ha,hbA,rfl⟩
      have pairB : Exec K [b,a] (insert b (insert a K)) := ⟨hb,haB,Set.insert_comm a b K⟩
      have left := pathMap_append R hp (exec_append pairA hs) x
      have right := pathMap_append R hp (exec_append pairB hs) x
      have left₂ := pathMap_append R pairA hs (pathMap R p hp x)
      have right₂ := pathMap_append R pairB hs (pathMap R p hp x)
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        left.trans (left₂.trans ((congrArg (fun y => pathMap R s hs y) hdiamond).trans
          (right₂.symm.trans right.symm)))
    have go : ∀ {l m}, Relation.ReflTransGen (LegalSwap I J) l m →
      ∀ hl : Exec I l J, ∀ hm : Exec I m J,
        pathMap R l hl x = pathMap R m hm x := by
      intro a b h
      induction h with
      | refl => intros; rfl
      | @tail b c hab hbc ih =>
        intro ha hc
        exact (ih ha hbc.1).trans (swap hbc hbc.1 hc)
    exact go chain hl hm

/-! ## Arbitrary graph transport and root fixed points -/

structure BiGraph (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ {v w}, Adj v w → Adj w v

inductive Walk {V : Type u} (G : BiGraph V) : V → V → Type u
  | nil (v : V) : Walk G v v
  | cons {v w z : V} (h : G.Adj v w) (p : Walk G w z) : Walk G v z

def Walk.append {V : Type u} {G : BiGraph V} :
    {u v w : V} → Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil _, q => q
  | _, _, _, .cons h p, q => .cons h (Walk.append p q)

def Walk.reverse {V : Type u} {G : BiGraph V} :
    {v w : V} → Walk G v w → Walk G w v
  | _, _, .nil v => .nil v
  | _, _, .cons h p => Walk.append p.reverse (.cons (G.symm h) (.nil _))

structure EdgeTransport {V : Type u} (G : BiGraph V) (F : V → Type v) where
  edge : ∀ {v w}, G.Adj v w → F v ≃ F w
  reverse : ∀ {v w} (h : G.Adj v w), edge (G.symm h) = (edge h).symm
  walk : ∀ {v w}, Walk G v w → F v ≃ F w
  walk_nil : ∀ v, walk (.nil v) = Equiv.refl _
  walk_cons : ∀ {v w z} (h : G.Adj v w) (p : Walk G w z),
    walk (.cons h p) = (edge h).trans (walk p)
  walk_append : ∀ {u v w} (p : Walk G u v) (q : Walk G v w),
    walk (Walk.append p q) = (walk p).trans (walk q)
  walk_reverse : ∀ {v w} (p : Walk G v w),
    walk p.reverse = (walk p).symm

/-- Walk transport is constructed from edges; its laws are no longer client assumptions. -/
def edgeWalk {V : Type u} {G : BiGraph V} {F : V → Type v}
    (edge : ∀ {v w}, G.Adj v w → F v ≃ F w) :
    ∀ {v w}, Walk G v w → F v ≃ F w
  | _, _, .nil _ => Equiv.refl _
  | _, _, .cons h p => (edge h).trans (edgeWalk edge p)

private theorem edgeWalk_append {V : Type u} {G : BiGraph V} {F : V → Type v}
    (edge : ∀ {v w}, G.Adj v w → F v ≃ F w)
    {a b c : V} (p : Walk G a b) (q : Walk G b c) :
    edgeWalk edge (p.append q) = (edgeWalk edge p).trans (edgeWalk edge q) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [Walk.append, edgeWalk, ih, Equiv.trans_assoc]

private theorem edgeWalk_reverse {V : Type u} {G : BiGraph V} {F : V → Type v}
    (edge : ∀ {v w}, G.Adj v w → F v ≃ F w)
    (rev : ∀ {v w} (h : G.Adj v w), edge (G.symm h) = (edge h).symm)
    {a b : V} (p : Walk G a b) : edgeWalk edge p.reverse = (edgeWalk edge p).symm := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [Walk.reverse, edgeWalk_append, ih]
    simp only [edgeWalk, Equiv.trans_refl, Equiv.symm_trans]
    rw [rev h]

def EdgeTransport.ofEdges {V : Type u} {G : BiGraph V} {F : V → Type v}
    (edge : ∀ {v w}, G.Adj v w → F v ≃ F w)
    (rev : ∀ {v w} (h : G.Adj v w), edge (G.symm h) = (edge h).symm) : EdgeTransport G F where
  edge := edge
  reverse := rev
  walk := edgeWalk edge
  walk_nil _ := rfl
  walk_cons _ _ := rfl
  walk_append := edgeWalk_append edge
  walk_reverse := edgeWalk_reverse edge rev

/-- Coordinate changes alter transport only. The walk and each literal edge occurrence remain. -/
def Walk.length {V : Type u} {G : BiGraph V} : ∀ {v w}, Walk G v w → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ p => p.length + 1

def GraphConnectedFrom {V : Type u} (G : BiGraph V) (r : V) : Prop :=
  ∀ v, Nonempty (Walk G r v)

def RootFixed {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) (r : V) (x : F r) : Prop :=
  ∀ p : Walk G r r, T.walk p x = x

noncomputable def rootSection
    {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) (r : V) (hc : GraphConnectedFrom G r)
    (x : F r) : ∀ v, F v :=
  fun v => T.walk (Classical.choice (hc v)) x

private theorem rootSection_parallel
    {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) (r : V) (hc : GraphConnectedFrom G r)
    {x : F r} (hfix : RootFixed T r x) {v w : V} (h : G.Adj v w) :
    T.edge h (rootSection T r hc x v) = rootSection T r hc x w := by
  classical
  let p : ∀ v, Walk G r v := fun v => Classical.choice (hc v)
  let loop : Walk G r r := Walk.append (Walk.append (p v) (.cons h (.nil w)))
      (p w).reverse
  have hloop := hfix loop
  have hh := congrArg (fun y => T.walk (p w) y) hloop
  dsimp [loop] at hh
  simp only [T.walk_append, T.walk_cons, T.walk_nil, T.walk_reverse,
    Equiv.trans_apply, Equiv.apply_symm_apply] at hh
  change T.edge h (T.walk (p v) x) = T.walk (p w) x
  simpa using hh

def Section {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) : Type _ :=
  {s : ∀ v, F v // ∀ {v w} (h : G.Adj v w), T.edge h (s v) = s w}

def RootFixedPoint {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) (r : V) : Type _ :=
  {x : F r // RootFixed T r x}

noncomputable def rootSectionMap
    {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) (r : V) (hc : GraphConnectedFrom G r) :
    RootFixedPoint T r → Section T := fun x =>
      ⟨rootSection T r hc x.1, rootSection_parallel T r hc x.2⟩

theorem rootSectionMap_bijective
    {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) (r : V) (hc : GraphConnectedFrom G r) :
    Function.Bijective (rootSectionMap T r hc) := by
  classical
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hr := congrArg (fun s : Section T => s.1 r) hxy
    let p : Walk G r r := Classical.choice (hc r)
    exact (x.2 p).symm.trans (hr.trans (y.2 p))
  · intro s
    let p : ∀ v, Walk G r v := fun v => Classical.choice (hc v)
    have walk_section : ∀ {a b : V} (q : Walk G a b),
        T.walk q (s.1 a) = s.1 b := by
      intro a b q
      induction q with
      | nil => simpa [T.walk_nil]
      | cons h q ih =>
          simpa [T.walk_cons, Equiv.trans_apply, s.2 h] using ih
    have hs : RootFixed T r (s.1 r) := by
      intro q
      exact walk_section q
    refine ⟨⟨s.1 r, hs⟩, ?_⟩
    apply Subtype.ext
    funext v
    exact walk_section (p v)

/-- Transport on the standard SimpleGraph walk carrier. -/
def simpleEdgeWalk {V : Type u} {G : SimpleGraph V} {F : V → Type v}
    (edge : ∀ {v w}, G.Adj v w → F v ≃ F w) :
    ∀ {v w}, G.Walk v w → F v ≃ F w
  | _, _, .nil => Equiv.refl _
  | _, _, .cons h p => (edge h).trans (simpleEdgeWalk edge p)

private theorem simpleEdgeWalk_concat {V : Type u} {G : SimpleGraph V} {F : V → Type v}
    (edge : ∀ {v w}, G.Adj v w → F v ≃ F w)
    {r v w : V} (p : G.Walk r v) (h : G.Adj v w) :
    simpleEdgeWalk edge (p.concat h) = (simpleEdgeWalk edge p).trans (edge h) := by
  induction p with
  | nil => rfl
  | cons h' p ih =>
    change (edge h').trans (simpleEdgeWalk edge (p.concat h)) = _
    simp only [ih, simpleEdgeWalk, Equiv.trans_assoc]

/-- For every rooted tree, unique root paths give coordinates in which every edge is identity.
No loop-flatness assumption is made. Only invertibility and reversal of the actual edge maps are used. -/
theorem tree_coordinate_trivialization {V : Type u} {G : SimpleGraph V} {F : V → Type v}
    (hG : G.IsTree) (r : V) (edge : ∀ {v w}, G.Adj v w → F v ≃ F w)
    (rev : ∀ {v w} (h : G.Adj v w), edge h.symm = (edge h).symm) :
    ∃ coordinates : ∀ v, F r ≃ F v,
      ∀ {v w} (h : G.Adj v w),
        ((coordinates v).trans (edge h)).trans (coordinates w).symm = Equiv.refl (F r) := by
  classical
  let p (v : V) : G.Walk r v := Classical.choose (hG.existsUnique_path r v)
  have hp (v : V) : (p v).IsPath := (Classical.choose_spec (hG.existsUnique_path r v)).1
  let coordinates (v : V) := simpleEdgeWalk edge (p v)
  refine ⟨coordinates, ?_⟩
  intro v w h
  have hcoord : (coordinates v).trans (edge h) = coordinates w := by
    by_cases hv : v ∈ (p w).support
    · have heq := hG.isAcyclic.path_concat (hp v) (hp w) h hv
      exact (simpleEdgeWalk_concat edge (p v) h).symm.trans (congrArg (simpleEdgeWalk edge) heq.symm)
    · have hw := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (hp v) (hp w) h hv
      have heq := hG.isAcyclic.path_concat (hp w) (hp v) h.symm hw
      have hh : coordinates v = (coordinates w).trans (edge h).symm := by
        rw [show coordinates v = simpleEdgeWalk edge (p v) from rfl, heq,
          simpleEdgeWalk_concat, rev]
      rw [hh]
      ext x
      simp
  rw [hcoord]
  ext x
  simp

#print axioms pathIndependent_iff_diamondCompatible
#print axioms rootSectionMap_bijective
#print axioms tree_coordinate_trivialization
end D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

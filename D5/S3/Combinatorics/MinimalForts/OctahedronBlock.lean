/- GID: D5/S3/Combinatorics/MinimalForts/OctahedronBlock
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/OctahedronBlock
   mirror-E: none(waiver:structural-counting-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite]
   utility: none
   digest: Structural classification and counting for complete equipartite graphs with two vertices per part. -/

import D5.S3.Combinatorics.MinimalForts.UniversalRoot
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Data.Fintype.BigOperators

/-! Whole parts and transversals describe all minimal forts without a bound on the number of parts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.OctahedronBlock

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.MinimalForts.UniversalRoot
open D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

private abbrev graph (m : ℕ) := SimpleGraph.completeEquipartiteGraph m 2

/-- The whole two-vertex part indexed by i. -/
def part {m : ℕ} (i : Fin m) : Finset (Fin m × Fin 2) := {(i, 0), (i, 1)}

/-- A transversal contains at most one vertex from each part. -/
def Transversal {m : ℕ} (S : Finset (Fin m × Fin 2)) : Prop :=
  Set.InjOn Prod.fst (S : Set (Fin m × Fin 2))

private theorem mem_part {m : ℕ} (i : Fin m) (v : Fin m × Fin 2) :
    v ∈ part i ↔ v.1 = i := by
  rcases v with ⟨j,b⟩
  fin_cases b <;> simp [part, Prod.mk.injEq]

private theorem card_part {m : ℕ} (i : Fin m) : (part i).card = 2 := by
  simp [part]

private theorem no_isolated (m : ℕ) (hm : 2 ≤ m) (v : Fin m × Fin 2) :
    ∃ w, (graph m).Adj v w := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨j,hj⟩ := exists_ne v.1
  exact ⟨(j,0), hj.symm⟩

private theorem neighbors (m : ℕ) (S : Finset (Fin m × Fin 2)) (v : Fin m × Fin 2) :
    finiteNeighbors (graph m) v ∩ S = S \ part v.1 := by
  ext w
  simp [finiteNeighbors, SimpleGraph.completeEquipartiteGraph_adj, mem_part, and_comm,
    ne_comm]

private theorem outside_fiber {m : ℕ} (S : Finset (Fin m × Fin 2))
    (v : Fin m × Fin 2) (hv : v ∉ S) : (S ∩ part v.1).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := (mem_part _ a).mp (Finset.mem_inter.mp ha).2
  have hb' := (mem_part _ b).mp (Finset.mem_inter.mp hb).2
  rcases v with ⟨i,c⟩
  rcases a with ⟨j,d⟩
  rcases b with ⟨k,e⟩
  dsimp at ha' hb'
  subst j; subst k
  have hd : (i,d) ∈ S := (Finset.mem_inter.mp ha).1
  have he : (i,e) ∈ S := (Finset.mem_inter.mp hb).1
  fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all

private theorem large_fort {m : ℕ} (S : Finset (Fin m × Fin 2)) (hc : 3 ≤ S.card) :
    IsFort (graph m) S := by
  refine ⟨Finset.card_pos.mp (by omega), ?_⟩
  intro v hv
  rw [neighbors, Finset.card_sdiff, Finset.inter_comm]
  have := outside_fiber S v hv
  omega

private theorem part_fort {m : ℕ} (i : Fin m) : IsFort (graph m) (part i) := by
  refine ⟨⟨(i,0), by simp [part]⟩, ?_⟩
  intro v hv
  have hi : v.1 ≠ i := by simpa [mem_part] using hv
  have he : finiteNeighbors (graph m) v ∩ part i = part i := by
    ext w
    simp only [Finset.mem_inter, finiteNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, SimpleGraph.completeEquipartiteGraph_adj]
    exact and_iff_right_of_imp (fun hw => by simpa [(mem_part _ _).mp hw] using hi)
  rw [he, card_part]
  omega

private theorem transversal_iff {m : ℕ} (S : Finset (Fin m × Fin 2)) :
    Transversal S ↔ ∀ i, ¬ part i ⊆ S := by
  constructor
  · intro h i hp
    have he := h (hp (by simp [part] : (i,0) ∈ part i))
      (hp (by simp [part] : (i,1) ∈ part i)) rfl
    have : (0 : Fin 2) = 1 := congrArg Prod.snd he
    exact (by decide : (0 : Fin 2) ≠ 1) this
  · intro h a ha b hb hab
    rcases a with ⟨i,c⟩
    rcases b with ⟨j,d⟩
    dsimp at hab
    subst j
    by_contra hne
    apply h i
    intro v hv
    have hv' := (mem_part _ _).mp hv
    rcases v with ⟨j,e⟩
    dsimp at hv'
    subst j
    fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all

private theorem transversal_fort_card {m : ℕ} (m2 : 2 ≤ m)
    (S : Finset (Fin m × Fin 2)) (ht : Transversal S) (hf : IsFort (graph m) S) :
    3 ≤ S.card := by
  have hpos := Finset.card_pos.mpr hf.1
  have hone := fort_card_ne_one (graph m) (no_isolated m m2) hf
  by_contra h
  have hc : S.card = 2 := by omega
  obtain ⟨a,ha⟩ := hf.1
  let v : Fin m × Fin 2 := (a.1, if a.2 = 0 then 1 else 0)
  have hfst : v.1 = a.1 := rfl
  have hne : v ≠ a := by
    rcases a with ⟨i,b⟩
    fin_cases b <;> simp [v]
  have hv : v ∉ S := fun hv => hne (ht hv ha hfst)
  have he : S ∩ part v.1 = {a} := by
    ext w
    constructor
    · intro hw
      exact Finset.mem_singleton.mpr (ht (Finset.mem_inter.mp hw).1 ha
        ((mem_part _ _).mp (Finset.mem_inter.mp hw).2 |>.trans hfst))
    · intro hw
      have hw' := Finset.mem_singleton.mp hw
      subst w
      exact Finset.mem_inter.mpr ⟨ha, (mem_part _ _).mpr hfst.symm⟩
  have := hf.2 v hv
  rw [neighbors, Finset.card_sdiff, Finset.inter_comm, he, Finset.card_singleton, hc] at this
  exact this rfl

/-- Every actual subset is minimal exactly when it is a whole part or a three-part transversal. -/
theorem equipartite_minimal_iff (m : ℕ) (hm : 2 ≤ m) (S : Finset (Fin m × Fin 2)) :
    MinimalFort (graph m) S ↔ (∃ i, S = part i) ∨ (S.card = 3 ∧ Transversal S) := by
  constructor
  · rintro ⟨hf,hmin⟩
    by_cases hp : ∃ i, part i ⊆ S
    · obtain ⟨i,hi⟩ := hp
      exact Or.inl ⟨i, Finset.Subset.antisymm (hmin _ hi (part_fort i)) hi⟩
    · have ht : Transversal S := (transversal_iff S).mpr (by simpa using hp)
      have hc := transversal_fort_card hm S ht hf
      obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq hc
      have he := hmin T hTS (large_fort T (by omega))
      exact Or.inr ⟨le_antisymm (hT ▸ Finset.card_le_card he) hc, ht⟩
  · rintro (⟨i,rfl⟩ | ⟨hc,ht⟩)
    · refine ⟨part_fort i, ?_⟩
      intro T hT hf
      have hn := Finset.card_pos.mpr hf.1
      have hne := fort_card_ne_one (graph m) (no_isolated m hm) hf
      have hle := Finset.card_le_card hT
      rw [card_part] at hle
      have he : T = part i := Finset.eq_of_subset_of_card_le hT (by rw [card_part]; omega)
      exact he ▸ Finset.Subset.refl _
    · refine ⟨large_fort S (by omega), ?_⟩
      intro T hT hf
      have htT : Transversal T := fun _ ha _ hb he => ht (hT ha) (hT hb) he
      have hthree := transversal_fort_card hm T htT hf
      have he : T = S := Finset.eq_of_subset_of_card_le hT (by omega)
      exact he ▸ Finset.Subset.refl _

private theorem pair_dominating {m : ℕ} (a b : Fin m × Fin 2) (hab : a.1 ≠ b.1) :
    (graph m).IsDominating (({a,b} : Finset _) : Set _) := by
  intro v
  by_cases ha : v.1 = a.1
  · exact Or.inr ⟨b, by simp, by change v.1 ≠ b.1; exact ha ▸ hab⟩
  · exact Or.inr ⟨a, by simp, ha⟩

private theorem singleton_not_dominating {m : ℕ} (a : Fin m × Fin 2) :
    ¬ (graph m).IsDominating (({a} : Finset _) : Set _) := by
  intro h
  let v : Fin m × Fin 2 := (a.1, if a.2 = 0 then 1 else 0)
  have hne : v ≠ a := by
    rcases a with ⟨i,b⟩
    fin_cases b <;> simp [v]
  rcases h v with hv | ⟨w,hw,hadj⟩
  · exact hne (by simpa using hv)
  · have hw' : w = a := by simpa using hw
    subst w
    exact hadj rfl

private theorem dominating_contains_pair {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (Fin m × Fin 2)) (hd : (graph m).IsDominating (S : Set _))
    (ht : Transversal S) : ∃ a ∈ S, ∃ b ∈ S, a.1 ≠ b.1 := by
  haveI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  let v : Fin m × Fin 2 := (Classical.choice inferInstance,0)
  have hn : S.Nonempty := by
    rcases hd v with hv | ⟨w,hw,_⟩
    · exact ⟨v,hv⟩
    · exact ⟨w,hw⟩
  obtain ⟨a,ha⟩ := hn
  by_contra h
  have he : S = {a} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨ha, ?_⟩
    intro b hb
    apply ht hb ha
    by_contra hne
    exact h ⟨b,hb,a,ha,hne⟩
  exact singleton_not_dominating a (he ▸ hd)

/-- The root-containing minimal forts correspond exactly to pairs from distinct parts. -/
theorem equipartite_rooted_iff (m : ℕ) (hm : 2 ≤ m) (S : Finset (Fin m × Fin 2)) :
    MinimalFort (cone (graph m)) (rootSet S) ↔ S.card = 2 ∧ Transversal S := by
  rw [minimalFort_rootSet_iff (graph m) (no_isolated m hm)]
  constructor
  · rintro ⟨hd,hfree⟩
    have ht : Transversal S := (transversal_iff S).mpr
      (fun i hi => hfree _ hi (part_fort i))
    obtain ⟨a,ha,b,hb,hab⟩ := dominating_contains_pair hm S hd.1 ht
    have hp : ({a,b} : Finset _) ⊆ S := by simp [Finset.insert_subset_iff,ha,hb]
    have he : S = {a,b} := Finset.Subset.antisymm
      (hd.2 _ hp (pair_dominating a b hab)) hp
    refine ⟨?_,ht⟩
    rw [he]
    simp [show a ≠ b from fun he => hab (congrArg Prod.fst he)]
  · rintro ⟨hc,ht⟩
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hp : ({a,b} : Finset _) ⊆ S := by simp [Finset.insert_subset_iff,ha,hb]
    have he : S = {a,b} := (Finset.eq_of_subset_of_card_le hp (by simpa [hab] using hc.ge)).symm
    have hparts : a.1 ≠ b.1 := fun h => hab (ht ha hb h)
    refine ⟨⟨he ▸ pair_dominating a b hparts, ?_⟩, ?_⟩
    · intro T hTS hdom v hv
      have haT : a ∈ T := by
        by_contra hna
        have hsub : T ⊆ ({b} : Set _) := by
          intro w hw
          have : w ∈ ({a,b} : Finset _) := he ▸ hTS hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · exact False.elim (hna hw)
          · rfl
        exact singleton_not_dominating b (fun w => by
          rcases hdom w with hw | ⟨u,hu,hadj⟩
          · exact Or.inl (hsub hw)
          · exact Or.inr ⟨u,hsub hu,hadj⟩)
      have hbT : b ∈ T := by
        by_contra hnb
        have hsub : T ⊆ ({a} : Set _) := by
          intro w hw
          have : w ∈ ({a,b} : Finset _) := he ▸ hTS hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · rfl
          · exact False.elim (hnb hw)
        exact singleton_not_dominating a (fun w => by
          rcases hdom w with hw | ⟨u,hu,hadj⟩
          · exact Or.inl (hsub hw)
          · exact Or.inr ⟨u,hsub hu,hadj⟩)
      have : v ∈ ({a,b} : Finset _) := he ▸ hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl <;> assumption
    · intro T hTS hf
      have htT : Transversal T := fun _ ha _ hb he => ht (hTS ha) (hTS hb) he
      have hthree := transversal_fort_card hm T htT hf
      have hle := Finset.card_le_card hTS
      omega

private def transversals (m k : ℕ) : Finset (Finset (Fin m × Fin 2)) :=
  by classical exact Finset.univ.filter (fun S => S.card = k ∧ Transversal S)

private def selections (m k : ℕ) :=
  Σ I : {I : Finset (Fin m) // I ∈ (Finset.univ : Finset (Fin m)).powersetCard k},
    (I.val → Fin 2)

private instance selections_fintype (m k : ℕ) : Fintype (selections m k) :=
  inferInstanceAs (Fintype (Σ I : {I : Finset (Fin m) // I ∈
    (Finset.univ : Finset (Fin m)).powersetCard k}, (I.val → Fin 2)))

private def encode {m k : ℕ} (p : selections m k) : Finset (Fin m × Fin 2) :=
  p.1.val.attach.image (fun i => (i.val, p.2 i))

private theorem encode_support {m k : ℕ} (p : selections m k) :
    (encode p).image Prod.fst = p.1.val := by
  ext i
  simp [encode]

private theorem encode_card {m k : ℕ} (p : selections m k) : (encode p).card = k := by
  rw [encode, Finset.card_image_of_injective]
  · simpa using (Finset.mem_powersetCard.mp p.1.property).2
  · intro a b h
    exact Subtype.ext (congrArg Prod.fst h)

private theorem encode_transversal {m k : ℕ} (p : selections m k) : Transversal (encode p) := by
  intro a ha b hb h
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
  have hij : i = j := Subtype.ext h
  subst j
  rfl

private theorem encode_injective (m k : ℕ) : Function.Injective (@encode m k) := by
  intro p q h
  have hI : p.1 = q.1 := Subtype.ext (by
    rw [← encode_support p, ← encode_support q, h])
  rcases p with ⟨I,f⟩
  rcases q with ⟨J,g⟩
  dsimp at hI
  subst J
  congr 1
  funext i
  have hi : (i.val,f i) ∈ encode ⟨I,g⟩ := h ▸ (by simp [encode])
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hi
  have hji : j = i := Subtype.ext (congrArg Prod.fst hj)
  subst j
  exact (congrArg Prod.snd hj).symm

private theorem encode_surjective {m k : ℕ} (S : Finset (Fin m × Fin 2))
    (hc : S.card = k) (ht : Transversal S) : ∃ p : selections m k, encode p = S := by
  classical
  let I := S.image Prod.fst
  have hI : I ∈ (Finset.univ : Finset (Fin m)).powersetCard k := by
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact (Finset.card_image_of_injOn ht).trans hc
  have hex (i : I) : ∃ b : Fin 2, (i.val,b) ∈ S := by
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp i.property
    exact ⟨v.2, by simpa [he] using hv⟩
  let f : I → Fin 2 := fun i => Classical.choose (hex i)
  refine ⟨⟨⟨I,hI⟩,f⟩, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact Classical.choose_spec (hex i)
  · intro hv
    let i : I := ⟨v.1, Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩
    have hf : (i.val,f i) ∈ S := Classical.choose_spec (hex i)
    have he : (i.val,f i) = v := ht hf hv rfl
    exact Finset.mem_image.mpr ⟨i, Finset.mem_attach _ _, he⟩

private theorem transversal_count (m k : ℕ) :
    (transversals m k).card = m.choose k * 2 ^ k := by
  classical
  have he : transversals m k = Finset.univ.image (@encode m k) := by
    ext S
    simp only [transversals, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hc,ht⟩
      obtain ⟨p,hp⟩ := encode_surjective S hc ht
      exact ⟨p,trivial,hp⟩
    · rintro ⟨p,_,rfl⟩
      exact ⟨encode_card p, encode_transversal p⟩
  rw [he, Finset.card_image_of_injective _ (encode_injective m k), Finset.card_univ]
  change Fintype.card (Σ I : {I : Finset (Fin m) // I ∈
    (Finset.univ : Finset (Fin m)).powersetCard k}, (I.val → Fin 2)) = _
  rw [Fintype.card_sigma]
  have hc (I : {I : Finset (Fin m) // I ∈ (Finset.univ : Finset (Fin m)).powersetCard k}) :
      Fintype.card (I.val → Fin 2) = 2 ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
      (Finset.mem_powersetCard.mp I.property).2]
  simp_rw [hc]
  simp [Finset.card_powersetCard]

/-- For every m at least two, the full fort and rooted families have polynomial binomial counts. -/
theorem equipartite_block (m : ℕ) (hm : 2 ≤ m) :
    Fintype.card (Fin m × Fin 2) = 2 * m ∧
    (minimalForts (graph m)).card = m + 8 * m.choose 3 ∧
    (rootedChoices (graph m)).card = 4 * m.choose 2 ∧
    ∀ v, ∃ w, (graph m).Adj v w := by
  classical
  refine ⟨by simp [Fintype.card_prod, Nat.mul_comm], ?_, ?_, no_isolated m hm⟩
  · have he : minimalForts (graph m) =
        (Finset.univ.image (@part m)) ∪ transversals m 3 := by
      ext S
      simp [minimalForts, equipartite_minimal_iff m hm, transversals, eq_comm]
    have hinj : Function.Injective (@part m) := by
      intro i j h
      have hi : (i,0) ∈ part j := h ▸ (by simp [part])
      exact (mem_part _ _).mp hi
    have hd : Disjoint (Finset.univ.image (@part m)) (transversals m 3) := by
      apply Finset.disjoint_left.mpr
      intro S hS ht
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
      have hc : (part i).card = 3 := (Finset.mem_filter.mp ht).2.1
      rw [card_part] at hc
      omega
    rw [he, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      transversal_count]
    omega
  · have he : rootedChoices (graph m) = transversals m 2 := by
      ext S
      simp [rootedChoices, transversals, equipartite_rooted_iff m hm]
    rw [he, transversal_count]
    omega

end D5.S3.Combinatorics.MinimalForts.OctahedronBlock

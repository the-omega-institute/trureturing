/- GID: D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.claim; result=D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.result; claim=D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.claim
   digest: A ten-vertex complex refutes normality preservation under flag completion. -/
/-
result — proof_shape: content (ridge-attachment path induction after inlining helpers).
escape_witness: none; admission_basis: open-problem-resolution (#29020; Refuted).
Direct frozen dependencies:
D5/S3/Geometry/FiniteRelativeSimplicialCollapse.AugmentedFace
  statement_id sha256:911ffbeb7ce4327a7412871a12eb37705920aa8156170875f1d400742c0449e8
D5/S3/Geometry/FiniteGraphVertexSubstitution.independenceComplex
  statement_id sha256:4db613ecb6e1058712d0d5830e27c07ab8925aeee97f7b3954b8d9b62768cd21
D5/S3/Geometry/FiniteAlexanderDualCollapse.simplex
  statement_id sha256:3cc96b8ebc13a31af97b073de8c5c256a8c4ebbc7c9b2b29bba0e22ee8d07bc4
The facet and minimal-nonface conditions and clique completion are written out;
proofs use the existing augmented-face and independence-complex definitions.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import D5.S3.Geometry.FiniteGraphVertexSubstitution
import D5.S3.Geometry.FiniteAlexanderDualCollapse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace D5.S3.Combinatorics.SimplicialComplexes.BenedettiMenaraNormalityRefutation

def Pure {n : ℕ} (K : AbstractSimplicialComplex (Fin n)) (d : ℕ) : Prop :=
  (∃ F : Finset (Fin n), (F ∈ K ∧ ∀ T : Finset (Fin n), T ∈ K → F ⊆ T → T = F)) ∧
    ∀ F : Finset (Fin n), (F ∈ K ∧ ∀ T : Finset (Fin n), T ∈ K → F ⊆ T → T = F) → F.card = d

def dualGraph {n : ℕ} (K : AbstractSimplicialComplex (Fin n)) (d : ℕ) : SimpleGraph ({F : Finset (Fin n) // (F ∈ K ∧ ∀ T : Finset (Fin n), T ∈ K → F ⊆ T → T = F)}) :=
  SimpleGraph.fromRel fun F H => (F.val ∩ H.val).card + 1 = d

def Normal {n : ℕ} (K : AbstractSimplicialComplex (Fin n)) (d : ℕ) : Prop :=
  ∀ sigma : Finset (Fin n), D5.S3.Geometry.FiniteRelativeSimplicialCollapse.AugmentedFace K.toPreAbstractSimplicialComplex sigma →
    ((dualGraph K d).induce {F : {F : Finset (Fin n) // (F ∈ K ∧ ∀ T : Finset (Fin n), T ∈ K → F ⊆ T → T = F)} | sigma ⊆ F.val}).Connected

def skeleton {n : ℕ} (K : AbstractSimplicialComplex (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ({u, v} : Finset (Fin n)) ∈ K

def Gap {n : ℕ} (K : AbstractSimplicialComplex (Fin n)) (d k : ℕ) : Prop :=
  ∀ M : Finset (Fin n), (¬ D5.S3.Geometry.FiniteRelativeSimplicialCollapse.AugmentedFace K.toPreAbstractSimplicialComplex M ∧
    ∀ T : Finset (Fin n), T ⊂ M → D5.S3.Geometry.FiniteRelativeSimplicialCollapse.AugmentedFace K.toPreAbstractSimplicialComplex T) → ¬ (3 ≤ M.card ∧ M.card + k ≤ d)

/-- The affirmative assertion in Question 9.1. -/
def claim : Prop :=
  ∀ (n : ℕ) (d : ℕ) (k : ℕ) (K : AbstractSimplicialComplex (Fin n)),
    let C := ({
      faces := {s | s.Nonempty ∧ (skeleton K).IsClique (s : Set (Fin n))}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        intro t hts ht
        exact ⟨ht, hs.2.subset (by exact_mod_cast hts)⟩
      singleton_mem v := ⟨Finset.singleton_nonempty v,
        by simpa only [Finset.coe_singleton] using (skeleton K).isClique_singleton v⟩
    } : AbstractSimplicialComplex (Fin n))
    2 ≤ k → k + 2 ≤ d → Pure K d → Normal K d → Gap K d k →
      Pure C d → Normal C d

private theorem completion_correspondence {n : ℕ} (K : AbstractSimplicialComplex (Fin n)) :
    ({
      faces := {s | s.Nonempty ∧ (skeleton K).IsClique (s : Set (Fin n))}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        intro t hts ht
        exact ⟨ht, hs.2.subset (by exact_mod_cast hts)⟩
      singleton_mem v := ⟨Finset.singleton_nonempty v,
        by simpa only [Finset.coe_singleton] using (skeleton K).isClique_singleton v⟩
    } : AbstractSimplicialComplex (Fin n)) =
      D5.S3.Geometry.FiniteGraphVertexSubstitution.independenceComplex (skeleton K)ᶜ := by
  ext s
  change (s.Nonempty ∧ (skeleton K).IsClique (s : Set (Fin n))) ↔
    (s.Nonempty ∧ (skeleton K)ᶜ.IsIndepSet (s : Set (Fin n)))
  simp only [SimpleGraph.isIndepSet_compl]

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private def facets : Fin 15 → Finset (Fin 10) := ![
  {7, 8, 0, 1}, {7, 8, 1, 2}, {7, 8, 2, 3},
  {7, 8, 3, 4}, {7, 8, 4, 5}, {7, 8, 5, 0},
  {6, 7, 0, 1}, {6, 7, 1, 2}, {6, 7, 2, 3}, {6, 7, 3, 4},
  {8, 9, 0, 1}, {8, 9, 5, 0}, {8, 9, 4, 5}, {8, 9, 3, 4},
  {6, 9, 0, 1}]

private def completedFacets (i : Fin 16) : Finset (Fin 10) :=
  if h : i.val < 15 then facets ⟨i.val,h⟩ else {6, 9, 3, 4}

private theorem facets_card : ∀ i, (facets i).card = 4 := by decide
private theorem facets_cover : ∀ v : (Fin 10), ∃ i, v ∈ facets i := by decide

-- The nonempty subsets of the supplied generating facets.
private noncomputable def generated {n m : ℕ} (f : Fin m → Finset (Fin n))
    (cover : ∀ v, ∃ i, v ∈ f i) : AbstractSimplicialComplex (Fin n) :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex (Fin n)
    (⨆ i, D5.S3.Geometry.FiniteAlexanderDualCollapse.simplex (f i)) (by
    intro v
    obtain ⟨i, hi⟩ := cover v
    exact (le_iSup (fun j => D5.S3.Geometry.FiniteAlexanderDualCollapse.simplex (f j)) i)
      ⟨Finset.singleton_nonempty v, Finset.singleton_subset_iff.mpr hi⟩)

private theorem generated_mem {n m : ℕ} (f : Fin m → Finset (Fin n))
    (cover : ∀ v, ∃ i, v ∈ f i) (s : Finset (Fin n)) :
    s ∈ generated f cover ↔ s.Nonempty ∧ ∃ i, s ⊆ f i := by
  change s ∈ (⋃ K ∈ Set.range (fun i => D5.S3.Geometry.FiniteAlexanderDualCollapse.simplex (f i)), K.faces) ↔ _
  simp only [Set.mem_iUnion, Set.mem_range, exists_prop, exists_exists_eq_and]
  change (∃ i, s.Nonempty ∧ s ⊆ f i) ↔ _
  exact exists_and_left

private theorem generated_facets {n m d : ℕ} (f : Fin m → Finset (Fin n))
    (cover : ∀ v, ∃ i, v ∈ f i) (hc : ∀ i, (f i).card = d) (hd : 0 < d)
    (s : Finset (Fin n)) : (s ∈ (generated f cover) ∧ ∀ T : Finset (Fin n), T ∈ (generated f cover) → s ⊆ T → T = s) ↔ ∃ i, s = f i := by
  simp_rw [generated_mem]
  constructor
  · rintro ⟨⟨hs,i,hi⟩,hmax⟩
    exact ⟨i, (hmax (f i) ⟨Finset.card_pos.mp (by rw [hc]; exact hd), i,
      Finset.Subset.refl _⟩ hi).symm⟩
  · rintro ⟨i,rfl⟩
    refine ⟨⟨Finset.card_pos.mp (by rw [hc]; exact hd),i,Finset.Subset.refl _⟩, ?_⟩
    rintro t ⟨ht,j,hj⟩ hit
    have he : f i = f j := Finset.eq_of_subset_of_card_le (hit.trans hj) (by rw [hc,hc])
    exact Finset.Subset.antisymm (he ▸ hj) hit

private theorem generated_pure {n m d : ℕ} (f : Fin m → Finset (Fin n))
    (cover : ∀ v, ∃ i, v ∈ f i) (hc : ∀ i, (f i).card = d)
    (hd : 0 < d) (hm : 0 < m) : Pure (generated f cover) d := by
  refine ⟨⟨f ⟨0,hm⟩, (generated_facets f cover hc hd _).mpr ⟨⟨0,hm⟩,rfl⟩⟩,?_⟩
  intro s hs
  obtain ⟨i,rfl⟩ := (generated_facets f cover hc hd s).mp hs
  exact hc i

private theorem shelling_normal {n m d : ℕ} (f : Fin m → Finset (Fin n))
    (cover : ∀ v, ∃ i, v ∈ f i) (hc : ∀ i, (f i).card = d)
    (hd : 0 < d) (hm : 0 < m)
    (attach : ∀ i j : Fin m, j < i → ∃ l : Fin m,
      l < i ∧ f i ∩ f j ⊆ f l ∧ (f i ∩ f l).card + 1 = d) :
    Normal (generated f cover) d := by
  classical
  intro sigma hsigma
  let K := generated f cover
  let G := (dualGraph K d).induce {F : {F : Finset (Fin n) // (F ∈ K ∧ ∀ T : Finset (Fin n), T ∈ K → F ⊆ T → T = F)} | sigma ⊆ F.val}
  let vertex (i : Fin m) (h : sigma ⊆ f i) : {F : {F : Finset (Fin n) // (F ∈ K ∧ ∀ T : Finset (Fin n), T ∈ K → F ⊆ T → T = F)} // sigma ⊆ F.val} :=
    ⟨⟨f i,(generated_facets f cover hc hd _).mpr ⟨i,rfl⟩⟩,h⟩
  have edge (i l : Fin m) (hi : sigma ⊆ f i) (hl : sigma ⊆ f l)
      (hr : (f i ∩ f l).card + 1 = d) : G.Adj (vertex i hi) (vertex l hl) := by
    change (dualGraph K d).Adj _ _
    refine ⟨?_, Or.inl hr⟩
    intro he
    have hv : f i = f l := congrArg Subtype.val he
    have hh : (f i ∩ f l).card = d := by rw [← hv, Finset.inter_self, hc]
    omega
  have paths : ∀ t : ℕ, ∀ i j : Fin m, i.val + j.val = t →
      ∀ (hi : sigma ⊆ f i) (hj : sigma ⊆ f j), G.Reachable (vertex i hi) (vertex j hj) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro i j ht hi hj
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · obtain ⟨l,hli,hsub,hr⟩ := attach j i hij
        have hl : sigma ⊆ f l := (Finset.subset_inter hj hi).trans hsub
        exact (ih (i.val+l.val) (by omega) i l rfl hi hl).trans (edge j l hj hl hr).reachable.symm
      · have he : i = j := Fin.ext hij
        subst j
        exact SimpleGraph.Reachable.rfl
      · obtain ⟨l,hli,hsub,hr⟩ := attach i j hij
        have hl : sigma ⊆ f l := (Finset.subset_inter hi hj).trans hsub
        exact (edge i l hi hl hr).reachable.trans (ih (l.val+j.val) (by omega) l j rfl hl hj)
  have inhabited : Nonempty {F : {F : Finset (Fin n) // (F ∈ K ∧ ∀ T : Finset (Fin n), T ∈ K → F ⊆ T → T = F)} // sigma ⊆ F.val} := by
    rcases hsigma with hsigma | hsigma
    · exact ⟨vertex ⟨0,hm⟩ (hsigma ▸ Finset.empty_subset _)⟩
    · obtain ⟨h, i, hi⟩ := (generated_mem f cover sigma).mp hsigma
      exact ⟨vertex i hi⟩
  change G.Connected
  refine { preconnected := ?_, nonempty := inhabited }
  intro u v
  obtain ⟨i,hi⟩ := (generated_facets f cover hc hd u.val.val).mp u.val.property
  obtain ⟨j,hj⟩ := (generated_facets f cover hc hd v.val.val).mp v.val.property
  have hui : u = vertex i (hi ▸ u.property) := by apply Subtype.ext; apply Subtype.ext; exact hi
  have hvj : v = vertex j (hj ▸ v.property) := by apply Subtype.ext; apply Subtype.ext; exact hj
  rw [hui,hvj]
  exact paths _ i j rfl _ _

private theorem attachment_certificate : ∀ i j : Fin 15, j < i → ∃ l : Fin 15,
    l < i ∧ facets i ∩ facets j ⊆ facets l ∧ (facets i ∩ facets l).card + 1 = 4 := by
  decide

private noncomputable def delta : AbstractSimplicialComplex (Fin 10) := generated facets facets_cover

private theorem delta_pure : Pure delta 4 :=
  generated_pure facets facets_cover facets_card (by decide) (by decide)

private theorem delta_normal : Normal delta 4 :=
  shelling_normal facets facets_cover facets_card (by decide) (by decide) attachment_certificate

private theorem completed_card : ∀ i, (completedFacets i).card = 4 := by decide
private theorem completed_cover : ∀ v : (Fin 10), ∃ i, v ∈ completedFacets i := by decide

private noncomputable def completed : AbstractSimplicialComplex (Fin 10) := generated completedFacets completed_cover

-- The pairwise clique condition on the ten vertices.
set_option maxRecDepth 65536 in
private theorem clique_classification : ∀ s : Finset (Fin 10),
    (∀ u ∈ s, ∀ v ∈ s, u ≠ v → ∃ i : Fin 15, ({u,v} : Finset (Fin 10)) ⊆ facets i) ↔ ∃ i : Fin 16, s ⊆ completedFacets i := by
  decide +kernel

private theorem completion_eq : (D5.S3.Geometry.FiniteGraphVertexSubstitution.independenceComplex (skeleton delta)ᶜ) = completed := by
  have test_iff (s : Finset (Fin 10)) :
      (skeleton delta).IsClique (s : Set (Fin 10)) ↔ (∀ u ∈ s, ∀ v ∈ s, u ≠ v → ∃ i : Fin 15, ({u,v} : Finset (Fin 10)) ⊆ facets i) := by
    rw [SimpleGraph.isClique_iff]
    constructor
    · intro h u hu v hv hne
      have he := h hu hv hne
      change u ≠ v ∧ (({u,v} : Finset (Fin 10)) ∈ delta ∨ ({v,u} : Finset (Fin 10)) ∈ delta) at he
      rcases he.2 with he | he
      · exact ((generated_mem facets facets_cover _).mp he).2
      · simpa only [Finset.pair_comm] using ((generated_mem facets facets_cover _).mp he).2
    · intro h u hu v hv hne
      change u ≠ v ∧ (({u,v} : Finset (Fin 10)) ∈ delta ∨ ({v,u} : Finset (Fin 10)) ∈ delta)
      exact ⟨hne, Or.inl ((generated_mem facets facets_cover _).mpr
        ⟨Finset.insert_nonempty _ _, h u hu v hv hne⟩)⟩
  ext s
  change (s.Nonempty ∧ (skeleton delta)ᶜ.IsIndepSet (s : Set (Fin 10))) ↔
    s ∈ generated completedFacets completed_cover
  rw [generated_mem, SimpleGraph.isIndepSet_compl, test_iff, clique_classification]

private theorem completion_pure : Pure ((D5.S3.Geometry.FiniteGraphVertexSubstitution.independenceComplex (skeleton delta)ᶜ)) 4 := by
  rw [completion_eq]
  exact generated_pure completedFacets completed_cover completed_card (by decide) (by decide)

private theorem bad_star_certificate : ∀ i j : Fin 16,
    ({6,9} : Finset (Fin 10)) ⊆ completedFacets i →
    ({6,9} : Finset (Fin 10)) ⊆ completedFacets j →
    (completedFacets i ∩ completedFacets j).card + 1 ≠ 4 := by decide

private theorem completion_not_normal : ¬ Normal ((D5.S3.Geometry.FiniteGraphVertexSubstitution.independenceComplex (skeleton delta)ᶜ)) 4 := by
  rw [completion_eq]
  intro hn
  let sigma : Finset (Fin 10) := {6,9}
  have hsigma : D5.S3.Geometry.FiniteRelativeSimplicialCollapse.AugmentedFace completed.toPreAbstractSimplicialComplex sigma := by
    right
    apply (generated_mem completedFacets completed_cover sigma).mpr
    exact ⟨by decide, (14 : Fin 16), by decide⟩
  have hconn := hn sigma hsigma
  let G := (dualGraph completed 4).induce {F : {F : Finset (Fin 10) // (F ∈ completed ∧ ∀ T : Finset (Fin 10), T ∈ completed → F ⊆ T → T = F)} | sigma ⊆ F.val}
  have hbot : G = ⊥ := by
    ext u v
    change (dualGraph completed 4).Adj u.val v.val ↔ False
    constructor
    · intro h
      obtain ⟨i,hi⟩ := (generated_facets completedFacets completed_cover completed_card (by decide) _).mp u.val.property
      obtain ⟨j,hj⟩ := (generated_facets completedFacets completed_cover completed_card (by decide) _).mp v.val.property
      have hui : sigma ⊆ completedFacets i := hi ▸ u.property
      have hvj : sigma ⊆ completedFacets j := hj ▸ v.property
      rcases h.2 with h | h
      · exact bad_star_certificate i j hui hvj (by simpa only [hi,hj] using h)
      · exact bad_star_certificate j i hvj hui (by simpa only [hi,hj] using h)
    · exact False.elim
  have hs : Subsingleton {F : {F : Finset (Fin 10) // (F ∈ completed ∧ ∀ T : Finset (Fin 10), T ∈ completed → F ⊆ T → T = F)} // sigma ⊆ F.val} :=
    (SimpleGraph.connected_bot_iff.mp (hbot ▸ hconn)).1
  let x : {F : {F : Finset (Fin 10) // (F ∈ completed ∧ ∀ T : Finset (Fin 10), T ∈ completed → F ⊆ T → T = F)} // sigma ⊆ F.val} :=
    ⟨⟨completedFacets 14, (generated_facets completedFacets completed_cover completed_card
      (by decide) _).mpr ⟨14,rfl⟩⟩, by decide⟩
  let y : {F : {F : Finset (Fin 10) // (F ∈ completed ∧ ∀ T : Finset (Fin 10), T ∈ completed → F ⊆ T → T = F)} // sigma ⊆ F.val} :=
    ⟨⟨completedFacets 15, (generated_facets completedFacets completed_cover completed_card
      (by decide) _).mpr ⟨15,rfl⟩⟩, by decide⟩
  have he : completedFacets 14 = completedFacets 15 :=
    congrArg (fun v : {F : {F : Finset (Fin 10) // (F ∈ completed ∧ ∀ T : Finset (Fin 10), T ∈ completed → F ⊆ T → T = F)} // sigma ⊆ F.val} => v.val.val) (hs.elim x y)
  exact (by decide : completedFacets 14 ≠ completedFacets 15) he

private theorem gap_delta : Gap delta 4 2 := by
  intro M hM h
  omega

theorem result : ¬ claim := by
  intro h
  have step := h 10 4 2 delta
  dsimp only at step
  rw [completion_correspondence] at step
  exact completion_not_normal
    (step (by decide) (by decide) delta_pure delta_normal gap_delta completion_pure)


end D5.S3.Combinatorics.SimplicialComplexes.BenedettiMenaraNormalityRefutation

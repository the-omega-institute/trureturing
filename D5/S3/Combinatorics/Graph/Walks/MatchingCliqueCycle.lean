/- GID: D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: Shortest matching lifts control powers and distances of clique cycles with arbitrary twists. -/

import D5.S3.Combinatorics.Graph.WellCoveredPowerCliqueProduct
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

set_option autoImplicit false

namespace MatchingCliqueCycle

open SimpleGraph
open WellCoveredPowerCliqueProduct (power IsMaximalIndep)

noncomputable section

variable {m t : ℕ}
abbrev Vertex (m t : ℕ) := Fin (m + 3) × Fin (t + 3)
abbrev Matchings (m t : ℕ) := Fin (m + 3) → Equiv.Perm (Fin (t + 3))

/-- The bijective transport along the positively oriented matching edges. -/
def forward (M : Matchings m t) : Equiv.Perm (Vertex m t) where
  toFun x := (x.1 + 1, M x.1 x.2)
  invFun x := (x.1 - 1, (M (x.1 - 1)).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Precisely the internal clique edges and the two orientations of matching edges. -/
def graph (M : Matchings m t) : SimpleGraph (Vertex m t) where
  Adj x y := (x.1 = y.1 ∧ x ≠ y) ∨ forward M x = y ∨ forward M y = x
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro x h
    have hstep : x.1 + 1 ≠ x.1 := by
      intro h
      simp at h
    rcases h with h | h | h
    · exact h.2 rfl
    · exact hstep (congrArg Prod.fst h)
    · exact hstep (congrArg Prod.fst h)⟩

def spectrum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ I : Finset V, IsMaximalIndep G I ∧ I.card = k}

private lemma base_connected (m : ℕ) : (cycleGraph (m + 3)).Connected :=
  cycleGraph_connected (n := m + 2)

private lemma base_step (i : Fin (m + 3)) : (cycleGraph (m + 3)).Adj i (i + 1) := by
  rw [cycleGraph_adj]
  right
  simp

private lemma base_adj {i j : Fin (m + 3)} :
    (cycleGraph (m + 3)).Adj i j ↔ j = i + 1 ∨ i = j + 1 := by
  rw [cycleGraph_adj]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr ((sub_eq_iff_eq_add').mp h)
    · exact Or.inl ((sub_eq_iff_eq_add').mp h)
  · intro h
    rcases h with h | h
    · exact Or.inr ((sub_eq_iff_eq_add').mpr h)
    · exact Or.inl ((sub_eq_iff_eq_add').mpr h)

private lemma edge_projection (M : Matchings m t) {x y : Vertex m t}
    (h : (graph M).Adj x y) : x.1 = y.1 ∨ (cycleGraph (m + 3)).Adj x.1 y.1 := by
  rcases h with h | h | h
  · exact Or.inl h.1
  · right
    rw [← h]
    exact base_step x.1
  · right
    rw [← h]
    exact (base_step y.1).symm

private lemma project_walk (M : Matchings m t) {x y : Vertex m t}
    (p : (graph M).Walk x y) :
    ∃ q : (cycleGraph (m + 3)).Walk x.1 y.1, q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨.nil, le_rfl⟩
  | @cons x z y hxz p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases edge_projection M hxz with h | h
    · refine ⟨q.copy h.symm rfl, ?_⟩
      simpa using Nat.le_succ_of_le hq
    · exact ⟨q.cons h, by simpa using Nat.succ_le_succ hq⟩

private lemma lift_walk (M : Matchings m t) {i j : Fin (m + 3)}
    (p : (cycleGraph (m + 3)).Walk i j) (a : Fin (t + 3)) :
    ∃ b : Fin (t + 3), ∃ q : (graph M).Walk (i, a) (j, b), q.length = p.length := by
  induction p generalizing a with
  | nil => exact ⟨a, .nil, rfl⟩
  | @cons i k j hik p ih =>
    rcases base_adj.mp hik with h | h
    · obtain ⟨b, q, hq⟩ := ih (M i a)
      have he : (graph M).Adj (i, a) (k, M i a) := by
        right; left; exact Prod.ext h.symm rfl
      exact ⟨b, q.cons he, by simp [hq]⟩
    · obtain ⟨b, q, hq⟩ := ih ((M k).symm a)
      have he : (graph M).Adj (i, a) (k, (M k).symm a) := by
        right; right; exact Prod.ext h.symm (by simp [forward])
      exact ⟨b, q.cons he, by simp [hq]⟩

private lemma fiber_walk (M : Matchings m t) (i : Fin (m + 3)) (a b : Fin (t + 3)) :
    ∃ q : (graph M).Walk (i, a) (i, b), q.length ≤ 1 := by
  by_cases h : a = b
  · subst b; exact ⟨.nil, by simp⟩
  · have hab : (graph M).Adj (i, a) (i, b) :=
      Or.inl ⟨rfl, fun he => h (congrArg Prod.snd he)⟩
    exact ⟨Walk.cons hab Walk.nil, by simp⟩

private lemma graph_connected (M : Matchings m t) : (graph M).Connected := by
  rw [connected_iff]
  constructor
  · intro x y
    obtain ⟨p⟩ := base_connected m x.1 y.1
    obtain ⟨b, q, _⟩ := lift_walk M p x.2
    obtain ⟨r, _⟩ := fiber_walk M y.1 b y.2
    exact ⟨q.append r⟩
  · infer_instance

private lemma base_dist_le_walk (M : Matchings m t) {x y : Vertex m t}
    (p : (graph M).Walk x y) : (cycleGraph (m + 3)).dist x.1 y.1 ≤ p.length := by
  obtain ⟨q, hq⟩ := project_walk M p
  exact le_trans ((cycleGraph (m + 3)).dist_le q) hq

/-- Projection and matching transport give the distance sandwich. -/
theorem distance_bounds (M : Matchings m t) (x y : Vertex m t) :
    (cycleGraph (m + 3)).dist x.1 y.1 ≤ (graph M).dist x y ∧
    (graph M).dist x y ≤ (cycleGraph (m + 3)).dist x.1 y.1 + 1 := by
  constructor
  · obtain ⟨p, hp⟩ := (graph_connected M).exists_walk_length_eq_dist x y
    simpa [hp] using base_dist_le_walk M p
  · obtain ⟨p, hp⟩ := (base_connected m).exists_walk_length_eq_dist x.1 y.1
    obtain ⟨b, q, hq⟩ := lift_walk M p x.2
    obtain ⟨r, hr⟩ := fiber_walk M y.1 b y.2
    have h := (graph M).dist_le (q.append r)
    have hetaX : (x.1, x.2) = x := by cases x; rfl
    have hetaY : (y.1, y.2) = y := by cases y; rfl
    simp only [Walk.length_append, hetaX, hetaY, hq, hp] at h
    omega


private lemma oriented_geodesic (M : Matchings m t) (R : Equiv.Perm (Vertex m t))
    (he : ∀ {x y}, (graph M).Adj x y →
      x.1 = y.1 ∨ R x = y ∨ R y = x)
    (hb : ∀ x, (cycleGraph (m + 3)).Adj x.1 (R x).1)
    {x y : Vertex m t} (p : (graph M).Walk x y) :
    ∀ u, R u = x → p.length + 1 ≤ (cycleGraph (m + 3)).dist u.1 y.1 →
      y = (R : Vertex m t → Vertex m t)^[p.length + 1] u := by
  induction p with
  | nil =>
    intro u hu _
    simpa using hu.symm
  | @cons x z y hxz p ih =>
    intro u hu hd
    have hux : (cycleGraph (m + 3)).dist u.1 x.1 = 1 := by
      rw [← hu]
      exact dist_eq_one_iff_adj.mpr (hb u)
    have htriangle := (base_connected m).dist_triangle (u := u.1) (v := x.1) (w := y.1)
    rw [hux] at htriangle
    rcases he hxz with h | h | h
    · have hproj := base_dist_le_walk M p
      rw [← h] at hproj
      simp only [Walk.length_cons] at hd
      omega
    · have hlower : p.length + 1 ≤ (cycleGraph (m + 3)).dist x.1 y.1 := by
        simp only [Walk.length_cons] at hd
        omega
      have hi := ih x h hlower
      simpa only [Walk.length_cons, Function.iterate_succ_apply, hu] using hi
    · have hzu : z = u := R.injective (h.trans hu.symm)
      have hproj := base_dist_le_walk M p
      rw [congrArg Prod.fst hzu] at hproj
      simp only [Walk.length_cons] at hd
      omega

private lemma shortest_endpoints (M : Matchings m t) {x y : Vertex m t}
    (p : (graph M).Walk x y)
    (h : p.length ≤ (cycleGraph (m + 3)).dist x.1 y.1) :
    y = (forward M : Vertex m t → Vertex m t)^[p.length] x ∨
    y = ((forward M).symm : Vertex m t → Vertex m t)^[p.length] x := by
  cases p with
  | nil => exact Or.inl rfl
  | @cons x z y hxz p =>
    have hedges : ∀ {a b}, (graph M).Adj a b →
        a.1 = b.1 ∨ forward M a = b ∨ forward M b = a := by
      intro a b hab
      rcases hab with hab | hab | hab
      · exact Or.inl hab.1
      · exact Or.inr (Or.inl hab)
      · exact Or.inr (Or.inr hab)
    rcases hedges hxz with hz | hz | hz
    · have hp := base_dist_le_walk M p
      rw [← hz] at hp
      simp only [Walk.length_cons] at h
      omega
    · left
      exact oriented_geodesic M (forward M) hedges (fun a => base_step a.1) p x hz h
    · right
      have hinv : (forward M).symm x = z := by rw [← hz]; simp
      have heinv : ∀ {a b}, (graph M).Adj a b →
          a.1 = b.1 ∨ (forward M).symm a = b ∨ (forward M).symm b = a := by
        intro a b hab
        rcases hedges hab with hab | hab | hab
        · exact Or.inl hab
        · right; right; rw [← hab]; simp
        · right; left; rw [← hab]; simp
      have hbinv : ∀ a : Vertex m t,
          (cycleGraph (m + 3)).Adj a.1 ((forward M).symm a).1 := by
        intro a
        have hb := (base_step ((forward M).symm a).1).symm
        simpa [forward] using hb
      exact oriented_geodesic M (forward M).symm heinv hbinv p x hinv h

private lemma power_projection_injective (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d)
    {I : Finset (Vertex m t)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ (power (graph M) d).Adj x y) :
    Set.InjOn Prod.fst (I : Set (Vertex m t)) := by
  intro x hx y hy heq
  by_contra hne
  apply hI x hx y hy hne
  refine ⟨hne, ?_⟩
  have hu := (distance_bounds M x y).2
  rw [heq, dist_self] at hu
  omega

private lemma forward_fiber (M : Matchings m t) (d : ℕ) (x : Vertex m t) :
    ((forward M : Vertex m t → Vertex m t)^[d] x).1 =
      (fun i : Fin (m + 3) => i + 1)^[d] x.1 := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    simp only [Function.iterate_succ_apply]
    exact ih (forward M x)

private lemma backward_fiber (M : Matchings m t) (d : ℕ) (x : Vertex m t) :
    (((forward M).symm : Vertex m t → Vertex m t)^[d] x).1 =
      (fun i : Fin (m + 3) => i - 1)^[d] x.1 := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    simp only [Function.iterate_succ_apply]
    exact ih ((forward M).symm x)

private lemma free_vertex (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d)
    {I : Finset (Vertex m t)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ (power (graph M) d).Adj x y)
    (i : Fin (m + 3))
    (hfar : ∀ y ∈ I, d ≤ (cycleGraph (m + 3)).dist i y.1) :
    ∃ a : Fin (t + 3), ∀ y ∈ I, ¬ (power (graph M) d).Adj (i, a) y := by
  classical
  let F := I.filter (fun y => y.1 = (fun j : Fin (m + 3) => j + 1)^[d] i)
  let B := I.filter (fun y => y.1 = (fun j : Fin (m + 3) => j - 1)^[d] i)
  let forbidden := (F.image (fun y =>
    (((forward M).symm : Vertex m t → Vertex m t)^[d] y).2)) ∪
    (B.image (fun y => ((forward M : Vertex m t → Vertex m t)^[d] y).2))
  have hinj := power_projection_injective M hd hI
  have hf : F.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  have hb : B.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  have hcard : forbidden.card ≤ 2 := by
    have hu := Finset.card_union_le (F.image (fun y =>
      (((forward M).symm : Vertex m t → Vertex m t)^[d] y).2))
      (B.image (fun y => ((forward M : Vertex m t → Vertex m t)^[d] y).2))
    have hf' := Finset.card_image_le (s := F)
      (f := fun y => (((forward M).symm : Vertex m t → Vertex m t)^[d] y).2)
    have hb' := Finset.card_image_le (s := B)
      (f := fun y => ((forward M : Vertex m t → Vertex m t)^[d] y).2)
    dsimp [forbidden]
    omega
  have hsmall : forbidden.card < (Finset.univ : Finset (Fin (t + 3))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  refine ⟨a, ?_⟩
  intro y hy hadj
  obtain ⟨p, hp⟩ := (graph_connected M).exists_walk_length_eq_dist (i, a) y
  have heq : p.length = d := by
    have hlo := (distance_bounds M (i, a) y).1
    have hfary := hfar y hy
    have hhi := hadj.2
    simp only [hp] at *
    omega
  have hs := shortest_endpoints M p (by simpa [heq] using hfar y hy)
  rw [heq] at hs
  rcases hs with hs | hs
  · apply ha
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩
    · rw [hs, forward_fiber]
    · rw [hs]
      have hit := (forward M).leftInverse_symm.iterate d
      exact congrArg Prod.snd (hit (i, a))
  · apply ha
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩
    · rw [hs, backward_fiber]
    · rw [hs]
      have hit := (forward M).symm.leftInverse_symm.iterate d
      exact congrArg Prod.snd (hit (i, a))

/-- A maximal independent set projects injectively to a maximal independent set. -/
theorem maximal_projection (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d)
    {I : Finset (Vertex m t)} (hI : IsMaximalIndep (power (graph M) d) I) :
    IsMaximalIndep (power (cycleGraph (m + 3)) (d - 1)) (I.image Prod.fst) ∧
      (I.image Prod.fst).card = I.card := by
  classical
  refine ⟨⟨?_, ?_⟩, Finset.card_image_of_injOn (power_projection_injective M hd hI.1)⟩
  · intro i hi j hj hij hadj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
    apply hI.1 x hx y hy (fun h => hij (congrArg Prod.fst h))
    refine ⟨fun h => hij (congrArg Prod.fst h), ?_⟩
    have hu := (distance_bounds M x y).2
    have hl := hadj.2
    omega
  · intro i hi
    by_contra hn
    have hfar : ∀ y ∈ I, d ≤ (cycleGraph (m + 3)).dist i y.1 := by
      intro y hy
      have hne : i ≠ y.1 := by
        intro h
        exact hi (Finset.mem_image.mpr ⟨y, hy, h.symm⟩)
      have hn' : ¬ (cycleGraph (m + 3)).dist i y.1 ≤ d - 1 := by
        intro h
        apply hn
        exact ⟨y.1, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hne, h⟩
      omega
    obtain ⟨a, ha⟩ := free_vertex M hd hI.1 i hfar
    have hnew : (i, a) ∉ I := by
      intro h
      exact hi (Finset.mem_image.mpr ⟨(i, a), h, rfl⟩)
    obtain ⟨y, hy, hadj⟩ := hI.2 (i, a) hnew
    exact ha y hy hadj

/-- Every maximal independent set of the base power has a lawful maximal lift. -/
theorem maximal_lift (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d)
    {S : Finset (Fin (m + 3))}
    (hS : IsMaximalIndep (power (cycleGraph (m + 3)) (d - 1)) S) :
    ∃ I : Finset (Vertex m t), IsMaximalIndep (power (graph M) d) I ∧
      I.image Prod.fst = S ∧ I.card = S.card := by
  classical
  let C : Finset (Finset (Vertex m t)) := Finset.univ.filter (fun I =>
    (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ (power (graph M) d).Adj x y) ∧
      I.image Prod.fst ⊆ S)
  have hc : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨I, hIC, hmax⟩ := C.exists_max_image Finset.card hc
  obtain ⟨hI, hsub⟩ := (Finset.mem_filter.mp hIC).2
  have heq : I.image Prod.fst = S := by
    apply Finset.Subset.antisymm hsub
    intro i hi
    by_contra hmissing
    have hfar : ∀ y ∈ I, d ≤ (cycleGraph (m + 3)).dist i y.1 := by
      intro y hy
      have hyS := hsub (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      have hne : i ≠ y.1 := by
        intro h
        exact hmissing (Finset.mem_image.mpr ⟨y, hy, h.symm⟩)
      have hn : ¬ (cycleGraph (m + 3)).dist i y.1 ≤ d - 1 :=
        fun h => hS.1 i hi y.1 hyS hne ⟨hne, h⟩
      omega
    obtain ⟨a, ha⟩ := free_vertex M hd hI i hfar
    have hnew : (i, a) ∉ I := by
      intro h
      exact hmissing (Finset.mem_image.mpr ⟨(i, a), h, rfl⟩)
    have hins : insert (i, a) I ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact (hxy rfl).elim
          · exact ha y hy
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · intro h; exact ha x hx h.symm
          · exact hI x hx y hy hxy
      · intro j hj
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · exact hsub (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hb := hmax _ hins
    rw [Finset.card_insert_of_notMem hnew] at hb
    omega
  have hmaximal : IsMaximalIndep (power (graph M) d) I := by
    refine ⟨hI, ?_⟩
    intro v hv
    have hclose : ∃ i ∈ S, (cycleGraph (m + 3)).dist v.1 i ≤ d - 1 := by
      by_cases h : v.1 ∈ S
      · exact ⟨v.1, h, by simp⟩
      · obtain ⟨i, hi, hadj⟩ := hS.2 v.1 h
        exact ⟨i, hi, hadj.2⟩
    obtain ⟨i, hi, hdist⟩ := hclose
    rw [← heq] at hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
    refine ⟨x, hx, ⟨fun h => hv (h ▸ hx), ?_⟩⟩
    have hu := (distance_bounds M v x).2
    rw [hxi] at hu
    omega
  refine ⟨I, hmaximal, heq, ?_⟩
  have hcard := Finset.card_image_of_injOn (power_projection_injective M hd hI)
  rw [heq] at hcard
  exact hcard.symm

/-- The spectra use cardinalities of actual maximal independent vertex sets. -/
theorem spectrum_power (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d) :
    spectrum (power (graph M) d) = spectrum (power (cycleGraph (m + 3)) (d - 1)) := by
  ext k
  constructor
  · rintro ⟨I, hI, hk⟩
    obtain ⟨hp, hc⟩ := maximal_projection M hd hI
    exact ⟨I.image Prod.fst, hp, hc.trans hk⟩
  · rintro ⟨S, hS, hk⟩
    obtain ⟨I, hI, _, hc⟩ := maximal_lift M hd hS
    exact ⟨I, hI, hc.trans hk⟩

private lemma diameter_shift (M : Matchings m t) :
    (graph M).diam = (cycleGraph (m + 3)).diam + 1 := by
  classical
  have hc := (connected_iff_ediam_ne_top).mp (graph_connected M)
  have hb := (connected_iff_ediam_ne_top).mp (base_connected m)
  apply Nat.le_antisymm
  · obtain ⟨x, y, hxy⟩ := (graph M).exists_dist_eq_diam
    have hu := (distance_bounds M x y).2
    have hd := (cycleGraph (m + 3)).dist_le_diam hb (u := x.1) (v := y.1)
    omega
  · obtain ⟨i, j, hij⟩ := (cycleGraph (m + 3)).exists_dist_eq_diam
    let x : Vertex m t := (i, 0)
    let D := (cycleGraph (m + 3)).diam
    let forbidden : Finset (Fin (t + 3)) :=
      {((forward M : Vertex m t → Vertex m t)^[D] x).2,
       (((forward M).symm : Vertex m t → Vertex m t)^[D] x).2}
    have hsmall : forbidden.card < (Finset.univ : Finset (Fin (t + 3))).card := by
      have hf : forbidden.card ≤ 2 := by
        dsimp only [forbidden]
        exact le_trans (Finset.card_insert_le _ _) (by simp)
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
    let y : Vertex m t := (j, a)
    have hfar : D < (graph M).dist x y := by
      by_contra hn
      obtain ⟨p, hp⟩ := (graph_connected M).exists_walk_length_eq_dist x y
      have hle : p.length ≤ D := by omega
      have hge : D ≤ p.length := by
        have h := base_dist_le_walk M p
        change (cycleGraph (m + 3)).dist i j ≤ p.length at h
        simpa [D, hij] using h
      have plen : p.length = D := by omega
      have hs := shortest_endpoints M p (by simpa [x, y, plen, D, hij])
      rw [plen] at hs
      rcases hs with hs | hs
      · apply ha
        exact Finset.mem_insert.mpr (Or.inl (congrArg Prod.snd hs))
      · apply ha
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg Prod.snd hs)))
    have hbound := (graph M).dist_le_diam hc (u := x) (v := y)
    dsimp [D] at hfar
    omega


private lemma base_adj_values {i j : Fin (m + 3)} :
    (cycleGraph (m + 3)).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val = 0 ∧ j.val + 1 = m + 3) ∨
      (j.val = 0 ∧ i.val + 1 = m + 3) := by
  rw [cycleGraph_adj']
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i < j
  · rw [Fin.coe_sub_iff_lt.mpr h, Fin.coe_sub_iff_le.mpr (le_of_lt h)]
    have hv : i.val < j.val := h
    omega
  · by_cases h' : j < i
    · rw [Fin.coe_sub_iff_le.mpr (le_of_lt h'), Fin.coe_sub_iff_lt.mpr h']
      have hv : j.val < i.val := h'
      omega
    · have heq : i = j := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      subst j
      simp only [sub_self, Fin.val_zero]
      omega

lemma cycle_distance (m : ℕ) :
    ∀ i j : Fin (m + 3), (cycleGraph (m + 3)).dist i j =
      WellCoveredPowerCliqueProduct.cycleMetric (m + 3) i j := by
  apply (WellCoveredPowerCliqueProduct.distance_certificate
    (cycleGraph (m + 3)) (WellCoveredPowerCliqueProduct.cycleMetric (m + 3))
    ?_ ?_ ?_).2
  · intro i j
    have hi := i.isLt
    have hj := j.isLt
    constructor
    · intro h
      apply Fin.ext
      simp only [WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist] at h
      omega
    · intro h; subst j; simp [WellCoveredPowerCliqueProduct.cycleMetric]
  · intro i j k h
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    rcases base_adj_values.mp h with h | h | h | h <;>
      simp only [WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist] <;> omega
  · intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have hne : i.val ≠ j.val := by
      intro heq
      apply h
      have heq' := Fin.ext heq
      subst j
      simp [WellCoveredPowerCliqueProduct.cycleMetric]
    by_cases hij : i.val < j.val
    · by_cases hshort : j.val - i.val ≤ m + 3 - (j.val - i.val)
      · let k : Fin (m + 3) := ⟨i.val + 1, by omega⟩
        refine ⟨k, base_adj_values.mpr (Or.inl rfl), ?_⟩
        dsimp [k, WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist]
        omega
      · by_cases hz : i.val = 0
        · let k : Fin (m + 3) := ⟨m + 2, by omega⟩
          refine ⟨k, base_adj_values.mpr (Or.inr (Or.inr (Or.inl ⟨hz, by rfl⟩))), ?_⟩
          dsimp [k, WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist]
          omega
        · let k : Fin (m + 3) := ⟨i.val - 1, by omega⟩
          refine ⟨k, base_adj_values.mpr (Or.inr (Or.inl (by dsimp [k]; omega))), ?_⟩
          dsimp [k, WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist]
          omega
    · have hji : j.val < i.val := by omega
      by_cases hshort : i.val - j.val ≤ m + 3 - (i.val - j.val)
      · let k : Fin (m + 3) := ⟨i.val - 1, by omega⟩
        refine ⟨k, base_adj_values.mpr (Or.inr (Or.inl (by dsimp [k]; omega))), ?_⟩
        dsimp [k, WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist]
        omega
      · by_cases hlast : i.val + 1 = m + 3
        · let k : Fin (m + 3) := 0
          refine ⟨k, base_adj_values.mpr (Or.inr (Or.inr (Or.inr ⟨rfl, hlast⟩))), ?_⟩
          dsimp [k, WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist]
          omega
        · let k : Fin (m + 3) := ⟨i.val + 1, by omega⟩
          refine ⟨k, base_adj_values.mpr (Or.inl rfl), ?_⟩
          dsimp [k, WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist]
          omega

private lemma base_diameter (m : ℕ) : (cycleGraph (m + 3)).diam = (m + 3) / 2 := by
  have hf := (connected_iff_ediam_ne_top).mp (base_connected m)
  apply Nat.le_antisymm
  · obtain ⟨i, j, hij⟩ := (cycleGraph (m + 3)).exists_dist_eq_diam
    rw [← hij, cycle_distance]
    have hi := i.isLt
    have hj := j.isLt
    simp only [WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist]
    omega
  · let j : Fin (m + 3) := ⟨(m + 3) / 2, by omega⟩
    have h := (cycleGraph (m + 3)).dist_le_diam hf (u := 0) (v := j)
    rw [cycle_distance] at h
    dsimp [WellCoveredPowerCliqueProduct.cycleMetric, Nat.dist, j] at h
    simp only [Fin.val_zero, Nat.zero_sub, zero_add, Nat.sub_zero] at h
    omega

/-- The sharp diameter holds for every matching family, including arbitrary monodromy. -/
theorem diameter (M : Matchings m t) : (graph M).diam = (m + 3) / 2 + 1 := by
  rw [diameter_shift, base_diameter]


end
end MatchingCliqueCycle

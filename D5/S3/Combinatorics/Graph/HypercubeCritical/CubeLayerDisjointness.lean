/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.claim
   digest: Actual distance-four cubic vertices with all neighbors at distance three have disjoint neighborhoods in an induced cube graph of girth at least eight. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
import Mathlib.Combinatorics.SimpleGraph.Metric
import Batteries.Tactic.OpenPrivate

/-! The cube-coordinate disjoint-neighborhood invariant, independent of slice
cardinalities, regularity, cycle classification, and the ambient cube dimension. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubeLayerDisjointness

open SimpleGraph
open scoped Classical
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip flip_flip flip_adj)
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private three_walk_endpoint_injective one_three_cross_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {n : ℕ} {f : V → Q n}
variable {L R : Finset V} {x y : V}

private structure FourPath (G : SimpleGraph V) (x y : V) where
  a : V
  b : V
  c : V
  xa : G.Adj x a
  ab : G.Adj a b
  bc : G.Adj b c
  cy : G.Adj c y
  xb : x ≠ b
  ac : a ≠ c
  by_ : b ≠ y

private lemma path_side
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V)) (hx : x ∈ L)
    (p : FourPath G x y) : y ∈ L := by
  have ha := hpart.mem_of_mem_adj hx p.xa
  have hb := hpart.mem_of_mem_adj' ha p.ab.symm
  have hc := hpart.mem_of_mem_adj hb p.bc
  exact hpart.mem_of_mem_adj' hc p.cy.symm

private lemma first_ne_of_last_ne
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (p q : FourPath G x y) (hc : p.c ≠ q.c) : p.a ≠ q.a := by
  intro ha
  have hy := path_side hpart hx p
  have h := three_walk_endpoint_injective hpart hg hy hy
    p.cy.symm p.bc.symm p.ab.symm q.cy.symm q.bc.symm q.ab.symm
    p.by_.symm p.ac.symm q.by_.symm q.ac.symm ⟨rfl, ha⟩
  exact hc h.2.1

private lemma no_cross_second
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (p q : FourPath G x y) (ha : p.a ≠ q.a) : ¬ G.Adj p.b q.a := by
  intro h
  exact one_three_cross_impossible hpart hg hx hx q.xa p.xa p.ab h
    p.xb ha ⟨rfl, rfl⟩

private lemma no_cross_third
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (p q : FourPath G x y) (ha : p.a ≠ q.a) : ¬ G.Adj q.b p.c := by
  intro h
  have hqc : q.a ≠ p.c := by
    intro he
    exact one_three_cross_impossible hpart hg hx hx q.xa p.xa p.ab p.bc
      p.xb p.ac ⟨rfl, he⟩
  have he := three_walk_endpoint_injective hpart hg hx hx
    p.xa p.ab p.bc q.xa q.ab h p.xb p.ac q.xb hqc ⟨rfl, rfl⟩
  exact ha he.2.1

private lemma three_directions
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (hf : Function.Injective f)
    (he : ∀ u v, G.Adj u v ↔ (hypercube n).Adj (f u) (f v))
    {a b c : V} (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hac : a ≠ c) {i j k : Fin n}
    (hi : f a = flip (f x) i) (hj : f b = flip (f a) j)
    (hk : f c = flip (f b) k) : i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact hxb (hf (by simpa [hi] using hj.symm))
  have hjk : j ≠ k := by
    intro h
    subst k
    exact hac (hf (by simpa [hj] using hk.symm))
  refine ⟨hij, ?_, hjk⟩
  intro hik
  subst k
  have hfc : f c = flip (f x) j := by
    rw [hk, hj, hi, flip_comm (flip (f x) i) j i, BalancedCriticalSpectrum.flip_flip]
  have hxc : G.Adj x c := (he x c).mpr (hfc ▸ flip_adj (f x) j)
  exact one_three_cross_impossible hpart hg hx hx hxc hxa hab hbc hxb hac ⟨rfl, rfl⟩

private def word {n : ℕ} (X : Q n) (a b c d : Fin n) : Q n :=
  flip (flip (flip (flip X a) b) c) d

private def support {n : ℕ} (X Y : Q n) : Finset (Fin n) :=
  Finset.univ.filter (fun t => X t ≠ Y t)

private lemma support_word_subset (X : Q n) (a b c d : Fin n) :
    support X (word X a b c d) ⊆ {a,b,c,d} := by
  intro t ht
  by_contra h
  have hn : t ≠ a ∧ t ≠ b ∧ t ≠ c ∧ t ≠ d := by simpa using h
  have ht' := (Finset.mem_filter.mp ht).2
  exact ht' (by simp [word, BalancedCriticalSpectrum.flip, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2])

private lemma support_word_eq (X : Q n) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    support X (word X a b c d) = {a,b,c,d} := by
  apply Finset.Subset.antisymm (support_word_subset X a b c d)
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl <;>
    simp [support, word, BalancedCriticalSpectrum.flip, *, Ne.symm]

private lemma word_directions_eq (X Y : Q n) (hcard : (support X Y).card = 4)
    {a b c d : Fin n} (h : Y = word X a b c d) :
    ({a,b,c,d} : Finset (Fin n)) = support X Y := by
  have hs : support X Y ⊆ {a,b,c,d} := h ▸ support_word_subset X a b c d
  exact (Finset.eq_of_subset_of_card_le hs (hcard ▸ Finset.card_le_four)).symm

private structure CubePath (G : SimpleGraph V) (f : V → Q n) (x y : V)
    extends FourPath G x y where
  i : Fin n
  j : Fin n
  k : Fin n
  l : Fin n
  fa : f a = flip (f x) i
  fb : f b = flip (f a) j
  fc : f c = flip (f b) k
  fy : f y = flip (f c) l
  ij : i ≠ j
  ik : i ≠ k
  jk : j ≠ k
  jl : j ≠ l
  kl : k ≠ l

private lemma cube_path
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (hf : Function.Injective f)
    (he : ∀ u v, G.Adj u v ↔ (hypercube n).Adj (f u) (f v))
    (p : FourPath G x y) : ∃ q : CubePath G f x y, q.toFourPath = p := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip ((he _ _).mp p.xa)
  obtain ⟨j, hj⟩ := adjacent_exists_flip ((he _ _).mp p.ab)
  obtain ⟨k, hk⟩ := adjacent_exists_flip ((he _ _).mp p.bc)
  obtain ⟨l, hl⟩ := adjacent_exists_flip ((he _ _).mp p.cy)
  have hfirst := three_directions hpart hg hx hf he p.xa p.ab p.bc p.xb p.ac hi hj hk
  have ha : p.a ∈ R := hpart.mem_of_mem_adj hx p.xa
  have hlast := three_directions hpart.symm hg ha hf he p.ab p.bc p.cy p.ac p.by_ hj hk hl
  exact ⟨⟨p, i, j, k, l, hi, hj, hk, hl, hfirst.1, hfirst.2.1,
    hfirst.2.2, hlast.2.1, hlast.2.2⟩, rfl⟩

private lemma path_word (p : CubePath G f x y) :
    f y = word (f x) p.i p.j p.k p.l := by
  rw [p.fy, p.fc, p.fb, p.fa]
  rfl

private lemma first_direction_ne (hf : Function.Injective f)
    (p q : CubePath G f x y) (ha : p.a ≠ q.a) : p.i ≠ q.i := by
  intro h
  exact ha (hf (p.fa.trans (h ▸ q.fa.symm)))

private lemma second_direction_ne
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (he : ∀ u v, G.Adj u v ↔ (hypercube n).Adj (f u) (f v))
    (p q : CubePath G f x y) (ha : p.a ≠ q.a) : p.j ≠ q.i := by
  intro h
  have hb : f p.b = flip (f q.a) p.i := by
    rw [p.fb, p.fa, q.fa, h, flip_comm]
  have hadj : G.Adj p.b q.a := (he _ _).mpr (hb ▸ (flip_adj (f q.a) p.i).symm)
  exact no_cross_second hpart hg hx p.toFourPath q.toFourPath ha hadj

private lemma third_direction_ne
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (he : ∀ u v, G.Adj u v ↔ (hypercube n).Adj (f u) (f v))
    (p q : CubePath G f x y) (ha : p.a ≠ q.a) (hj : p.j = q.j) : p.k ≠ q.i := by
  intro h
  have hc : f p.c = flip (f q.b) p.i := by
    rw [p.fc, p.fb, p.fa, q.fb, q.fa, ← hj, ← h]
    rw [flip_comm (flip (f x) p.i) p.j p.k,
      flip_comm (f x) p.i p.k, flip_comm (flip (f x) p.k) p.i p.j]
  have hadj : G.Adj q.b p.c := (he _ _).mpr (hc ▸ flip_adj (f q.b) p.i)
  exact no_cross_third hpart hg hx p.toFourPath q.toFourPath ha hadj

private lemma fan_direction
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (hf : Function.Injective f)
    (he : ∀ u v, G.Adj u v ↔ (hypercube n).Adj (f u) (f v))
    (p q r : CubePath G f x y)
    (hpq : p.a ≠ q.a) (hpr : p.a ≠ r.a) (hqr : q.a ≠ r.a) : p.i = p.l := by
  by_contra hil
  have hs : support (f x) (f y) = {p.i,p.j,p.k,p.l} := by
    rw [path_word p]
    exact support_word_eq _ p.ij p.ik hil p.jk p.jl p.kl
  have hcard : (support (f x) (f y)).card = 4 := by
    rw [hs]
    simp [p.ij, p.ik, hil, p.jk, p.jl, p.kl]
  let D := support (f x) (f y)
  have mem (s : CubePath G f x y) :
      s.i ∈ D ∧ s.j ∈ D ∧ s.k ∈ D ∧ s.l ∈ D := by
    have h := word_directions_eq (f x) (f y) hcard (path_word s)
    dsimp only [D]
    rw [← h]
    simp
  have hiq := first_direction_ne hf p q hpq
  have hir := first_direction_ne hf p r hpr
  have hqr' := first_direction_ne hf q r hqr
  have hjq := second_direction_ne hpart hg hx he p q hpq
  have hjr := second_direction_ne hpart hg hx he p r hpr
  have hqi := second_direction_ne hpart hg hx he q p hpq.symm
  have hqrj := second_direction_ne hpart hg hx he q r hqr
  have hri := second_direction_ne hpart hg hx he r p hpr.symm
  have hrq := second_direction_ne hpart hg hx he r q hqr.symm
  have hD : ({p.i,q.i,r.i,p.j} : Finset (Fin n)) = D := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact (mem p).1
      · exact (mem q).1
      · exact (mem r).1
      · exact (mem p).2.1
    · have hc : ({p.i,q.i,r.i,p.j} : Finset (Fin n)).card = 4 := by
        simp [hiq, hir, hqr', p.ij, hjq, hjr, Ne.symm]
      simpa only [hc] using hcard.le
  have hjqeq : p.j = q.j := by
    have hm := (mem q).2.1
    rw [← hD] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · exact (hqi h).elim
    · exact (q.ij h.symm).elim
    · exact (hqrj h).elim
    · exact h.symm
  have hjreq : p.j = r.j := by
    have hm := (mem r).2.1
    rw [← hD] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · exact (hri h).elim
    · exact (hrq h).elim
    · exact (r.ij h.symm).elim
    · exact h.symm
  have hkq := third_direction_ne hpart hg hx he p q hpq hjqeq
  have hkr := third_direction_ne hpart hg hx he p r hpr hjreq
  have hm := (mem p).2.2.1
  rw [← hD] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h
  · exact p.ik h.symm
  · exact hkq h
  · exact hkr h
  · exact p.jk h.symm

private lemma prefix_of_edist_three {w : V} (hw : G.edist x w = 3) :
    ∃ a b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b w ∧ x ≠ b ∧ a ≠ w := by
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_eq_coe (k := 3) hw
  cases p with
  | nil => simp at hp
  | @cons _ a _ hxa p =>
    cases p with
    | nil => simp at hp
    | @cons _ b _ hab p =>
      have hlen : p.length = 1 := by simp only [Walk.length_cons] at hp; omega
      have hbw := p.adj_of_length_eq_one hlen
      refine ⟨a, b, hxa, hab, hbw, ?_, ?_⟩
      · intro hxb
        subst b
        have h := G.edist_eq_one_iff_adj.mpr hbw
        rw [hw] at h
        norm_num at h
      · intro haw
        subst a
        have h := G.edist_eq_one_iff_adj.mpr hxa
        rw [hw] at h
        norm_num at h

private lemma second_ne_endpoint (hy : G.edist x y = 4)
    {a b : V} (hxa : G.Adj x a) (hab : G.Adj a b) : b ≠ y := by
  intro hby
  subst b
  have h := (Walk.cons hxa (Walk.cons hab Walk.nil)).edist_le
  rw [hy] at h
  norm_num at h

private lemma path_of_neighbor (hy : G.edist x y = 4)
    {w : V} (hw : G.edist x w = 3) (hwy : G.Adj w y) :
    ∃ p : FourPath G x y, p.c = w := by
  obtain ⟨a,b,hxa,hab,hbw,hxb,haw⟩ := prefix_of_edist_three hw
  exact ⟨⟨a,b,w,hxa,hab,hbw,hwy,hxb,haw,second_ne_endpoint hy hxa hab⟩, rfl⟩

private lemma final_flip
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hx : x ∈ L)
    (hf : Function.Injective f)
    (he : ∀ u v, G.Adj u v ↔ (hypercube n).Adj (f u) (f v))
    (hy : G.edist x y = 4) (hdeg : G.degree y = 3)
    (hneighbors : ∀ w, G.Adj y w → G.edist x w = 3)
    (p : FourPath G x y) :
    ∃ i : Fin n, f p.a = flip (f x) i ∧ f y = flip (f p.c) i := by
  classical
  have hw : p.c ∈ G.neighborFinset y := (G.mem_neighborFinset _ _).mpr p.cy.symm
  have hc : ((G.neighborFinset y).erase p.c).card = 2 := by
    have h := Finset.card_erase_add_one hw
    rw [G.card_neighborFinset_eq_degree, hdeg] at h
    omega
  obtain ⟨u,v,huv,heq⟩ := Finset.card_eq_two.mp hc
  have hu : u ∈ (G.neighborFinset y).erase p.c := by rw [heq]; simp
  have hv : v ∈ (G.neighborFinset y).erase p.c := by rw [heq]; simp
  have hwu : p.c ≠ u := (Finset.mem_erase.mp hu).1.symm
  have hwv : p.c ≠ v := (Finset.mem_erase.mp hv).1.symm
  have hyu : G.Adj y u := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hu).2
  have hyv : G.Adj y v := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hv).2
  obtain ⟨q,hq⟩ := path_of_neighbor hy (hneighbors u hyu) hyu.symm
  obtain ⟨r,hr⟩ := path_of_neighbor hy (hneighbors v hyv) hyv.symm
  have hpq : p.a ≠ q.a := first_ne_of_last_ne hpart hg hx p q (by simpa [hq] using hwu)
  have hpr : p.a ≠ r.a := first_ne_of_last_ne hpart hg hx p r (by simpa [hr] using hwv)
  have hqr : q.a ≠ r.a := first_ne_of_last_ne hpart hg hx q r (by simpa [hq,hr] using huv)
  obtain ⟨P,hP⟩ := cube_path hpart hg hx hf he p
  obtain ⟨Q,hQ⟩ := cube_path hpart hg hx hf he q
  obtain ⟨S,hS⟩ := cube_path hpart hg hx hf he r
  have hPa : P.a = p.a := congrArg FourPath.a hP
  have hPc : P.c = p.c := congrArg FourPath.c hP
  have hQa : Q.a = q.a := congrArg FourPath.a hQ
  have hSa : S.a = r.a := congrArg FourPath.a hS
  have hdir := fan_direction hpart hg hx hf he P Q S
    (by simpa [hPa,hQa] using hpq) (by simpa [hPa,hSa] using hpr)
    (by simpa [hQa,hSa] using hqr)
  exact ⟨P.i, by simpa [hPa] using P.fa, by simpa [hPc,← hdir] using P.fy⟩

private lemma flip_direction_injective (X : Q n) {i j : Fin n}
    (h : flip X i = flip X j) : i = j := by
  by_contra hij
  have hcoord := congrFun h i
  simp [BalancedCriticalSpectrum.flip, hij] at hcoord

/-- A failure of the genuine distance-layer disjoint-neighborhood property in a
finite induced cube graph of extended girth at least eight. The bipartition is
actual and contains the root on its left side. No fan or coordinate certificate
is an input. -/
def claim : Prop :=
  ∃ n m : ℕ, ∃ G : SimpleGraph (Fin m), ∃ f : Fin m → Q n,
    ∃ L R : Finset (Fin m), ∃ x y z w : Fin m,
      Function.Injective f ∧
      (∀ a b, G.Adj a b ↔ (hypercube n).Adj (f a) (f b)) ∧
      G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)) ∧
      x ∈ L ∧ (8 : ℕ∞) ≤ G.egirth ∧
      G.edist x y = 4 ∧ G.edist x z = 4 ∧
      G.degree y = 3 ∧ G.degree z = 3 ∧
      (∀ u, G.Adj y u → G.edist x u = 3) ∧
      (∀ u, G.Adj z u → G.edist x u = 3) ∧
      y ≠ z ∧ G.Adj y w ∧ G.Adj z w

/-- Property (D): distinct distance-four degree-three vertices whose neighbors
all lie at graph distance three cannot share a neighbor. -/
theorem result : ¬ claim := by
  rintro ⟨n,m,G,f,L,R,x,y,z,w,hf,he,hpart,hx,hg,hy,hz,hdy,hdz,hny,hnz,hyz,hyw,hzw⟩
  obtain ⟨a,b,hxa,hab,hbw,hxb,haw⟩ := prefix_of_edist_three (hny w hyw)
  let p : FourPath G x y :=
    ⟨a,b,w,hxa,hab,hbw,hyw.symm,hxb,haw,second_ne_endpoint hy hxa hab⟩
  let q : FourPath G x z :=
    ⟨a,b,w,hxa,hab,hbw,hzw.symm,hxb,haw,second_ne_endpoint hz hxa hab⟩
  obtain ⟨i,hai,hyi⟩ := final_flip hpart hg hx hf he hy hdy hny p
  obtain ⟨j,haj,hzj⟩ := final_flip hpart hg hx hf he hz hdz hnz q
  have hij : i = j := flip_direction_injective (f x) (hai.symm.trans haj)
  apply hyz
  apply hf
  rw [hij] at hyi
  exact hyi.trans hzj.symm

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubeLayerDisjointness

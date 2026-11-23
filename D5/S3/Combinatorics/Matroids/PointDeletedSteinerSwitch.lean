/- GID: D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A matching edge replaced by a four-edge path has one possible triangle. -/

import D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap

/-! # The leave of a switch in a point-deleted Steiner packing -/

namespace D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch

private def PathAdjacent {V : Type*} (p : Fin 5 → V) (x y : V) : Prop :=
  ∃ i j, p i = x ∧ p j = y ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)

private def RemainingMatch {V : Type*} (p : Fin 5 → V) (m : V → V) (x y : V) : Prop :=
  x ≠ p 0 ∧ x ≠ p 4 ∧ y ≠ p 0 ∧ y ≠ p 4 ∧ m x = y

/-- The residual matching and the four successive path edges. -/
def SwitchedLeave {V : Type*} (p : Fin 5 → V) (m : V → V) (x y : V) : Prop :=
  PathAdjacent p x y ∨ RemainingMatch p m x y

private theorem two_path_edges {V : Type*} {p : Fin 5 → V} {x y z : V}
    (injective : Function.Injective p) (xy : PathAdjacent p x y)
    (yz : PathAdjacent p y z) (distinct : x ≠ z) :
    ∃ i k : Fin 5, p i = x ∧ p k = z ∧ (i.val + 2 = k.val ∨ k.val + 2 = i.val) := by
  obtain ⟨i, j, hi, hj, step₁⟩ := xy
  obtain ⟨j', k, hj', hk, step₂⟩ := yz
  have eq := injective (hj.trans hj'.symm)
  subst j'
  have ne : i.val ≠ k.val := fun same => distinct (hi.symm.trans (Fin.ext same ▸ hk))
  exact ⟨i, k, hi, hk, by omega⟩

private theorem path_two_then_match {V : Type*} {p : Fin 5 → V} {m : V → V}
    (injective : Function.Injective p) (involutive : Function.Involutive m) {x y z : V}
    (xy : PathAdjacent p x y) (yz : PathAdjacent p y z) (zx : SwitchedLeave p m z x)
    (distinct : x ≠ z) : m (p 1) = p 3 := by
  obtain ⟨i, k, hi, hk, distance⟩ := two_path_edges injective xy yz distinct
  rcases zx with ⟨l, j, hl, hj, step⟩ | ⟨nz₀, nz₄, nx₀, nx₄, mate⟩
  · have eli := injective (hj.trans hi.symm)
    have elk := injective (hl.trans hk.symm)
    subst j
    subst l
    omega
  have internal (l : Fin 5) (n₀ : p l ≠ p 0) (n₄ : p l ≠ p 4) :
      1 ≤ l.val ∧ l.val ≤ 3 := by
    have h₀ : l.val ≠ 0 := fun eq => n₀ (congrArg p (Fin.ext eq))
    have h₄ : l.val ≠ 4 := fun eq => n₄ (congrArg p (Fin.ext eq))
    omega
  have il := internal i (by rw [hi]; exact nx₀) (by rw [hi]; exact nx₄)
  have kl := internal k (by rw [hk]; exact nz₀) (by rw [hk]; exact nz₄)
  rcases distance with lower | upper
  · have i1 : i = 1 := Fin.ext (by omega)
    have k3 : k = 3 := Fin.ext (by omega)
    rw [i1] at hi
    rw [k3] at hk
    rw [hi, hk]
    rw [← mate, involutive]
  · have i3 : i = 3 := Fin.ext (by omega)
    have k1 : k = 1 := Fin.ext (by omega)
    rw [i3] at hi
    rw [k1] at hk
    simpa only [hi, hk] using mate

private theorem matched_path_triangle {V : Type*} {p : Fin 5 → V} {m : V → V}
    (injective : Function.Injective p) (involutive : Function.Involutive m)
    (fixedPointFree : ∀ x, m x ≠ x) :
    (∃ x y z, SwitchedLeave p m x y ∧ SwitchedLeave p m y z ∧
      SwitchedLeave p m z x) ↔ m (p 1) = p 3 := by
  have distinct {x y : V} (h : SwitchedLeave p m x y) : x ≠ y := by
    intro eq
    subst y
    rcases h with ⟨i, j, hi, hj, step⟩ | ⟨_, _, _, _, e⟩
    · have same := injective (hi.trans hj.symm)
      subst j
      omega
    · exact fixedPointFree _ e
  have two_matches {x y z : V} (xy : RemainingMatch p m x y)
      (yz : RemainingMatch p m y z) : z = x := by
    obtain ⟨_, _, _, _, e₁⟩ := xy
    obtain ⟨_, _, _, _, e₂⟩ := yz
    rw [← e₁, involutive] at e₂
    exact e₂.symm
  constructor
  · rintro ⟨x, y, z, xy, yz, zx⟩
    have hxy := distinct xy
    have hyz := distinct yz
    have hzx := distinct zx
    rcases xy with (xy | xy)
    · rcases yz with (yz | yz)
      · exact path_two_then_match injective involutive xy yz zx hzx.symm
      · rcases zx with (zx | zx)
        · exact path_two_then_match injective involutive zx xy (Or.inr yz) hyz.symm
        · exact (hxy (two_matches yz zx)).elim
    · rcases yz with (yz | yz)
      · rcases zx with (zx | zx)
        · exact path_two_then_match injective involutive yz zx (Or.inr xy) hxy.symm
        · exact (hyz (two_matches zx xy)).elim
      · exact (hzx (two_matches xy yz)).elim
  · intro mate
    have reverse : m (p 3) = p 1 := by rw [← mate, involutive]
    have different {i j : Fin 5} (ne : i ≠ j) : p i ≠ p j := fun eq => ne (injective eq)
    refine ⟨p 1, p 2, p 3, Or.inl ⟨1, 2, rfl, rfl, Or.inl rfl⟩,
      Or.inl ⟨2, 3, rfl, rfl, Or.inl rfl⟩, Or.inr ?_⟩
    exact ⟨different (by decide), different (by decide), different (by decide),
      different (by decide), reverse⟩


open Set
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)

private def PairIs {V : Type*} (a b x y : V) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

private theorem triple_pairs {V : Type*} (a b c : V) {x y : V} (ne : x ≠ y) :
    (x ∈ ({a,b,c} : Set V) ∧ y ∈ ({a,b,c} : Set V)) ↔
      PairIs a b x y ∨ PairIs b c x y ∨ PairIs c a x y := by
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hy⟩
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact (ne rfl).elim | simp [PairIs]
  · rintro ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)) <;>
      simp

private theorem path_pairs {V : Type*} (p : Fin 5 → V) (x y : V) :
    PathAdjacent p x y ↔
      PairIs (p 0) (p 1) x y ∨ PairIs (p 1) (p 2) x y ∨
      PairIs (p 2) (p 3) x y ∨ PairIs (p 3) (p 4) x y := by
  constructor
  · rintro ⟨i,j,hi,hj,step⟩
    have enum : ∀ i j : Fin 5, (i.val + 1 = j.val ∨ j.val + 1 = i.val) →
        PairIs (0 : Fin 5) 1 i j ∨ PairIs 1 2 i j ∨ PairIs 2 3 i j ∨ PairIs 3 4 i j := by
      unfold PairIs
      decide
    rcases enum i j step with h | h | h | h <;>
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [PairIs, ← hi, ← hj]
  · rintro ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) |
        (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨0,1,rfl,rfl,Or.inl rfl⟩
    · exact ⟨1,0,rfl,rfl,Or.inr rfl⟩
    · exact ⟨1,2,rfl,rfl,Or.inl rfl⟩
    · exact ⟨2,1,rfl,rfl,Or.inr rfl⟩
    · exact ⟨2,3,rfl,rfl,Or.inl rfl⟩
    · exact ⟨3,2,rfl,rfl,Or.inr rfl⟩
    · exact ⟨3,4,rfl,rfl,Or.inl rfl⟩
    · exact ⟨4,3,rfl,rfl,Or.inr rfl⟩

/-- Remove the two consecutive packing blocks and insert the block on the even path indices. -/
def switchedPacking {r : ℕ} (P : Set (Set (Fin r))) (p : Fin 5 → Fin r) :
    Set (Set (Fin r)) :=
  insert {p 0,p 2,p 4} (P \ {{p 0,p 1,p 2},{p 2,p 3,p 4}})

set_option maxHeartbeats 500000 in
-- The two packing families and the leave are checked together across the four path edges.
private theorem replace_two_blocks {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) {p : Fin 5 → Fin r} (injective : Function.Injective p)
    {m : Fin r → Fin r} (involutive : Function.Involutive m)
    (oldLeave : ∀ x y, Uncovered P x y ↔ m x = y)
    (endpoints : m (p 0) = p 4)
    (left : ({p 0,p 1,p 2} : Set (Fin r)) ∈ P)
    (right : ({p 2,p 3,p 4} : Set (Fin r)) ∈ P) :
    IsPartialSteiner (switchedPacking P p) ∧ (switchedPacking P p).ncard + 1 = P.ncard ∧
      ∀ x y, Uncovered (switchedPacking P p) x y ↔ SwitchedLeave p m x y := by
  classical
  let a := p 0
  let b := p 1
  let v := p 2
  let d := p 3
  let c := p 4
  have ab : a ≠ b := fun h => (by decide : (0 : Fin 5) ≠ 1) (injective h)
  have av : a ≠ v := fun h => (by decide : (0 : Fin 5) ≠ 2) (injective h)
  have ad : a ≠ d := fun h => (by decide : (0 : Fin 5) ≠ 3) (injective h)
  have ac : a ≠ c := fun h => (by decide : (0 : Fin 5) ≠ 4) (injective h)
  have bv : b ≠ v := fun h => (by decide : (1 : Fin 5) ≠ 2) (injective h)
  have bd : b ≠ d := fun h => (by decide : (1 : Fin 5) ≠ 3) (injective h)
  have bc : b ≠ c := fun h => (by decide : (1 : Fin 5) ≠ 4) (injective h)
  have vd : v ≠ d := fun h => (by decide : (2 : Fin 5) ≠ 3) (injective h)
  have vc : v ≠ c := fun h => (by decide : (2 : Fin 5) ≠ 4) (injective h)
  have dc : d ≠ c := fun h => (by decide : (3 : Fin 5) ≠ 4) (injective h)
  let B : Set (Fin r) := {a,b,v}
  let D : Set (Fin r) := {v,d,c}
  let A : Set (Fin r) := {a,v,c}
  let removed : Set (Set (Fin r)) := {B,D}
  let Q := insert A (P \ removed)
  have removed_sub : removed ⊆ P := by
    intro s hs
    rcases (show s = B ∨ s = D from hs) with rfl | rfl
    · exact left
    · exact right
  have deleted_distinct : B ≠ D := by
    intro e
    have ha : a ∈ D := e ▸ (show a ∈ B by simp [B])
    simp [D,av,ad,ac] at ha
  have free : Uncovered P a c := (oldLeave a c).mpr endpoints
  have edgeSet (x y : Fin r) (ne : x ≠ y) :
      Uncovered Q x y ↔
        ¬(x ∈ A ∧ y ∈ A) ∧ (Uncovered P x y ∨ ∃ t ∈ removed, x ∈ t ∧ y ∈ t) := by
    constructor
    · intro h
      refine ⟨fun both => h.2 ⟨A,by simp [Q],both.1,both.2⟩,?_⟩
      by_cases exists_used : Covered P x y
      · obtain ⟨s,hs,hx,hy⟩ := exists_used
        by_cases rm : s ∈ removed
        · exact Or.inr ⟨s,rm,hx,hy⟩
        · exact (h.2 ⟨s,Or.inr ⟨hs,rm⟩,hx,hy⟩).elim
      · exact Or.inl ⟨ne, exists_used⟩
    · rintro ⟨outside, reason⟩
      refine ⟨ne,?_⟩
      rintro ⟨s,hs,hx,hy⟩
      rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs
      · exact outside ⟨hx,hy⟩
      · rcases reason with unused | ⟨t,ht,htx,hty⟩
        · exact unused.2 ⟨s,hs.1,hx,hy⟩
        · exact hs.2 (valid.2 t (removed_sub ht) s hs.1 x y ne htx hty hx hy ▸ ht)
  have no_conflict {s : Set (Fin r)} (hs : s ∈ P \ removed) {x y : Fin r} (ne : x ≠ y)
      (hx : x ∈ A) (hy : y ∈ A) (hsx : x ∈ s) (hsy : y ∈ s) : False := by
    have t := (triple_pairs a v c ne).mp ⟨hx,hy⟩
    rcases t with ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · have e := valid.2 B left s hs.1 a v ne (by simp [B]) (by simp [B]) hsx hsy
      exact hs.2 (e ▸ (show B ∈ removed by simp [removed]))
    · have e := valid.2 B left s hs.1 v a ne (by simp [B]) (by simp [B]) hsx hsy
      exact hs.2 (e ▸ (show B ∈ removed by simp [removed]))
    · have e := valid.2 D right s hs.1 v c ne (by simp [D]) (by simp [D]) hsx hsy
      exact hs.2 (e ▸ (show D ∈ removed by simp [removed]))
    · have e := valid.2 D right s hs.1 c v ne (by simp [D]) (by simp [D]) hsx hsy
      exact hs.2 (e ▸ (show D ∈ removed by simp [removed]))
    · exact free.2 ⟨s,hs.1,hsy,hsx⟩
    · exact free.2 ⟨s,hs.1,hsx,hsy⟩
  have validQ : IsPartialSteiner Q := by
    constructor
    · intro s hs
      rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs
      · exact Set.ncard_eq_three.mpr ⟨a,v,c,av,ac,vc,rfl⟩
      · exact valid.1 s hs.1
    · intro s hs t ht x y ne hx hy tx ty
      rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs <;>
        rcases (show t = A ∨ t ∈ P \ removed from ht) with rfl | ht
      · rfl
      · exact (no_conflict ht ne hx hy tx ty).elim
      · exact (no_conflict hs ne tx ty hx hy).elim
      · exact valid.2 s hs.1 t ht.1 x y ne hx hy tx ty
  have absent : A ∉ P \ removed := fun h => free.2 ⟨A,h.1, by simp [A],by simp [A]⟩
  have count := Set.ncard_sdiff_add_ncard_of_subset removed_sub
  rw [show removed.ncard = 2 from Set.ncard_pair deleted_distinct] at count
  have newCount : Q.ncard + 1 = P.ncard := by
    rw [show Q = insert A (P \ removed) from rfl, Set.ncard_insert_of_notMem absent]
    omega
  refine ⟨validQ,newCount,?_⟩
  change ∀ x y, Uncovered Q x y ↔ SwitchedLeave p m x y
  intro x y
  by_cases ne : x = y
  · subst y
    refine iff_of_false (fun h => h.1 rfl) ?_
    intro h
    rcases h with ⟨i,j,hi,hj,step⟩ | ⟨_,_,_,_,e⟩
    · have eq := injective (hi.trans hj.symm)
      subst j
      omega
    · exact ((oldLeave _ _).mpr e).1 rfl
  have reverse : m c = a := by
    change m (p 4) = p 0
    rw [← endpoints, involutive]
  have surviving : (¬(x ∈ A ∧ y ∈ A) ∧ Uncovered P x y) ↔ RemainingMatch p m x y := by
    constructor
    · rintro ⟨outside,h⟩
      have e := (oldLeave x y).mp h
      change x ≠ a ∧ x ≠ c ∧ y ≠ a ∧ y ≠ c ∧ m x = y
      have symm : m y = x := by rw [← e,involutive]
      refine ⟨?_,?_,?_,?_,e⟩
      · rintro rfl
        have eq : y = c := e.symm.trans endpoints
        exact outside ⟨by simp [A],by simp [A,eq]⟩
      · rintro rfl
        have eq : y = a := e.symm.trans reverse
        exact outside ⟨by simp [A],by simp [A,eq]⟩
      · rintro rfl
        have eq : x = c := symm.symm.trans endpoints
        exact outside ⟨by simp [A,eq],by simp [A]⟩
      · rintro rfl
        have eq : x = a := symm.symm.trans reverse
        exact outside ⟨by simp [A,eq],by simp [A]⟩
    · rintro ⟨nx,nxc,ny,nyc,e⟩
      have unused := (oldLeave x y).mpr e
      refine ⟨?_,unused⟩
      rintro ⟨hx,hy⟩
      change x ≠ a at nx
      change x ≠ c at nxc
      change y ≠ a at ny
      change y ≠ c at nyc
      have xv : x = v := by simpa [A,nx,nxc] using hx
      have yv : y = v := by simpa [A,ny,nyc] using hy
      exact unused.1 (xv.trans yv.symm)
  have freed : (¬(x ∈ A ∧ y ∈ A) ∧ ∃ t ∈ removed, x ∈ t ∧ y ∈ t) ↔
      PathAdjacent p x y := by
    clear * - p a b v d c x y ne ab av ad ac bv bd bc vd vc dc A B D removed
    have removed_pair :
        (∃ t ∈ removed, x ∈ t ∧ y ∈ t) ↔
          (x ∈ B ∧ y ∈ B) ∨ (x ∈ D ∧ y ∈ D) := by
      constructor
      · rintro ⟨t,ht,hx,hy⟩
        rcases (show t = B ∨ t = D from ht) with rfl | rfl
        · exact Or.inl ⟨hx,hy⟩
        · exact Or.inr ⟨hx,hy⟩
      · rintro (⟨hx,hy⟩ | ⟨hx,hy⟩)
        · exact ⟨B,by simp [removed],hx,hy⟩
        · exact ⟨D,by simp [removed],hx,hy⟩
    rw [removed_pair, path_pairs p]
    constructor
    · rintro ⟨outside, covered⟩
      rw [triple_pairs a v c ne] at outside
      have av_eq : PairIs v a x y ↔ PairIs a v x y := by simp [PairIs,or_comm]
      have vc_eq : PairIs c v x y ↔ PairIs v c x y := by simp [PairIs,or_comm]
      rcases covered with hb | hd
      · rw [triple_pairs a b v ne, av_eq] at hb
        tauto
      · rw [triple_pairs v d c ne, vc_eq] at hd
        tauto
    · intro path
      have hb : b ∉ A := by simp [A,ab.symm,bv,bc]
      have hd : d ∉ A := by simp [A,ad.symm,vd.symm,dc]
      refine ⟨?_,?_⟩
      · rintro ⟨hx,hy⟩
        rcases path with
          ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) |
           (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · exact hb hy
        · exact hb hx
        · exact hb hx
        · exact hb hy
        · exact hd hy
        · exact hd hx
        · exact hd hx
        · exact hd hy
      · rw [triple_pairs a b v ne, triple_pairs v d c ne]
        tauto
  rw [edgeSet x y ne, and_or_left, surviving, freed, SwitchedLeave, or_comm]


open RankThreeSaturatedTopGap (Maximal maximal_of_no_uncovered_triple insert_uncovered_triangle)

private theorem switched_maximal_iff {r : ℕ} {Q : Set (Set (Fin r))}
    (valid : IsPartialSteiner Q) {p : Fin 5 → Fin r} (injective : Function.Injective p)
    {m : Fin r → Fin r} (involutive : Function.Involutive m) (noFixed : ∀ x, m x ≠ x)
    (leave : ∀ x y, Uncovered Q x y ↔ SwitchedLeave p m x y) :
    Maximal Q ↔ m (p 1) ≠ p 3 := by
  classical
  constructor
  · intro maximal obstruction
    obtain ⟨a,b,c,ab,bc,ca⟩ := (matched_path_triangle injective involutive noFixed).mpr obstruction
    have h₁ := (leave a b).mpr ab
    have h₂ := (leave b c).mpr bc
    have h₃ := (leave c a).mpr ca
    let A : Set (Fin r) := {a,b,c}
    have eq : insert A Q = Q :=
      maximal _ (insert_uncovered_triangle valid h₁ h₂ h₃) (Set.subset_insert _ _)
    exact h₁.2 ⟨A,eq ▸ Set.mem_insert _ _,by simp [A],by simp [A]⟩
  · intro obstruction
    apply maximal_of_no_uncovered_triple
    intro a b c ab bc ca
    by_contra! unused
    apply obstruction
    exact (matched_path_triangle injective involutive noFixed).mp
      ⟨a,b,c,(leave _ _).mp ⟨ab,unused.1⟩,
        (leave _ _).mp ⟨bc,unused.2.1⟩,(leave _ _).mp ⟨ca,unused.2.2⟩⟩


open RankThreeSaturatedTopGap (pair_completion)

/-- Retained blocks after removing a point, relabelled by the canonical complementary embedding. -/
def pointDeletedFamily {r : ℕ} (S : Set (Set (Fin (r + 1)))) (q : Fin (r + 1)) :
    Set (Set (Fin r)) :=
  {s | q.succAbove '' s ∈ S}

private theorem deleted_leaves_matching {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)) :
    IsPartialSteiner (pointDeletedFamily S q) ∧
      ∃ m : Fin r → Fin r, Function.Involutive m ∧ (∀ a, m a ≠ a) ∧
        (∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b) := by
  classical
  let embed := q.succAbove
  let P := pointDeletedFamily S q
  have inj : Function.Injective embed := Fin.succAbove_right_injective
  have outside (a : Fin r) : embed a ≠ q := Fin.succAbove_ne q a
  have validP : IsPartialSteiner P := by
    constructor
    · intro s hs
      change (embed '' s) ∈ S at hs
      rw [← Set.ncard_image_of_injective s inj]
      exact valid.1 _ hs
    · intro s hs t ht a b ne as bs at' bt
      change (embed '' s) ∈ S at hs
      change (embed '' t) ∈ S at ht
      apply (Set.image_injective.mpr inj)
      exact valid.2 _ hs _ ht _ _ (fun h => ne (inj h))
        ⟨a,as,rfl⟩ ⟨b,bs,rfl⟩ ⟨a,at',rfl⟩ ⟨b,bt,rfl⟩
  have partner (a : Fin r) : ∃ b : Fin r, b ≠ a ∧ ({q,embed a,embed b} : Set (Fin (r+1))) ∈ S := by
    have ne := (outside a).symm
    obtain ⟨c,cq,ca,hc⟩ := pair_completion valid ne (complete q (embed a) ne)
    obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq cq
    change embed b = c at hb
    refine ⟨b,fun e => ca (hb.symm.trans (congrArg embed e)),?_⟩
    rw [hb]
    exact hc
  choose m mates using partner
  have equal_of_pair {a b : Fin r}
      (h : ({q,embed a,embed b} : Set (Fin (r+1))) ∈ S) : m a = b := by
    have eq := valid.2 _ (mates a).2 _ h q (embed a) (outside a).symm
      (by simp) (by simp) (by simp) (by simp)
    have mem : embed (m a) ∈ ({q,embed a,embed b} : Set (Fin (r+1))) :=
      eq ▸ (show embed (m a) ∈ ({q,embed a,embed (m a)} : Set (Fin (r+1))) by simp)
    simpa only [mem_insert_iff, mem_singleton_iff, outside, inj.eq_iff, (mates a).1,
      false_or] using mem
  have inv : Function.Involutive m := by
    intro a
    apply equal_of_pair
    have reverse : ({q,embed (m a),embed a} : Set (Fin (r+1))) = {q,embed a,embed (m a)} := by
      ext i
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rw [reverse]
    exact (mates a).2
  refine ⟨validP, m, inv, fun a => (mates a).1, ?_⟩
  intro a b
  constructor
  · intro leave
    obtain ⟨s,hs,ha,hb⟩ := complete (embed a) (embed b) (fun h => leave.1 (inj h))
    by_cases hq : q ∈ s
    · have sub : ({q,embed a,embed b} : Set (Fin (r+1))) ⊆ s := by
        simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hq (And.intro ha hb)
      have card : ({q,embed a,embed b} : Set (Fin (r+1))).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨q,embed a,embed b,(outside a).symm,(outside b).symm,
          fun h => leave.1 (inj h),rfl⟩
      have eq := Set.eq_of_subset_of_ncard_le sub (by rw [valid.1 s hs, card])
      exact equal_of_pair (eq.symm ▸ hs)
    · let t := embed ⁻¹' s
      have before : embed '' t = s := by
        apply Set.image_preimage_eq_of_subset
        intro x hx
        exact Fin.exists_succAbove_eq (fun eq => hq (eq ▸ hx))
      have ht : t ∈ P := by
        change embed '' t ∈ S
        rwa [before]
      exact (leave.2 ⟨t,ht,ha,hb⟩).elim
  · intro eq
    subst b
    refine ⟨(mates a).1.symm, ?_⟩
    rintro ⟨s,hs,ha,hb⟩
    change embed '' s ∈ S at hs
    have same := valid.2 _ hs _ (mates a).2 (embed a) (embed (m a))
      (fun h => (mates a).1 (inj h).symm) ⟨a,ha,rfl⟩ ⟨m a,hb,rfl⟩ (by simp) (by simp)
    have mem : q ∈ embed '' s :=
      same.symm ▸ (show q ∈ ({q,embed a,embed (m a)} : Set (Fin (r+1))) by simp)
    obtain ⟨x,_,eq⟩ := mem
    exact outside x eq



private theorem block_distinct {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) {a b c : Fin r} (block : ({a,b,c} : Set (Fin r)) ∈ P) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have card := valid.1 _ block
  have at_most_two (x y : Fin r) : ({x,y} : Set (Fin r)).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le x ({y} : Set (Fin r))
  refine ⟨?_,?_,?_⟩
  · intro eq
    subst b
    have upper := at_most_two a c
    simp only [insert_idem] at card
    omega
  · intro eq
    subst c
    have same : ({a,b,a} : Set (Fin r)) = {a,b} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rw [same] at card
    have upper := at_most_two a b
    omega
  · intro eq
    subst c
    have upper := at_most_two a b
    rw [show ({a,b,b} : Set (Fin r)) = {a,b} by ext x; simp] at card
    omega

private theorem switch_vertices {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) {a b v d c : Fin r}
    (left : ({a,b,v} : Set (Fin r)) ∈ P) (right : ({v,d,c} : Set (Fin r)) ∈ P)
    (free : Uncovered P a c) : Function.Injective ([a,b,v,d,c].get : Fin 5 → Fin r) := by
  obtain ⟨ab,av,bv⟩ := block_distinct valid left
  obtain ⟨vd,vc,dc⟩ := block_distinct valid right
  have bc : b ≠ c := by
    intro eq
    exact free.2 ⟨{a,b,v},left,by simp,by simp [eq]⟩
  have ad : a ≠ d := by
    intro eq
    exact free.2 ⟨{v,d,c},right,by simp [eq],by simp⟩
  have bd : b ≠ d := by
    intro eq
    have same := valid.2 _ left _ right b v bv (by simp) (by simp)
      (by simp [eq]) (by simp)
    have mem : a ∈ ({v,d,c} : Set (Fin r)) :=
      same ▸ (show a ∈ ({a,b,v} : Set (Fin r)) by simp)
    simp [av,ad,free.1] at mem
  have nodup : [a,b,v,d,c].Nodup := by
    simp [List.nodup_cons,ab,av,ad,free.1,bv,bd,bc,vd,vc,dc]
  exact nodup.injective_get

private theorem switch_for_pair {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) {m : Fin r → Fin r} (involutive : Function.Involutive m)
    (noFixed : ∀ a, m a ≠ a) (oldLeave : ∀ a b, Uncovered P a b ↔ m a = b)
    (a v : Fin r) (ne : v ≠ a) (notMate : v ≠ m a) :
    ∃ b d : Fin r, let p : Fin 5 → Fin r := [a,b,v,d,m a].get
      ({a,v,b} : Set (Fin r)) ∈ P ∧ ({m a,v,d} : Set (Fin r)) ∈ P ∧
        Function.Injective p ∧ IsPartialSteiner (switchedPacking P p) ∧
        (switchedPacking P p).ncard + 1 = P.ncard ∧
        (∀ x y, Uncovered (switchedPacking P p) x y ↔ SwitchedLeave p m x y) ∧
        (Maximal (switchedPacking P p) ↔ d ≠ m b) := by
  classical
  let c := m a
  have av : Covered P a v := by
    by_contra h
    exact notMate (((oldLeave _ _).mp ⟨ne.symm,h⟩).symm)
  have cv : Covered P c v := by
    by_contra h
    have e := (oldLeave c v).mp ⟨notMate.symm,h⟩
    exact ne (e.symm.trans (involutive a))
  obtain ⟨b,ba,bv,hb⟩ := pair_completion valid ne.symm av
  obtain ⟨d,dc,dv,hd⟩ := pair_completion valid notMate.symm cv
  have ac_free : Uncovered P a c := (oldLeave _ _).mpr rfl
  let p : Fin 5 → Fin r := [a,b,v,d,c].get
  have left : ({p 0,p 1,p 2} : Set (Fin r)) ∈ P := by
    change ({a,b,v} : Set (Fin r)) ∈ P
    convert hb using 1
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  have right : ({p 2,p 3,p 4} : Set (Fin r)) ∈ P := by
    change ({v,d,c} : Set (Fin r)) ∈ P
    convert hd using 1
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  have inj : Function.Injective p := switch_vertices valid left right ac_free
  obtain ⟨hQ,count,leave⟩ := replace_two_blocks valid inj involutive oldLeave
    (show m (p 0) = p 4 from rfl) left right
  have max := switched_maximal_iff hQ inj involutive noFixed leave
  exact ⟨b,d,hb,hd,inj,hQ,count,leave,max.trans (not_congr eq_comm)⟩

/-- The switch on a point-deleted system replaces one matching edge by a four-edge path. -/
theorem point_deleted_switch {r : ℕ} (S : Set (Set (Fin (r + 1))))
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b) (q : Fin (r + 1)) :
    let P := pointDeletedFamily S q
    IsPartialSteiner P ∧
      ∃ m : Fin r → Fin r, Function.Involutive m ∧ (∀ a, m a ≠ a) ∧
        (∀ a b, Uncovered P a b ↔ m a = b) ∧
        ∀ a v, v ≠ a → v ≠ m a →
          ∃ b d : Fin r, let p : Fin 5 → Fin r := [a,b,v,d,m a].get
            ({a,v,b} : Set (Fin r)) ∈ P ∧ ({m a,v,d} : Set (Fin r)) ∈ P ∧
              Function.Injective p ∧ IsPartialSteiner (switchedPacking P p) ∧
              (switchedPacking P p).ncard + 1 = P.ncard ∧
              (∀ x y, Uncovered (switchedPacking P p) x y ↔ SwitchedLeave p m x y) ∧
              (Maximal (switchedPacking P p) ↔ d ≠ m b) := by
  intro P
  obtain ⟨hP,m,inv,noFixed,leave⟩ := deleted_leaves_matching valid complete q
  exact ⟨hP,m,inv,noFixed,leave,switch_for_pair hP inv noFixed leave⟩


open RankThreeSaturatedTopGap (leaveNeighbors packing_leave_count vertex_leave_count)
open RankThreeInternalSizeSpectrum (fibers_card_eq)

private theorem optimal_size_of_matching_leave {r : ℕ} {P : Set (Set (Fin r))}
    (positive : 0 < r) (valid : IsPartialSteiner P) {m : Fin r → Fin r}
    (leave : ∀ a b, Uncovered P a b ↔ m a = b) :
    P.ncard = r * (r - 2) / 6 ∧
      ∀ Q : Set (Set (Fin r)), IsPartialSteiner Q → Q.ncard ≤ P.ncard := by
  classical
  have h₁ (a : Fin r) : leaveNeighbors P a = {m a} := by
    ext b
    change Uncovered P a b ↔ b = m a
    rw [leave a b, eq_comm]
  have count : 6 * P.ncard = r * (r - 2) := by
    have h := packing_leave_count valid
    have sum := fibers_card_eq (leaveNeighbors P)
    change ({p : Fin r × Fin r | Uncovered P p.1 p.2} : Set _).ncard =
      ∑ a : Fin r, (leaveNeighbors P a).ncard at sum
    have full_sum : ∑ a : Fin r, (leaveNeighbors P a).ncard = r := by
      simp [h₁]
    rw [sum, full_sum] at h
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm r 2]
    omega
  have even : r % 2 = 0 := by
    let a : Fin r := ⟨0,positive⟩
    have h := vertex_leave_count valid a
    rw [h₁, Set.ncard_singleton] at h
    omega
  refine ⟨by rw [← count]; omega, ?_⟩
  intro Q validQ
  have first (a : Fin r) : 1 ≤ (leaveNeighbors Q a).ncard := by
    have h := vertex_leave_count validQ a
    omega
  have sum := fibers_card_eq (leaveNeighbors Q)
  change ({p : Fin r × Fin r | Uncovered Q p.1 p.2} : Set _).ncard =
    ∑ a : Fin r, (leaveNeighbors Q a).ncard at sum
  have cap : r ≤ ∑ a : Fin r, (leaveNeighbors Q a).ncard := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun a _ => first a)
  have h := packing_leave_count validQ
  rw [sum] at h
  rw [Nat.mul_sub_left_distrib, Nat.mul_comm r 2] at count
  omega

open RankThreeInternalTriplePotentials (Row LiftedLineFamily)
open RankThreeOmissionPotentials (covers)
open RankThreeInternalSteinerDecomposition (extendedFamily forward_decomposition)
open RankThreeInternalSizeSpectrum
open D5.S3.Combinatorics.LatinEulerianMultiples (IsLatin)

/-- A successful matching switch realizes the first deficit below the saturated maximum. -/
theorem matching_switch_first_deficit {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (P : Set (Set (Fin r))) (valid : IsPartialSteiner P) (m : Fin r → Fin r)
    (leave : ∀ a b, Uncovered P a b ↔ m a = b)
    (p : Fin 5 → Fin r) (endpoints : m (p 0) = p 4)
    (first : ({p 0,p 1,p 2} : Set (Fin r)) ∈ P)
    (second : ({p 2,p 3,p 4} : Set (Fin r)) ∈ P) (success : m (p 1) ≠ p 3) :
    let N := 3 ^ d * r ^ 2 + 3 ^ (d + 1) * (r * (r - 2) / 6)
    (∃ G, IsSaturatedInternalExtension mixed G ∧ G.ncard = N) ∧
    (∃ G, IsSaturatedInternalExtension mixed G ∧ G.ncard + 1 = N) ∧
    (∀ G, IsInternalExtension mixed G → G.ncard ≤ N) := by
  classical
  intro N
  let I := Row d × ZMod 3
  let M := P.ncard
  have positive : 0 < r := Nat.zero_lt_of_lt (p 0).isLt
  obtain ⟨formula, upper⟩ := optimal_size_of_matching_leave positive valid leave
  have classes : Fintype.card I = 3 ^ (d + 1) := by
    simp [I, Row, Fintype.card_prod, pow_succ]
  have N_eq : N = 3 ^ d * r ^ 2 + Fintype.card I * M := by
    simp only [N,classes,M,formula]
  have noFixed (a : Fin r) : m a ≠ a := fun eq => ((leave a a).mpr eq).1 rfl
  have involutive : Function.Involutive m := by
    intro a
    apply (leave (m a) a).mp
    have h := (leave a (m a)).mpr rfl
    exact ⟨h.1.symm, fun ⟨s,hs,hma,ha⟩ => h.2 ⟨s,hs,ha,hma⟩⟩
  have maximal : Maximal P := by
    apply maximal_of_no_uncovered_triple
    intro a b c ab bc ca
    by_contra! h
    have hab := (leave a b).mp ⟨ab,h.1⟩
    have hbc := (leave b c).mp ⟨bc,h.2.1⟩
    rw [← hab,involutive] at hbc
    exact ca hbc.symm
  have inj : Function.Injective p := by
    have repr : p = ([p 0,p 1,p 2,p 3,p 4].get : Fin 5 → Fin r) := by
      funext i
      fin_cases i <;> rfl
    rw [repr]
    exact switch_vertices valid first second ((leave _ _).mpr endpoints)
  let Q := switchedPacking P p
  obtain ⟨validQ,countQ,leaveQ⟩ :=
    replace_two_blocks valid inj involutive leave endpoints first second
  have maxQ : Maximal Q := (switched_maximal_iff validQ inj involutive noFixed leaveQ).mpr success
  let : NeZero r := ⟨positive.ne'⟩
  obtain ⟨labels,hlabels⟩ := RankThreeMinimumInternalAdditions.residue_indexing r
  let e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r) := fun _ => labels
  have he (x : Row d) (a : ZMod (3 * r)) :
      (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a := hlabels a
  let bridge := saturated_internal_extension_iff e he hd mixed family crosses mixedUnique
  obtain ⟨sq,latin⟩ := latin_exists r
  let L : Row d → Fin r → Fin r → Fin r := fun _ => sq
  have count (K : Row d → Fin r → Fin r → Fin r) (F : Row d → ZMod 3 → Set (Set (Fin r)))
      (hF : ∀ x c, IsPartialSteiner (F x c)) :
      (extendedFamily e K F).ncard = 3 ^ d * r ^ 2 + ∑ i : I, (F i.1 i.2).ncard := by
    rw [counting_decomposition e K F hF, packingEntries, fibers_card_eq (fun i : I => F i.1 i.2)]
  let F₀ : Row d → ZMod 3 → Set (Set (Fin r)) := fun _ _ => P
  have full : IsSaturatedInternalExtension mixed (extendedFamily e L F₀) :=
    (bridge _).mpr ⟨L,F₀,fun _ => latin,fun _ _ => valid,fun _ _ => maximal,rfl⟩
  have full_size : (extendedFamily e L F₀).ncard = N := by
    rw [count L F₀ (fun _ _ => valid), N_eq]
    simp [F₀,M]
  let i₀ : I := (0,0)
  let F₁ (x : Row d) (c : ZMod 3) := if (x,c) = i₀ then Q else P
  have valid₁ (x : Row d) (c : ZMod 3) : IsPartialSteiner (F₁ x c) := by
    by_cases h : (x,c) = i₀
    · simpa only [F₁, ite_eq_left h] using (show IsPartialSteiner Q from validQ)
    · simpa only [F₁, ite_eq_right h] using valid
  have max₁ (x : Row d) (c : ZMod 3) : Maximal (F₁ x c) := by
    by_cases h : (x,c) = i₀ <;> simp [F₁,h,maximal,maxQ]
  have small : IsSaturatedInternalExtension mixed (extendedFamily e L F₁) :=
    (bridge _).mpr ⟨L,F₁,fun _ => latin,valid₁,max₁,rfl⟩
  have small_size : (extendedFamily e L F₁).ncard + 1 = N := by
    rw [count L F₁ valid₁, ← full_size, count L F₀ (fun _ _ => valid)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀),
      ← Finset.sum_erase_add (f := fun i : I => (F₀ i.1 i.2).ncard) _ (Finset.mem_univ i₀)]
    have eq : ∑ i ∈ Finset.univ.erase i₀, (F₁ i.1 i.2).ncard =
        ∑ i ∈ Finset.univ.erase i₀, (F₀ i.1 i.2).ncard := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [F₁,F₀,(Finset.mem_erase.mp hi).1]
    rw [eq]
    simp only [F₁,F₀,Prod.mk.eta,ite_true]
    change Q.ncard + 1 = P.ncard at countQ
    omega
  refine ⟨⟨_,full,full_size⟩,⟨_,small,small_size⟩,?_⟩
  rintro G ⟨U,internal,same,distinct,unique,dim,rfl⟩
  obtain ⟨K,F,_,validF,split⟩ :=
    forward_decomposition e he hd mixed internal family crosses same distinct unique dim
  rw [split, count K F validF, N_eq]
  apply Nat.add_le_add_left
  calc
    (∑ i : I, (F i.1 i.2).ncard) ≤ ∑ _i : I, M :=
      Finset.sum_le_sum fun i _ => upper _ (validF i.1 i.2)
    _ = _ := by simp

end D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch

/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual T complements splice into a complete two-star core cycle. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open Equiv

private def tau (m : ℕ) : Configuration m :=
  Equiv.swap (0 : Fin (m + 1)) (Fin.last m)

def CoreDomain (m : ℕ) (v : Configuration m) : Prop :=
  Star ((a m * c m) (Fin.last m))
      (residualList (a m * c m) : Cycle (Fin (m + 1))) v ∨
    Star ((tau m * (a m * c m)) (Fin.last m))
      (residualList (tau m * (a m * c m)) : Cycle (Fin (m + 1))) v

def coreGraph (m : ℕ) : SimpleGraph {v : Configuration m // CoreDomain m v} :=
  (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).induce
    {v | CoreDomain m v}

def cutStart {m : ℕ} : Fin m ⊕ Fin (m - 2) → Configuration m
  | .inl i => if i.val = m - 1 then 1 else tCircleAnchor (.inl i)
  | .inr j => tCircleAnchor (.inr j)

def cutGenerator {m : ℕ} : Fin m ⊕ Fin (m - 2) → Configuration m
  | .inl i => if m - 2 ≤ i.val then a m else b m
  | .inr _ => b m

private def cutOrder {m : ℕ} (hm : 4 ≤ m) : List (Fin m ⊕ Fin (m - 2)) :=
  [.inl ⟨m - 1, by omega⟩] ++
    List.ofFn (fun j : Fin (m - 2) => .inl ⟨j.val, by have hj := j.isLt; omega⟩) ++
    [.inl ⟨m - 2, by omega⟩] ++ List.ofFn (fun j : Fin (m - 2) => .inr j)

private theorem half_endpoint {m : ℕ} (hm : 4 ≤ m) :
    a m * c m * (b m * c m) ^ (m - 2) = tau m := by
  simpa only [tHalfWord, List.prod_append, List.prod_cons, List.prod_nil,
    mul_one, List.prod_flatten, List.map_replicate, List.prod_replicate, tau] using
    native_t_halfword_swap (by omega : 3 ≤ m)

theorem tau_bc_rotation {m : ℕ} (hm : 4 ≤ m) :
    Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (b m * c m) =
      finRotate (m + 1) := by
  apply Equiv.ext
  intro i
  rw [Equiv.Perm.mul_apply, bc_apply (by omega : 2 ≤ m)]
  by_cases hi : i.val < m
  · rw [dif_pos hi]
    by_cases hil : i.val = m - 1
    · have he : (⟨(i.val + 1) % m, by
        have hn := Nat.mod_lt (i.val + 1) (by omega : 0 < m)
        omega⟩ : Fin (m + 1)) = 0 := by
        apply Fin.ext
        simp [hil, show m - 1 + 1 = m by omega]
      rw [he]
      simp only [Equiv.swap_apply_left, finRotate_apply]
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
      rw [hil, show m - 1 + 1 = m by omega,
        Nat.mod_eq_of_lt (by omega : m < m + 1)]
    · have hmod : (i.val + 1) % m = i.val + 1 :=
        Nat.mod_eq_of_lt (by omega)
      have hn0 : (⟨(i.val + 1) % m, by
        have hn := Nat.mod_lt (i.val + 1) (by omega : 0 < m)
        omega⟩ : Fin (m + 1)) ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_zero, hmod] at hv
        omega
      have hnl : (⟨(i.val + 1) % m, by
        have hn := Nat.mod_lt (i.val + 1) (by omega : 0 < m)
        omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_last, hmod] at hv
        omega
      rw [Equiv.swap_apply_of_ne_of_ne hn0 hnl, finRotate_apply]
      apply Fin.ext
      simp only [hmod, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt (by omega : 1 < m + 1),
        Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
  · have he : i = Fin.last m := Fin.ext (by change i.val = m; have hb := i.isLt; omega)
    rw [dif_neg hi, he]
    simp [finRotate_apply]


private theorem last_gap_rotation {m : ℕ} (hm : 4 ≤ m) :
    tCircleAnchor (.inl ⟨m - 1, by omega⟩ : Fin m ⊕ Fin (m - 2)) =
      finRotate (m + 1) := by
  change a m * c m * (b m * c m) ^ (m - 1) = _
  rw [show m - 1 = (m - 2) + 1 by omega, pow_succ,
    ← mul_assoc, half_endpoint hm, tau, tau_bc_rotation hm]

private theorem circle_rotation {m : ℕ} (z : Configuration m) :
    configurationCycle (z * finRotate (m + 1)) = configurationCycle z := by
  apply Cycle.coe_eq_coe.mpr
  rw [show List.ofFn (z * finRotate (m + 1)) = (List.ofFn z).rotate 1 from
    by simpa only [pow_one] using rotate_pow_list z 1]
  exact List.IsRotated.symm ⟨1, rfl⟩

theorem native_cut_circle_iff {m : ℕ} (hm : 4 ≤ m)
    (p : Fin m ⊕ Fin (m - 2)) (v : Configuration m) :
    Circle (cutStart p) v ↔ Circle (tCircleAnchor p) v := by
  cases p with
  | inl i =>
    by_cases hi : i.val = m - 1
    · have he : i = ⟨m - 1, by omega⟩ := Fin.ext hi
      have hr := circle_rotation (1 : Configuration m)
      simp only [one_mul] at hr
      simp only [cutStart, hi, ↓reduceIte]
      rw [he, last_gap_rotation hm]
      simp only [Circle, hr]
    · simp only [cutStart, if_neg hi]
  | inr j => rfl

private theorem star_of_gap_circle {m : ℕ} (hm : 3 ≤ m)
    (z v : Configuration m) (i : Fin m) (hi : Circle (gapAnchor z i) v) :
    Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v := by
  let p := (circleEquiv hm (gapAnchor z i)).symm ⟨v, hi⟩
  have hp := congrArg Subtype.val ((circleEquiv hm (gapAnchor z i)).apply_symm_apply
    ⟨v, hi⟩)
  change circleCoordinate (gapAnchor z i) p = v at hp
  have hc := (coordinateEquiv hm z (i, p)).property
  change Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1)))
    (circleCoordinate (gapAnchor z i) p) at hc
  exact hp ▸ hc

private theorem circle_in_domain {m : ℕ} (hm : 4 ≤ m)
    (p : Fin m ⊕ Fin (m - 2)) (v : Configuration m)
    (hv : Circle (tCircleAnchor p) v) : CoreDomain m v := by
  cases p with
  | inl i =>
    exact Or.inl (star_of_gap_circle (by omega : 3 ≤ m) (a m * c m) v i hv)
  | inr j =>
    apply Or.inr
    apply star_of_gap_circle (by omega : 3 ≤ m) (tau m * (a m * c m)) v
      ⟨j.val, by have hj := j.isLt; omega⟩
    simpa only [tau, tCircleAnchor, gapAnchor, mul_assoc] using hv

private theorem cutGenerator_mem {m : ℕ} (p : Fin m ⊕ Fin (m - 2)) :
    cutGenerator p = a m ∨ cutGenerator p = b m := by
  cases p with
  | inl i => simp only [cutGenerator]; split <;> simp
  | inr j => exact Or.inr rfl

private theorem exists_native_complement {m : ℕ} (hm : 4 ≤ m)
    (z g : Configuration m) (hg : g = a m ∨ g = b m) :
    ∃ w : (SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).Walk z (z * g),
      w.IsPath ∧ w.length = 2 * (m + 1) - 1 ∧
        (∀ v : Configuration m, v ∈ w.support ↔ Circle z v) := by
  rcases hg with rfl | rfl
  · obtain ⟨w, hp, hl, _, hs⟩ := native_a_complement (by omega : 3 ≤ m) z
    refine ⟨w.mapLe (SimpleGraph.deleteEdges_le _), hp.mapLe _, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.length_mapLe] using hl
    · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hs
  · obtain ⟨w, hp, hl, _, hs⟩ := native_b_complement (by omega : 3 ≤ m) z
    refine ⟨w.mapLe (SimpleGraph.deleteEdges_le _), hp.mapLe _, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.length_mapLe] using hl
    · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hs

/-- The literal old T cuts, specified from their native ports before choosing
any complement or Hamilton cycle. -/
def CoreDeletedEdge (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  ∃ p : Fin m ⊕ Fin (m - 2), e = s(cutStart p, cutStart p * cutGenerator p)

/-- Every owner contributes all of its native edges except its literal T cut. -/
def CoreUncut (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  ∃ p : Fin m ⊕ Fin (m - 2), NativeCircleEdge (cutStart p) e ∧
    e ≠ s(cutStart p, cutStart p * cutGenerator p)

/-- The complete literal T c connections are independently indexed by the cuts. -/
def TSeam (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  ∃ p : Fin m ⊕ Fin (m - 2),
    e = s(cutStart p * cutGenerator p, cutStart p * cutGenerator p * c m)

private def retainsNative {m : ℕ} (p : Fin m ⊕ Fin (m - 2))
    (r : Piece (coreGraph m)) : Prop :=
  ∀ (x y : {v : Configuration m // CoreDomain m v}) (g : Configuration m),
    Circle (tCircleAnchor p) x.val → (g = a m ∨ g = b m) →
    y.val = x.val * g →
    s(x.val, y.val) ≠ s(cutStart p, cutStart p * cutGenerator p) →
    s(x, y) ∈ r.walk.edges

set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_core_piece {m : ℕ} (hm : 4 ≤ m) (p : Fin m ⊕ Fin (m - 2)) :
    ∃ r : Piece (coreGraph m),
      r.start.val = cutStart p ∧ r.finish.val = cutStart p * cutGenerator p ∧
        r.walk.IsPath ∧ r.walk.length = 2 * (m + 1) - 1 ∧
          (∀ v : {v : Configuration m // CoreDomain m v},
            v ∈ r.walk.support ↔ Circle (tCircleAnchor p) v.val) ∧ retainsNative p r ∧
          (∀ e : Sym2 (Configuration m),
            e ∈ r.walk.edges.map (Sym2.map Subtype.val) ↔
              NativeCircleEdge (cutStart p) e ∧
                e ≠ s(cutStart p, cutStart p * cutGenerator p)) := by
  obtain ⟨w, hp, hl, hs⟩ := exists_native_complement hm
    (cutStart p) (cutGenerator p) (cutGenerator_mem p)
  have hle : SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m)) ≤
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
    SimpleGraph.mulCayley_mono (by intro x hx; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢; tauto)
  let q := w.mapLe hle
  have hqp : q.IsPath := hp.mapLe hle
  have hql : q.length = 2 * (m + 1) - 1 :=
    (SimpleGraph.Walk.length_mapLe hle w).trans hl
  have hq : ∀ x ∈ q.support, x ∈ {v | CoreDomain m v} := by
    intro x hx
    have hc : Circle (cutStart p) x := hs x |>.mp (by
      simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hx)
    exact circle_in_domain hm p x ((native_cut_circle_iff hm p x).mp hc)
  let r := q.induce {v | CoreDomain m v} hq
  have hrs : r.support.map Subtype.val = q.support := by
    have he := congrArg SimpleGraph.Walk.support (SimpleGraph.Walk.map_induce q hq)
    rw [SimpleGraph.Walk.support_map] at he
    change r.support.map Subtype.val = q.support at he
    exact he
  have hredges : r.edges.map (Sym2.map Subtype.val) = w.edges := by
    have heq := congrArg SimpleGraph.Walk.edges (SimpleGraph.Walk.map_induce q hq)
    rw [SimpleGraph.Walk.edges_map] at heq
    change r.edges.map (Sym2.map Subtype.val) = q.edges at heq
    simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using heq
  refine ⟨⟨_, _, r⟩, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    have hmapped : (r.support.map Subtype.val).Nodup := by
      rw [hrs]
      exact hqp.support_nodup
    exact hmapped.of_map
  · have he := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.map_induce q hq)
    simp only [SimpleGraph.Walk.length_map] at he
    exact he.trans hql
  · intro v
    change v ∈ r.support ↔ Circle (tCircleAnchor p) v.val
    have hmemb : v ∈ r.support ↔ v.val ∈ q.support := by
      rw [← hrs]
      constructor
      · intro hv
        exact List.mem_map.mpr ⟨v, hv, rfl⟩
      · intro hv
        obtain ⟨x, hx, hval⟩ := List.mem_map.mp hv
        have h : x = v := Subtype.ext hval
        exact h ▸ hx
    rw [hmemb]
    simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using
      (hs v.val).trans (native_cut_circle_iff hm p v.val)
  · intro x y g hx hg hy hne
    have he : s(x.val, y.val) ∈ w.edges := by
      rw [hy]
      apply (native_complement_edge_inventory (by omega : 3 ≤ m)
        (cutStart p) (cutGenerator p) (cutGenerator_mem p) w hp hl hs
        x.val g ((native_cut_circle_iff hm p x.val).mpr hx) hg).mpr
      simpa only [hy] using hne
    rw [← hredges] at he
    obtain ⟨e, he, heq⟩ := List.mem_map.mp he
    have heq' : Sym2.map Subtype.val e = Sym2.map Subtype.val s(x, y) := heq
    have hexy : e = s(x, y) := Sym2.map.injective Subtype.val_injective heq'
    exact hexy ▸ he
  · intro e
    change e ∈ r.edges.map (Sym2.map Subtype.val) ↔ _
    rw [hredges]
    exact native_complement_full_edge_inventory (by omega : 3 ≤ m)
      (cutStart p) (cutGenerator p) (cutGenerator_mem p) w hp hl hs e


private noncomputable def corePiece {m : ℕ} (hm : 4 ≤ m)
    (p : Fin m ⊕ Fin (m - 2)) : Piece (coreGraph m) :=
  Classical.choose (exists_core_piece hm p)

private theorem corePiece_spec {m : ℕ} (hm : 4 ≤ m) (p : Fin m ⊕ Fin (m - 2)) :
    (corePiece hm p).start.val = cutStart p ∧
      (corePiece hm p).finish.val = cutStart p * cutGenerator p ∧
        (corePiece hm p).walk.IsPath ∧
          (corePiece hm p).walk.length = 2 * (m + 1) - 1 ∧
            (∀ v : {v : Configuration m // CoreDomain m v},
              v ∈ (corePiece hm p).walk.support ↔ Circle (tCircleAnchor p) v.val) ∧
            retainsNative p (corePiece hm p) ∧
            (∀ e : Sym2 (Configuration m),
              e ∈ (corePiece hm p).walk.edges.map (Sym2.map Subtype.val) ↔
                NativeCircleEdge (cutStart p) e ∧
                  e ≠ s(cutStart p, cutStart p * cutGenerator p)) :=
  Classical.choose_spec (exists_core_piece hm p)

private theorem owner_unique {m : ℕ} (hm : 4 ≤ m) (v : Configuration m)
    (p q : Fin m ⊕ Fin (m - 2))
    (hp : Circle (tCircleAnchor p) v) (hq : Circle (tCircleAnchor q) v) : p = q := by
  have hd := circle_in_domain hm p v hp
  have hs : Star ((a m * c m) (Fin.last m))
      (residualList (a m * c m) : Cycle (Fin (m + 1))) v ∨
      Star ((Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) (Fin.last m))
        (residualList (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) :
          Cycle (Fin (m + 1))) v := hd
  obtain ⟨i, _, hi⟩ := (native_t_circle_partition hm v).mp hs
  exact (hi p hp).trans (hi q hq).symm

private theorem cutOrder_mem {m : ℕ} (hm : 4 ≤ m) (p : Fin m ⊕ Fin (m - 2)) :
    p ∈ cutOrder hm := by
  cases p with
  | inl i =>
    by_cases hi : i.val < m - 2
    · have he : Sum.inl i ∈ List.ofFn
          (fun j : Fin (m - 2) =>
            (Sum.inl ⟨j.val, by have hj := j.isLt; omega⟩ : Fin m ⊕ Fin (m - 2))) :=
        List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, by congr 1⟩
      simp only [cutOrder, List.mem_append, List.mem_singleton] at *
      tauto
    · by_cases hi2 : i.val = m - 2
      · have he : i = ⟨m - 2, by omega⟩ := Fin.ext hi2
        simp [cutOrder, he]
      · have he : i = ⟨m - 1, by omega⟩ :=
          Fin.ext (by change i.val = m - 1; have hb := i.isLt; omega)
        simp [cutOrder, he]
  | inr j => simp [cutOrder]

private theorem cutOrder_nodup {m : ℕ} (hm : 4 ≤ m) : (cutOrder hm).Nodup := by
  let lo := List.ofFn (fun j : Fin (m - 2) =>
    (Sum.inl ⟨j.val, by have hj := j.isLt; omega⟩ : Fin m ⊕ Fin (m - 2)))
  let up := List.ofFn (fun j : Fin (m - 2) => (Sum.inr j : Fin m ⊕ Fin (m - 2)))
  let first : Fin m ⊕ Fin (m - 2) := .inl ⟨m - 1, by omega⟩
  let mid : Fin m ⊕ Fin (m - 2) := .inl ⟨m - 2, by omega⟩
  have hlo : lo.Nodup := List.nodup_ofFn.mpr (by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin m => x.val) (Sum.inl.inj h)))
  have hup : up.Nodup := List.nodup_ofFn.mpr (by intro i j h; exact Sum.inr.inj h)
  have hmid : (mid :: up).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp only [up, List.mem_ofFn]
      rintro ⟨j, hj⟩
      change Sum.inr j = Sum.inl _ at hj
      cases hj
    · exact hup
  have htail : (lo ++ mid :: up).Nodup := hlo.append hmid (by
    rw [List.disjoint_left]
    intro p hp hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    rcases List.mem_cons.mp hq with he | he
    · have hv := congrArg (fun x : Fin m => x.val) (Sum.inl.inj he)
      have hj := j.isLt
      change j.val = m - 2 at hv
      omega
    · obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
      cases hk)
  have hfirst : first ∉ lo ++ mid :: up := by
    intro hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hp
      have hv := congrArg (fun x : Fin m => x.val) (Sum.inl.inj hj)
      have hb := j.isLt
      change j.val = m - 1 at hv
      omega
    · rcases List.mem_cons.mp hp with hp | hp
      · have hv := congrArg (fun x : Fin m => x.val) (Sum.inl.inj hp)
        change m - 1 = m - 2 at hv
        omega
      · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hp
        change Sum.inr j = Sum.inl _ at hj
        cases hj
  have h : (first :: (lo ++ mid :: up)).Nodup :=
    List.nodup_cons.mpr ⟨hfirst, htail⟩
  simpa only [first, lo, mid, up, cutOrder, List.singleton_append,
    List.append_assoc, List.cons_append, List.nil_append] using h

private theorem core_support_nodup {m : ℕ} (hm : 4 ≤ m) :
    ((cutOrder hm).flatMap (fun p => (corePiece hm p).walk.support)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro p _
    exact (corePiece_spec hm p).2.2.1.support_nodup
  · exact (cutOrder_nodup hm).imp (by
      intro p q hpq
      change List.Disjoint (corePiece hm p).walk.support (corePiece hm q).walk.support
      rw [List.disjoint_left]
      intro v hp hq
      apply hpq
      exact owner_unique hm v.val p q
        ((corePiece_spec hm p).2.2.2.2.1 v |>.mp hp)
        ((corePiece_spec hm q).2.2.2.2.1 v |>.mp hq))

private def cutNext {m : ℕ} (p q : Fin m ⊕ Fin (m - 2)) : Prop :=
  cutStart p * cutGenerator p * c m = cutStart q

private theorem lower_cut {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    cutStart (.inl ⟨j.val, by have hj := j.isLt; omega⟩ : Fin m ⊕ Fin (m - 2)) =
        a m * c m * (b m * c m) ^ j.val ∧
      cutGenerator (.inl ⟨j.val, by have hj := j.isLt; omega⟩ :
        Fin m ⊕ Fin (m - 2)) = b m := by
  have hj := j.isLt
  simp [cutStart, cutGenerator, tCircleAnchor, gapAnchor,
    show j.val ≠ m - 1 by omega, show ¬ m - 2 ≤ j.val by omega]

private theorem first_cut {m : ℕ} (hm : 4 ≤ m) :
    cutStart (.inl ⟨m - 1, by omega⟩ : Fin m ⊕ Fin (m - 2)) = 1 ∧
      cutGenerator (.inl ⟨m - 1, by omega⟩ : Fin m ⊕ Fin (m - 2)) = a m := by
  simp [cutStart, cutGenerator, show m - 2 ≤ m - 1 by omega]

private theorem middle_cut {m : ℕ} (hm : 4 ≤ m) :
    cutStart (.inl ⟨m - 2, by omega⟩ : Fin m ⊕ Fin (m - 2)) = tau m ∧
      cutGenerator (.inl ⟨m - 2, by omega⟩ : Fin m ⊕ Fin (m - 2)) = a m := by
  simp only [cutStart, cutGenerator, show m - 2 ≠ m - 1 by omega,
    if_false, le_refl, if_true, tCircleAnchor, gapAnchor]
  exact ⟨half_endpoint hm, trivial⟩

private theorem ofFn_endpoints {α : Type*} {n : ℕ} (hn : 0 < n)
    (f : Fin n → α) :
    (List.ofFn f).head? = some (f ⟨0, hn⟩) ∧
      (List.ofFn f).getLast? = some (f ⟨n - 1, by omega⟩) := by
  cases n with
  | zero => omega
  | succ k =>
    constructor
    · rw [List.ofFn_succ]
      rfl
    · rw [List.ofFn_succ_last]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
      rfl

private theorem cutOrder_closed_chain {m : ℕ} (hm : 4 ≤ m) :
    (cutOrder hm ++ [(Sum.inl ⟨m - 1, by omega⟩ : Fin m ⊕ Fin (m - 2))]).IsChain cutNext := by
  let lo := List.ofFn (fun j : Fin (m - 2) =>
    (Sum.inl ⟨j.val, by have hj := j.isLt; omega⟩ : Fin m ⊕ Fin (m - 2)))
  let up := List.ofFn (fun j : Fin (m - 2) => (Sum.inr j : Fin m ⊕ Fin (m - 2)))
  let first : Fin m ⊕ Fin (m - 2) := .inl ⟨m - 1, by omega⟩
  let mid : Fin m ⊕ Fin (m - 2) := .inl ⟨m - 2, by omega⟩
  have hlo : lo.IsChain cutNext := by
    apply List.isChain_ofFn.mpr
    intro i hi
    dsimp [cutNext]
    rw [(lower_cut hm ⟨i, by omega⟩).1, (lower_cut hm ⟨i, by omega⟩).2,
      (lower_cut hm ⟨i + 1, hi⟩).1]
    simp only [pow_succ, mul_assoc]
  have hup : up.IsChain cutNext := by
    apply List.isChain_ofFn.mpr
    intro i hi
    simp only [cutNext, cutStart, cutGenerator, tCircleAnchor,
      pow_succ, mul_assoc]
  have hlohead : lo.head? = some (.inl ⟨0, by omega⟩) :=
    (ofFn_endpoints (by omega : 0 < m - 2) _).1
  have hlotail : lo.getLast? = some (.inl ⟨m - 3, by omega⟩) := by
    have h := (ofFn_endpoints (by omega : 0 < m - 2)
      (fun j : Fin (m - 2) =>
        (Sum.inl ⟨j.val, by have hj := j.isLt; omega⟩ : Fin m ⊕ Fin (m - 2)))).2
    convert h using 1
  have huphead : up.head? = some (.inr ⟨0, by omega⟩) :=
    (ofFn_endpoints (by omega : 0 < m - 2) _).1
  have huptail : up.getLast? = some (.inr ⟨m - 3, by omega⟩) := by
    have h := (ofFn_endpoints (by omega : 0 < m - 2)
      (fun j : Fin (m - 2) => (Sum.inr j : Fin m ⊕ Fin (m - 2)))).2
    convert h using 1
  have hflo : ([first] ++ lo).IsChain cutNext := by
    apply List.IsChain.append (List.IsChain.singleton _) hlo
    simp only [List.getLast?_singleton, hlohead, Option.mem_some_iff]
    intro x hx y hy
    subst x; subst y
    dsimp [cutNext, first]
    rw [(first_cut hm).1, (first_cut hm).2,
      (lower_cut hm ⟨0, by omega⟩).1]
    simp
  have hflom : (([first] ++ lo) ++ [mid]).IsChain cutNext := by
    apply hflo.append (List.IsChain.singleton _)
    simp only [List.getLast?_append, hlotail, Option.some_or,
      List.head?_singleton, Option.mem_some_iff]
    intro x hx y hy
    subst x; subst y
    dsimp [cutNext, mid]
    rw [(lower_cut hm ⟨m - 3, by omega⟩).1,
      (lower_cut hm ⟨m - 3, by omega⟩).2, (middle_cut hm).1]
    have he := half_endpoint hm
    rw [show m - 2 = (m - 3) + 1 by omega, pow_succ] at he
    simpa only [Fin.val_mk, mul_assoc] using he
  have hall : ((([first] ++ lo) ++ [mid]) ++ up).IsChain cutNext := by
    apply hflom.append hup
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      huphead, Option.mem_some_iff]
    intro x hx y hy
    subst x; subst y
    dsimp [cutNext, mid]
    rw [(middle_cut hm).1, (middle_cut hm).2]
    simp [cutStart, tCircleAnchor, tau, mul_assoc]
  have hclose : (((([first] ++ lo) ++ [mid]) ++ up) ++ [first]).IsChain cutNext := by
    apply hall.append (List.IsChain.singleton _)
    simp only [List.getLast?_append, huptail, Option.some_or,
      List.head?_singleton, Option.mem_some_iff]
    intro x hx y hy
    subst x; subst y
    dsimp [cutNext, first]
    rw [(first_cut hm).1]
    simp only [cutStart, cutGenerator, tCircleAnchor]
    have he : tau m * (a m * c m * (b m * c m) ^ (m - 2)) = 1 := by
      rw [half_endpoint hm]
      simp [tau]
    rw [show m - 2 = (m - 3) + 1 by omega, pow_succ] at he
    simpa only [tau, mul_assoc] using he
  simpa only [cutOrder, first, mid, lo, up, List.append_assoc] using hclose

private theorem c_ne_one {m : ℕ} (hm : 4 ≤ m) : c m ≠ 1 := by
  intro h
  have he : (c m (0 : Fin (m + 1))).val = m - 2 := by
    rw [c_apply]
    change (if 0 < m - 1 then m - 2 else 0) = m - 2
    exact if_pos (by omega : 0 < m - 1)
  have hz : (c m (0 : Fin (m + 1))).val = 0 := by rw [h]; rfl
  omega

private theorem core_piece_adj {m : ℕ} (hm : 4 ≤ m)
    (p q : Fin m ⊕ Fin (m - 2)) (h : cutNext p q) :
    (coreGraph m).Adj (corePiece hm p).finish (corePiece hm q).start := by
  change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj _ _
  rw [SimpleGraph.mulCayley_adj']
  have he : (corePiece hm p).finish.val * c m = (corePiece hm q).start.val := by
    rw [(corePiece_spec hm p).2.1, (corePiece_spec hm q).1]
    exact h
  constructor
  · intro hn
    apply c_ne_one hm
    change (corePiece hm p).finish.val = (corePiece hm q).start.val at hn
    exact mul_left_cancel (he.trans (hn.symm.trans (mul_one _).symm))
  · exact ⟨c m, by simp, Or.inl he⟩

private theorem linked_of_chain {V : Type*} {G : SimpleGraph V}
    (p : Piece G) (ps : List (Piece G))
    (h : (p :: ps).IsChain (fun x y => G.Adj x.finish y.start)) : Linked p ps := by
  induction ps generalizing p with
  | nil => trivial
  | cons q qs ih =>
    exact ⟨(List.isChain_cons_cons.mp h).1, ih q (List.isChain_cons_cons.mp h).2⟩

private theorem linked_close {V : Type*} {G : SimpleGraph V}
    (p q : Piece G) (ps : List (Piece G)) (h : Linked p (ps ++ [q])) :
    Linked p ps ∧ G.Adj (finish p ps) q.start := by
  induction ps generalizing p with
  | nil => exact ⟨trivial, h.1⟩
  | cons r rs ih =>
    obtain ⟨hr, hc⟩ := ih r h.2
    exact ⟨⟨h.1, hr⟩, hc⟩

private theorem finish_seam {m : ℕ} (p q : Piece (coreGraph m))
    (ps : List (Piece (coreGraph m)))
    (h : (p :: (ps ++ [q])).IsChain
      (fun x y => x.finish.val * c m = y.start.val)) :
    (finish p ps).val * c m = q.start.val := by
  induction ps generalizing p with
  | nil => exact (List.isChain_cons_cons.mp h).1
  | cons r rs ih => exact ih r (List.isChain_cons_cons.mp h).2

private theorem core_connection_in_edges {m : ℕ}
    (p t r : Piece (coreGraph m)) (ps : List (Piece (coreGraph m)))
    (h : (p :: (ps ++ [t])).IsChain
      (fun x y => x.finish.val * c m = y.start.val)) (hr : r ∈ p :: ps) :
    s(r.finish.val, r.finish.val * c m) ∈
      s((finish p ps).val, t.start.val) :: (chainEdges p ps).map (Sym2.map Subtype.val) := by
  induction ps generalizing p with
  | nil =>
    have he : r = p := List.mem_singleton.mp hr
    subst r
    rw [(List.isChain_cons_cons.mp h).1]
    exact List.mem_cons_self
  | cons q qs ih =>
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      have hs := (List.isChain_cons_cons.mp h).1
      simp only [chainEdges, List.map_append, List.map_cons, Sym2.map_mk,
        List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inl (congrArg (fun v => s(p.finish.val, v)) hs)))
    · have ht := ih q (List.isChain_cons_cons.mp h).2 hr
      simp only [chainEdges, finish, List.map_append, List.map_cons, Sym2.map_mk,
        List.mem_cons, List.mem_append] at ht ⊢
      tauto

private theorem core_finish_owner {m : ℕ} (hm : 4 ≤ m)
    (p : Piece (coreGraph m)) (ps : List (Piece (coreGraph m)))
    (h : ∀ r ∈ p :: ps, ∃ i : Fin m ⊕ Fin (m - 2), r = corePiece hm i) :
    ∃ i : Fin m ⊕ Fin (m - 2), (finish p ps).val = cutStart i * cutGenerator i := by
  induction ps generalizing p with
  | nil =>
    obtain ⟨i, hi⟩ := h p List.mem_cons_self
    refine ⟨i, ?_⟩
    change p.finish.val = _
    rw [hi]
    exact (corePiece_spec hm i).2.1
  | cons q qs ih =>
    exact ih q (fun r hr => h r (List.mem_cons_of_mem p hr))

private theorem piece_edges_in_chain {V : Type*} {G : SimpleGraph V}
    (p r : Piece G) (ps : List (Piece G)) (hr : r ∈ p :: ps)
    (e : Sym2 V) (he : e ∈ r.walk.edges) : e ∈ chainEdges p ps := by
  induction ps generalizing p with
  | nil =>
    have hre : r = p := List.mem_singleton.mp hr
    subst r
    exact he
  | cons q qs ih =>
    simp only [chainEdges, List.mem_append, List.mem_cons]
    rcases List.mem_cons.mp hr with hre | hr
    · subst r
      exact Or.inl he
    · exact Or.inr (Or.inr (ih q hr))

/-- The actual native complements, with the literal alternating c connections,
cover exactly the union of both deletion-defined T supplier stars. The first
edge of the resulting Hamilton cycle is the actual closing c edge. Every other
native a/b edge in the core is retained, and the complete raw edge set is exactly
the independently indexed uncut native edges and T c seams. -/
theorem native_core_hamiltonian_cycle_with_full_inventory {m : ℕ} (hm : 4 ≤ m) :
    ∃ z : {v : Configuration m // CoreDomain m v}, z.val = 1 ∧
      ∃ w : (coreGraph m).Walk z z, w.IsHamiltonianCycle ∧
        (∃ y : {v : Configuration m // CoreDomain m v},
          y.val = c m ∧ w.edges.head? = some s(z, y)) ∧
        (∀ (x y : {v : Configuration m // CoreDomain m v}) (g : Configuration m),
          (g = a m ∨ g = b m) → y.val = x.val * g →
          ¬ CoreDeletedEdge m s(x.val, y.val) → s(x, y) ∈ w.edges) ∧
        ∀ e : Sym2 (Configuration m),
          e ∈ w.edges.map (Sym2.map Subtype.val) ↔ CoreUncut m e ∨ TSeam m e := by
  classical
  let : BEq {v : Configuration m // CoreDomain m v} := instBEqOfDecidableEq
  let first : Fin m ⊕ Fin (m - 2) := .inl ⟨m - 1, by omega⟩
  let rest : List (Fin m ⊕ Fin (m - 2)) :=
    List.ofFn (fun j : Fin (m - 2) =>
      .inl ⟨j.val, by have hj := j.isLt; omega⟩) ++
      [.inl ⟨m - 2, by omega⟩] ++ List.ofFn (fun j : Fin (m - 2) => .inr j)
  have horder : cutOrder hm = first :: rest := by
    simp [cutOrder, first, rest, List.append_assoc]
  let p := corePiece hm first
  let ps := rest.map (corePiece hm)
  have hchain : (first :: (rest ++ [first])).IsChain cutNext := by
    simpa only [horder, List.cons_append] using cutOrder_closed_chain hm
  have hactual : (p :: (ps ++ [p])).IsChain
      (fun x y => (coreGraph m).Adj x.finish y.start) := by
    have hc := List.isChain_map_of_isChain
      (S := fun (x y : Piece (coreGraph m)) => (coreGraph m).Adj x.finish y.start)
      (corePiece hm) (fun x y hxy => core_piece_adj hm x y hxy) hchain
    simpa only [List.map_cons, List.map_append, List.map_singleton, List.map_nil,
      p, ps] using hc
  obtain ⟨hl, hclose⟩ := linked_close p p ps (linked_of_chain p _ hactual)
  have hfull : ∀ v : {v : Configuration m // CoreDomain m v},
      ((p :: ps).flatMap (fun z => z.walk.support)).count v = 1 := by
    intro v
    apply List.count_eq_one_of_mem
    · simpa only [horder, List.flatMap_cons, List.flatMap_map, Function.comp_def,
        p, ps] using core_support_nodup hm
    · obtain ⟨i, hi, _⟩ := (native_t_circle_partition hm v.val).mp v.property
      have hv : v ∈ (cutOrder hm).flatMap (fun z => (corePiece hm z).walk.support) :=
        List.mem_flatMap.mpr ⟨i, cutOrder_mem hm i,
        ((corePiece_spec hm i).2.2.2.2.1 v).mpr hi⟩
      simpa only [horder, List.flatMap_cons, List.flatMap_map, Function.comp_def,
        p, ps] using hv
  have hsize : 3 ≤ ((p :: ps).flatMap (fun z => z.walk.support)).length := by
    have hp := (corePiece_spec hm first).2.2.2.1
    have hs := SimpleGraph.Walk.length_support p.walk
    change p.walk.length = 2 * (m + 1) - 1 at hp
    simp only [List.flatMap_cons, List.length_append]
    omega
  obtain ⟨w, hw, _, he⟩ := exists_spliced_hamiltonian_cycle p ps hl hclose hfull hsize
  have hstart : p.start.val = 1 :=
    (corePiece_spec hm first).1.trans (first_cut hm).1
  have hseams : (p :: (ps ++ [p])).IsChain
      (fun x y => x.finish.val * c m = y.start.val) := by
    have hc := List.isChain_map_of_isChain
      (S := fun (x y : Piece (coreGraph m)) => x.finish.val * c m = y.start.val)
      (corePiece hm) (fun x y hxy => by
        rw [(corePiece_spec hm x).2.1, (corePiece_spec hm y).1]
        exact hxy) hchain
    simpa only [List.map_cons, List.map_append, List.map_singleton, List.map_nil,
      p, ps] using hc
  have hfinal : (finish p ps).val = c m := by
    have hh := finish_seam p p ps hseams
    rw [hstart] at hh
    have ht := congrArg (· * c m) hh
    simpa only [mul_assoc, c_sq, mul_one, one_mul] using ht
  have hpieces (r : Piece (coreGraph m)) (hr : r ∈ p :: ps) :
      ∃ i : Fin m ⊕ Fin (m - 2), r = corePiece hm i := by
    have hmapped : r ∈ (cutOrder hm).map (corePiece hm) := by
      simpa only [horder, List.map_cons, p, ps] using hr
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hmapped
    exact ⟨i, hi.symm⟩
  have hpiece_mem (i : Fin m ⊕ Fin (m - 2)) : corePiece hm i ∈ p :: ps := by
    have hmapped : corePiece hm i ∈ (cutOrder hm).map (corePiece hm) :=
      List.mem_map.mpr ⟨i, cutOrder_mem hm i, rfl⟩
    simpa only [horder, List.map_cons, p, ps] using hmapped
  have hclass (d : Sym2 {v : Configuration m // CoreDomain m v})
      (hd : d ∈ chainEdges p ps) :
      CoreUncut m (Sym2.map Subtype.val d) ∨ TSeam m (Sym2.map Subtype.val d) := by
    rcases chain_edge_cases p ps d hd with ⟨r, hr, he⟩ | ⟨j, hj, he⟩
    · obtain ⟨i, rfl⟩ := hpieces r hr
      exact Or.inl ⟨i, ((corePiece_spec hm i).2.2.2.2.2.2 _).mp
        (List.mem_map.mpr ⟨d, he, rfl⟩)⟩
    · have hc := hseams
      rw [← List.cons_append] at hc
      have hrel := List.isChain_iff_getElem.mp hc.left_of_append j hj
      obtain ⟨i, hi⟩ := hpieces ((p :: ps)[j]'(by omega)) (List.getElem_mem _)
      refine Or.inr ⟨i, ?_⟩
      rw [he, Sym2.map_mk, ← hrel, hi, (corePiece_spec hm i).2.1]
  have hclosing : TSeam m (Sym2.map Subtype.val s(p.start, finish p ps)) := by
    obtain ⟨i, hi⟩ := core_finish_owner hm p ps hpieces
    have hs := finish_seam p p ps hseams
    refine ⟨i, ?_⟩
    rw [Sym2.map_mk, ← hs, hi]
    exact Sym2.eq_swap
  refine ⟨p.start, hstart, w, hw, ?_, ?_, ?_⟩
  · refine ⟨finish p ps, hfinal, ?_⟩
    rw [he]
    rfl
  · intro x y g hg hy hdeleted
    obtain ⟨i, hi, _⟩ := (native_t_circle_partition hm x.val).mp x.property
    have hpiece : corePiece hm i ∈ p :: ps := by
      have hmemb : corePiece hm i ∈ (cutOrder hm).map (corePiece hm) :=
        List.mem_map.mpr ⟨i, cutOrder_mem hm i, rfl⟩
      simpa only [horder, List.map_cons, p, ps] using hmemb
    have hretained := (corePiece_spec hm i).2.2.2.2.2.1 x y g hi hg hy (by
      intro heq
      exact hdeleted ⟨i, heq⟩)
    rw [he]
    exact List.mem_cons_of_mem _ (List.mem_reverse.mpr
      (piece_edges_in_chain p (corePiece hm i) ps hpiece _ hretained))
  · intro e
    constructor
    · intro hew
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hew
      rw [he, List.mem_cons, List.mem_reverse] at hd
      rcases hd with hd | hd
      · subst d
        exact Or.inr hclosing
      · exact hclass d hd
    · rintro (⟨i, hinv⟩ | ⟨i, rfl⟩)
      · have hp := ((corePiece_spec hm i).2.2.2.2.2.2 e).mpr hinv
        obtain ⟨d, hd, hde⟩ := List.mem_map.mp hp
        refine List.mem_map.mpr ⟨d, ?_, hde⟩
        rw [he]
        exact List.mem_cons_of_mem _ (List.mem_reverse.mpr
          (piece_edges_in_chain p (corePiece hm i) ps (hpiece_mem i) d hd))
      · have hconn := core_connection_in_edges p p (corePiece hm i) ps hseams (hpiece_mem i)
        rw [(corePiece_spec hm i).2.1] at hconn
        have hraw : w.edges.map (Sym2.map Subtype.val) =
            s(p.start.val, (finish p ps).val) ::
              ((chainEdges p ps).map (Sym2.map Subtype.val)).reverse := by
          rw [he, List.map_cons, Sym2.map_mk, List.map_reverse]
        rw [hraw, List.mem_cons, List.mem_reverse]
        rcases List.mem_cons.mp hconn with hconn | hconn
        · exact Or.inl (hconn.trans Sym2.eq_swap)
        · exact Or.inr hconn


/-- Preserve the established core-cycle API for existing contact iteration
consumers. The stronger construction also carries the complete edge set. -/
theorem native_core_hamiltonian_cycle {m : ℕ} (hm : 4 ≤ m) :
    ∃ z : {v : Configuration m // CoreDomain m v}, z.val = 1 ∧
      ∃ w : (coreGraph m).Walk z z, w.IsHamiltonianCycle ∧
        (∃ y : {v : Configuration m // CoreDomain m v},
          y.val = c m ∧ w.edges.head? = some s(z, y)) ∧
        ∀ (x y : {v : Configuration m // CoreDomain m v}) (g : Configuration m),
          (g = a m ∨ g = b m) → y.val = x.val * g →
          ¬ CoreDeletedEdge m s(x.val, y.val) → s(x, y) ∈ w.edges := by
  obtain ⟨z, hz, w, hw, hfirst, hretains, _⟩ :=
    native_core_hamiltonian_cycle_with_full_inventory hm
  exact ⟨z, hz, w, hw, hfirst, hretains⟩

#print axioms native_core_hamiltonian_cycle_with_full_inventory

#print axioms native_core_hamiltonian_cycle

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing

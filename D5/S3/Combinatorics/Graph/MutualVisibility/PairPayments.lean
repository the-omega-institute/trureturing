/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/PairPayments
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: A minimal rooted pair gives simultaneous distinct cut payments for inward triple replacements. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Geodesics
import D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity

/-! All payments belong to one actual cut and use one fixed inward predecessor. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}

theorem minimal_pair_exists (hH : H.Connected) (C : Finset (Configuration H))
    (s : Configuration H) (w : V)
    (hne : ∃ u v, u ≠ v ∧ CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩) :
    ∃ u v, u ≠ v ∧ CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩ ∧
      ∀ a b, a ≠ b → CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩ →
        H.dist u w + H.dist v w ≤ H.dist a w + H.dist b w := by
  classical
  let E : Set (V × V) := {q | q.1 ≠ q.2 ∧
    CutReach (reconfiguration H) C s ⟨{q.1, q.2}, visible_pair hH q.1 q.2⟩}
  have hE : E.Nonempty := by
    obtain ⟨u, v, huv, hr⟩ := hne
    exact ⟨(u, v), huv, hr⟩
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image E
    (fun q : V × V => H.dist q.1 w + H.dist q.2 w) (Set.toFinite E) hE
  exact ⟨q.1, q.2, hq.1, hq.2, fun a b hab hr => hmin (a, b) ⟨hab, hr⟩⟩

private theorem inward_cut_payment (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w u v p y : V}
    (hdom : Dominates H w u v) (hpu : H.Adj p u)
    (hp : H.dist p w + 1 = H.dist u w)
    (hmin : ∀ a b, a ≠ b →
      CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩ →
      H.dist u w + H.dist v w ≤ H.dist a w + H.dist b w)
    (huy : H.Adj u y) (hvy : H.Adj v y)
    (hS : Visible H {u, v, y})
    (hT : CutReach (reconfiguration H) C s ⟨{u, v, y}, hS⟩) :
    ∃ T ∈ C, T.val \ {u, v} = {p, y} := by
  obtain ⟨hpv, hpy, Q, P, hQ, hP, hTQ, hQP, hmass⟩ :=
    inward_replacement hH hdom huy hvy hpu hp hS
  have hPout : ¬ CutReach (reconfiguration H) C s P := by
    intro hr
    have he : P = ⟨{p, y}, visible_pair hH p y⟩ := Subtype.ext hP
    rw [he] at hr
    have := hmin p y hpy hr
    omega
  have hcut := cutReach_two_step_payment hT hTQ hQP hPout
  have hQS : Q.val \ {u, v} = {p, y} := by
    rw [hQ]
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    have := hpu.ne
    have := huy.ne
    have := hvy.ne
    aesop
  have hPS : P.val \ {u, v} = {p, y} := by
    rw [hP]
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    have := hpu.ne
    have := huy.ne
    have := hvy.ne
    aesop
  exact hcut.elim (fun h => ⟨Q, h, hQS⟩) (fun h => ⟨P, h, hPS⟩)

private theorem two_label_payments_injective (B : Finset V) (p : V)
    (E : Finset V) (f : V → Configuration H)
    (hp : p ∉ E) (hs : ∀ y ∈ E, (f y).val \ B = {p, y}) :
    Set.InjOn f E := by
  intro y hy z hz he
  have hpair : ({p, y} : Finset V) = {p, z} := by rw [← hs y hy, ← hs z hz, he]
  have hyz : y ∈ ({p, z} : Finset V) := hpair ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyz
  exact hyz.elim (fun h => (hp (h ▸ hy)).elim) id

def localCutClass (C : Finset (Configuration H)) (B : Finset V) (y : V) :
    Finset (Configuration H) := C.filter fun T => y ∈ T.val ∧ T.val ⊆ insert y B

private theorem localCutClass_disjoint (C : Finset (Configuration H)) (B : Finset V)
    {y z : V} (hy : y ∉ B) (hz : z ∉ B) (hne : y ≠ z) :
    Disjoint (localCutClass C B y) (localCutClass C B z) := by
  apply Finset.disjoint_left.mpr
  intro T hTy hTz
  have h1 := (Finset.mem_filter.mp hTy).2
  have h2 := (Finset.mem_filter.mp hTz).2
  have hmem := h2.2 h1.1
  exact (Finset.mem_insert.mp hmem).elim hne hy

private theorem two_label_payment_not_local (C : Finset (Configuration H)) (B : Finset V)
    {p y z : V} {T : Configuration H} (hp : p ∉ B) (hy : y ∉ B) (hpy : p ≠ y)
    (hT : T.val \ B = {p, y}) : T ∉ localCutClass C B z := by
  intro hlocal
  have hsub := (Finset.mem_filter.mp hlocal).2.2
  have hpT : p ∈ T.val := (Finset.mem_sdiff.mp (by rw [hT]; simp)).1
  have hyT : y ∈ T.val := (Finset.mem_sdiff.mp (by rw [hT]; simp)).1
  have hpz : p = z := (Finset.mem_insert.mp (hsub hpT)).elim id (fun h => (hp h).elim)
  have hyz : y = z := (Finset.mem_insert.mp (hsub hyT)).elim id (fun h => (hy h).elim)
  exact hpy (hpz.trans hyz.symm)

theorem simultaneous_inward_payments (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w u v p : V}
    (hdom : Dominates H w u v) (hpu : H.Adj p u)
    (hp : H.dist p w + 1 = H.dist u w)
    (hmin : ∀ a b, a ≠ b →
      CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩ →
      H.dist u w + H.dist v w ≤ H.dist a w + H.dist b w)
    (E : Finset V)
    (hE : ∀ y ∈ E, H.Adj u y ∧ H.Adj v y ∧
      ∃ hS : Visible H {u, v, y}, CutReach (reconfiguration H) C s ⟨{u, v, y}, hS⟩) :
    ∃ F : Finset (Configuration H), F ⊆ C ∧ F.card = E.card ∧
      Disjoint F (C.filter fun T => T.val ⊆ {u, v}) ∧
      ∀ z, Disjoint F (localCutClass C {u, v} z) := by
  classical
  have hpay : ∀ y ∈ E, ∃ T ∈ C, T.val \ {u, v} = {p, y} := by
    intro y hy
    obtain ⟨huy, hvy, hS, hT⟩ := hE y hy
    exact inward_cut_payment hH C s hdom hpu hp hmin huy hvy hS hT
  let f : V → Configuration H := fun y =>
    if hy : y ∈ E then Classical.choose (hpay y hy) else ⟨∅, visible_empty H⟩
  have hf : ∀ y ∈ E, f y ∈ C ∧ (f y).val \ {u, v} = {p, y} := by
    intro y hy
    have hfy : f y = Classical.choose (hpay y hy) := by simp [f, hy]
    rw [hfy]
    exact Classical.choose_spec (hpay y hy)
  have hpE : p ∉ E := by
    intro hpe
    obtain ⟨hup, hvp, hS, _⟩ := hE p hpe
    have hrep := inward_replacement hH hdom hup hvp hpu hp hS
    exact hrep.2.1 rfl
  have hinj := two_label_payments_injective {u, v} p E f hpE (fun y hy => (hf y hy).2)
  refine ⟨E.image f, ?_, Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · intro T hT
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hT
    exact (hf y hy).1
  · apply Finset.disjoint_left.mpr
    intro T hTF hTI
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hTF
    have hsub := (Finset.mem_filter.mp hTI).2
    have hm : p ∈ (f y).val \ {u, v} := by rw [(hf y hy).2]; simp
    exact (Finset.mem_sdiff.mp hm).2 (hsub (Finset.mem_sdiff.mp hm).1)
  · intro z
    apply Finset.disjoint_left.mpr
    intro T hTF hTL
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hTF
    have hsup := (hf y hy).2
    have hm1 : p ∈ (f y).val \ {u, v} := by rw [hsup]; simp
    have hm2 : y ∈ (f y).val \ {u, v} := by rw [hsup]; simp
    have hpy : p ≠ y := fun h => hpE (h.symm ▸ hy)
    exact two_label_payment_not_local C {u, v}
      (Finset.mem_sdiff.mp hm1).2 (Finset.mem_sdiff.mp hm2).2 hpy hsup hTL

theorem joint_cut_budget (C : Finset (Configuration H)) (B : Finset V)
    (Y : Finset V) (hY : Disjoint Y B) (F : Finset (Configuration H)) (hFC : F ⊆ C)
    (hFI : Disjoint F (C.filter fun T => T.val ⊆ B))
    (hFL : ∀ y ∈ Y, Disjoint F (localCutClass C B y)) :
    (C.filter fun T => T.val ⊆ B).card +
      (∑ y ∈ Y, (localCutClass C B y).card) + F.card ≤ C.card := by
  classical
  let I := C.filter fun T => T.val ⊆ B
  let L := Y.biUnion (localCutClass C B)
  have hYL : (Y : Set V).PairwiseDisjoint (localCutClass C B) := by
    intro y hy z hz hyz
    exact localCutClass_disjoint C B
      (Finset.disjoint_left.mp hY hy) (Finset.disjoint_left.mp hY hz) hyz
  have hLcard : L.card = ∑ y ∈ Y, (localCutClass C B y).card := Finset.card_biUnion hYL
  have hIL : Disjoint I L := by
    apply Finset.disjoint_left.mpr
    intro T hTI hTL
    obtain ⟨y, hy, hTy⟩ := Finset.mem_biUnion.mp hTL
    have hB := (Finset.mem_filter.mp hTI).2
    have hyT := (Finset.mem_filter.mp hTy).2.1
    exact Finset.disjoint_left.mp hY hy (hB hyT)
  have hF_L : Disjoint F L := by
    apply Finset.disjoint_left.mpr
    intro T hTF hTL
    obtain ⟨y, hy, hTy⟩ := Finset.mem_biUnion.mp hTL
    exact Finset.disjoint_left.mp (hFL y hy) hTF hTy
  have hIFL : Disjoint (I ∪ L) F := Finset.disjoint_union_left.mpr ⟨hFI.symm, hF_L.symm⟩
  have hsub : I ∪ L ∪ F ⊆ C := by
    intro T hT
    rcases Finset.mem_union.mp hT with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mp h).1
      · obtain ⟨y, _, hTy⟩ := Finset.mem_biUnion.mp h
        exact (Finset.mem_filter.mp hTy).1
    · exact hFC h
  have hb := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hIFL, Finset.card_union_of_disjoint hIL, hLcard] at hb
  exact hb

end D5.S3.Combinatorics.Graph.MutualVisibility

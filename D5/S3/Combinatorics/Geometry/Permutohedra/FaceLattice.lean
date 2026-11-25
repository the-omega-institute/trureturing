/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/FaceLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cut chains with bottom form the face lattice, with joins by common cuts. -/
import D5.S3.Combinatorics.Graph.PrefixHamming.ExactDimension
import Mathlib.Data.Finset.Sort

/-! The permutohedron face lattice presented by proper cut chains. -/

namespace Rossi
open Finset D5.S3.Combinatorics.Graph.PrefixHamming

set_option genSizeOfSpec false in
set_option genInjectivity false in
structure CutChain (n : ℕ) where
  cuts : Finset (Finset (Fin n))
  proper : ∀ c ∈ cuts, 0 < c.card ∧ c.card < n
  comparable : ∀ c ∈ cuts, ∀ d ∈ cuts, c ⊆ d ∨ d ⊆ c

@[ext (iff := false)] theorem CutChain.ext_cuts {n : ℕ} {c d : CutChain n}
    (h : c.cuts = d.cuts) : c = d := by cases c; cases d; cases h; rfl

instance {n : ℕ} : PartialOrder (CutChain n) where
  le x y := y.cuts ⊆ x.cuts
  le_refl _ := Subset.rfl
  le_trans _ _ _ hab hbc := Subset.trans hbc hab
  le_antisymm _ _ hab hba := CutChain.ext_cuts (Subset.antisymm hba hab)

instance {n : ℕ} : DecidableEq (CutChain n) := fun x y =>
  decidable_of_iff (x.cuts = y.cuts) ⟨CutChain.ext_cuts, congrArg CutChain.cuts⟩

abbrev Face (n : ℕ) := WithBot (CutChain n)

def faceSup {n : ℕ} : Face n → Face n → Face n
  | none, y => y
  | some x, none => ↑x
  | some x, some y => ↑({
      cuts := x.cuts ∩ y.cuts
      proper := fun c hc => x.proper c (mem_inter.mp hc).1
      comparable := fun c hc d hd => x.comparable c (mem_inter.mp hc).1 d (mem_inter.mp hd).1
    } : CutChain n)

private theorem coe_le_coe {n : ℕ} {x y : CutChain n} :
    (x : Face n) ≤ (y : Face n) ↔ y.cuts ⊆ x.cuts := WithBot.coe_le_coe

theorem faceSup_lub {n : ℕ} (x y : Face n) : IsLUB {x, y} (faceSup x y) := by
  suffices h : (x ≤ faceSup x y ∧ y ≤ faceSup x y) ∧
      (∀ z : Face n, x ≤ z ∧ y ≤ z → faceSup x y ≤ z) by
    simpa only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_ofPred_eq, Set.forall_mem_insert,
      Set.forall_mem_singleton] using h
  cases x using WithBot.recBotCoe
  · exact ⟨⟨bot_le, le_rfl⟩, fun z hz => hz.2⟩
  rename_i x
  cases y using WithBot.recBotCoe
  · exact ⟨⟨le_rfl, bot_le⟩, fun z hz => hz.1⟩
  rename_i y
  refine ⟨⟨coe_le_coe.2 inter_subset_left, coe_le_coe.2 inter_subset_right⟩, ?_⟩
  rintro z ⟨hx, hy⟩
  cases z using WithBot.recBotCoe
  · exact (WithBot.coe_ne_bot (le_bot_iff.mp hx)).elim
  exact coe_le_coe.2 (subset_inter (coe_le_coe.1 hx) (coe_le_coe.1 hy))

def compatible {n : ℕ} (x y : CutChain n) : Prop :=
  ∀ c ∈ x.cuts ∪ y.cuts, ∀ d ∈ x.cuts ∪ y.cuts, c ⊆ d ∨ d ⊆ c

private def unionChain {n : ℕ} (x y : CutChain n) (h : compatible x y) : CutChain n where
  cuts := x.cuts ∪ y.cuts
  proper := fun c hc => (mem_union.mp hc).elim (x.proper c) (y.proper c)
  comparable := h

noncomputable def faceInf {n : ℕ} : Face n → Face n → Face n
  | none, _ => ⊥
  | some _, none => ⊥
  | some x, some y => by
    classical
    exact if h : compatible x y then ↑(unionChain x y h) else ⊥

theorem faceInf_glb {n : ℕ} (x y : Face n) : IsGLB {x, y} (faceInf x y) := by
  suffices h : (faceInf x y ≤ x ∧ faceInf x y ≤ y) ∧
      (∀ z : Face n, z ≤ x ∧ z ≤ y → z ≤ faceInf x y) by
    simpa only [IsGLB, IsGreatest, lowerBounds, upperBounds, Set.mem_ofPred_eq, Set.forall_mem_insert,
      Set.forall_mem_singleton] using h
  cases x using WithBot.recBotCoe
  · exact ⟨⟨le_rfl, bot_le⟩, fun z hz => hz.1⟩
  rename_i x
  cases y using WithBot.recBotCoe
  · exact ⟨⟨bot_le, le_rfl⟩, fun z hz => hz.2⟩
  rename_i y
  classical
  let v : Face n := if h : compatible x y then ↑(unionChain x y h) else ⊥
  change (v ≤ (x : Face n) ∧ v ≤ (y : Face n)) ∧
    (∀ z : Face n, z ≤ (x : Face n) ∧ z ≤ (y : Face n) → z ≤ v)
  unfold v
  by_cases h : compatible x y
  · rw [dite_eq_left h]
    exact ⟨⟨coe_le_coe.2 subset_union_left, coe_le_coe.2 subset_union_right⟩,
      fun z ⟨hx, hy⟩ => by
        cases z using WithBot.recBotCoe
        · exact bot_le
        exact coe_le_coe.2 (union_subset (coe_le_coe.1 hx) (coe_le_coe.1 hy))⟩
  · rw [dite_eq_right h]
    refine ⟨⟨bot_le, bot_le⟩, ?_⟩
    rintro z ⟨hx, hy⟩
    cases z using WithBot.recBotCoe
    · exact le_rfl
    rename_i z
    have hu : x.cuts ∪ y.cuts ⊆ z.cuts := union_subset (coe_le_coe.1 hx) (coe_le_coe.1 hy)
    exact (h (fun c hc d hd => z.comparable c (hu hc) d (hu hd))).elim

noncomputable instance {n : ℕ} : Lattice (Face n) :=
  Lattice.ofIsLUBofIsGLB faceSup faceInf faceSup_lub faceInf_glb

def flag {n : ℕ} (p : Equiv.Perm (Fin n)) : CutChain n where
  cuts := univ.image fun d : Rank n => prefixSet p d.1.val
  proper := by
    intro c hc
    obtain ⟨d, _, rfl⟩ := mem_image.mp hc
    rw [prefix_card p d.1.isLt]
    exact ⟨d.2, d.1.isLt⟩
  comparable := by
    intro c hc d hd
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    obtain ⟨j, _, rfl⟩ := mem_image.mp hd
    have mono : Monotone (prefixSet p) := by
      intro a b hab x hx
      rw [mem_prefix] at hx ⊢
      exact lt_of_lt_of_le hx hab
    exact (le_total i.1.val j.1.val).imp (fun h => mono h) (fun h => mono h)

theorem CutChain.eq_of_card_eq {n : ℕ} (x : CutChain n) {c d : Finset (Fin n)}
    (hc : c ∈ x.cuts) (hd : d ∈ x.cuts) (he : c.card = d.card) : c = d :=
  (x.comparable c hc d hd).elim
    (fun h => eq_of_subset_of_card_le h he.ge) (fun h => (eq_of_subset_of_card_le h he.le).symm)

theorem mem_flag {n : ℕ} (p : Equiv.Perm (Fin n)) {c : Finset (Fin n)}
    (hc : c.card < n) (hp : 0 < c.card) :
    c ∈ (flag p).cuts ↔ prefixSet p c.card = c := by
  change c ∈ univ.image _ ↔ _
  rw [mem_image]
  constructor
  · rintro ⟨d, _, hd⟩
    have he : c.card = d.1.val := hd ▸ prefix_card p d.1.isLt
    simpa only [he] using hd
  · intro h
    exact ⟨⟨⟨c.card, hc⟩, hp⟩, mem_univ _, h⟩

theorem prefix_mem_flag {n : ℕ} (p : Equiv.Perm (Fin n)) (d : Rank n) :
    prefixSet p d.1.val ∈ (flag p).cuts := mem_image_of_mem _ (mem_univ d)

def atom {n : ℕ} (p : Equiv.Perm (Fin n)) : Face n := ↑(flag p)

theorem atom_isAtom {n : ℕ} (p : Equiv.Perm (Fin n)) : IsAtom (atom p) := by
  refine ⟨WithBot.coe_ne_bot, ?_⟩
  intro a ha
  cases a using WithBot.recBotCoe
  · rfl
  rename_i a
  change (a : Face n) < (flag p : Face n) at ha
  have hs : a ≤ flag p := WithBot.coe_le_coe.1 ha.le
  have he : a = flag p := by
    apply CutChain.ext_cuts (Subset.antisymm ?_ hs)
    intro c hc
    obtain ⟨hp, hn⟩ := a.proper c hc
    let d : Rank n := ⟨⟨c.card, hn⟩, hp⟩
    have hmem := prefix_mem_flag p d
    have heq := a.eq_of_card_eq hc (hs hmem) (prefix_card p hn).symm
    exact heq.symm ▸ hmem
  exact (ha.ne (congrArg (fun y : CutChain n => (y : Face n)) he)).elim

def rank {n : ℕ} : Face n → ℤ
  | none => -1
  | some x => (n : ℤ) - 1 - x.cuts.card

theorem join_eq {n : ℕ} {A : Finset (Face n)} {x : CutChain n}
    (hA : ∃ a ∈ A, a ≠ ⊥)
    (hc : ∀ c, c ∈ x.cuts ↔ ∀ y : CutChain n, (y : Face n) ∈ A → c ∈ y.cuts) :
    A.sup id = (x : Face n) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    cases a using WithBot.recBotCoe
    · exact bot_le
    exact WithBot.coe_le_coe.2 (fun c h => (hc c).1 h _ ha)
  · have hn : A.sup id ≠ ⊥ := by
      obtain ⟨a, ha, hne⟩ := hA
      intro h
      apply hne
      exact le_bot_iff.mp (h ▸ Finset.le_sup (f := id) ha)
    cases he : A.sup id using WithBot.recBotCoe
    · exact (hn he).elim
    rename_i z
    apply WithBot.coe_le_coe.2
    intro c hc'
    apply (hc c).2
    intro y hy
    have hyz : (y : Face n) ≤ (z : Face n) := he ▸ Finset.le_sup (f := id) hy
    have hsub : y ≤ z := WithBot.coe_le_coe.1 hyz
    exact hsub hc'

theorem sup_cuts {n : ℕ} {A : Finset (Face n)} {x : CutChain n}
    (h : A.sup id = (x : Face n)) (c : Finset (Fin n)) :
    c ∈ x.cuts ↔ ∀ y : CutChain n, (y : Face n) ∈ A → c ∈ y.cuts := by
  have hn : ∃ y : CutChain n, (y : Face n) ∈ A := by
    by_contra! ha
    have hle : A.sup id ≤ ⊥ := Finset.sup_le (fun a ha' => by
      cases a using WithBot.recBotCoe
      · exact le_rfl
      exact (ha _ ha').elim)
    exact WithBot.coe_ne_bot (le_bot_iff.mp (h ▸ hle))
  obtain ⟨y, hy⟩ := hn
  classical
  let z : CutChain n := {
    cuts := y.cuts.filter fun d => ∀ a : CutChain n, (a : Face n) ∈ A → d ∈ a.cuts
    proper := fun d hd => y.proper d (mem_filter.mp hd).1
    comparable := fun d hd e he => y.comparable d (mem_filter.mp hd).1 e (mem_filter.mp he).1
  }
  have hz := join_eq (x := z) ⟨↑y, hy, WithBot.coe_ne_bot⟩ (fun d => by
    change d ∈ y.cuts.filter _ ↔ _
    rw [mem_filter]
    exact ⟨And.right, fun h => ⟨h y hy, h⟩⟩)
  have he : x = z := WithBot.coe_injective (h.symm.trans hz)
  rw [he]
  change c ∈ y.cuts.filter _ ↔ _
  rw [mem_filter]
  exact ⟨And.right, fun h => ⟨h y hy, h⟩⟩

theorem strict_of_extra_cut {n : ℕ} {B : Finset (Face n)} {x : CutChain n}
    (hle : B.sup id ≤ (x : Face n)) {c : Finset (Fin n)} (hcx : c ∉ x.cuts)
    (hB : ∀ y : CutChain n, (y : Face n) ∈ B → c ∈ y.cuts) :
    B.sup id < (x : Face n) := by
  apply lt_of_le_of_ne hle
  intro h
  exact hcx ((sup_cuts h c).2 hB)

theorem proper_lt_of_erase_lt {α : Type*} [DecidableEq α] [SemilatticeSup α] [OrderBot α]
    {A : Finset α} {x : α} (h : ∀ a ∈ A, (A.erase a).sup id < x) :
    ∀ B : Finset α, B ⊂ A → B.sup id < x := by
  intro B hB
  obtain ⟨a, ha, hBa⟩ := Finset.ssubset_iff_exists_subset_erase.mp hB
  exact lt_of_le_of_lt (Finset.sup_mono hBa) (h a ha)

end Rossi

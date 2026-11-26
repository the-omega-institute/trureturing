/- GID: D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Order.WithBot, mathlib/module/Mathlib.Order.Interval.Set.OrdConnected, mathlib/module/Mathlib.Order.Bounds.Basic, mathlib/module/Mathlib.Data.Set.Operations]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.claim; result=D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.result; claim=D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.claim
   digest: A five-element strong hyperlattice refutes Nayak et al.'s Birkhoff lattice conjecture. -/

/-
result
proof_shape: content
Direct frozen dependencies: none
escape_witness: Witness.no_glb excludes a greatest lower bound of the singleton at
  the top of the Boolean square and the whole carrier, using the two atom intervals.
admission_basis: open-problem-resolution
-/

import Mathlib.Data.Set.Operations
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.WithBot

/-! # Convex subhyperlattices can fail to form a lattice in Birkhoff order

The source is Nayak et al., arXiv:2611.10526v1, Definitions 1.1–1.3 and 1.10,
Proposition 3.1, and the conjecture in Section 5.
-/

set_option autoImplicit false

namespace D5.S0.Certificates.Algebra.NayakStrongHyperlatticeRefutation

open Set

universe u

/-- Union extension of a hyperoperation in both arguments (Definition 1.1). -/
def hyperExtend {α : Type u} (j : α → α → Set α) (A B : Set α) : Set α :=
  {w | ∃ x ∈ A, ∃ y ∈ B, w ∈ j x y}

/-- Definition 1.2 with the set extensions made explicit. -/
structure StrongJoinHyperlattice (α : Type u) where
  nonempty : Nonempty α
  meet : α → α → α
  hjoin : α → α → Set α
  hjoin_nonempty : ∀ x y, (hjoin x y).Nonempty
  meet_idem : ∀ x, meet x x = x
  hjoin_diag : ∀ x, x ∈ hjoin x x
  meet_assoc : ∀ x y z, meet (meet x y) z = meet x (meet y z)
  hjoin_assoc : ∀ x y z, hyperExtend hjoin (hjoin x y) {z} =
    hyperExtend hjoin {x} (hjoin y z)
  meet_comm : ∀ x y, meet x y = meet y x
  hjoin_comm : ∀ x y, hjoin x y = hjoin y x
  absorb_meet : ∀ x y, x ∈ Set.image2 meet {x} (hjoin x y)
  absorb_hjoin : ∀ x y, x ∈ hjoin x (meet x y)
  strong : ∀ x y, y ∈ hjoin x y → meet x y = x

namespace StrongJoinHyperlattice

variable {α : Type u} (H : StrongJoinHyperlattice α)

@[instance_reducible]
def meetOrder : PartialOrder α where
  le x y := H.meet x y = x
  le_refl := H.meet_idem
  le_trans x y z hxy hyz := by
    change H.meet x y = x at hxy
    change H.meet y z = y at hyz
    calc
      H.meet x z = H.meet (H.meet x y) z := by rw [hxy]
      _ = H.meet x (H.meet y z) := H.meet_assoc x y z
      _ = x := by rw [hyz, hxy]
  le_antisymm x y hxy hyx := by
    change H.meet x y = x at hxy
    change H.meet y x = y at hyx
    exact hxy.symm.trans ((H.meet_comm x y).trans hyx)

/-- The two descriptions of the order in Definition 1.3. -/
private theorem le_iff_mem_hjoin (x y : α) :
    letI := H.meetOrder
    x ≤ y ↔ y ∈ H.hjoin x y := by
  let _ := H.meetOrder
  constructor
  · intro h
    change H.meet x y = x at h
    have habs := H.absorb_hjoin y x
    rwa [H.meet_comm y x, h, H.hjoin_comm y x] at habs
  · exact H.strong x y

end StrongJoinHyperlattice

/-- The nonempty, operation-closed, order-convex sets of Definitions 1.3 and 1.10. -/
def CS {α : Type u} (H : StrongJoinHyperlattice α) : Type u :=
  letI := H.meetOrder
  {S : Set α // S.Nonempty ∧
    (∀ x ∈ S, ∀ y ∈ S, H.meet x y ∈ S ∧ H.hjoin x y ⊆ S) ∧ S.OrdConnected}

/-- Both original Birkhoff clauses have an element of A below an element of B. -/
def birkhoffLE {α : Type u} (H : StrongJoinHyperlattice α) (A B : CS H) : Prop :=
  letI := H.meetOrder
  IsCofinalFor A.val B.val ∧ IsCoinitialFor B.val A.val

/-- The partial order of Proposition 3.1, derived from the original axioms. -/
@[instance_reducible]
def birkhoffOrder {α : Type u} (H : StrongJoinHyperlattice α) : PartialOrder (CS H) where
  le := birkhoffLE H
  le_refl A := by
    let _ := H.meetOrder
    exact ⟨IsCofinalFor.rfl, IsCoinitialFor.rfl⟩
  le_trans A B C hAB hBC := by
    let _ := H.meetOrder
    change birkhoffLE H A B at hAB
    change birkhoffLE H B C at hBC
    exact ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩
  le_antisymm A B hAB hBA := by
    let _ := H.meetOrder
    change birkhoffLE H A B at hAB
    change birkhoffLE H B A at hBA
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨l, hl, hlx⟩ := hBA.2 hx
      obtain ⟨r, hr, hxr⟩ := hAB.1 hx
      exact B.property.2.2.out hl hr ⟨hlx, hxr⟩
    · intro hx
      obtain ⟨l, hl, hlx⟩ := hAB.2 hx
      obtain ⟨r, hr, hxr⟩ := hBA.1 hx
      exact A.property.2.2.out hl hr ⟨hlx, hxr⟩

/-- The full lattice conjecture of Section 5, at an arbitrary carrier universe. -/
def claimAt : Prop :=
  ∀ (α : Type u) (H : StrongJoinHyperlattice α),
    letI := birkhoffOrder H
    ∀ X Y : CS H,
      (∃ M, IsGLB ({X, Y} : Set (CS H)) M) ∧
      (∃ J, IsLUB ({X, Y} : Set (CS H)) J)

/-- The closed instance of the Section 5 conjecture with carriers in `Type 0`. -/
def claim : Prop := claimAt.{0}

namespace Witness

private abbrev Carrier := ULift.{u} (WithTop (Bool × Bool))

private abbrev embed (p : Bool × Bool) : Carrier.{u} := ULift.up (p : WithTop _)
private abbrev a : Carrier.{u} := embed (true, false)
private abbrev b : Carrier.{u} := embed (false, true)
private abbrev c : Carrier.{u} := embed (true, true)

private theorem a_lt_c : a.{u} < c.{u} := by
  change ((true, false) : WithTop (Bool × Bool)) < (true, true)
  exact WithTop.coe_lt_coe.mpr (lt_of_le_of_ne ⟨le_rfl, by decide⟩ (by decide))

private theorem b_lt_c : b.{u} < c.{u} := by
  change ((false, true) : WithTop (Bool × Bool)) < (true, true)
  exact WithTop.coe_lt_coe.mpr (lt_of_le_of_ne ⟨by decide, le_rfl⟩ (by decide))
private theorem a_sup_b : a.{u} ⊔ b.{u} = c.{u} := rfl

private theorem eq_c_or_top_of_c_le (v : Carrier.{u}) (h : c ≤ v) : v = c ∨ v = ⊤ := by
  rcases v with ⟨v⟩
  cases v with
  | top => exact Or.inr rfl
  | coe p =>
    apply Or.inl
    have hp : (true, true) ≤ p := WithTop.coe_le_coe.mp h
    have hp' : p ≤ (true, true) := ⟨by cases p.1 <;> decide, by cases p.2 <;> decide⟩
    have heq := le_antisymm hp' hp
    subst p
    rfl

/-- The ordinary join, together with the new top when the join is c and the inputs differ. -/
private def join (x y : Carrier.{u}) : Set Carrier.{u} :=
  {w | w = x ⊔ y ∨ (w = ⊤ ∧ x ⊔ y = c ∧ x ≠ y)}

private theorem different_iff (x y : Carrier.{u}) (hs : x ⊔ y = c) :
    x ≠ y ↔ x ≠ c ∨ y ≠ c := by
  constructor
  · intro h
    by_cases hx : x = c
    · exact Or.inr (fun hy => h (hx.trans hy.symm))
    · exact Or.inl hx
  · intro h hxy
    subst y
    have hx : x = c := by simpa only [sup_idem] using hs
    exact h.elim (fun hne => hne hx) (fun hne => hne hx)

private theorem mem_join {x y w : Carrier.{u}} :
    w ∈ join x y ↔ w = x ⊔ y ∨ (w = ⊤ ∧ x ⊔ y = c ∧ (x ≠ c ∨ y ≠ c)) := by
  change (w = x ⊔ y ∨ (w = ⊤ ∧ x ⊔ y = c ∧ x ≠ y)) ↔ _
  by_cases hs : x ⊔ y = c
  · simp only [different_iff x y hs]
  · simp [hs]

private theorem sup_mem_join (x y : Carrier.{u}) : x ⊔ y ∈ join x y :=
  mem_join.mpr (Or.inl rfl)

private theorem join_comm (x y : Carrier.{u}) : join x y = join y x := by
  ext w
  simp only [mem_join, sup_comm x y, or_comm (a := x ≠ c)]

private theorem join_self (x : Carrier.{u}) : join x x = {x} := by
  ext w
  simp [mem_join]

private theorem join_top_left (z : Carrier.{u}) : join ⊤ z = {⊤} := by
  ext w
  constructor
  · intro hw
    rcases mem_join.mp hw with h | h
    · simpa using h
    · exact h.1
  · intro hw
    exact mem_join.mpr (Or.inl (by simpa using hw))

private theorem le_of_mem_join {x y w : Carrier.{u}} (hw : w ∈ join x y) : x ≤ w := by
  rcases mem_join.mp hw with rfl | ⟨rfl, _, _⟩
  · exact le_sup_left
  · exact le_top

/-- In a left-associated triple, the extra top depends only on the total join
and whether all three inputs equal c. -/
private theorem mem_join_three (x y z w : Carrier.{u}) :
    (∃ v ∈ join x y, w ∈ join v z) ↔
      w = (x ⊔ y) ⊔ z ∨
        (w = ⊤ ∧ (x ⊔ y) ⊔ z = c ∧ (x ≠ c ∨ y ≠ c ∨ z ≠ c)) := by
  constructor
  · rintro ⟨v, hv, hw⟩
    rcases mem_join.mp hv with rfl | ⟨rfl, hxy, he⟩
    · rcases mem_join.mp hw with h | ⟨ht, hs, he⟩
      · exact Or.inl h
      · right
        refine ⟨ht, hs, ?_⟩
        rcases he with hr | hz
        · by_cases hx : x = c
          · by_cases hy : y = c
            · exact (hr (by simp [hx, hy])).elim
            · exact Or.inr (Or.inl hy)
          · exact Or.inl hx
        · exact Or.inr (Or.inr hz)
    · rw [join_top_left] at hw
      have ht : w = ⊤ := hw
      have hle : c ≤ (x ⊔ y) ⊔ z := hxy ▸ le_sup_left
      rcases eq_c_or_top_of_c_le _ hle with hs | hs
      · exact Or.inr ⟨ht, hs, he.imp_right Or.inl⟩
      · exact Or.inl (ht.trans hs.symm)
  · rintro (h | ⟨ht, hs, he⟩)
    · exact ⟨x ⊔ y, sup_mem_join x y, mem_join.mpr (Or.inl h)⟩
    · by_cases hxy : x ⊔ y = c
      · by_cases hin : x ≠ c ∨ y ≠ c
        · exact ⟨⊤, mem_join.mpr (Or.inr ⟨rfl, hxy, hin⟩),
            join_top_left z ▸ ht⟩
        · have hz : z ≠ c := by
            rcases he with hx | hy | hz
            · exact (hin (Or.inl hx)).elim
            · exact (hin (Or.inr hy)).elim
            · exact hz
          exact ⟨x ⊔ y, sup_mem_join x y, mem_join.mpr (Or.inr ⟨ht, hs, Or.inr hz⟩)⟩
      · exact ⟨x ⊔ y, sup_mem_join x y, mem_join.mpr (Or.inr ⟨ht, hs, Or.inl hxy⟩)⟩

private theorem join_assoc (x y z : Carrier.{u}) :
    hyperExtend join (join x y) {z} = hyperExtend join {x} (join y z) := by
  ext w
  simp only [hyperExtend, mem_ofPred_eq, mem_singleton_iff, exists_eq_left]
  have reorder :
      (∃ v ∈ join y z, w ∈ join x v) ↔ (∃ v ∈ join y z, w ∈ join v x) := by
    simp_rw [join_comm x _]
  rw [reorder, mem_join_three, mem_join_three, sup_comm (y ⊔ z) x, ← sup_assoc]
  tauto

/-- The certified five-element strong join hyperlattice. -/
private def hyperlattice : StrongJoinHyperlattice Carrier.{u} where
  nonempty := ⟨⊤⟩
  meet := (· ⊓ ·)
  hjoin := join
  hjoin_nonempty x y := ⟨x ⊔ y, sup_mem_join x y⟩
  meet_idem := inf_idem
  hjoin_diag x := by simpa using sup_mem_join x x
  meet_assoc := inf_assoc
  hjoin_assoc := join_assoc
  meet_comm := inf_comm
  hjoin_comm := join_comm
  absorb_meet x y := by
    simpa only [inf_sup_self] using
      mem_image2_of_mem (f := (· ⊓ ·)) (mem_singleton x) (sup_mem_join x y)
  absorb_hjoin x y := by
    simpa only [sup_inf_self] using sup_mem_join x (x ⊓ y)
  strong x y hy := inf_eq_left.mpr (le_of_mem_join hy)

private theorem induced_le_iff {x y : Carrier.{u}} :
    @LE.le _ hyperlattice.{u}.meetOrder.toLE x y ↔ x ≤ y :=
  inf_eq_left

private abbrev Convex := CS hyperlattice.{u}

private def singleC : Convex.{u} := by
  refine ⟨{c}, ⟨c, rfl⟩, ?_, ?_⟩
  · intro x hx y hy
    have hx' : x = c := hx
    have hy' : y = c := hy
    subst x
    subst y
    constructor
    · exact hyperlattice.{u}.meet_idem c.{u}
    · change join c.{u} c.{u} ⊆ {c.{u}}
      rw [join_self]
  · exact @ordConnected_singleton _ hyperlattice.{u}.meetOrder c.{u}

private def whole : Convex.{u} := by
  refine ⟨univ, ⟨⊤, mem_univ _⟩, ?_, ?_⟩
  · exact fun _ _ _ _ => ⟨mem_univ _, subset_univ _⟩
  · exact @ordConnected_univ _ hyperlattice.{u}.meetOrder.toPreorder

private def atomInterval (d : Carrier.{u}) (hd : d < c) : Convex.{u} := by
  refine ⟨Icc ⊥ d, ⟨⊥, ⟨le_rfl, bot_le⟩⟩, ?_, ?_⟩
  · intro x hx y hy
    refine ⟨⟨bot_le, inf_le_left.trans hx.2⟩, ?_⟩
    intro w hw
    have hsup : x ⊔ y ≤ d := sup_le hx.2 hy.2
    rcases mem_join.mp hw with rfl | ⟨_, he, _⟩
    · exact ⟨bot_le, hsup⟩
    · exact ((hsup.trans_lt hd).ne he).elim
  · apply (@ordConnected_def _ hyperlattice.{u}.meetOrder.toPreorder _).2
    intro x _ y hy z hz
    exact ⟨bot_le, (induced_le_iff.mp hz.2).trans hy.2⟩

private theorem mem_atomInterval {d x : Carrier.{u}} {hd : d < c} :
    x ∈ (atomInterval d hd).val ↔ x ≤ d := by
  change (⊥ ≤ x ∧ x ≤ d) ↔ x ≤ d
  exact ⟨And.right, fun h => ⟨bot_le, h⟩⟩

private theorem interval_le_single (d : Carrier.{u}) (hd : d < c) :
    birkhoffLE hyperlattice (atomInterval d hd) singleC := by
  constructor
  · intro x hx
    exact ⟨c, rfl, induced_le_iff.mpr (le_trans (mem_atomInterval.mp hx) hd.le)⟩
  · intro y _
    exact ⟨⊥, mem_atomInterval.mpr bot_le, induced_le_iff.mpr bot_le⟩

private theorem interval_le_whole (d : Carrier.{u}) (hd : d < c) :
    birkhoffLE hyperlattice (atomInterval d hd) whole := by
  constructor
  · intro x _
    exact ⟨x, mem_univ x, induced_le_iff.mpr le_rfl⟩
  · intro y _
    exact ⟨⊥, mem_atomInterval.mpr bot_le, induced_le_iff.mpr bot_le⟩

private theorem no_glb :
    letI := birkhoffOrder hyperlattice.{u}
    ¬ ∃ M : Convex.{u}, IsGLB ({singleC, whole} : Set Convex.{u}) M := by
  let _ := birkhoffOrder hyperlattice.{u}
  rintro ⟨M, hM⟩
  have hMC : birkhoffLE hyperlattice M singleC :=
    hM.1 (show singleC ∈ ({singleC, whole} : Set Convex.{u}) by simp)
  have hMW : birkhoffLE hyperlattice M whole :=
    hM.1 (show whole ∈ ({singleC, whole} : Set Convex.{u}) by simp)
  have lower (d : Carrier.{u}) (hd : d < c) :
      atomInterval d hd ∈ lowerBounds ({singleC, whole} : Set Convex.{u}) := by
    intro s hs
    rcases mem_insert_iff.mp hs with rfl | hs
    · exact interval_le_single d hd
    · have := mem_singleton_iff.mp hs
      subst s
      exact interval_le_whole d hd
  obtain ⟨m, hm, hmle⟩ := hMW.2 (show (⊥ : Carrier.{u}) ∈ whole.val from mem_univ _)
  have hzero : (⊥ : Carrier.{u}) ∈ M.val := by
    have heq := le_antisymm (induced_le_iff.mp hmle) bot_le
    simpa only [heq] using hm
  have atom_mem (d : Carrier.{u}) (hd : d < c) : d ∈ M.val := by
    have hIM : birkhoffLE hyperlattice (atomInterval d hd) M := hM.2 (lower d hd)
    obtain ⟨v, hv, hdv⟩ := hIM.1 (mem_atomInterval.mpr (le_refl d))
    exact @OrdConnected.out _ hyperlattice.{u}.meetOrder.toPreorder M.val
      M.property.2.2 ⊥ hzero v hv d ⟨induced_le_iff.mpr bot_le, hdv⟩
  have htJoin : (⊤ : Carrier.{u}) ∈ join a b :=
    mem_join.mpr (Or.inr ⟨rfl, a_sup_b, Or.inl a_lt_c.ne⟩)
  have ht : (⊤ : Carrier.{u}) ∈ M.val :=
    (M.property.2.1 a.{u} (atom_mem a.{u} a_lt_c.{u})
      b.{u} (atom_mem b.{u} b_lt_c.{u})).2 htJoin
  obtain ⟨v, hv, htv⟩ := hMC.1 ht
  have hv' : v = c := hv
  have hc : c ∈ join (⊤ : Carrier.{u}) c :=
    (hyperlattice.le_iff_mem_hjoin ⊤ c).mp (hv' ▸ htv)
  rw [join_top_left] at hc
  exact WithTop.not_top_le_coe (a := (true, true)) (show (⊤ : Carrier.{u}) ≤ c from
    (mem_singleton_iff.mp hc) ▸ le_rfl)

end Witness

/-- The same finite countermodel lifts to every carrier universe. -/
private theorem refute : ¬ claimAt.{u} := by
  intro h
  exact Witness.no_glb (h Witness.Carrier.{u} Witness.hyperlattice.{u} _ _).1

/-- The convex subhyperlattices of a strong join hyperlattice need not form a lattice. -/
theorem result : ¬ claim := refute.{0}

end D5.S0.Certificates.Algebra.NayakStrongHyperlatticeRefutation

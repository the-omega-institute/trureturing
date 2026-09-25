/- GID: D5/S3/Combinatorics/Posets/PPartitions/Chambers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/PPartitions/Chambers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Sort]
   utility: none
   digest: Stable standardization partitions labelled P-partitions into extension chambers. -/

import D5.S3.Combinatorics.Posets.PPartitions.Definitions
import Mathlib.Data.Prod.Lex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.PPartitions

noncomputable section

universe u

variable {α : Type u} [Fintype α] [PartialOrder α]

private theorem exists_adjacent_descent {n : ℕ} (v : Fin n → ℕ) {i j : Fin n}
    (hij : i < j) (hdrop : v j < v i) :
    ∃ k : Fin (n - 1), i.val ≤ k.val ∧ k.val < j.val ∧
      v ⟨k.val + 1, by omega⟩ < v ⟨k.val, by omega⟩ := by
  by_contra h
  push Not at h
  have hstep : ∀ (k : ℕ) (hik : i.val ≤ k) (hkj : k < j.val),
      v ⟨k, hkj.trans j.isLt⟩ ≤ v ⟨k + 1, by omega⟩ := by
    intro k hik hkj
    have hkpred : k < n - 1 := by omega
    exact h ⟨k, hkpred⟩ hik hkj
  have chain : ∀ (a b : ℕ) (hia : i.val ≤ a) (hab : a ≤ b)
      (hbj : b ≤ j.val) (hbn : b < n),
      v ⟨a, hab.trans_lt hbn⟩ ≤ v ⟨b, hbn⟩ := by
    intro a b hia hab hbj hbn
    induction b generalizing a with
    | zero =>
        have : a = 0 := by omega
        subst a
        rfl
    | succ b ih =>
        by_cases ha : a = b + 1
        · subst a
          rfl
        · have hab' : a ≤ b := by omega
          exact (ih a hia hab' (by omega) (by omega)).trans (hstep b (by omega) (by omega))
  have hmono := chain i.val j.val le_rfl hij.le le_rfl j.isLt
  exact (not_le_of_gt hdrop) hmono

private def stableKey {bound : ℕ} (ω : α → ℕ) (p : PPartition ω bound) (x : α) :
    OrderDual (Fin bound) ×ₗ ℕ :=
  toLex (OrderDual.toDual (p.1 x), ω x)

private structure StablePoint (α : Type u) where
  val : α

private def stablePointEquiv : StablePoint α ≃ α where
  toFun := StablePoint.val
  invFun := StablePoint.mk
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable instance : Fintype (StablePoint α) :=
  Fintype.ofEquiv α stablePointEquiv.symm

private noncomputable def stableEquiv {bound : ℕ} (ω : α → ℕ)
    (hω : Function.Injective ω) (p : PPartition ω bound) :
    Fin (Fintype.card α) ≃ α := by
  letI : LinearOrder (StablePoint α) :=
    LinearOrder.lift' (fun x : StablePoint α => stableKey ω p x.val) fun x y h => by
      rcases x with ⟨x⟩
      rcases y with ⟨y⟩
      exact congrArg StablePoint.mk (hω (congrArg (fun z => (ofLex z).2) h))
  exact (Fintype.orderIsoFinOfCardEq (StablePoint α) (k := Fintype.card α)
    (Fintype.card_congr stablePointEquiv)).toEquiv.trans stablePointEquiv

private noncomputable def standardExtension {bound : ℕ} (ω : α → ℕ)
    (hω : Function.Injective ω) (p : PPartition ω bound) : EnumeratingExtension α := by
  refine ⟨stableEquiv ω hω p, ?_⟩
  have hsort : StrictMono (fun i => stableKey ω p (stableEquiv ω hω p i)) := by
    intro i j hij
    unfold stableEquiv
    dsimp only
    letI : LinearOrder (StablePoint α) :=
      LinearOrder.lift' (fun x : StablePoint α => stableKey ω p x.val) fun x y h => by
        rcases x with ⟨x⟩
        rcases y with ⟨y⟩
        exact congrArg StablePoint.mk (hω (congrArg (fun z => (ofLex z).2) h))
    exact (Fintype.orderIsoFinOfCardEq (StablePoint α) (k := Fintype.card α)
      (Fintype.card_congr stablePointEquiv)).strictMono hij
  intro x y hxy
  have hkey : stableKey ω p x < stableKey ω p y := by
    change toLex (OrderDual.toDual (p.1 x), ω x) <
      toLex (OrderDual.toDual (p.1 y), ω y)
    rw [Prod.Lex.toLex_lt_toLex]
    have hp := p.2.1 hxy.le
    by_cases heq : p.1 x = p.1 y
    · right
      refine ⟨congrArg OrderDual.toDual heq, ?_⟩
      have hne : ω x ≠ ω y := fun h => ne_of_lt hxy (hω h)
      have hnlt : ¬ω y < ω x := fun h => ne_of_lt (p.2.2 hxy h) heq.symm
      omega
    · left
      exact (show p.1 y < p.1 x from lt_of_le_of_ne hp fun h => heq h.symm)
  by_contra hpos
  have hrev : (stableEquiv ω hω p).symm y ≤ (stableEquiv ω hω p).symm x :=
    le_of_not_gt hpos
  have hkeyrev := hsort.monotone hrev
  simp only [Equiv.apply_symm_apply] at hkeyrev
  exact (not_le_of_gt hkey) hkeyrev

private def chamberOfPartition {bound : ℕ} (ω : α → ℕ) (hω : Function.Injective ω)
    (p : PPartition ω bound) : Chamber ω (standardExtension ω hω p) bound := by
  let e := standardExtension ω hω p
  have hsort : StrictMono (fun i => stableKey ω p (stableEquiv ω hω p i)) := by
    intro i j hij
    unfold stableEquiv
    dsimp only
    letI : LinearOrder (StablePoint α) :=
      LinearOrder.lift' (fun x : StablePoint α => stableKey ω p x.val) fun x y h => by
        rcases x with ⟨x⟩
        rcases y with ⟨y⟩
        exact congrArg StablePoint.mk (hω (congrArg (fun z => (ofLex z).2) h))
    exact (Fintype.orderIsoFinOfCardEq (StablePoint α) (k := Fintype.card α)
      (Fintype.card_congr stablePointEquiv)).strictMono hij
  refine ⟨fun i => p.1 (e i), ?_, ?_⟩
  · intro i j hij
    have hkey : stableKey ω p (e i) ≤ stableKey ω p (e j) := by
      exact hsort.monotone hij
    exact Prod.Lex.monotone_fst _ _ hkey
  · intro i hi
    have hkey : stableKey ω p (e ⟨i.val, by omega⟩) <
        stableKey ω p (e ⟨i.val + 1, by omega⟩) := by
      exact hsort (Fin.mk_lt_mk.mpr (by omega))
    change toLex (_, _) < toLex (_, _) at hkey
    rw [Prod.Lex.toLex_lt_toLex] at hkey
    rcases hkey with hvalue | hlabel
    · exact hvalue
    · exact False.elim ((not_lt_of_ge hi.le) hlabel.2)

private def partitionOfChamber {bound : ℕ} (ω : α → ℕ) (hω : Function.Injective ω)
    (c : Σ e : EnumeratingExtension α, Chamber ω e bound) : PPartition ω bound := by
  let e := c.1
  let s := c.2.1
  refine ⟨fun x => s (e.1.symm x), ?_⟩
  constructor
  · intro x y hxy
    rcases hxy.eq_or_lt with rfl | hxy
    · rfl
    · exact c.2.2.1 (e.2 hxy).le
  · intro x y hxy hlabel
    have hpos : e.1.symm x < e.1.symm y := e.2 hxy
    obtain ⟨k, hk0, hk1, hkdesc⟩ :=
      exists_adjacent_descent (fun i => ω (e i)) hpos (by simpa using hlabel)
    have hstrict := c.2.2.2 k hkdesc
    have hleft : s ⟨k.val, by omega⟩ ≤ s (e.1.symm x) :=
      c.2.2.1 hk0
    have hright : s (e.1.symm y) ≤ s ⟨k.val + 1, by omega⟩ := by
      apply c.2.2.1
      exact Fin.mk_le_mk.mpr (Nat.succ_le_iff.mpr hk1)
    exact lt_of_le_of_lt hright (lt_of_lt_of_le hstrict hleft)

/-- Stable sorting by decreasing partition value and then increasing label is an
equivalence between labelled `P`-partitions and the disjoint union of all chambers. -/
noncomputable def chamberEquiv {bound : ℕ} (ω : α → ℕ) (hω : Function.Injective ω) :
    PPartition ω bound ≃ Σ e : EnumeratingExtension α, Chamber ω e bound where
  toFun p := ⟨standardExtension ω hω p, chamberOfPartition ω hω p⟩
  invFun := partitionOfChamber ω hω
  left_inv p := by
    apply Subtype.ext
    funext x
    simp [partitionOfChamber, chamberOfPartition]
  right_inv c := by
    rcases c with ⟨e, s⟩
    have heq : standardExtension ω hω (partitionOfChamber ω hω ⟨e, s⟩) = e := by
      let p := partitionOfChamber ω hω ⟨e, s⟩
      have he_key_strict : StrictMono (fun i => stableKey ω p (e i)) := by
        intro i j hij
        simp only [stableKey, p, partitionOfChamber, Equiv.symm_apply_apply]
        change toLex (OrderDual.toDual (s.1 i), ω (e i)) <
          toLex (OrderDual.toDual (s.1 j), ω (e j))
        rw [Prod.Lex.toLex_lt_toLex]
        have hs : s.1 j ≤ s.1 i := s.2.1 hij.le
        by_cases hv : s.1 i = s.1 j
        · right
          refine ⟨congrArg OrderDual.toDual hv, ?_⟩
          have hnlt : ¬ω (e j) < ω (e i) := by
            intro hdrop
            obtain ⟨k, hk0, hk1, hkdesc⟩ :=
              exists_adjacent_descent (fun r => ω (e r)) hij hdrop
            have hstrict := s.2.2 k hkdesc
            have hleft : s.1 ⟨k.val, by omega⟩ ≤ s.1 i := s.2.1 hk0
            have hright : s.1 j ≤ s.1 ⟨k.val + 1, by omega⟩ := by
              apply s.2.1
              exact Fin.mk_le_mk.mpr (Nat.succ_le_iff.mpr hk1)
            exact ne_of_lt (lt_of_le_of_lt hright (lt_of_lt_of_le hstrict hleft)) hv.symm
          have hne : ω (e i) ≠ ω (e j) := fun h =>
            ne_of_lt hij (e.1.injective (hω h))
          omega
        · left
          exact (show s.1 j < s.1 i from lt_of_le_of_ne hs fun h => hv h.symm)
      have hkey_inj : Function.Injective (stableKey ω p) := fun x y h =>
        hω (congrArg (fun z => (ofLex z).2) h)
      let keys := Finset.univ.image (stableKey ω p)
      have hcard : keys.card = Fintype.card α := by
        rw [Finset.card_image_of_injective _ hkey_inj]
        simp
      have he_fun := Finset.orderEmbOfFin_unique (s := keys) hcard
        (fun i => Finset.mem_image.mpr ⟨e i, Finset.mem_univ _, rfl⟩) he_key_strict
      have hstd_fun := Finset.orderEmbOfFin_unique (s := keys) hcard
        (fun i => Finset.mem_image.mpr
          ⟨(standardExtension ω hω p) i, Finset.mem_univ _, rfl⟩)
        (by
          intro i j hij
          change stableKey ω p (stableEquiv ω hω p i) <
            stableKey ω p (stableEquiv ω hω p j)
          unfold stableEquiv
          letI : LinearOrder (StablePoint α) :=
            LinearOrder.lift' (fun x : StablePoint α => stableKey ω p x.val) fun x y h => by
              rcases x with ⟨x⟩
              rcases y with ⟨y⟩
              exact congrArg StablePoint.mk (hω (congrArg (fun z => (ofLex z).2) h))
          exact (Fintype.orderIsoFinOfCardEq (StablePoint α) (k := Fintype.card α)
            (Fintype.card_congr stablePointEquiv)).strictMono hij)
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply hkey_inj
      exact congrFun (hstd_fun.trans he_fun.symm) i
    let c : Σ ext : EnumeratingExtension α, Chamber ω ext bound :=
      ⟨standardExtension ω hω (partitionOfChamber ω hω ⟨e, s⟩),
        chamberOfPartition ω hω (partitionOfChamber ω hω ⟨e, s⟩)⟩
    let d : Σ ext : EnumeratingExtension α, Chamber ω ext bound := ⟨e, s⟩
    change c = d
    have hcd : c.1 = d.1 := heq
    have hs : ∀ i, c.2.1 i = d.2.1 i := by
      intro i
      change s.1 (e.1.symm ((standardExtension ω hω
        (partitionOfChamber ω hω ⟨e, s⟩)) i)) = s.1 i
      rw [show (standardExtension ω hω (partitionOfChamber ω hω ⟨e, s⟩)) i = e i
        from congrArg (fun ext : EnumeratingExtension α => ext i) heq]
      simp
    rcases c with ⟨ec, sc⟩
    rcases d with ⟨ed, sd⟩
    dsimp at hcd hs
    subst ed
    congr 1
    apply Subtype.ext
    funext i
    exact hs i

end

end D5.S3.Combinatorics.Posets.PPartitions

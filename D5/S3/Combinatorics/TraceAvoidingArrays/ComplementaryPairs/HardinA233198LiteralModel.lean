/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal eight-colour rectangle and its pair and row representations. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Literal fibres and canonical first-use labels on the contained-edge graph.
The fibreEquiv and labelledEquiv constructions support all five counting theorems.
The finite colour identities normalize these constructions; no finite agreement
is substituted for the all-height counting statements. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233198PairFibres

open scoped BigOperators

abbrev Cell (n : ℕ) := Fin n × Fin 4

/-- The natural row-major rank, with width exactly four. -/
def rank {n : ℕ} (v : Cell n) : ℕ := 4 * v.1.val + v.2.val

/-- The three directed representatives of the undirected contained bonds. -/
def Edge {n : ℕ} (v w : Cell n) : Prop :=
  (v.1 = w.1 ∧ w.2.val = v.2.val + 1) ∨
  (w.1.val = v.1.val + 1 ∧ v.2 = w.2) ∨
  (w.1.val = v.1.val + 1 ∧ v.2.val = w.2.val + 1)

def Bond (x y : Fin 8) : Prop := x ≠ y ∧ x.val + y.val ≠ 7

def Earlier {V : Type*} (r : V → ℕ) (f : V → Fin 8) (v : V)
    (c : Fin 8) : Prop := ∃ w, r w < r v ∧ f w = c

/-- These are the three literal prerequisite clauses, with no surjectivity demand. -/
def Normal {V : Type*} (r : V → ℕ) (f : V → Fin 8) : Prop :=
  ∀ v,
    (2 ≤ (f v).val ∧ (f v).val ≤ 6 → Earlier r f v 1) ∧
    (f v = 3 ∨ f v = 4 ∨ f v = 5 → Earlier r f v 2) ∧
    (f v = 4 → Earlier r f v 3)

/-- The anchor is an existential in order to reject height zero. -/
def Legal {n : ℕ} (f : Cell n → Fin 8) : Prop :=
  (∃ h : 0 < n, f (⟨0, h⟩, 0) = 0) ∧ Normal rank f ∧
    ∀ v w, Edge v w → Bond (f v) (f w)

noncomputable def a (n : ℕ) : ℕ := Nat.card {f : Cell n → Fin 8 // Legal f}

/-- The coefficient at zero is explicitly zero; no empty-array count is used. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

noncomputable def numerator : PowerSeries ℚ :=
  PowerSeries.X * (11 - 1760 * PowerSeries.X + 99328 * PowerSeries.X ^ 2 -
    3080192 * PowerSeries.X ^ 3 + 55050240 * PowerSeries.X ^ 4 -
    369098752 * PowerSeries.X ^ 5)

noncomputable def denominator : PowerSeries ℚ :=
  (1 - 16 * PowerSeries.X) *
    (1 - 192 * PowerSeries.X + 10240 * PowerSeries.X ^ 2 -
      278528 * PowerSeries.X ^ 3 + 4194304 * PowerSeries.X ^ 4)

/-- Pair r consists of r and 7-r. -/
abbrev pair := HardinA233196Strip.beta

def lower (c : Fin 4) : Fin 8 := ⟨c.val, by omega⟩

def colour (c : Fin 4) (b : Bool) : Fin 8 :=
  if b then ⟨7 - c.val, by omega⟩ else lower c

def orientation (x : Fin 8) : Bool := decide (4 ≤ x.val)

/-- First means that there is no strictly earlier vertex in the same pair. -/
def First {V : Type*} (r : V → ℕ) (p : V → Fin 4) (v : V) : Prop :=
  ∀ w, r w < r v → p w ≠ p v

/-- Pairs two and three need an earlier pair one; pair three also needs pair two. -/
def PairNormal {V : Type*} (r : V → ℕ) (p : V → Fin 4) : Prop :=
  ∀ v,
    (2 ≤ (p v).val → ∃ w, r w < r v ∧ p w = 1) ∧
    (p v = 3 → ∃ w, r w < r v ∧ p w = 2)

/-- A pair map has the same edges as the literal array and the same first-use order. -/
def PairLegal {n : ℕ} (p : Cell n → Fin 4) : Prop :=
  (∃ h : 0 < n, p (⟨0, h⟩, 0) = 0) ∧ PairNormal rank p ∧
    ∀ v w, Edge v w → p v ≠ p w

/-- The non-first vertices carry the independent binary choices. -/
def Free {n : ℕ} (p : Cell n → Fin 4) := {v : Cell n // ¬ First rank p v}

noncomputable def fibreCount {n : ℕ} (p : Cell n → Fin 4) : ℕ :=
  Nat.card {f : Cell n → Fin 8 // Legal f ∧ (fun v => pair (f v)) = p}

/-! Ordinary labelled colourings of the identical contained-edge graph. -/

def Proper {q n : ℕ} (f : Cell n → Fin q) : Prop :=
  ∀ v w, Edge v w → f v ≠ f w

noncomputable def ordinaryCount (q n : ℕ) : ℕ :=
  Nat.card {f : Cell n → Fin q // Proper f}

noncomputable def ordinarySeries (q : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (ordinaryCount q n : ℚ)

def RowOK {q : ℕ} (r : Fin 4 → Fin q) : Prop :=
  ∀ j : Fin 3, r j.castSucc ≠ r j.succ

instance {q : ℕ} (r : Fin 4 → Fin q) : Decidable (RowOK r) :=
  inferInstanceAs (Decidable (∀ j : Fin 3, r j.castSucc ≠ r j.succ))

abbrev Row (q : ℕ) := {r : Fin 4 → Fin q // RowOK r}

def compatible {q : ℕ} (r s : Row q) : Prop :=
  (∀ j : Fin 4, r.1 j ≠ s.1 j) ∧
    ∀ j : Fin 3, r.1 j.succ ≠ s.1 j.castSucc

instance {q : ℕ} (r s : Row q) : Decidable (compatible r s) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

private theorem pair_colour : ∀ c b, pair (colour c b) = c := by decide

private theorem colour_orientation : ∀ x, colour (pair x) (orientation x) = x := by decide

private theorem orientation_colour : ∀ c b, orientation (colour c b) = b := by decide

private theorem pair_lower : ∀ c, pair (lower c) = c := by decide

private theorem bond_iff : ∀ x y, Bond x y ↔ pair x ≠ pair y := by
  intro x y
  exact HardinA233196Strip.colour_bond_iff x y

private def FirstLower {V : Type*} (r : V → ℕ) (f : V → Fin 8) : Prop :=
  ∀ v, pair (f v) ≠ 0 → First r (fun w => pair (f w)) v → f v = lower (pair (f v))

private theorem normal_first_lower {V : Type*} {r : V → ℕ} {f : V → Fin 8}
    (hf : Normal r f) : FirstLower r f := by
  intro v hn hfirst
  have h := hf v
  generalize hx : f v = x at *
  fin_cases x
  · exact False.elim (hn rfl)
  · rfl
  · rfl
  · rfl
  · obtain ⟨w, hw, he⟩ := h.2.2 rfl
    exact False.elim (hfirst w hw (by change pair (f w) = pair (f v); rw [he, hx]; rfl))
  · obtain ⟨w, hw, he⟩ := h.2.1 (Or.inr (Or.inr rfl))
    exact False.elim (hfirst w hw (by change pair (f w) = pair (f v); rw [he, hx]; rfl))
  · obtain ⟨w, hw, he⟩ := h.1 (by decide)
    exact False.elim (hfirst w hw (by change pair (f w) = pair (f v); rw [he, hx]; rfl))
  · exact False.elim (hn rfl)

private theorem normal_pair {V : Type*} {r : V → ℕ} {f : V → Fin 8}
    (hf : Normal r f) : PairNormal r (fun v => pair (f v)) := by
  intro v
  have h := hf v
  constructor
  · intro hv
    have hx : 2 ≤ (f v).val ∧ (f v).val ≤ 6 :=
      (by decide : ∀ x : Fin 8, 2 ≤ (pair x).val → 2 ≤ x.val ∧ x.val ≤ 6) (f v) hv
    obtain ⟨w, hw, he⟩ := h.1 hx
    exact ⟨w, hw, by change pair (f w) = 1; rw [he]; rfl⟩
  · intro hv
    have hx : f v = 3 ∨ f v = 4 ∨ f v = 5 :=
      (by decide : ∀ x : Fin 8, pair x = 3 → x = 3 ∨ x = 4 ∨ x = 5) (f v) hv
    obtain ⟨w, hw, he⟩ := h.2.1 hx
    exact ⟨w, hw, by change pair (f w) = 2; rw [he]; rfl⟩

private theorem low_representative {V : Type*} {r : V → ℕ} {f : V → Fin 8}
    (hf : FirstLower r f) {c : Fin 4} (hc : c ≠ 0) {v : V}
    (hv : pair (f v) = c) : ∃ w, r w ≤ r v ∧ f w = lower c := by
  classical
  have hex : ∃ t : ℕ, ∃ w, r w = t ∧ pair (f w) = c := ⟨r v, v, rfl, hv⟩
  obtain ⟨w, hw, hwp⟩ := Nat.find_spec hex
  have hfirst : First r (fun z => pair (f z)) w := by
    intro z hz he
    have hlt : r z < Nat.find hex := by omega
    exact Nat.find_min hex hlt ⟨z, rfl, he.trans hwp⟩
  refine ⟨w, ?_, ?_⟩
  · have := Nat.find_min' hex (show ∃ z, r z = r v ∧ pair (f z) = c from ⟨v, rfl, hv⟩)
    omega
  · simpa [hwp] using hf w (by simpa [hwp] using hc) hfirst

private theorem low_before {V : Type*} {r : V → ℕ} {f : V → Fin 8}
    (hf : FirstLower r f) {c : Fin 4} (hc : c ≠ 0) {v : V}
    (hv : ∃ w, r w < r v ∧ pair (f w) = c) : Earlier r f v (lower c) := by
  obtain ⟨w, hw, hp⟩ := hv
  obtain ⟨z, hz, he⟩ := low_representative hf hc hp
  exact ⟨z, lt_of_le_of_lt hz hw, he⟩

private theorem normal_of_pair {V : Type*} {r : V → ℕ} {f : V → Fin 8}
    (hp : PairNormal r (fun v => pair (f v))) (hl : FirstLower r f) : Normal r f := by
  intro v
  have h := hp v
  have repeated (c : Fin 4) (hc : c ≠ 0) (he : pair (f v) = c)
      (hne : f v ≠ lower c) : Earlier r f v (lower c) := by
    classical
    have hn : ¬ First r (fun w => pair (f w)) v := by
      intro hfirst
      exact hne (by simpa [he] using hl v (by simpa [he] using hc) hfirst)
    simp only [First, not_forall, not_not] at hn
    obtain ⟨w, hw, hpair⟩ := hn
    exact low_before hl hc ⟨w, hw, hpair.trans he⟩
  constructor
  · intro hx
    by_cases he : f v = 6
    · exact repeated 1 (by decide) (by rw [he]; rfl) (by rw [he]; decide)
    · have hpv : 2 ≤ (pair (f v)).val :=
        (by decide : ∀ x : Fin 8, (2 ≤ x.val ∧ x.val ≤ 6) → x ≠ 6 →
          2 ≤ (pair x).val) (f v) hx he
      exact low_before hl (by decide : (1 : Fin 4) ≠ 0) (h.1 hpv)
  constructor
  · intro hx
    by_cases he : f v = 5
    · exact repeated 2 (by decide) (by rw [he]; rfl) (by rw [he]; decide)
    · have hpv : pair (f v) = 3 := by
        rcases hx with hx | hx | hx <;> simp_all [pair, HardinA233196Strip.beta]
      exact low_before hl (by decide : (2 : Fin 4) ≠ 0) (h.2 hpv)
  · intro he
    exact repeated 3 (by decide) (by rw [he]; rfl) (by rw [he]; decide)

private theorem rank_injective {n : ℕ} : Function.Injective (@rank n) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have hj := j.isLt
  have hl := l.isLt
  have hi : i.val = k.val := by simp only [rank] at h; omega
  have hje : j.val = l.val := by simp only [rank] at h; omega
  exact Prod.ext (Fin.ext hi) (Fin.ext hje)

private theorem first_anchor {n : ℕ} (p : Cell n → Fin 4) (h : 0 < n) :
    First rank p (⟨0, h⟩, 0) := by
  intro w hw
  simp [rank] at hw

private theorem first_zero_eq_anchor {n : ℕ} {f : Cell n → Fin 8} (hf : Legal f)
    {v : Cell n} (hp : pair (f v) = 0) (hv : First rank (fun w => pair (f w)) v) :
    f v = 0 := by
  obtain ⟨hn, ha⟩ := hf.1
  have hr : rank v = 0 := by
    by_contra hne
    have hlt : rank (⟨0, hn⟩, 0) < rank v := by
      simpa [rank] using Nat.pos_of_ne_zero hne
    exact hv (⟨0, hn⟩, 0) hlt (by
      change pair (f (⟨0, hn⟩, 0)) = pair (f v)
      rw [ha, hp]; rfl)
  have he : v = (⟨0, hn⟩, 0) := rank_injective (by simpa [rank] using hr)
  simpa [he] using ha

private theorem legal_first {n : ℕ} {f : Cell n → Fin 8} (hf : Legal f)
    {v : Cell n} (hv : First rank (fun w => pair (f w)) v) :
    f v = lower (pair (f v)) := by
  by_cases hp : pair (f v) = 0
  · have he := first_zero_eq_anchor hf hp hv
    simp [he, pair, HardinA233196Strip.beta, lower]
  · exact normal_first_lower hf.2.1 v hp hv

private theorem pair_legal {n : ℕ} {f : Cell n → Fin 8} (hf : Legal f) :
    PairLegal (fun v => pair (f v)) := by
  refine ⟨?_, normal_pair hf.2.1, ?_⟩
  · obtain ⟨hn, ha⟩ := hf.1
    exact ⟨hn, by change pair (f (⟨0, hn⟩, 0)) = 0; rw [ha]; rfl⟩
  · intro v w he
    exact (bond_iff _ _).mp (hf.2.2 v w he)

private noncomputable def lift {n : ℕ} (p : Cell n → Fin 4) (b : Free p → Bool)
    (v : Cell n) : Fin 8 := by
  classical
  exact if h : First rank p v then lower (p v) else colour (p v) (b ⟨v, h⟩)

private theorem pair_lift {n : ℕ} (p : Cell n → Fin 4) (b : Free p → Bool) :
    (fun v => pair (lift p b v)) = p := by
  classical
  funext v
  unfold lift
  split_ifs <;> simp only [pair_lower, pair_colour]

private theorem lift_legal {n : ℕ} {p : Cell n → Fin 4} (hp : PairLegal p)
    (b : Free p → Bool) : Legal (lift p b) := by
  classical
  refine ⟨?_, normal_of_pair ?_ ?_, ?_⟩
  · obtain ⟨hn, ha⟩ := hp.1
    exact ⟨hn, by simp [lift, first_anchor, ha, lower]⟩
  · simpa only [pair_lift] using hp.2.1
  · intro v _ hv
    have hv' : First rank p v := by simpa only [pair_lift] using hv
    simp only [lift, dite_eq_left hv', pair_lower]
  · intro v w he
    apply (bond_iff _ _).mpr
    simpa only [show ∀ z, pair (lift p b z) = p z from congrFun (pair_lift p b)]
      using hp.2.2 v w he

private noncomputable def fibreEquiv {n : ℕ} {p : Cell n → Fin 4} (hp : PairLegal p) :
    {f : Cell n → Fin 8 // Legal f ∧ (fun v => pair (f v)) = p} ≃ (Free p → Bool) where
  toFun f v := orientation (f.1 v.1)
  invFun b := ⟨lift p b, lift_legal hp b, pair_lift p b⟩
  left_inv f := by
    classical
    apply Subtype.ext
    funext v
    change lift p (fun w => orientation (f.1 w.1)) v = f.1 v
    unfold lift
    split_ifs with hv
    · have hv' : First rank (fun w => pair (f.1 w)) v := by rw [f.2.2]; exact hv
      have he := legal_first f.2.1 hv'
      simpa only [congrFun f.2.2 v] using he.symm
    · simpa only [← congrFun f.2.2 v] using colour_orientation (f.1 v)
  right_inv b := by
    classical
    funext v
    change orientation (lift p b v.1) = b v
    simp only [lift, dite_eq_right v.2, orientation_colour]
    exact congrArg b (Subtype.ext rfl)

/-- Every legal pair map has exactly two choices at every non-first cell. -/
theorem literal_fibre_card {n : ℕ} {p : Cell n → Fin 4} (hp : PairLegal p) :
    fibreCount p = 2 ^ Nat.card (Free p) := by
  classical
  letI : Fintype (Free p) := by unfold Free; infer_instance
  unfold fibreCount
  rw [Nat.card_congr (fibreEquiv hp)]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]

private noncomputable def firstRangeEquiv {n : ℕ} (p : Cell n → Fin 4) :
    {v : Cell n // First rank p v} ≃ Set.range p :=
  Equiv.ofBijective (fun v => ⟨p v.1, v.1, rfl⟩) (by
    constructor
    · intro v w he
      have hp : p v.1 = p w.1 := congrArg Subtype.val he
      apply Subtype.ext
      apply rank_injective
      rcases lt_trichotomy (rank v.1) (rank w.1) with h | h | h
      · exact False.elim (w.2 v.1 h hp)
      · exact h
      · exact False.elim (v.2 w.1 h hp.symm)
    · rintro ⟨c, v, hv⟩
      classical
      have hex : ∃ t : ℕ, ∃ w, rank w = t ∧ p w = c := ⟨rank v, v, rfl, hv⟩
      obtain ⟨w, hw, hp⟩ := Nat.find_spec hex
      have hf : First rank p w := by
        intro z hz he
        apply Nat.find_min hex (show rank z < Nat.find hex by omega)
        exact ⟨z, rfl, he.trans hp⟩
      exact ⟨⟨w, hf⟩, Subtype.ext hp⟩)

private theorem free_card {n : ℕ} (p : Cell n → Fin 4) :
    Nat.card (Free p) = 4 * n - Nat.card (Set.range p) := by
  classical
  have he := Fintype.card_congr (firstRangeEquiv p)
  simp only [Free, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_prod, Fintype.card_fin]
  rw [he, Nat.mul_comm n 4]

/-- One colour is forced per used pair, including the anchored pair zero. -/
theorem literal_fibre_power {n : ℕ} {p : Cell n → Fin 4} (hp : PairLegal p) :
    fibreCount p = 2 ^ (4 * n - Nat.card (Set.range p)) := by
  rw [literal_fibre_card hp, free_card]

private noncomputable def allFibresEquiv (n : ℕ) :
    {f : Cell n → Fin 8 // Legal f} ≃
      Σ p : {p : Cell n → Fin 4 // PairLegal p},
        {f : Cell n → Fin 8 // Legal f ∧ (fun v => pair (f v)) = p.1} :=
  (Equiv.sigmaSubtypeFiberEquiv
    (fun f : {f : Cell n → Fin 8 // Legal f} => fun v => pair (f.1 v))
    PairLegal (fun f => pair_legal f.2)).symm.trans
      (Equiv.sigmaCongrRight fun p => Equiv.subtypeSubtypeEquivSubtypeInter
        Legal (fun f => (fun v => pair (f v)) = p.1))

section

attribute [local instance] Classical.propDecidable

/-- Summing the disjoint literal fibres retains every absent-pair case. -/
theorem literal_count_by_pairs (n : ℕ) :
    a n = ∑ p : {p : Cell n → Fin 4 // PairLegal p},
      2 ^ (4 * n - Nat.card (Set.range p.1)) := by
  classical
  unfold a
  rw [Nat.card_congr (allFibresEquiv n), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  exact literal_fibre_power p.2

end

private noncomputable def firstKey {n : ℕ} (f : Cell n → Fin 4) (c : Fin 4) : ℕ := by
  classical
  exact if h : ∃ t, ∃ v, rank v = t ∧ f v = c then Nat.find h else 4 * n + c.val

private theorem rank_lt {n : ℕ} (v : Cell n) : rank v < 4 * n := by
  have := v.1.isLt
  have := v.2.isLt
  unfold rank
  omega

private theorem firstKey_spec {n : ℕ} {f : Cell n → Fin 4} {c : Fin 4}
    (h : firstKey f c < 4 * n) : ∃ v, rank v = firstKey f c ∧ f v = c := by
  classical
  unfold firstKey at *
  split_ifs at * with he
  · exact Nat.find_spec he
  · omega

private theorem firstKey_le {n : ℕ} (f : Cell n → Fin 4) (v : Cell n) :
    firstKey f (f v) ≤ rank v := by
  classical
  unfold firstKey
  rw [dif_pos ⟨rank v, v, rfl, rfl⟩]
  exact Nat.find_min' _ ⟨v, rfl, rfl⟩

private theorem firstKey_injective {n : ℕ} (f : Cell n → Fin 4) :
    Function.Injective (firstKey f) := by
  classical
  intro c d he
  by_cases hc : firstKey f c < 4 * n
  · obtain ⟨v, hv, hvc⟩ := firstKey_spec hc
    obtain ⟨w, hw, hwd⟩ := firstKey_spec (he ▸ hc)
    have h := rank_injective (hv.trans (he.trans hw.symm))
    exact hvc.symm.trans ((congrArg f h).trans hwd)
  · have hd : ¬ firstKey f d < 4 * n := by simpa [← he] using hc
    have absent (x : Fin 4) (hx : ¬ firstKey f x < 4 * n) :
        ¬ ∃ t, ∃ v, rank v = t ∧ f v = x := by
      rintro ⟨t, v, hv, hfx⟩
      have hh := firstKey_le f v
      rw [hfx] at hh
      exact hx (lt_of_le_of_lt hh (rank_lt v))
    have hh : 4 * n + c.val = 4 * n + d.val := by
      simpa only [firstKey, dif_neg (absent c hc), dif_neg (absent d hd)] using he
    exact Fin.ext (by omega)

private noncomputable def keySet {n : ℕ} (f : Cell n → Fin 4) : Finset ℕ :=
  Finset.univ.image (firstKey f)

private theorem keySet_card {n : ℕ} (f : Cell n → Fin 4) : (keySet f).card = 4 := by
  classical
  simp [keySet, Finset.card_image_of_injective _ (firstKey_injective f)]

private noncomputable def indexPerm {n : ℕ} (f : Cell n → Fin 4) : Equiv.Perm (Fin 4) := by
  classical
  exact Equiv.ofBijective (fun c => ((keySet f).orderIsoOfFin (keySet_card f)).symm
    ⟨firstKey f c, by simp [keySet]⟩) (by
      have hi : Function.Injective (fun c => ((keySet f).orderIsoOfFin
          (keySet_card f)).symm ⟨firstKey f c, by simp [keySet]⟩) := by
        intro c d he
        apply firstKey_injective f
        exact congrArg Subtype.val (((keySet f).orderIsoOfFin
          (keySet_card f)).symm.injective he)
      exact ⟨hi, Finite.surjective_of_injective hi⟩)

private theorem indexPerm_lt {n : ℕ} (f : Cell n → Fin 4) (c d : Fin 4) :
    indexPerm f c < indexPerm f d ↔ firstKey f c < firstKey f d := by
  exact ((keySet f).orderIsoOfFin (keySet_card f)).symm.lt_iff_lt

private theorem normalize_legal {n : ℕ} {f : Cell n → Fin 4} (hn : 0 < n)
    (hf : Proper f) : PairLegal (fun v => indexPerm f (f v)) := by
  classical
  have before (v : Cell n) (c : Fin 4) (hc : c < indexPerm f (f v)) :
      ∃ w, rank w < rank v ∧ indexPerm f (f w) = c := by
    let d := (indexPerm f).symm c
    have hd : firstKey f d < firstKey f (f v) :=
      (indexPerm_lt f d (f v)).mp (by simpa [d] using hc)
    obtain ⟨w, hw, hfw⟩ := firstKey_spec
      (lt_trans hd (lt_of_le_of_lt (firstKey_le f v) (rank_lt v)))
    have hv := firstKey_le f v
    exact ⟨w, by omega, by simp [hfw, d]⟩
  refine ⟨⟨hn, ?_⟩, ?_, ?_⟩
  · by_contra he
    have hpos : (0 : Fin 4) < indexPerm f (f (⟨0, hn⟩, 0)) := by
      exact Fin.pos_iff_ne_zero.mpr he
    obtain ⟨w, hw, _⟩ := before (⟨0, hn⟩, 0) 0 hpos
    simp [rank] at hw
  · intro v
    constructor
    · intro hv
      change 2 ≤ (indexPerm f (f v)).val at hv
      exact before v 1 (by change 1 < (indexPerm f (f v)).val; omega)
    · intro hv
      change indexPerm f (f v) = 3 at hv
      exact before v 2 (by rw [hv]; decide)
  · intro v w he
    exact fun h => hf v w he ((indexPerm f).injective h)

private theorem pair_before {n : ℕ} {p : Cell n → Fin 4} (hp : PairLegal p)
    (v : Cell n) (c : Fin 4) (hc : c < p v) : ∃ w, rank w < rank v ∧ p w = c := by
  have h := hp.2.1 v
  fin_cases c
  · obtain ⟨hn, ha⟩ := hp.1
    refine ⟨(⟨0, hn⟩, 0), ?_, ha⟩
    have hv : rank v ≠ 0 := by
      intro he
      have heq : v = (⟨0, hn⟩, 0) := rank_injective (by simpa [rank] using he)
      rw [heq, ha] at hc
      exact (lt_irrefl _ hc)
    change 0 < rank v
    omega
  · exact h.1 (by change 1 < (p v).val at hc; omega)
  · exact h.2 (by apply Fin.ext; change 2 < (p v).val at hc; have := (p v).isLt; omega)
  · have := (p v).isLt
    change 3 < (p v).val at hc
    omega

private theorem pair_unique {n : ℕ} {p t : Cell n → Fin 4}
    (hp : PairLegal p) (ht : PairLegal t)
    (he : ∀ v w, p v = p w ↔ t v = t w) : p = t := by
  funext v
  have all : ∀ k, ∀ v : Cell n, rank v = k → p v = t v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      rcases lt_trichotomy (p v) (t v) with hlt | heq | hgt
      · obtain ⟨w, hw, htw⟩ := pair_before ht v (p v) hlt
        have hw' := ih (rank w) (by omega) w rfl
        have hpw : p w = p v := hw'.trans htw
        have htv : t w = t v := (he w v).mp hpw
        exact False.elim ((ne_of_lt hlt) (htw.symm.trans htv))
      · exact heq
      · obtain ⟨w, hw, hpw⟩ := pair_before hp v (t v) hgt
        have hw' := ih (rank w) (by omega) w rfl
        have htw : t w = t v := hw'.symm.trans hpw
        have hpv : p w = p v := (he w v).mpr htw
        exact False.elim ((ne_of_lt hgt) (hpw.symm.trans hpv))
  exact all (rank v) v rfl

private noncomputable def labelled {q n : ℕ}
    (x : Σ p : {p : Cell n → Fin 4 // PairLegal p}, Set.range p.1 ↪ Fin q) :
    {f : Cell n → Fin q // Proper f} :=
  ⟨fun v => x.2 ⟨x.1.1 v, v, rfl⟩, by
    intro v w he hh
    exact x.1.2.2.2 v w he (congrArg Subtype.val (x.2.injective hh))⟩

private theorem labelled_injective {q n : ℕ} : Function.Injective (@labelled q n) := by
  rintro ⟨⟨p, hp⟩, e⟩ ⟨⟨t, ht⟩, d⟩ he
  have hv (v : Cell n) : e ⟨p v, v, rfl⟩ = d ⟨t v, v, rfl⟩ :=
    congrFun (congrArg Subtype.val he) v
  have hpt : p = t := pair_unique hp ht (by
    intro v w
    constructor
    · intro hh
      have hh' : d ⟨t v, v, rfl⟩ = d ⟨t w, w, rfl⟩ := by
        rw [← hv v, ← hv w]
        exact congrArg e (Subtype.ext hh)
      exact congrArg (fun c : Set.range t => c.1) (d.injective hh')
    · intro hh
      have hh' : e ⟨p v, v, rfl⟩ = e ⟨p w, w, rfl⟩ := by
        rw [hv v, hv w]
        exact congrArg d (Subtype.ext hh)
      exact congrArg (fun c : Set.range p => c.1) (e.injective hh'))
  subst t
  have hed : e = d := by
    apply Function.Embedding.ext
    intro c
    rcases c with ⟨c, v, rfl⟩
    exact hv v
  subst d
  rfl

private theorem labelled_surjective {q n : ℕ} (hq : q ≤ 4) (hn : 0 < n) :
    Function.Surjective (@labelled q n) := by
  classical
  rintro ⟨f, hf⟩
  let g : Cell n → Fin 4 := fun v => Fin.castLE hq (f v)
  have hg : Proper g := by
    intro v w he hh
    exact hf v w he (Fin.ext (congrArg (fun x : Fin 4 => x.val) hh))
  let p : Cell n → Fin 4 := fun v => indexPerm g (g v)
  have hp : PairLegal p := normalize_legal hn hg
  have hker (v w : Cell n) : p v = p w ↔ f v = f w := by
    constructor
    · intro he
      have hh := (indexPerm g).injective he
      exact Fin.ext (congrArg (fun x : Fin 4 => x.val) hh)
    · intro he
      exact congrArg (fun x => indexPerm g (Fin.castLE hq x)) he
  let chooseV (c : Set.range p) : Cell n := Classical.choose c.2
  have chosen (c : Set.range p) : p (chooseV c) = c.1 := Classical.choose_spec c.2
  let e : Set.range p ↪ Fin q := {
    toFun := fun c => f (chooseV c)
    inj' := by
      intro c d he
      apply Subtype.ext
      exact (chosen c).symm.trans (((hker _ _).mpr he).trans (chosen d)) }
  refine ⟨⟨⟨p, hp⟩, e⟩, ?_⟩
  apply Subtype.ext
  funext v
  exact (hker _ _).mp (chosen ⟨p v, v, rfl⟩)

private noncomputable def labelledEquiv {q n : ℕ} (hq : q ≤ 4) (hn : 0 < n) :
    (Σ p : {p : Cell n → Fin 4 // PairLegal p}, Set.range p.1 ↪ Fin q) ≃
      {f : Cell n → Fin q // Proper f} :=
  Equiv.ofBijective labelled ⟨labelled_injective, labelled_surjective hq hn⟩

section

attribute [local instance] Classical.propDecidable

/-- Injective labels count every used-block partition, with unused labels retained. -/
theorem ordinary_count_by_pairs (q n : ℕ) (hq : q ≤ 4) (hn : 0 < n) :
    ordinaryCount q n = ∑ p : {p : Cell n → Fin 4 // PairLegal p},
      q.descFactorial (Nat.card (Set.range p.1)) := by
  classical
  unfold ordinaryCount
  rw [Nat.card_congr (labelledEquiv hq hn).symm, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]

private theorem pair_range_bounds {n : ℕ} {p : Cell n → Fin 4} (hp : PairLegal p) :
    2 ≤ Nat.card (Set.range p) ∧ Nat.card (Set.range p) ≤ 4 := by
  classical
  obtain ⟨hn, _⟩ := hp.1
  let v : Cell n := (⟨0, hn⟩, 0)
  let w : Cell n := (⟨0, hn⟩, 1)
  have hne : p v ≠ p w := hp.2.2 v w (Or.inl ⟨rfl, rfl⟩)
  letI : Nontrivial (Set.range p) := ⟨⟨⟨p v, v, rfl⟩, ⟨p w, w, rfl⟩,
    fun he => hne (congrArg Subtype.val he)⟩⟩
  constructor
  · have h := Fintype.one_lt_card (α := Set.range p)
    rw [← Nat.card_eq_fintype_card] at h
    omega
  · simpa using (Nat.card_le_card_of_injective
      (f := fun c : Set.range p => c.1) Subtype.val_injective)

/-- The literal fibre sum equals the precise weighted ordinary-colouring count. -/
theorem literal_ordinary_count (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = 16 ^ (n - 1) *
      ((ordinaryCount 4 n : ℚ) / 24 + (ordinaryCount 3 n : ℚ) / 6 +
        5 * (ordinaryCount 2 n : ℚ) / 4) := by
  classical
  rw [literal_count_by_pairs,
    ordinary_count_by_pairs 4 n (by decide) hn,
    ordinary_count_by_pairs 3 n (by decide) hn,
    ordinary_count_by_pairs 2 n (by decide) hn]
  push_cast
  have point (p : {p : Cell n → Fin 4 // PairLegal p}) :
      (2 : ℚ) ^ (4 * n - Nat.card (Set.range p.1)) =
        16 ^ (n - 1) *
          ((4 : ℕ).descFactorial (Nat.card (Set.range p.1)) / (24 : ℚ) +
            (3 : ℕ).descFactorial (Nat.card (Set.range p.1)) / (6 : ℚ) +
            5 * (2 : ℕ).descFactorial (Nat.card (Set.range p.1)) / (4 : ℚ)) := by
    obtain ⟨hlo, hhi⟩ := pair_range_bounds p.2
    have he : 4 * n - Nat.card (Set.range p.1) =
        4 * (n - 1) + (4 - Nat.card (Set.range p.1)) := by omega
    rw [he, pow_add, pow_mul]
    norm_num only [show (2 : ℚ) ^ 4 = 16 by norm_num]
    congr 1
    generalize Nat.card (Set.range p.1) = k at *
    interval_cases k <;> norm_num [Nat.descFactorial_succ]
  calc
    _ = ∑ p : {p : Cell n → Fin 4 // PairLegal p},
        16 ^ (n - 1) *
          ((4 : ℕ).descFactorial (Nat.card (Set.range p.1)) / (24 : ℚ) +
            (3 : ℕ).descFactorial (Nat.card (Set.range p.1)) / (6 : ℚ) +
            5 * (2 : ℕ).descFactorial (Nat.card (Set.range p.1)) / (4 : ℚ)) :=
      Finset.sum_congr rfl (fun p _ => point p)
    _ = _ := by
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_mul, mul_add]

end

end D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233198PairFibres

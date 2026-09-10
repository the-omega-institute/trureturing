/- GID: D5/S0/History/Spacetime/HFEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/HFEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed small hereditary finite set universe with literal set and pair codes. -/

import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.Data.Set.Finite.Powerset

set_option autoImplicit false

namespace D5.S0.History.Spacetime.HFEncoding

noncomputable section

/-- A fixed small copy of the elements of the hereditary finite set universe. -/
abbrev HF : Type := Shrink.{0} (ZFSet.vonNeumann Ordinal.omega0 : ZFSet.{0})

/-- The exact representation bridge to Mathlib's set universe. -/
def hf_equiv : HF ≃ (ZFSet.vonNeumann Ordinal.omega0 : ZFSet.{0}) :=
  (equivShrink _).symm

def toZF (a : HF) : ZFSet.{0} := (hf_equiv a).val

theorem rank_toZF (a : HF) : ZFSet.rank (toZF a) < Ordinal.omega0 :=
  ZFSet.mem_vonNeumann.mp (hf_equiv a).property

theorem toZF_injective : Function.Injective toZF :=
  fun _ _ h => hf_equiv.injective (Subtype.ext h)

def ofZF (a : ZFSet.{0}) (h : a.rank < Ordinal.omega0) : HF :=
  hf_equiv.symm ⟨a, ZFSet.mem_vonNeumann.mpr h⟩

@[simp] theorem toZF_ofZF (a : ZFSet.{0}) (h : a.rank < Ordinal.omega0) :
    toZF (ofZF a h) = a := by simp [toZF, ofZF]

def empty : HF := ofZF ∅ (by simp [Ordinal.omega0_pos])

def insert (a b : HF) : HF :=
  ofZF (Insert.insert (toZF a) (toZF b)) (by
    simpa only [ZFSet.rank_insert, max_lt_iff, Order.succ_eq_add_one] using
      And.intro (Ordinal.isSuccLimit_omega0.succ_lt (rank_toZF a)) (rank_toZF b))

@[simp] theorem toZF_empty : toZF empty = ∅ := toZF_ofZF _ _

@[simp] theorem toZF_insert (a b : HF) :
    toZF (insert a b) = Insert.insert (toZF a) (toZF b) := toZF_ofZF _ _

/-- Literal Kuratowski pairing, transported through the fixed small copy. -/
def pair (a b : HF) : HF := insert (insert a empty) (insert (insert a (insert b empty)) empty)

@[simp] theorem toZF_pair (a b : HF) :
    toZF (pair a b) = ZFSet.pair (toZF a) (toZF b) := by
  simp [pair, ZFSet.pair]

@[simp] theorem pair_inj {a b c d : HF} : pair a b = pair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h' := congrArg toZF h
    simp only [toZF_pair, ZFSet.pair_inj] at h'
    exact ⟨toZF_injective h'.1, toZF_injective h'.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Natural numbers are finite von Neumann ordinals, not hierarchy levels. -/
def natCode (n : Nat) : HF :=
  ofZF (Ordinal.toZFSet n) (by simpa using Ordinal.natCast_lt_omega0 n)

@[simp] theorem toZF_natCode (n : Nat) : toZF (natCode n) = Ordinal.toZFSet n :=
  toZF_ofZF _ _

@[simp] theorem natCode_inj {m n : Nat} : natCode m = natCode n ↔ m = n := by
  constructor
  · intro h
    have h' := Ordinal.toZFSet_injective (by simpa using congrArg toZF h)
    exact_mod_cast h'
  · exact congrArg natCode

/-- Fixed event occurrence tags. Source identifiers are separate data. -/
def eventTag (i : Fin 3) (e : HF) : HF := pair (natCode i.val) e

@[simp] theorem eventTag_inj {i j : Fin 3} {e f : HF} :
    eventTag i e = eventTag j f ↔ i = j ∧ e = f := by
  simp [eventTag, Fin.ext_iff]

def mem (a b : HF) : Prop := toZF a ∈ toZF b

@[simp] theorem mem_empty (a : HF) : ¬ mem a empty := by simp [mem]

@[simp] theorem mem_insert (a b c : HF) : mem a (insert b c) ↔ a = b ∨ mem a c := by
  simp [mem, toZF_injective.eq_iff]

@[ext] theorem hf_ext {a b : HF} (h : ∀ e, mem e a ↔ mem e b) : a = b := by
  apply toZF_injective
  apply ZFSet.ext
  intro z
  constructor <;> intro hz
  · have hr := (ZFSet.rank_lt_of_mem hz).trans (rank_toZF a)
    simpa [mem] using (h (ofZF z hr)).mp (by simpa [mem] using hz)
  · have hr := (ZFSet.rank_lt_of_mem hz).trans (rank_toZF b)
    simpa [mem] using (h (ofZF z hr)).mpr (by simpa [mem] using hz)

private theorem finite_vonNeumann_nat (n : Nat) :
    Set.Finite (ZFSet.vonNeumann (n : Ordinal.{0}) : Set ZFSet.{0}) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ZFSet.vonNeumann_add_one]
    have : Finite (𝒫 (ZFSet.vonNeumann (n : Ordinal.{0}) : Set ZFSet.{0})) :=
      ih.powerset.to_subtype
    have : Finite ((ZFSet.vonNeumann (n : Ordinal.{0})).powerset) :=
      Finite.of_equiv _ (ZFSet.powersetEquiv _).symm
    exact Set.toFinite _

theorem members_finite (a : HF) : Set.Finite {e | mem e a} := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (rank_toZF a)
  have hz : Set.Finite (toZF a : Set ZFSet.{0}) :=
    (finite_vonNeumann_nat n).subset (ZFSet.subset_vonNeumann.mpr hn.le)
  exact hz.preimage toZF_injective.injOn

/-- All members, with no enumeration order or common cardinality bound. -/
def members (a : HF) : Finset HF := (members_finite a).toFinset

@[simp] theorem mem_members {a e : HF} : e ∈ members a ↔ mem e a :=
  Set.Finite.mem_toFinset _

private def listCode : List HF → HF
  | [] => empty
  | a :: s => insert a (listCode s)

private theorem mem_listCode (e : HF) (s : List HF) : mem e (listCode s) ↔ e ∈ s := by
  induction s with
  | nil => simp [listCode]
  | cons a s ih => simp [listCode, ih]

def setCode (s : Finset HF) : HF := listCode s.toList

@[simp] theorem mem_setCode (e : HF) (s : Finset HF) : mem e (setCode s) ↔ e ∈ s := by
  simp [setCode, mem_listCode]

@[simp] theorem members_setCode (s : Finset HF) : members (setCode s) = s := by
  ext e; simp

@[simp] theorem setCode_members (a : HF) : setCode (members a) = a := by
  apply hf_ext; intro e; simp

/-- Finite sets of event names and literal HF sets have both exact round trips. -/
def finite_set_equiv : Finset HF ≃ HF where
  toFun := setCode
  invFun := members
  left_inv := members_setCode
  right_inv := setCode_members

/-- A natural code is characterized by the set-theoretic ordinal predicate. -/
def IsNatCode (c : HF) : Prop := ZFSet.IsOrdinal (toZF c)

theorem natCode_valid (n : Nat) : IsNatCode (natCode n) := by
  simpa [IsNatCode] using ZFSet.isOrdinal_toZFSet (n : Ordinal.{0})

def nat_code_equiv : Nat ≃ {c : HF // IsNatCode c} :=
  Equiv.ofBijective (fun n => ⟨natCode n, natCode_valid n⟩) ⟨
    fun _ _ h => natCode_inj.mp (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (rank_toZF c)
      refine ⟨n, Subtype.ext (toZF_injective ?_)⟩
      simpa [← hn] using hc.toZFSet_rank_eq⟩

@[simp] theorem nat_code_equiv_val (n : Nat) : (nat_code_equiv n).val = natCode n := rfl

/-- Independent structural grammar for a two-field tuple. -/
def PairCode (P Q : HF → Prop) (c : HF) : Prop :=
  ∃ a b, c = pair a b ∧ P a ∧ Q b

/-- Combining two proved representations preserves literal tuple structure. -/
def prod_code_equiv {α β : Type} {P Q : HF → Prop}
    (e : α ≃ {c // P c}) (f : β ≃ {c // Q c}) :
    α × β ≃ {c // PairCode P Q c} :=
  Equiv.ofBijective (fun v =>
    ⟨pair (e v.1).val (f v.2).val, _, _, rfl, (e v.1).property, (f v.2).property⟩) ⟨by
      intro a b h
      have hp := pair_inj.mp (congrArg Subtype.val h)
      exact Prod.ext (e.injective (Subtype.ext hp.1)) (f.injective (Subtype.ext hp.2)), by
      rintro ⟨c, a, b, rfl, ha, hb⟩
      refine ⟨(e.symm ⟨a, ha⟩, f.symm ⟨b, hb⟩), Subtype.ext ?_⟩
      simp⟩

@[simp] theorem prod_code_equiv_val {α β : Type} {P Q : HF → Prop}
    (e : α ≃ {c // P c}) (f : β ≃ {c // Q c}) (v : α × β) :
    (prod_code_equiv e f v).val = pair (e v.1).val (f v.2).val := rfl

end
end D5.S0.History.Spacetime.HFEncoding

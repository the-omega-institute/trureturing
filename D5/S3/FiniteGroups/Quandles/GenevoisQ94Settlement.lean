import D5.S3.FiniteGroups.Quandles.TaThreeInvariantRefutation

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.QuotientGroup.Defs

namespace D5.S3.FiniteGroups.Quandles.GenevoisQ94Settlement

structure Oposet (I : Type) [PartialOrder I] where
  orthogonal : I → I → Prop
  symmetric : Std.Symm orthogonal
  irreflexive : ∀ i : I, ¬ orthogonal i i
  incomparable : ∀ {i j : I}, orthogonal i j → ¬ i ≤ j ∧ ¬ j ≤ i
  downward : ∀ {i j k : I}, i ≤ j → orthogonal j k → orthogonal i k

abbrev LowerIndex {I : Type} [PartialOrder I] (k : I) := {i : I // i < k}

structure LowerAction {I : Type} [PartialOrder I] (G : I → Type)
    [∀ i, Group (G i)] (k : I) where
  onIndex : G k →* Equiv.Perm (LowerIndex k)
  onFactor : ∀ (b : G k) (i : LowerIndex k), G i.val ≃* G (onIndex b i).val
  one_action : ∀ (i : LowerIndex k) (a : G i.val),
    (⟨onIndex 1 i, onFactor 1 i a⟩ : Σ j : LowerIndex k, G j.val) = ⟨i, a⟩
  mul_action : ∀ (b c : G k) (i : LowerIndex k) (a : G i.val),
    (⟨onIndex (b * c) i, onFactor (b * c) i a⟩ : Σ j : LowerIndex k, G j.val) =
      ⟨onIndex b (onIndex c i), onFactor b (onIndex c i) (onFactor c i a)⟩

def LowerAction.apply {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] {k : I} (A : LowerAction G k) (b : G k) (i : LowerIndex k)
    (a : G i.val) : Σ j : LowerIndex k, G j.val :=
  ⟨A.onIndex b i, A.onFactor b i a⟩

def PreservesOrder {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] {k : I} (A : LowerAction G k) : Prop :=
  ∀ (b : G k) (i j : LowerIndex k), A.onIndex b i ≤ A.onIndex b j ↔ i ≤ j

def IsQuandleAction {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (A : ∀ k : I, LowerAction G k)
    (order : ∀ k : I, PreservesOrder (A k)) : Prop :=
  ∀ (i j k : I) (hij : i < j) (hjk : j < k)
      (a : G i) (b : G j) (c : G k),
    let aUnderB := (A j).apply b ⟨i, hij⟩ a
    let aUnderC := (A k).apply c ⟨i, lt_trans hij hjk⟩ a
    let bUnderC := (A k).apply c ⟨j, hjk⟩ b
    let aLeft := (A k).apply c ⟨aUnderB.1.val, lt_trans aUnderB.1.property hjk⟩ aUnderB.2
    let hij' : aUnderC.1.val < bUnderC.1.val :=
      (lt_iff_lt_of_le_iff_le' (order k c _ _) (order k c _ _)).2 hij
    let aRight := (A bUnderC.1.val).apply bUnderC.2 ⟨aUnderC.1.val, hij'⟩ aUnderC.2
    (⟨aLeft.1.val, aLeft.2⟩ : Σ l : I, G l) = ⟨aRight.1.val, aRight.2⟩

structure QuandleSystem (I : Type) [PartialOrder I] (G : I → Type)
    [∀ i, Group (G i)] where
  oposet : Oposet I
  nontrivial : ∀ i : I, Nontrivial (G i)
  action : ∀ k : I, LowerAction G k
  preservesOrder : ∀ k : I, PreservesOrder (action k)
  preservesOrthogonal : ∀ (k : I) (b : G k) (i j : LowerIndex k),
    oposet.orthogonal ((action k).onIndex b i).val ((action k).onIndex b j).val ↔
      oposet.orthogonal i.val j.val
  quandle : IsQuandleAction action preservesOrder

def relators {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) : Set (Monoid.CoprodI G) :=
  {r | ∃ (i j : I) (a : G i) (b : G j),
    let ai := Monoid.CoprodI.of a
    let bj := Monoid.CoprodI.of b
    (S.oposet.orthogonal i j ∧ r = ai * bj * (bj * ai)⁻¹) ∨
      ∃ h : i < j,
        let ba := (S.action j).apply b ⟨i, h⟩ a
        r = ai * bj * (bj * Monoid.CoprodI.of ba.2)⁻¹}

abbrev QuandleProduct {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) :=
  Monoid.CoprodI G ⧸ Subgroup.normalClosure (relators S)

def factor {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) (i : I) : G i →* QuandleProduct S :=
  (QuotientGroup.mk' (Subgroup.normalClosure (relators S))).comp Monoid.CoprodI.of

def standardParabolic {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) (J : Set I) :
    Subgroup (QuandleProduct S) :=
  Subgroup.closure {q | ∃ (j : I), j ∈ J ∧ ∃ a : G j, factor S j a = q}

def claim : Prop :=
  ∀ (I : Type) (_ : PartialOrder I) (G : I → Type) (_ : ∀ i : I, Group (G i))
    (S : QuandleSystem I G) (J L : Set I) (g h : QuandleProduct S),
    ∃ (T : Set I) (k : QuandleProduct S),
      (standardParabolic S J).map (MulAut.conj g).toMonoidHom ⊓
        (standardParabolic S L).map (MulAut.conj h).toMonoidHom =
          (standardParabolic S T).map (MulAut.conj k).toMonoidHom

end D5.S3.FiniteGroups.Quandles.GenevoisQ94Settlement

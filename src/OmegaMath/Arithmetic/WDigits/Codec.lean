module
prelude

public import OmegaMath.Arithmetic.Euclidean.Division
public import OmegaMath.Arithmetic.WDigits

/-!
Omega original.

The finite greedy W-digit encoder. Lists store zero-based W positions in
strictly decreasing order, with a gap of at least two between positions.
-/

noncomputable section
@[expose] public section

namespace Omega.Arithmetic.WDigits

/-- The sum of the weights at all occupied W positions. -/
def decode (digits : NatList) : Nat :=
  NatList.rec .zero (fun index _ tail => (wValue index).add tail) digits

/-- All occupied positions are below `bound`, with gaps of at least two. -/
def LegalBelow (bound : Nat) (digits : NatList) : Prop :=
  NatList.rec (motive := fun _ => Nat → Prop) (fun _ => True)
    (fun index _ legalTail cap => And (Nat.lt index cap) (legalTail index.pred)) digits bound

private theorem legalBelow_weaken {a b : Nat} (h : Nat.le a b) (digits : NatList) :
    LegalBelow a digits → LegalBelow b digits :=
  NatList.rec (motive := fun digits => LegalBelow a digits → LegalBelow b digits)
    (fun _ => True.intro)
    (fun index _ _ hds => And.intro (lt_of_lt_of_le (a := index) hds.left h) hds.right)
    digits

private theorem wValue_succ (i : Nat) :
    Eq (wValue i.succ) ((wValue i).add (wValue i.pred)) :=
  Nat.rec (motive := fun n => Eq (wValue n.succ) ((wValue n).add (wValue n.pred))) Eq.refl
    (fun n _ => (wValue_add_two n).trans (Nat.add_comm (wValue n) (wValue n.succ))) i

private theorem wValue_mono {a b : Nat} (h : Nat.le a b) : Nat.le (wValue a) (wValue b) :=
  (Nat.rec (motive := fun b => ∀ a, Nat.le a b → Nat.le (wValue a) (wValue b))
    (fun a => Nat.rec (motive := fun a => Nat.le a .zero → Nat.le (wValue a) (wValue .zero))
      (fun _ => Nat.le.refl _) (fun _ _ h => False.elim h) a)
    (fun b ih a h => (le_or_lt a b).elim
      (fun hab => Nat.le_trans (ih a hab) (le_of_lt (wValue_lt_succ b)))
      (fun hba => Eq.subst (fun i => Nat.le (wValue i) (wValue b.succ))
        (Nat.le_antisymm h hba).symm (Nat.le.refl _))) b) a h

/-- A legal word supported below position `bound` has value below its weight. -/
theorem decode_lt_wValue (bound : Nat) (digits : NatList) (h : LegalBelow bound digits) :
    Nat.lt (decode digits) (wValue bound) :=
  (NatList.rec (motive := fun ds => ∀ k, LegalBelow k ds → Nat.lt (decode ds) (wValue k))
    (fun k _ => Nat.le_trans (Nat.le.refl .one) (wValue_mono (Nat.zero_le k)))
    (fun i rest ih _ legal =>
      have tail := ih i.pred legal.right
      have step := add_lt_add_left tail (wValue i)
      Nat.le_trans (Eq.subst (Nat.lt (decode (.cons i rest))) (wValue_succ i).symm step)
        (wValue_mono legal.left)) digits) bound h

private def atMost (a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => .true)
    (fun _ prev => fun b => Nat.rec .false (fun b _ => prev b) b) a b

private theorem atMost_cases (a b : Nat) (P : Bool → Prop)
    (fits : Nat.le a b → P .true) (exceeds : Nat.lt b a → P .false) :
    P (atMost a b) :=
  (Nat.rec (motive := fun a => ∀ b (P : Bool → Prop),
      (Nat.le a b → P .true) → (Nat.lt b a → P .false) → P (atMost a b))
    (fun b _ fits _ => fits (Nat.zero_le b))
    (fun a ih b => Nat.rec (motive := fun b => ∀ (P : Bool → Prop),
        (Nat.le a.succ b → P .true) → (Nat.lt b a.succ → P .false) → P (atMost a.succ b))
      (fun _ _ exceeds => exceeds (Nat.zero_le a))
      (fun b _ P fits exceeds => ih b P fits exceeds) b) a) b P fits exceeds

private theorem add_sub_of_le {a b : Nat} (h : Nat.le a b) : Eq (a.add (b.sub a)) b :=
  (Nat.rec (motive := fun a => ∀ b, Nat.le a b → Eq (a.add (b.sub a)) b)
    (fun b _ => Nat.zero_add b)
    (fun a ih b => Nat.rec (motive := fun b => Nat.le a.succ b → Eq (a.succ.add (b.sub a.succ)) b)
      (fun h => False.elim h)
      (fun b _ hab => (congrArg (Nat.add a.succ) (Nat.succ_sub_succ_eq_sub b a)).trans
        ((Nat.succ_add a (b.sub a)).trans (congrArg Nat.succ (ih b hab)))) b) a) b h

private theorem lt_of_add_lt_add_left {a b c : Nat} (h : Nat.lt (c.add a) (c.add b)) : Nat.lt a b :=
  (le_or_lt b a).elim
    (fun hba => False.elim (lt_irrefl _ (lt_of_lt_of_le h (Nat.add_le_add_left hba c))))
    (fun hab => hab)

private structure EncoderPair where
  current : Nat → NatList
  previous : Nat → NatList

private def encoderPair (bound : Nat) : EncoderPair :=
  Nat.rec ⟨fun _ => .nil, fun _ => .nil⟩ (fun i pair =>
    ⟨fun n => Bool.rec (pair.current n)
      (.cons i (pair.previous (n.sub (wValue i)))) (atMost (wValue i) n), pair.current⟩) bound

private def CorrectBelow (bound : Nat) (encode : Nat → NatList) : Prop :=
  ∀ n, Nat.lt n (wValue bound) →
    And (LegalBelow bound (encode n)) (Eq (decode (encode n)) n)

private theorem encoderPair_correct (bound : Nat) :
    And (CorrectBelow bound (encoderPair bound).current)
      (CorrectBelow bound.pred (encoderPair bound).previous) :=
  let base : CorrectBelow .zero (fun _ => .nil) := fun n hn =>
    And.intro True.intro ((Nat.le_antisymm (Nat.le_of_succ_le_succ hn) (Nat.zero_le n)).symm)
  Nat.rec (motive := fun k => And (CorrectBelow k (encoderPair k).current)
      (CorrectBelow k.pred (encoderPair k).previous))
    (And.intro base base)
    (fun i ih => And.intro
      (fun n hn =>
        let pair := encoderPair i
        let weight := wValue i
        let rest := n.sub weight
        let choose := fun b => Bool.rec (motive := fun _ => NatList)
          (pair.current n) (.cons i (pair.previous rest)) b
        atMost_cases weight n
          (fun b => And (LegalBelow i.succ (choose b)) (Eq (decode (choose b)) n))
          (fun hw =>
            have split := add_sub_of_le hw
            have remainderBound : Nat.lt rest (wValue i.pred) :=
              lt_of_add_lt_add_left (c := weight)
                (Eq.subst (Nat.lt (weight.add rest)) (wValue_succ i)
                  (Eq.subst (fun a => Nat.lt a (wValue i.succ)) split.symm hn))
            have old := ih.right rest remainderBound
            have legal : LegalBelow i.succ (.cons i (pair.previous rest)) :=
              And.intro (Nat.le.refl i.succ) old.left
            show And (LegalBelow i.succ (.cons i (pair.previous rest)))
                (Eq (decode (.cons i (pair.previous rest))) n) from
              And.intro legal ((congrArg (Nat.add weight) old.right).trans split))
          (fun small =>
            have old := ih.left n small
            show And (LegalBelow i.succ (pair.current n)) (Eq (decode (pair.current n)) n) from
              And.intro (legalBelow_weaken (Nat.le.step (Nat.le.refl i)) (pair.current n) old.left)
                old.right)) ih.left) bound

/-- The occupied positions of a canonical W word decrease with gaps of at least two. -/
def IsCanonical (digits : NatList) : Prop :=
  NatList.rec True (fun index tail _ => LegalBelow index.pred tail) digits

private theorem legalBelow_canonical (bound : Nat) (digits : NatList) :
    LegalBelow bound digits → IsCanonical digits :=
  NatList.rec (motive := fun ds => LegalBelow bound ds → IsCanonical ds)
    (fun h => h) (fun _ _ _ h => h.right) digits

private theorem weight_le_decode_cons (index : Nat) (tail : NatList) :
    Nat.le (wValue index) (decode (.cons index tail)) :=
  Nat.add_le_add_left (Nat.zero_le (decode tail)) (wValue index)

private theorem decode_cons_pos (index : Nat) (tail : NatList) :
    Nat.lt .zero (decode (.cons index tail)) :=
  Nat.le_trans (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le index)) (succ_le_wValue index))
    (weight_le_decode_cons index tail)

private theorem decode_cons_lt_of_head_lt {i j : Nat} {left right : NatList}
    (h : Nat.lt i j) (hl : IsCanonical (.cons i left)) :
    Nat.lt (decode (.cons i left)) (decode (.cons j right)) :=
  lt_of_lt_of_le (decode_lt_wValue j (.cons i left)
    (show LegalBelow j (.cons i left) from And.intro h hl)) (weight_le_decode_cons j right)

/-- Two canonical W words with the same value have identical occupied positions. -/
theorem decode_injective (left right : NatList) (hl : IsCanonical left) (hr : IsCanonical right)
    (h : Eq (decode left) (decode right)) : Eq left right :=
  (NatList.rec (motive := fun left => ∀ right, IsCanonical left → IsCanonical right →
      Eq (decode left) (decode right) → Eq left right)
    (fun right => NatList.rec (motive := fun right => IsCanonical .nil → IsCanonical right →
        Eq (decode .nil) (decode right) → Eq NatList.nil right)
      (fun _ _ _ => Eq.refl)
      (fun j ys _ _ _ h => False.elim (ne_of_lt (decode_cons_pos j ys) h)) right)
    (fun i xs ih right => NatList.rec (motive := fun right =>
        IsCanonical (.cons i xs) → IsCanonical right →
          Eq (decode (.cons i xs)) (decode right) → Eq (NatList.cons i xs) right)
      (fun _ _ h => False.elim (ne_of_lt (decode_cons_pos i xs) h.symm))
      (fun j ys _ hx hy h =>
        (le_or_lt i j).elim
          (fun hij => (le_or_lt j i).elim
            (fun hji =>
              let sameHead : ∀ k, Eq i k → IsCanonical (.cons k ys) →
                  Eq (decode (.cons i xs)) (decode (.cons k ys)) → Eq (NatList.cons i xs) (.cons k ys) :=
                fun _ e => Eq.rec (motive := fun k _ => IsCanonical (.cons k ys) →
                    Eq (decode (.cons i xs)) (decode (.cons k ys)) → Eq (NatList.cons i xs) (NatList.cons k ys))
                  (fun hy h => congrArg (NatList.cons i)
                    (ih ys (legalBelow_canonical i.pred xs hx) (legalBelow_canonical i.pred ys hy)
                      (Nat.add_left_cancel (a := wValue i) h))) e
              sameHead j (Nat.le_antisymm hij hji) hy h)
            (fun hji => False.elim (ne_of_lt (decode_cons_lt_of_head_lt (i := i) (j := j) (left := xs) (right := ys) hji hx) h)))
          (fun hij => False.elim (ne_of_lt (decode_cons_lt_of_head_lt (i := j) (j := i) (left := ys) (right := xs) hij hy) h.symm))) right)
    left) right hl hr h

end Omega.Arithmetic.WDigits
end

namespace Omega.Arithmetic.WDigits

/-- The occupied zero-based W positions of `n`, largest first. -/
public def encode (n : Nat) : NatList := (encoderPair n).current n

public theorem encode_legal (n : Nat) : LegalBelow n (encode n) :=
  ((encoderPair_correct n).left n (succ_le_wValue n)).left

public theorem decode_encode (n : Nat) : Eq (decode (encode n)) n :=
  ((encoderPair_correct n).left n (succ_le_wValue n)).right

public theorem encode_isCanonical (n : Nat) : IsCanonical (encode n) :=
  legalBelow_canonical n (encode n) (encode_legal n)

public theorem encode_decode (digits : NatList) (h : IsCanonical digits) :
    Eq (encode (decode digits)) digits :=
  decode_injective (encode (decode digits)) digits (encode_isCanonical (decode digits)) h
    (decode_encode (decode digits))

end Omega.Arithmetic.WDigits

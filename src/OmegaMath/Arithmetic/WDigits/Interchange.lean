module
prelude

public import OmegaMath.Arithmetic.WDigits.Codec

/-!
Omega original.

Faithful encodings of natural numbers transport words through their common
value. Both directions and the preservation of predicates follow from the
inverse laws of the decoders.
-/

noncomputable section
@[expose] public section

namespace Omega.Arithmetic.WDigits

structure NumberEncoding (Word : Type u) where
  decode : Word → Nat
  encode : Nat → Word

def Bijective {A : Type u} {B : Type v} (f : A → B) : Prop :=
  And (∀ a b, Eq (f a) (f b) → Eq a b) (∀ b, Exists fun a => Eq (f a) b)

namespace NumberEncoding
def Faithful {Word : Type u} (encoding : NumberEncoding Word) : Prop :=
  And (∀ w, Eq (encoding.encode (encoding.decode w)) w)
    (∀ n, Eq (encoding.decode (encoding.encode n)) n)


def transport {A : Type u} {B : Type v} (source : NumberEncoding A)
    (destination : NumberEncoding B) (w : A) : B :=
  destination.encode (source.decode w)

theorem decode_bijective {Word : Type u} (encoding : NumberEncoding Word) (h : encoding.Faithful) :
    Bijective encoding.decode :=
  And.intro
    (fun a b hEq => (h.left a).symm.trans
      ((congrArg encoding.encode hEq).trans (h.left b)))
    (fun n => Exists.intro (encoding.encode n) (h.right n))

theorem transport_decode {A : Type u} {B : Type v} (source : NumberEncoding A)
    (destination : NumberEncoding B) (h : destination.Faithful) (w : A) :
    Eq (destination.decode (source.transport destination w)) (source.decode w) :=
  h.right (source.decode w)

theorem transport_bijective {A : Type u} {B : Type v} (source : NumberEncoding A)
    (destination : NumberEncoding B) (hs : source.Faithful) (hd : destination.Faithful) : Bijective (source.transport destination) :=
  And.intro
    (fun a b h => (source.decode_bijective hs).left a b
      ((source.transport_decode destination hd a).symm.trans
        ((congrArg destination.decode h).trans (source.transport_decode destination hd b))))
    (fun b => Exists.intro (destination.transport source b)
      ((congrArg destination.encode (destination.transport_decode source hs b)).trans
        (hd.left b)))

theorem transport_predicate {A : Type u} {B : Type v} (source : NumberEncoding A)
    (destination : NumberEncoding B) (hd : destination.Faithful) (predicate : Nat → Prop) (w : A) :
    Iff (predicate (source.decode w)) (predicate (destination.decode (source.transport destination w))) :=
  Iff.intro (Eq.subst predicate (source.transport_decode destination hd w).symm)
    (Eq.subst predicate (source.transport_decode destination hd w))

end NumberEncoding

/-- Decoding is bijective from the canonical lists to the natural numbers. -/
theorem decode_canonical_bijective :
    And (∀ a b, IsCanonical a → IsCanonical b → Eq (decode a) (decode b) → Eq a b)
      (∀ n, Exists fun w => And (IsCanonical w) (Eq (decode w) n)) :=
  And.intro decode_injective (fun n => Exists.intro (encode n)
    (And.intro (encode_isCanonical n) (decode_encode n)))

end Omega.Arithmetic.WDigits

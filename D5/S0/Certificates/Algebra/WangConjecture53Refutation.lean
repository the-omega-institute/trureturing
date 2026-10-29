/- GID: D5/S0/Certificates/Algebra/WangConjecture53Refutation
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/WangConjecture53Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Defs, mathlib/module/Mathlib.GroupTheory.Congruence.Defs, mathlib/module/Mathlib.Data.ENat.Lattice]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Algebra/WangConjecture53Refutation.claim; result=D5/S0/Certificates/Algebra/WangConjecture53Refutation.result; claim=D5/S0/Certificates/Algebra/WangConjecture53Refutation.claim
   digest: A six-element ordinary rational semigroup algebra refutes Wang's Conjecture 5.3. -/

/- admission_basis: open-problem-resolution (issue #23871)
   Private helpers are consumed by the designated refutation result.
   No contracted semigroup algebra is used. -/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Lcm
import Mathlib.Tactic

namespace D5.S0.Certificates.Algebra.WangConjecture53Refutation

noncomputable section

/-- Index n denotes the positive multiple (n+1)a, without adjoining an identity. -/
def positiveMultiple {S : Type*} [Add S] (a : S) : ℕ → S
  | 0 => a
  | n + 1 => positiveMultiple a n + a

/-- The positive cyclic subsemigroup, including no artificial zeroth multiple. -/
def cyclic {S : Type*} [Add S] (a : S) : Set S := Set.range (positiveMultiple a)

/-- The source's cyclic idempotent specification. -/
def IsCyclicIdempotent {S : Type*} [Add S] (a e : S) : Prop :=
  e ∈ cyclic a ∧ e + e = e

/-- Choose the cyclic idempotent; the fallback is irrelevant whenever one exists. -/
def cyclicIdempotent {S : Type*} [Add S] (a : S) : S :=
  if h : ∃ e, IsCyclicIdempotent a e then h.choose else a

/-- Being a group with an identity in the positive cyclic subsemigroup itself. -/
def CyclicIsGroup {S : Type*} [Add S] (a : S) : Prop :=
  ∃ e ∈ cyclic a, (∀ x ∈ cyclic a, e + x = x) ∧
    ∀ x ∈ cyclic a, ∃ y ∈ cyclic a, x + y = e

/-- Least positive eventual shift of the positive multiples: the cyclic period. -/
def period {S : Type*} [Add S] (a : S) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ k, ∀ m, k ≤ m →
    positiveMultiple a (m + n) = positiveMultiple a m}

/-- LCM of cyclic periods, rather than cyclic indices or sizes. -/
def semigroupExponent (S : Type*) [Add S] [Finite S] : ℕ := by
  letI := Fintype.ofFinite S
  exact Finset.univ.lcm (period (S := S))

/-- The paper's root-count definition; encard also distinguishes infinite root sets. -/
def Splitting (S K : Type*) [Add S] [Finite S] [Field K] : Prop :=
  {z : K | z ^ semigroupExponent S = 1}.encard = semigroupExponent S

/-- Both source admissibility alternatives, with no characteristic restriction in (i). -/
def Admissible (S K : Type*) [Add S] [Finite S] [Field K] : Prop :=
  Splitting S K ∨ ∃ p k : ℕ, p.Prime ∧ CharP K p ∧ semigroupExponent S = p ^ k

/-- The ordinary semigroup-algebra factor; every semigroup label is retained. -/
def factor {S K : Type*} [AddCommSemigroup S] [Field K] (s : S) (a : K) :
    AddMonoidAlgebra K S :=
  AddMonoidAlgebra.single s 1 - AddMonoidAlgebra.single (cyclicIdempotent s) a

/-- Positive products do not presume that a general semigroup algebra has a unit.
The empty branch is unused for positive lengths; zero is included separately in d. -/
def factorProduct {S K : Type*} [AddCommSemigroup S] [Field K] :
    List S → (ℕ → K) → AddMonoidAlgebra K S
  | [], _ => 0
  | [s], c => factor s (c 0)
  | s :: t :: l, c => factor s (c 0) * factorProduct (t :: l) (fun i => c (i+1))

/-- Independent nonzero coefficients at every position; extending a finite tuple by
ones gives exactly the finite-tuple quantifier in Definition 2.1. -/
def GoodSequence {S K : Type*} [AddCommSemigroup S] [Field K] (l : List S) : Prop :=
  ∀ c : ℕ → K, (∀ i, c i ≠ 0) → factorProduct l c ≠ 0

/-- Supremum of admissible finite lengths in ENat. Infinity means unboundedness,
not a finite sequence or an asserted infinite product. Adding zero changes no supremum. -/
def algebraicD (S K : Type*) [AddCommSemigroup S] [Field K] : ℕ∞ :=
  ⨆ (l : List S) (_ : GoodSequence (K := K) l), (l.length : ℕ∞)

/-- Principal ideal membership, with the element itself even without an identity. -/
def Below {S : Type*} [Add S] (x a : S) : Prop := x = a ∨ ∃ c, x = a + c

/-- Green H is equality of principal ideals. -/
def Green {S : Type*} [Add S] (a b : S) : Prop := ∀ x, Below x a ↔ Below x b

private theorem below_trans {S : Type*} [AddSemigroup S] {x a b : S}
    (h : Below x a) (g : Below a b) : Below x b := by
  rcases h with rfl | ⟨c, rfl⟩
  · exact g
  · rcases g with rfl | ⟨d, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
    · exact Or.inr ⟨d+c, add_assoc _ _ _⟩

private theorem green_add_right {S : Type*} [AddCommSemigroup S] {a b : S}
    (h : Green a b) (c : S) : Green (a+c) (b+c) := by
  have hab : Below a b := (h a).mp (Or.inl rfl)
  have hba : Below b a := (h b).mpr (Or.inl rfl)
  have step {x y : S} (hxy : Below x y) : Below (x+c) (y+c) := by
    rcases hxy with rfl | ⟨d, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨d, by ac_rfl⟩
  intro x
  exact ⟨fun hx => below_trans hx (step hab), fun hx => below_trans hx (step hba)⟩

/-- The actual Green congruence, not a numerical proxy. -/
def greenCon (S : Type*) [AddCommSemigroup S] : AddCon S where
  r := Green
  iseqv := ⟨fun _ _ => Iff.rfl, fun h x => (h x).symm,
    fun h g x => (h x).trans (g x)⟩
  add' := by
    intro a b c d hab hcd
    have h₁ := green_add_right hab c
    have h₂ := green_add_right hcd b
    simpa only [add_comm c b, add_comm d b] using
      (show Green (a+c) (d+b) from fun x => (h₁ x).trans (h₂ x))

/-- Canonical quotient S/H. -/
def GreenQuotient (S : Type*) [AddCommSemigroup S] := (greenCon S).Quotient

/-- A sequence sum with the source's empty-sum convention: the empty sequence
sums to an identity only when that identity already exists in the semigroup. -/
def SequenceSum {S : Type*} [AddSemigroup S] : List S → S → Prop
  | [], a => ∀ x : S, a + x = x ∧ x + a = x
  | x :: l, a => l.foldl (· + ·) x = a

/-- Proper subsequences include the empty one. Enumerating unordered sequences
as lists preserves all submultisets and their sums in a commutative semigroup. -/
def IrreducibleAt {S : Type*} [AddSemigroup S] (l : List S) (a : S) : Prop :=
  SequenceSum l a ∧ ∀ u, u.Sublist l → u.length < l.length → ¬ SequenceSum u a

/-- Relative Davenport constant: supremum of irreducible lengths at the given sum. -/
def relativeD {S : Type*} [AddSemigroup S] (a : S) : ℕ∞ :=
  ⨆ (l : List S) (_ : IrreducibleAt l a), (l.length : ℕ∞)

/-- The H-class as a subtype of the actual carrier. -/
def HClass {S : Type*} [Add S] (a : S) := {x : S // Green x a}

/-- Actual translations on H_a realized by an element of S. Equal functions
are identified; no identity is adjoined and the carrier is allowed to be empty. -/
def Gamma {S : Type*} [Add S] (a : S) :=
  {f : HClass a → HClass a // ∃ c : S, ∀ x, (f x).val = c + x.val}

instance gammaAdd {S : Type*} [AddCommSemigroup S] (a : S) : Add (Gamma a) where
  add f g := ⟨f.val ∘ g.val, by
    rcases f.property with ⟨c, hc⟩
    rcases g.property with ⟨d, hd⟩
    exact ⟨c+d, fun x => by simp only [Function.comp_apply, hc, hd, add_assoc]⟩⟩

instance gammaAddCommSemigroup {S : Type*} [AddCommSemigroup S] (a : S) :
    AddCommSemigroup (Gamma a) where
  add_assoc f g h := by apply Subtype.ext; rfl
  add_comm f g := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rcases f.property with ⟨c, hc⟩
    rcases g.property with ⟨d, hd⟩
    change (f.val (g.val x)).val = (g.val (f.val x)).val
    rw [hc, hd, hd, hc]
    ac_rfl

/-- Epsilon detects the whole positive cyclic group property, not just idempotence. -/
def epsilon {S : Type*} [Add S] (a : S) : ℕ∞ := if CyclicIsGroup a then 0 else 1

/-- The exact source right side, with the actual quotient and translation semigroup. -/
def rightSide (S K : Type*) [AddCommSemigroup S] [Field K] : ℕ∞ :=
  ⨆ a : S, epsilon a * relativeD ((greenCon S).toQuotient a) + algebraicD (Gamma a) K

/-- Wang arXiv:2509.18724v1 Conjecture 5.3, over all finite commutative
semigroups and fields, preserving the splitting/characteristic disjunction. -/
def claim : Prop :=
  ∀ (S : Type) [AddCommSemigroup S] [Finite S] (K : Type) [Field K],
    Admissible S K → algebraicD S K = rightSide S K

/-- Six independent basis labels: (b,n), b in {0,1}, n in {0,1,2}. -/
structure Model where
  bit : Fin 2
  level : Fin 3
  deriving DecidableEq, Fintype

/-- Union in the first coordinate and addition truncated at two in the second. -/
def modelAdd (x y : Model) : Model :=
  ⟨max x.bit y.bit, ⟨min 2 (x.level.val + y.level.val), by omega⟩⟩

instance modelAddCommMonoid : AddCommMonoid Model where
  add := modelAdd
  zero := ⟨0,0⟩
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_zero := by decide
  nsmul := nsmulRec

end
end D5.S0.Certificates.Algebra.WangConjecture53Refutation

/- GID: D5/S3/Combinatorics/CayleyHosts/DoubleStarHostDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleyHosts/DoubleStarHostDefs
   mirror-E: none(waiver:fokam-souop-bitjoka-conjecture-twenty-seven-statement-definition)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Cayley, mathlib/module/Mathlib.Data.Fintype.Card, mathlib/module/Mathlib.Order.Lattice.Nat]
   utility: none
   digest: Fokam Souop and Bitjoka's Conjecture 27 on the least abelian Cayley host of a double star. -/

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CayleyHosts.DoubleStarHostDefs

/-! Fixed public statement: R. Fokam Souop and L. Bitjoka, *Induced Embeddings of Graphs into
    Abelian Cayley Graphs*, arXiv:2609.01486v2, Section 10.1: "Conjecture 27. η(D_{q,q}) = 5q
    for all q ≥ 2." Definition 1: an injection f : V(G) → Γ is an induced embedding into
    Cay(Γ, S) if for all u ≠ v, f(u) ∼ f(v) in the host if and only if uv ∈ E(G); η(G) is the
    least |Γ| over finite abelian groups Γ admitting one. Connection sets are symmetric and omit
    0; `SimpleGraph.addCayley s` joins u ≠ v when v − u or u − v lies in s, so as s ranges over
    all subsets of Γ these graphs are exactly the Cayley graphs with symmetric connection sets
    omitting 0. Every finite abelian group is isomorphic to one in `Type`. D_{q,q} is the double
    star: two adjacent centres, each with q pendant leaves. -/

open SimpleGraph

/-- The double star `D_{q,q}`: vertex `(side, none)` is the centre of that side and
`(side, some i)` is its `i`-th leaf. -/
def doubleStar (q : ℕ) : SimpleGraph (Bool × Option (Fin q)) :=
  SimpleGraph.fromRel fun x y =>
    (x.2 = none ∧ y.2 = none) ∨ (x.1 = y.1 ∧ x.2 = none ∧ y.2 ≠ none)

/-- `f` is an induced embedding of `G` into the Cayley graph of `Γ` with connection set `s`. -/
def IsInducedEmbedding {V Γ : Type*} [AddCommGroup Γ] (G : SimpleGraph V) (s : Set Γ)
    (f : V → Γ) : Prop :=
  Function.Injective f ∧ ∀ u v, u ≠ v → ((addCayley s).Adj (f u) (f v) ↔ G.Adj u v)

/-- `η(G)`: the least order of a finite abelian group admitting an induced embedding of `G`
into one of its Cayley graphs. -/
noncomputable def eta {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N | ∃ (Γ : Type) (_ : AddCommGroup Γ) (_ : Fintype Γ), Fintype.card Γ = N ∧
    ∃ (s : Set Γ) (f : V → Γ), IsInducedEmbedding G s f}

/-- Conjecture 27. -/
def claim : Prop := ∀ q : ℕ, 2 ≤ q → eta (doubleStar q) = 5 * q

end D5.S3.Combinatorics.CayleyHosts.DoubleStarHostDefs

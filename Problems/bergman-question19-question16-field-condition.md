---
slug: bergman-question19-question16-field-condition
bibkey: bergman2014eggert
doi: 10.1090/conm/609/12101
url: https://arxiv.org/abs/1206.0326v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result
---

# Bergman's Question 19: the field condition in Question 16

## Problem

Bergman, *Thoughts on Eggert's Conjecture*, arXiv:1206.0326v2,
Contemporary Mathematics 609 (2014), 1–17, Question 16, asks:

> Let R be a finite-dimensional nilpotent commutative algebra over an
> algebraically closed field F, let V be a subspace of R, and let n be a
> positive integer such that every nonzero element of V has nonzero n-th
> power. Must dim R ≥ n dim V?

Question 19 explicitly asks whether, for Question 16, algebraic closedness
can be dropped or weakened to “F is infinite”. The target is only this
field-condition branch, retaining associativity and commutativity. Convention 2
assumes associativity unless explicitly stated otherwise; an identity is not
required. All dimensions and all linear structures use the same F.

The affirmative infinite-field assertion is quantified over every infinite
field F, every finite-dimensional F-vector space R with an actual F-bilinear
multiplication satisfying associativity and commutativity, every linear
subspace V, and every positive integer n. Common global nilpotence and
nonvanishing n-th powers of every nonzero vector in V are its antecedents.
The conclusion is n dim_F V ≤ dim_F R.

| Source clause | Lean counterpart |
| --- | --- |
| every infinite field | `F : Type`, `[Field F]`, `[Infinite F]` |
| F-vector space | `R : Type`, `[AddCommGroup R]`, `[Module F R]` |
| finite dimension | `[FiniteDimensional F R]` |
| F-bilinear multiplication | `μ : R →ₗ[F] R →ₗ[F] R` |
| associativity | `∀ x y z, μ (μ x y) z = μ x (μ y z)` |
| commutativity | `∀ x y, μ x y = μ y x` |
| common nilpotence | `CommonNilpotent μ` |
| actual F-linear subspace | `V : Submodule F R` |
| positive exponent | `n : ℕ`, `0 < n` |
| all nonzero vectors | `∀ v ∈ V, v ≠ 0 → … ≠ 0` |
| n-th power without identity | `(List.replicate (n-1) v).foldr (fun x y => μ x y) v` |
| dimension bound | `n * Module.finrank F V ≤ Module.finrank F R` |
| exact negation | closed `claim : Prop`, designated `result : ¬ claim` |

`CommonNilpotent μ` means that there is k in N such that every list xs of
length k and every terminal z have `xs.foldr μ z = 0`. The terminal is an
additional factor: the common vanishing length is k+1, always positive.
Under associativity this is global algebra nilpotence, equivalently the
corresponding product-span being zero. It is stronger than pointwise
nilpotence. For positive n the displayed power has exactly n factors;
for n=1 it is v. The closed assertion uses ordinary small carriers, including
arbitrary infinite carriers. The counterexample lies in these universes and
also refutes the unrestricted mathematical assertion.

## Motivation

Over an infinite field a quadratic form can have no nonzero zero while
taking values in a one-dimensional space. An annihilating scalar output
then separates the dimension of a subspace from the nonvanishing of its
squares. A counterexample over Q resolves both the arbitrary-field and
infinite-field alternatives as one field-condition question.

## Gap

The algebraically closed hypothesis can force nontrivial zeros of a
homogeneous polynomial system; infinitude alone does not. The rational construction
realizes this obstruction with associative multiplication and common global
nilpotence, with nonvanishing verified for every nonzero vector of V.

## Route

Set F=Q and R=(Q × Q) × Q with the ordinary coordinatewise vector-space
structure and the bilinear multiplication

$$
\mu(((a,b),c),((d,e),f))=((0,0),ad+be).
$$

`LinearMap.mk₂` includes proofs of additivity and scalar linearity in each
argument. All outputs lie in the last coordinate, and that line annihilates
R. Thus both bracketings of every triple product are zero, proving
associativity and common nilpotence with k=2 (three factors). Symmetry gives
commutativity. None of these laws is assumed as a countermodel hypothesis.

Let V be the range of the linear injection `(a,b) ↦ ((a,b),0)`. It is a
Submodule of dimension two. For every vector in V,

$$
\mu(((a,b),0),((a,b),0))=((0,0),a^2+b^2).
$$

The pinned Mathlib result `mul_self_add_mul_self_eq_zero` over Q shows that a
vanishing square forces a=b=0. Therefore all nonzero vectors in V have
nonzero square. `LinearMap.finrank_range_of_inj` and product-space finrank
give dim_Q V=2 and dim_Q R=3. At n=2 the claimed conclusion is 4≤3.

Bergman's Example 20, author TeX label `E.nonassoc`, already supplies the
inner-product mechanism. Its graded real algebra has dimensions d,1,d and
is explicitly nonassociative; its scalar middle component acts into the
third component and its nonvanishing map is cubing. The present multiplication
uses the degree-one/degree-two truncation, making the scalar line annihilate
everything and hence making the algebra associative. The countermodel uses
rational squares. The inner-product mechanism is credited to Bergman; no
independent invention of it is claimed.

## Falsifier

Any omitted infinite-field, finite-dimension, bilinearity, associativity,
commutativity, common product-nilpotence, subspace, universal nonzero-vector,
positive-exponent or same-field condition invalidates the proposed target
match. Reading k=2 as two factors would be an indexing error: it means three
factors. Pointwise nilpotence or checks on a finite collection of vectors
would not suffice. A prior exact associative settlement would invalidate the
open-problem-resolution admission basis, even though the compiled statement
remains a mathematical refutation.

## Evidence

The primary arXiv v2 HTML and author TeX agree on Convention 2, Question 16,
Question 19 and Example 20. The author TeX SHA256 is
`b8a3d395046cc8459a77b5657f6dab8fa37b11af7012ffd0c4f2dd73c9eb80cc`.
The exact labels and line ranges are in `Library/Certificates/bergman2014eggert.md`.
The author text retains the remark that no examples are known to it without
algebraic closedness.

The bounded literature screen inspected arXiv:1309.0053 without locating an
answer to this field branch. Repository, pinned-Mathlib and bounded third-party
Lean searches supplied no exact result. OpenAlex was rate-limited and a World
Scientific prior-work text was inaccessible. The repository's Bergman
Question 15 settlement concerns a different question. These findings do not
establish worldwide absence of prior work or priority.

The formal evidence is
`D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result`, whose type
is the literal negation of the closed definition `claim : Prop`. The proof
constructs the rational bilinear multiplication and verifies its laws, common
nilpotence and nonvanishing squares; it derives the dimension contradiction
inside Lean. `mul_self_add_mul_self_eq_zero` supplies the rational
sum-of-squares step, and `LinearMap.finrank_range_of_inj` and product-space
finrank supply the dimensions. The axiom closure consists of
`Classical.choice`, `Quot.sound` and `propext`.

## Triage

### What the settlement shows

Proved: `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result`
refutes the universal infinite-field assertion with an associative,
commutative, globally nilpotent rational algebra. This is the field-condition
branch of Question 19 attached to Question 16. The same rational model
refutes the arbitrary-field alternative; these are one subsidiary question.

The mechanism is anisotropy of `a²+b²` over Q. The two-dimensional coordinate
plane has nonvanishing squares valued in a one-dimensional annihilating line.
Making that line annihilate every element forces every triple product to
vanish and both associative bracketings to agree. Infinitude alone therefore
cannot replace algebraic closedness in the proposed dimension bound.
Bergman's Example 20 supplies the inner-product mechanism; its original
nonassociative cubing algebra remains distinct from this associative
quadratic truncation.

Computed within the Lean proof: the local dimension identities `hV` and `hR`
are `dim_Q V = 2` and `dim_Q R = 3`. At exponent two the proposed bound is
`4 ≤ 3`, and `norm_num` closes the contradiction. These are exact symbolic
calculations in `result`, with no numerical experiment or finite-vector
sampling.

Open outside this settlement: Question 16 over algebraically closed fields,
the noncommutative branches of Question 19, and Eggert's conjecture. This
result changes none of those scopes.

Open successor candidate: for every infinite field F of characteristic
other than two admitting an anisotropic binary quadratic form q on F²,
construct an associative commutative nilpotent algebra R = F² ⊕ F with
V = F² ⊕ {0}, nonzero squares on every nonzero vector of V, and
`dim_F R = 3 < 2 dim_F V = 4`. The proposed product uses the symmetric
polarization `B_q(u,v) = (q(u+v)-q(u)-q(v))/2` in the annihilating last
coordinate. This generalization is not established by the delivered theorem.
It still needs a Lean construction of the bilinear polarization, its
square identity `B_q(v,v)=q(v)`, associativity and commutativity, common
three-factor nilpotence, anisotropy-based universal nonvanishing, exact
same-field dimensions and the resulting literal refutation. No companion
theorem is claimed.

## ASSUMED-UNVERIFIED

Worldwide priority and absence of any unlocated earlier exact answer remain
unverified. The bounded literature screen and its access limits are stated
in Evidence. No originality claim is made for Bergman's inner-product
mechanism or for the quadratic construction.

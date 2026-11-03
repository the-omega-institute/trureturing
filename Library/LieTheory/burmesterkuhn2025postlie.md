---
bibkey: burmesterkuhn2025postlie
authors: Annika Burmester; Ulf Kühn
year: 2025
title: "On post-Lie structures for free Lie algebras"
doi: 10.48550/arXiv.2504.19661
url: https://arxiv.org/html/2504.19661v1
claim: "Conjecture 4.29: for every k >= 0 the ari coproduct preserves the increasing k-level filtration in its right tensor factor on all rational word polynomials."
strata_touched:
  - D5/S1/Words/PostLie/AriWordOperations
  - D5/S1/Words/PostLie/AriProjection
  - D5/S1/Words/PostLie/AriWordProduct
  - D5/S1/Words/PostLie/AriCoproductFiltration
license: citation-only
triage: anchor
---

# Ari coproduct and the right-factor level filtration

## Verified locator

The original source is Annika Burmester and Ulf Kühn, *On post-Lie structures
for free Lie algebras*, arXiv:2504.19661v1, submitted 28 April 2025.
The verified DOI is `10.48550/arXiv.2504.19661`; the original full text is
<https://arxiv.org/html/2504.19661v1>, its TeX is
<https://arxiv.org/src/2504.19661v1>, and its version history is
<https://arxiv.org/abs/2504.19661>. The inspected history lists v1 only.

The target is the whole Conjecture 4.29. Its carrier is the finite rational
concatenation-word algebra on `v_0,v_1,...`, including the empty word. For
all natural `k,r`, let `lambda_k(w)` count letters different from `v_k` and
let `F_r^k` be the rational span of words with `lambda_k(w) <= r`.
The assertion is

\[
\Delta_a(F_r^k)\subseteq
\operatorname{image}\bigl(H\otimes_{\mathbb Q}F_r^k
 \longrightarrow H\otimes_{\mathbb Q}H\bigr).
\]

No restriction to positive indices, homogeneous inputs, a fixed word length,
or a single generator is part of this assertion.

## Original finite operations and pairing

Definition 4.2 specifies
`beta(0,0)=1`, both mixed-zero values zero, and
`beta(a,l)=choose(a-1,l-1)` when `a,l>0`.
The signed multiplicity of equal-length index tuples is

\[
\mu_{\mathbf a,\mathbf l}
 =(-1)^{\sum a_i+\sum l_i}\prod_i\beta(a_i,l_i).
\]

For nonzero multiplicity, each `l_i <= a_i` and `l_i=0` exactly when `a_i=0`.
The converse stated in Remark 4.3(i) fails at mixed-zero pairs and is not used.

The letter-action presentation is the first equality in the full proof of
Proposition 4.19, taking its Lie factors to be individual generators. Lemma
4.10 derives that equality from the magmatic Definition 4.8 and its extension;
Definition 1.9 is the enveloping extension. Thus for a nonempty concatenation
word `A=v_(a_1)...v_(a_m)` and `s>0`, the original action is the finite sum

\[
 A\triangleright_a v_s
 =\sum_{0\le l_i\le a_i}\mu_{\mathbf a,\mathbf l}
 [\cdots[[v_{s+\sum_i(a_i-l_i)},v_{l_1}],v_{l_2}],\ldots,v_{l_m}],
 \qquad [p,q]=pq-qp.
\]

The empty word acts identically on every generator. Every nonempty word acts
by zero on `v_0`. This is the presentation used here; the different naive
associative extension excluded in Remark 4.16 is not used. No additional
magmatic or enveloping realization is postulated.

Proposition 2.1 gives `A star B` by assigning every position of `A` to one
of `length(B)+1` slots. Letters in each slot retain their original order.
A term is slot zero followed by, in the order of the letters of `B`, the
action of slot `j+1` on letter `j` of `B`. Every assignment is counted,
even if repeated letters give the same resulting tuple. Primitive unshuffle
sends a generator to the sum of its placements in the individual slots;
its algebra-homomorphism extension gives these assignments with their
multiplicities.

The ordinary word pairing is equation (18). Definition 1.20 characterizes
the dual coproduct uniquely, and Remark 1.22 describes its coefficients as
`[A tensor B] Delta_a(w) = [w](A star B)`.
The ordinary pairing is symmetric. Its symmetry identifies the source
convention, which pairs the product on the left, with the coefficient
convention that pairs the input basis word on the left. There is no
factorial or divided-power normalization. Example 4.28 omits the
two unit tensor terms in its display; the full defining pairing, rather
than a reduced-coproduct convention, specifies the operation here.
The source weight is `gamma(0)=1` and `gamma(i)=i` for positive `i`.

## Projection and finite transpose argument

The concatenation algebra map `pi_k:H -> Q[t]` sends `v_k` to `t` and every
other generator to zero. For every finite rational polynomial `P` and every
natural `d`, including zero, its `t^d` coefficient equals the coefficient
of the unique pure word `v_k^d` in `P`. Every ordinary commutator projects
to zero. Consequently a nonempty left word acting on any generator has
zero pure projection. The empty-left-word branch is the original generator.
Thus an action output for `v_s` has at least one letter different from
`v_k` whenever `s != k`.

Concatenation adds these counts. Finite sums and rational cancellation
cannot create support outside the union of the summand supports. Applying
this fact to the ordered unshuffle formula gives

\[
 [w](A\star_a B)\ne0\quad\Longrightarrow\quad
 \lambda_k(B)\le\lambda_k(w).
\]

The nonzero multiplicity condition preserves zero positions and hence the
original weight despite the shifted positive index. The action and product
are homogeneous for this weight. A word of weight at most `N` has length
at most `N` and all indices at most `N`. Bounded lists over the genuinely
finite alphabet `Fin(N+1)`, filtered by weight, therefore give exactly the
finite window of such words. For a word `w` of weight `N`, the tensor sum
with coefficients `[w](A star B)` over that window has the full ordinary
transpose coefficients for every pair, including pairs outside the window.
It is an ordinary algebraic tensor, not a completed tensor series.

The coefficient support bound places that tensor in the span of pairs
whose second word has level at most `lambda_k(w)`. Each spanning tensor
is the image of an actual element of `H tensor F_r^k`. Rational linearity
then gives the full assertion for arbitrary `P` in the rational span.
These are classical projection and support ingredients; their use here
is a synthesis directed at the specific original assertion.

## Bounded prior-art limits

The inspected relevant passages of arXiv:2508.05024v1, 2603.05038v1,
2609.25168v1, and 2610.37351v1 did not identify a settlement of the whole
Conjecture 4.29. MathDB page 368177 concerns Appendix A.7's uri multiplicity
threshold shuffle assertion and is a different problem. The bounded
source-title, author, and operation searches did not identify an exact posted
solution. Rate-limited citation APIs do not establish a complete citation
search. These observations assert neither worldwide absence nor priority.

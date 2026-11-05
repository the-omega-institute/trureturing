---
bibkey: bergman2014eggert
authors: George M. Bergman
year: 2014
title: Thoughts on Eggert's Conjecture
doi: 10.1090/conm/609/12101
url: https://arxiv.org/abs/1206.0326v2
claim: Questions 15 and 19 ask about powers in contracted semigroup spans and the field-condition extension of the nilpotent-algebra dimension bound from Question 16.
strata_touched:
  - D5/S0/Certificates/Algebra/BergmanQuestion15Refutation
  - D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation
license: citation-only
triage: anchor
---

# Powers in semigroup and nilpotent algebras

George M. Bergman, *Thoughts on Eggert's Conjecture*, Contemporary Mathematics
609 (2014), 1–17, DOI 10.1090/conm/609/12101, arXiv:1206.0326v2,
2013-01-02. The author TeX labels Question 15 `Q.F0X^n`:

> Suppose X is a finite subset of a commutative semigroup S with zero, n a
> positive integer such that the n-th power map is one-to-one on X and does not
> take any nonzero element of X to 0, and F a field of characteristic 0. Must
> every nonzero element of the span FX of X in F_0 S have nonzero n-th power?

The paper assumes associative algebras without an identity in general. Its
contracted semigroup algebra has free basis S minus its absorbing zero. A
product that is zero in S becomes the zero vector, rather than a new basis
vector. These conventions distinguish Question 15 from uncontracted semigroup
algebras and from the positive-characteristic example preceding it.

The author source is https://math.berkeley.edu/~gbergman/papers/Eggert.tex
(SHA256 b8a3d395046cc8459a77b5657f6dab8fa37b11af7012ffd0c4f2dd73c9eb80cc).
The author PDF is https://math.berkeley.edu/~gbergman/papers/Eggert.pdf
(SHA256 91b9055006a1befd188a205d5d14d3b2576ab5a09fc434b04b974d34fbcbb0e4).
Their question wording agrees with the v2 source. Direct publisher-PDF access
was unavailable; the author copy supplies the published-version reading.

## Verified locator

- URL: https://arxiv.org/abs/1206.0326v2
- DOI: 10.1090/conm/609/12101
- Version: v2, 2013-01-02; published in Contemporary Mathematics 609 (2014).
- Source locator: Question 15, author TeX label `Q.F0X^n`, lines 732–740.
- Source capture SHA256: `b8a3d395046cc8459a77b5657f6dab8fa37b11af7012ffd0c4f2dd73c9eb80cc`.


## The field-condition branch of Question 19

Question 16 (author TeX label `Q.V->`, lines 789–795) asks:

> Let R be a finite-dimensional nilpotent commutative algebra over an
> algebraically closed field F, let V be a subspace of R, and let n be a
> positive integer such that every nonzero element of V has nonzero n-th
> power. Must dim R ≥ n dim V?

Question 19 (label `Q.rash`, lines 879–886) asks:

> Does the generalization of Conjecture 8, or an affirmative answer to any
> of Questions 11, 15, 16, 17 or 18, hold if the commutativity hypothesis is
> dropped, and/or, in the case of Question 16, if the assumption that F be
> algebraically closed is dropped (or perhaps weakened to “F is infinite”)?

The immediately preceding paragraph, lines 870–877, says the author has no
examples showing failure without algebraic closedness. Convention 2, label
`Cv.cm_ass`, lines 151–170, makes all dimensions dimensions over F and assumes
associative algebras, not necessarily with an identity. The formal target
retains associativity and commutativity and changes only the field condition.
A rational counterexample refutes both the arbitrary-field alternative and
the infinite-field alternative as one field-condition question. It makes no
assertion about the algebraically closed case, the noncommutative branches,
or Eggert's conjecture.

## Example 20 and the quadratic mechanism

Example 20, label `E.nonassoc`, lines 906–936, is prior work of Bergman. It
uses a real inner product on W in a graded commutative **nonassociative**
algebra with dimensions d, 1, d, and nonvanishing cubing on the degree-one
part. Its scalar degree-two component multiplies into a nonzero degree-three
copy of W.

The associative quadratic model uses the degree-one/degree-two truncation
of this mechanism: on `(F × F) × F`, set

$$
((a,b),c)((d,e),f)=((0,0),ad+be).
$$

The degree-two scalar line annihilates the entire algebra. Every triple
product is consequently zero with either bracketing, so associativity holds.
Over F = Q, `a²+b²=0` forces `a=b=0`. The coordinate plane V has dimension 2,
the ambient algebra has dimension 3, and exponent 2 would require `3 ≥ 4`.
The inner-product mechanism is credited to Bergman; Example 20 itself is not
an associative counterexample to this field-condition branch.

The bounded source and duplicate screen located no exact settlement of this
branch in the checked scope. That statement is not an exhaustive worldwide
priority claim and does not assert that the quadratic construction is new.

## Additional verified locators

- Primary HTML: https://arxiv.org/html/1206.0326v2, Questions 16 and 19,
  Convention 2, and Example 20.
- Author TeX: https://math.berkeley.edu/~gbergman/papers/Eggert.tex;
  labels `Cv.cm_ass`, `Q.V->`, `Q.rash`, and `E.nonassoc` at the line ranges above.
- Author TeX SHA256:
  `b8a3d395046cc8459a77b5657f6dab8fa37b11af7012ffd0c4f2dd73c9eb80cc`.

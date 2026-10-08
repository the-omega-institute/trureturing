---
bibkey: wainwrightjordan2008graphical
authors: Martin J. Wainwright and Michael I. Jordan
year: 2008
title: Graphical Models, Exponential Families, and Variational Inference
doi: 10.1561/2200000001
url: https://people.eecs.berkeley.edu/~jordan/papers/wainwright-jordan-fnt.pdf
claim: "Junction-tree marginals factor through their shared separators; the paper defines mutual information and Kullback–Leibler divergence by probability-ratio logarithms."
strata_touched: []
license: citation-only
triage: anchor
---

# Shared separators and finite probability-ratio information

The [author PDF](https://people.eecs.berkeley.edu/~jordan/papers/wainwright-jordan-fnt.pdf)
is the Foundations and Trends in Machine Learning 1(1–2), 1–305 text.
Section 2.5.2, equation (2.12), printed p. 32, divides products of clique
marginals by separator marginals with the indicated multiplicities.
Example 2.2, pp. 32–33, specializes to a three-node Markov chain:

$$
p(x_1,x_2,x_3)=\frac{p(x_1,x_2)p(x_2,x_3)}{p(x_2)}.
$$

Proposition 2.1 on p. 33 gives a distribution realizing normalized,
locally consistent junction-tree marginals. This constructs a completion;
it does not identify every arbitrary joint law with those marginals.
The [pyramid reference, §六](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)
uses the two-clique instance with separator $z$. At zero separator mass
all associated nonnegative cells vanish; the consumer assigns zero there
and proves normalization without dividing by zero.

Equation (4.13), p. 82, defines pairwise mutual information by the
joint-to-product ratio. Section 5.2.2, equation (5.9), p. 132, defines
the modern Kullback–Leibler divergence $D(q\Vert p)$ as the expectation
under $q$ of $\log(q/p)$. The consumer's §九 uses base-two finite sums,
states support inclusion and proves nonnegativity by the ordinary log
inequality, including boundary probabilities. Its exact entropy-gap
identity, native reply loss and degenerate apex treatment are the
consumer's elementary finite-law applications. They are not attributed
to the paper's exponential-family parameter formulas or to a missing
primary historical source.

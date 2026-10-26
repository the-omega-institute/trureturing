---
bibkey: kumarpengtran2022complexity
authors: Aarya Kumar, Siyu Peng, and Vincent Tran
year: 2022
title: Integer Complexity Generalizations in Various Rings
doi: 10.48550/arXiv.2211.04379
url: https://arxiv.org/abs/2211.04379v1
claim: "Conjecture 4.4 states that E(m, 2) is the third most inefficient for odd m."
strata_touched:
  - D5/S3/Arith/Congruence/KumarPengTranModularComplexity
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ArithUnits/kumarpengtran2022complexity -->

# Modular integer complexity

## Verified locator

DOI: 10.48550/arXiv.2211.04379

Source: https://arxiv.org/abs/2211.04379v1

## Definitions and conjecture

Page 1:

> An expression refers to a sequence of x’s, which are joined together by +, ·, and () in the usual sense.

> The complexity of a number n, denoted as ||n|| is equal to the smallest number of 1’s needed to write n as an equation using addition and multiplication.

Page 28:

> In this section, we shall denote the base as s.

> The representations with base s span every element of ℤ/mℤ if and only if s ∈ Uₘ.

> The inefficiency E of an element, which will be used as a base, s ∈ ℤ/mℤ is defined as E(m, s) = max(‖0‖, ‖1‖, ‖2‖, …, ‖m − 1‖). In other words, the maximum complexity of an element of ℤ/mℤ with x = s.

Conjecture 4.4, page 29:

> E(m, 2) is the third most inefficient for odd m.

## Mathematical correspondence

Expressions are binary trees with leaves x and internal nodes for addition or
multiplication. Leaf counts give expression sizes; evaluation at s takes values
in ZMod m. Complexity is the natural infimum of the sizes of expressions with
the required value. Inefficiency is the finite supremum over all residues.

The formal proposition in issue #19529 reads third place by counting individual
unit bases with strictly larger inefficiency: at most two for each odd m ≥ 3.
At m = 17, the repository proves that base 2 has inefficiency at most six and
bases 1, 3 and 16 each have inefficiency greater than six. It refutes that
cardinal-ranking proposition. Bases 3 and 16 tie; the witness does not refute
dense ranking by distinct inefficiency values. The paper gives no explicit
tie rule. Exact inefficiencies and minimality are not separate Lean claims.

## Literature boundary

The search reported in issue #19529 inspected arXiv v1 and the MathDB
integer-complexity tag and located no settlement. A post-review revision
mentioned on an author's CV was not read. Completeness is
ASSUMED-UNVERIFIED. Conjectures 4.2 and 4.3 and asymptotic behaviour remain
outside this formal settlement.

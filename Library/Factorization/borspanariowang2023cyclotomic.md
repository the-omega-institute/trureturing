---
bibkey: borspanariowang2023cyclotomic
authors: Alexander Bors, Daniel Panario, and Qiang Wang
year: 2023
title: Functional graphs of generalized cyclotomic mappings of finite fields
doi: 10.4171/MEMS/23
url: https://arxiv.org/abs/2304.00181v1
claim: "Question 6.3.1 asks whether the lower limit of AC(T_m)/(log² m/log log m) is positive."
strata_touched:
  - D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Factorization/borspanariowang2023cyclotomic -->

# Arithmetic complexity of singleton partitions

## Verified locator

DOI: 10.4171/MEMS/23

Source: https://arxiv.org/abs/2304.00181v1

Alexander Bors, Daniel Panario and Qiang Wang, *Functional graphs of generalized
cyclotomic mappings of finite fields*, arXiv:2304.00181v1; Memoirs of the European
Mathematical Society 23. Page numbers below refer to the arXiv version.

## Definitions and question

Pages 10-11:

> For a given positive integer m, we define the notion of an m-(in)congruence to be an (in)congruence of the form ν(x ≡ b (mod a)) where ν ∈ {∅, ¬} is a “logical sign”, and a, b are integers with a ≥ 1 and a | m.

Definition 1.5, page 10:

> We identify the elements of Z/mZ with their standard representatives in {0, 1, . . . , m − 1}.

Definition 1.5(1), pages 10-11:

> There is a unique partition of Z/mZ, which we denote by P(x ≡ b_j (mod a_j) : j = 1, 2, . . . , K), such that each block of this partition is the solution set modulo m of a system of m-CCs of the form

The displayed system is ν_1(x ≡ b_1 (mod a_1)), …, ν_K(x ≡ b_K (mod a_K)),
with each logical sign chosen independently from {∅, ¬}.

Definition 1.5(3), page 11:

> When P is an arithmetic partition of Z/mZ, then the smallest value of K ∈ N_0 such that P is spanned by K suitably chosen m-congruences is called the (arithmetic) complexity of P, written AC(P).

Section 6.3, page 188, identifies

> the trivial partition T_m of Z/mZ, all of whose blocks are singletons

Question 6.3.1, page 189:

> Is it true that lim inf_{m→∞} AC(T_m)/(log² m/log log m) > 0?

## Mathematical correspondence

A test stores a positive natural modulus a dividing m and an integer residue b.
Truth at a natural representative x is Int.ModEq with x and a cast to integers.
The singleton partition condition says that two representatives below m with
identical test truth values coincide. AC(T_m) is the natural-number infimum of
the sizes of separating families. The lower limit uses EReal and natural indices;
all logarithms and quotients in the normalized ratio are real.

The repository's proof derives the prime-power totient lower bound by a fibre
injection and a charge estimate. Chebyshev's least-common-multiple estimate then
gives an eventual normalized ratio at least 1/64. The source's stronger exact
upper-bound expression is not asserted to be optimal for every modulus here.

## Literature boundary

The source search recorded in issue #19381 inspected arXiv v1, the published
memoir's Question 6.3.1, excerpts of arXiv:2609.30191 and Qiang Wang's publication
list. Wang's survey and normal-bases paper and the Bors-Glasby paper were not read
in full. Prior-art completeness remains ASSUMED-UNVERIFIED.

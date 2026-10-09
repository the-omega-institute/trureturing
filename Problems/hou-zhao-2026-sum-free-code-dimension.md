---
slug: hou-zhao-2026-sum-free-code-dimension
bibkey: hou2026sumfreedom
doi: 10.48550/arXiv.2609.31489
url: https://arxiv.org/abs/2609.31489v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/SumFreeCodeDimensionRefutation.result
---

# Hou–Zhao: the dimension of a sum-free function's code

## Problem

Xiang-Dong Hou and Shujun Zhao, “Further Results on Sum-Freedom of Binary
and q-ary Functions”, arXiv:2609.31489v1, §4.2, printed p. 14,
immediately after Theorem 4.6:

> There are some open questions. In Theorem 4.1, the dimension and minimum
> weight of the code C(f ) are determined and they are independent of f as long as
> f is APN, i.e., 2nd order sum-free. Do we have the same conclusion for the code
> Cs (f ) in Theorems 4.5 and 4.6, where f is an sth order sum-free function? If the
> dimension k and the minimum weight d of Cs (f ) depend on the sum-free function f ,
> what are the ranges for k and d? Likely, these questions will lead the investigation
> of sum-free functions to new directions.

Definition (1.1) requires a nonzero function sum on every s-dimensional
affine subspace. Equation (4.7) defines C_s(f) as the kernel of the
parity-check matrix consisting of generator rows of
R_q(s(q−1)−1,n), followed by the n coordinate rows of f.

The dimension-only universal assertion, specialized to q = 3, is

$$
\forall n,s\in\mathbb N,\quad
n\ge2,\ 1\le s\le n-1\ \Longrightarrow\
\forall f,g:\mathbb F_3^n\to\mathbb F_3^n,\quad
\operatorname{SumFree}_s(f)\land\operatorname{SumFree}_s(g)
\ \Longrightarrow\ \dim C_s(f)=\dim C_s(g).
$$

The closed Lean definitions `claim : Prop` and `result : ¬ claim`
retain exactly these quantifiers. They settle dimension independence
negatively, without settling minimum-distance independence or either full range.

## Motivation

The binary APN case has function-independent code parameters in Theorem 4.1.
The question asks whether that phenomenon extends to arbitrary sum-free order
and general fields. A fixed admissible pair with different kernel dimensions
rules out such a general extension.

## Gap

Tier 1: the paper explicitly poses this question after Theorem 4.6.
arXiv lists only version 1 of arXiv:2609.31489 (submitted 2026-09-25).
A literature check on 2026-10-09 found no accessible work answering the
question. It covered exact-title and identifier searches for later versions
and citing works, follow-up searches on sum-free functions after 2026-09-25,
and the earlier sum-free literature: Carlet (J. Cryptology 38, 2025;
Des. Codes Cryptogr. 93, 2025), Carlet–Hou (Des. Codes Cryptogr. 93, 2025),
Ebeling–Hou–Rydell–Zhao (arXiv:2410.10426), Hou–Zhao (arXiv:2502.04545,
arXiv:2504.21805), Kaspers (arXiv:2603.28266), Carlet–Thornburgh
(arXiv:2608.23888) and arXiv:2609.22394.
The only citing work located, Cheng (arXiv:2610.06445), counts zero-sum
subspaces of the binary inverse function and does not treat C_s(f).

Heering, Kaspers and Taranchuk (arXiv:2605.22958) are the closest prior work.
For non-degenerate binary (n,m)-functions with 2 ≤ s ≤ n−2, their
Theorem 1.1 and Lemma 4.3 give dim C_s(F) = dim RM(n−s,n) − m and minimum
distance 3·2^{s−1}. These parameters are independent of F in the binary
non-degenerate class. They do not address q > 2 or degenerate functions.
Theorem 4.6 of Hou–Zhao assumes only q > 2 and 1 ≤ s ≤ n−1.
The full text of Carlet's WAIFI 2026 chapter (ePrint 2024/1693) was not
accessible. Its abstract does not mention C_s(f).

## Route

Take q = 3, n = 2 and s = 1, with

$$
f(x,y)=(x^2+y^2,0),\qquad g(x,y)=(x^2,y^2).
$$

For every a and every nonzero v, summing over a + tv gives

$$
\sum_{t\in\mathbb F_3}f(a+tv)=(-(v_1^2+v_2^2),0),\qquad
\sum_{t\in\mathbb F_3}g(a+tv)=(-v_1^2,-v_2^2).
$$

In the ternary field a nonzero square is one, so v_1² + v_2² vanishes only
at v = 0. Both functions are first-order sum-free. The Lean proof checks the
finite sums for all translates and all nonzero one-element direction families,
and uses the singleton linear-independence criterion.

The Reed–Muller part R_3(1,2) has the rows 1, x, y. The full parity matrices
have exactly the same kernels as the following compressed row families:

$$
A_f=(1,x,y,x^2+y^2),\qquad A_g=(1,x,y,x^2,y^2).
$$

Explicit right inverses supported on the points (0,0), (0,1), (0,2), (1,0)
for A_f, and additionally (2,0) for A_g, satisfy A_f B_f = I_4 and
A_g B_g = I_5. Lean checks both products entrywise and proves equality of
the compressed kernels with the original kernels. Thus the original parity
ranks are four and five. Rank–nullity on the nine-dimensional word space gives

$$
\dim_{\mathbb F_3} C_1(f)=5,\qquad
\dim_{\mathbb F_3} C_1(g)=4.
$$

## Falsifier

The refutation would fail if either function had a zero sum on an affine line,
if the monomial rows differed from the reduced degree-at-most-one rows,
if the compression altered the kernel, or if either right inverse were invalid.
Each obligation is discharged in Lean, with code dimension defined literally
as `Module.finrank (ZMod 3)` of the parity-check linear map's kernel.

## Evidence

`D5/S3/Arith/SumFreeCodeDimensionRefutation.result` is a closed theorem
of type `¬ claim`. The module compiles with Lean 4.33.0. Its axiom closure is
`propext`, `Classical.choice`, `Quot.sound`. It uses no `sorry`, new axiom,
or `native_decide`. The finite certificates are reduced and checked by Lean.

Two independent exact Python computations over F_3 agree with the Lean
dimensions: both check all twelve affine lines of F_3^2 and compute
parity-check nullities five and four from the original parity equations.
The kernel dimensions, rather than these Python calculations, support `result`.

## Triage

- [refuted: D5/S3/Arith/SumFreeCodeDimensionRefutation.result]
  Dimension independence fails for q = 3, n = 2, s = 1.
  Theorem 4.6 states bounds, not equality of dimensions, and is not contradicted.
- [proved, by rank–nullity, not formalized] The mechanism is exact. Let R be
  the row space of R_q(s(q−1)−1, n) and let ρ(f) be the dimension of the span
  of the coordinate rows of f modulo R. Then
  dim C_s(f) = q^n − dim R − ρ(f). Dimension dependence therefore occurs
  exactly when sum-free functions of the same order have different ρ.
  In the nine-point pair, the norm map x² + y² adds one row (its second
  coordinate is zero) and the split-square map adds two.
  If every nonzero F_q-linear combination of the coordinates of f lies outside R,
  then ρ(f) = n and dim C_s(f) = q^n − dim R − n. This matches the
  Heering–Kaspers–Taranchuk binary formula for non-degenerate functions.
  The counterexample therefore separates degenerate from non-degenerate
  functions. Among non-degenerate functions it does not create dimension
  dependence.
- [computed] There is also a second-order example at q = 3, n = 4, s = 2. In
  K = F_3[T]/(T^4+T+2), identified with F_3^4, let
  G(x) = x^8 and F(x) = x^8+x^72 = Tr_{K/F_9}(x^8).
  Two independent computations find no zero sum on any of the 1,170 affine planes,
  Reed–Muller rank 31, parity ranks 33 and 35, and code dimensions 48 and 46
  for F and G respectively. Here ρ(F) = 2 because F takes values in F_9.
  This example is computed evidence only; the Lean theorem uses the nine-point
  first-order example.
- [computed] Both nine-point codes have minimum distance four, as obtained
  by enumerating their kernel bases' linear combinations. This equality for the
  displayed pair does not establish minimum-distance independence for other functions.
- [open] Decide whether the minimum weight of C_s(f) is independent of f
  among non-degenerate q-ary sth order sum-free functions; the dimension is
  independent there by the rank formula above.
- [open] Determine the ranges of k and d as f varies over all sum-free functions.
  The displayed dimensions supply two attained k values, not a classification.

## ASSUMED-UNVERIFIED

The literature check covers the accessible corpus listed under Gap.
Forward-citation indices (Google Scholar, Semantic Scholar, NASA ADS)
returned no usable results, and the full text of ePrint 2024/1693 and of
the final journal versions of three earlier Hou papers was not inspected.
The rank formula, the second-order certificate and the minimum-distance
calculations are not formalized in this module.


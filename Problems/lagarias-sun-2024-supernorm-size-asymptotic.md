---
slug: lagarias-sun-2024-supernorm-size-asymptotic
bibkey: lagariassun2024supernorm
doi: null
url: https://arxiv.org/abs/2308.15303v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Partitions/SupernormSizeAsymptotic.result
---

## Problem

Jeffrey C. Lagarias and Chenyang Sun, *Asymptotics of reciprocal supernorm
partition statistics*, arXiv:2308.15303v1, Conjecture 3.5, page 10,
equation (3.16), states:

> There holds $\widehat W_{\rm size}(n)\sim e^\gamma/n$, as $n\to\infty$.

The source's equation (3.1) defines

$$
\widehat W_{\rm size}(n)
=\sum_{\lambda:\,|\lambda|=n}\frac{1}{\widehat N(\lambda)},
\qquad
\widehat N(\lambda)=\prod_{k\ge1}p_k^{m_k(\lambda)},
$$

where $p_k$ is the $k$-th prime, $p_1=2$, and $m_k(\lambda)$ is the
multiplicity of part $k$. The empty product is one. This dossier uses the
arXiv v1 locator throughout; it assigns no conjecture number or page number
to the journal version.

The exact Lean conclusion is

```lean
Tendsto (fun n : ℕ => (n : ℝ) * Wsize n) atTop
  (𝓝 (Real.exp Real.eulerMascheroniConstant))
```

The native `Nat.Partition n` contains positive parts summing to exactly `n`.
`partPrime k = Nat.nth Nat.Prime (k - 1)` gives the source's $p_k$ for every
positive part. Its value at zero is two, whereas the source separately sets
$p_0=1$; zero never occurs as a partition part. `supernorm` preserves every
multiplicity, and `Wsize` sums its real reciprocal over the entire finite
size ensemble. Since $e^\gamma>0$, the displayed limit is equivalent to the
quoted asymptotic: for every $\epsilon>0$, eventually
$|n\widehat W_{\rm size}(n)-e^\gamma|<\epsilon$.

## Motivation

Cumulative asymptotics do not imply the required pointwise asymptotic.
For example, for $c>0$, the nonnegative sequence
$a_{2r}=c/r$ and $a_{2r-1}=0$ has cumulative mass asymptotic to $c\log n$
but $na_n$ alternates between $2c$ and zero. The size statistic needs
additional information about its positive convolution recurrence. No
monotonicity assumption is imposed on its individual values.

## Gap

The literature search covered Lagarias–Sun's original paper, including
Theorem 3.4 and Conjecture 3.5; the later citations by
Botkin–Dawsey–Hemmer–Just–Schneider (2024/2025), Schneider (2025), and
Gómez-Aíza (2026); and the classical coefficient asymptotics of
Knopfmacher–Ridley (1993), Braaksma–Stark (1997), Bender/Odlyzko,
Bell–Burris (2003), and Barbour–Granovsky (2005).
No settlement of the size conjecture was found within this scope.
Theorem 3.4 gives cumulative information, leaving the pointwise limit as
the mathematical gap.

Knopfmacher–Ridley, *Reciprocal sums over partitions and compositions*
(1993), treats reciprocal part weights $1/k$ rather than $1/p_k$.
Braaksma–Stark, *A Darboux-Type Theorem for Slowly Varying Functions*
(1997), Theorem 2, page 55, assumes a positive power exponent and
complex-domain hypotheses; the present logarithmic regime has exponent zero.
Bender's product-coefficient theorem, as stated in Odlyzko's author manuscript,
section 7, Theorem 7.1, requires distinct convergence radii, whereas both
factors in the present recurrence $zF'=FB$ have radius one.
The related Bell–Burris and Barbour–Granovsky results checked do not give
the required pointwise limit with constant $e^\gamma$ under its present
hypotheses. This bounded search establishes neither exhaustive literature
coverage nor priority.

## Route

Write $a_n=\widehat W_{\rm size}(n)$ and

$$
A_n=\sum_{k=0}^n a_k,
\qquad
E_m=\prod_{d=1}^m(1-p_d^{-1})^{-1}.
$$

Finite occupation boxes use the existing positive-energy partition
correspondence: coordinate $i$ records the multiplicity of part $i+1$.
Finite products of geometric sums tend to $E_m$. Their weighted energy
moments are at most $mE_m$, using $p_d\ge d+1$. Removing the mass with
energy greater than $n$ gives, for $n\ge1$,

$$
E_m\left(1-\frac mn\right)\le A_n\le E_n.
$$

Mertens' product theorem and the prime number theorem give
$E_m/\log m\to e^\gamma$. With $m=\lfloor n/\log n\rfloor$,
$m\to\infty$, $m/n\to0$, and $\log m/\log n\to1$. Hence
$A_n/\log n\to e^\gamma$. This cumulative conclusion is an ingredient,
not a new claim about the source's already established cumulative behavior.

Marking repeated parts and deleting them through the existing deletion
equivalence gives the exact finite recurrence

$$
na_n=\sum_{j=1}^n b_j a_{n-j},
\qquad
b_j=\sum_{d\mid j}\frac{d}{p_d^{j/d}}.
$$

Its proper-divisor remainder satisfies

$$
b_j=\frac{j}{p_j}+R_j,
\qquad
0\le R_j\le\frac{2\tau(j)}j.
$$

Indeed, with $r=j/d\ge2$, the bound
$r d^2\le2(d+1)^r$ and $p_d\ge d+1$ make each proper-divisor summand
at most $2/j$. The existing divisor subpower bound yields
$R_j\log j\to0$, so $b_j\log j\to1$ and $b_j\to0$.

Put $q=\lfloor n/2\rfloor$ and split the recurrence exactly as

$$
na_n=T_n+U_n,
\qquad
T_n=\sum_{0\le k<n-q}b_{n-k}a_k,
\qquad
U_n=\sum_{j=1}^q b_j a_{n-j}.
$$

Uniformity of $b_j\log n\to1$ on the corresponding half window and the
cumulative limit imply $T_n\to e^\gamma$. Cesaro averaging gives
$n^{-1}\sum_{j=1}^q b_j\to0$. Choose the bound on $T_n$ and the threshold
for this last average before choosing $K$. Strong induction then proves
$na_n\le K$ for every $n\ge1$. Therefore

$$
0\le U_n\le\frac{2K}{n}\sum_{j=1}^q b_j\longrightarrow0,
$$

which proves the complete natural-index pointwise limit.

## Falsifier

A counterexample would consist of $\epsilon>0$ and arbitrarily large natural
$n$ with $|n\widehat W_{\rm size}(n)-e^\gamma|\ge\epsilon$.
A finite prefix of values cannot establish or refute the asserted eventual
bound. A mismatch between prime indexing, part multiplicities, the full size
ensemble, or the quantified limit would also invalidate the claimed source
correspondence.

## Evidence

The exact settling declaration is
`D5.S3.Arith.Partitions.SupernormSizeAsymptotic.result` in
`D5/S3/Arith/Partitions/SupernormSizeAsymptotic.lean`.
Its proof uses the native partition definitions and the positive finite
recurrence above. The scoped Lean report checks the unconditional limit;
there is no unproved-step hypothesis parameter.

The numerical inputs are reused from
`PrimeBoundarySecondOrder.pi_normalized`, `Mertens.E₃.bound''`, and
`DivisorSubpower.card_divisors_subpower`. Partition conversion reuses
`energyFiberEquivPartition`; repeated deletion reuses
`OverpartitionThreshold.shiftEquiv`. The first-prime identity is
`Nat.nth_prime_zero_eq_two`.

The source correspondence is recorded in
`Blueprint/D5/S3/Arith/Partitions/SupernormSizeAsymptotic.scribe.cs` and
[the source note](../Library/Factorization/lagariassun2024supernorm.md).

## Triage

| item | status | evidence and boundary |
| --- | --- | --- |
| arXiv v1 Conjecture 3.5, the size ensemble | Lean proved | The exact unconditional `result` above. |
| Native size weights, the cumulative limit, and the positive convolution argument | Lean proved | Consumed ingredients of the same module's proof of `result`. |
| arXiv v1 Conjecture 3.7, the max ensemble | Paper proved; not a Lean settlement here | For $n\ge1$, its mass is $E_n-E_{n-1}=E_n/p_n$. Mertens and $p_n\sim n\log n$, $\log p_n\sim\log n$ give $e^\gamma/n$. No max-ensemble declaration or separate resolution claim is included. |
| arXiv v1 Conjecture 3.8 and the Lehmer equivalence | Paper claim; not Lean proved here | The source compares Conjecture 3.5 with Lehmer's reciprocal-norm theorem $W_{\rm size}(n)\sim e^{-\gamma}n$ to obtain $W_{\rm size}(n)\widehat W_{\rm size}(n)\sim1$. The norm statistic, Lehmer theorem, and equivalence are not established by this module. |
| arXiv v1 Conjecture 3.6, the perimeter ensemble | Unresolved here | The size deletion recurrence and localization argument do not supply the perimeter recurrence. No perimeter conclusion is claimed. |
| Literature completeness and priority | Unverified | The bounded search above does not establish worldwide absence of an earlier proof. |

## ASSUMED-UNVERIFIED

The journal version's conjecture numbering and pagination are unverified.
The literature search is limited to the objects listed in Gap; completeness
and priority are unverified.
The source's attribution to Lehmer and the equivalence with Conjecture 3.8
remain paper-level statements in this dossier.

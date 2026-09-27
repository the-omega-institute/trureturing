[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# All eight-prime cores containing 3 and 5

Let a finite family have pairwise distinct odd moduli greater than one. Assume
an actual block has eight prime vertices containing $3$ and $5$, and every
other block has at most seven vertices. Under the inherited Chapter 23 and
Chapter 31 conditional-domain interfaces and the ordinary source transport,
the family is noncovering. More precisely, the extendible core Haar measure is
greater than

\[
\frac1{2200000}.
\]

This chapter closes the three profiles in which the core does not contain both
$7$ and $11$. The profile containing both $7,11$ is the four-case result
of [Chapter 38](38-eight-prime-cores-containing-three-five-seven-eleven.md),
verified by `variable_eight_core_certificate.py`. Together they cover every
eight-prime core containing $3,5$. The conclusion remains conditional on the
ordinary source and Chapter 23/31 interfaces; it is not a Lean theorem and it
does not resolve unrestricted Erdős--Selfridge #7.

## Finite profile exhaustion

Write the six core primes other than $3,5$ in increasing order. There are
four disjoint cases:

* both $7$ and $11$ occur; this is Chapter 38;
* $7$ occurs and $11$ does not;
* $11$ occurs and $7$ does not;
* neither $7$ nor $11$ occurs.

In the second case, the first omitted prime in the sequence

\[
13,17,19,23,29
\]

is $r$, or all five occur. In the third case the same first-omission split
is made after $11$. In the last case the sequence is

\[
13,17,19,23,29,31,
\]

with the same first-omission split. Each branch has a coordinatewise lower
proxy for the six source coordinates. Actual later primes may be arbitrarily
large.

## Shared budget

For a skipped prime $s\ge13$, the exact six-child conditional-kernel rows
give the root-3 costs $k_s$ for $s=13,17,19,23,29,31,37,41,43,47,53$.
All minima at least $59$ are charged by the inherited all-large tail

\[
\sum_{n\ge29}2^{-n}=2^{-28}.
\]

The profile bases are:

\[
 B_{7\text{-only}}=k_{11}=\frac{46408}{768123},
 \qquad
 B_{11\text{-only}}=f(7)=\frac18,
 \qquad
 B_{\mathrm{neither}}=f(7)+f(11)=\frac16.
\]

For a branch whose first omitted small prime is $r$, the deletion budget is

\[
B_{\mathrm{profile}}+\sum_{r\le s\le53}k_s+2^{-28}.
\]

For the no-omission branches the sum starts after the final guaranteed core
coordinate: at $31$ in the 7-only and 11-only profiles, and at $37$ in the
neither profile. The distinct-minimum block decomposition makes this one
budget on one transported source measure; it is not a sum of independently
optimized probability laws.

## Exact branch table

The certificate checks the source mass $m$, joint cap $D$, and

\[
H=(m-B)/D
\]

for all 19 branches. The weakest branch is the exact 7-only core

\[
\{3,5,7,13,17,19,23,29\},
\]

with

\[
H=1.6818388944128326\cdot10^{-5}>\frac1{2200000}.
\]

The next weakest exact branches are the 11-only core

\[
\{3,5,11,13,17,19,23,29\}
\]

with $H=4.3279542016462567\cdot10^{-4}$, and the neither core

\[
\{3,5,13,17,19,23,29,31\}
\]

with $H=4.52038763906137\cdot10^{-4}$. Every first-omission branch has a
larger margin.

The exact rational producer is
[`all_three_five_eight_core_certificate.py`](../frontier/cover-geometry/all_three_five_eight_core_certificate.py),
with its generated
[`JSON`](../frontier/cover-geometry/all_three_five_eight_core_certificate.json).
Run:

    python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_three_five_eight_core_certificate.py \
      --output /tmp/eight-prime-profile-budget.json

The input geometry and ordinary source helpers are SHA-pinned by the
certificate. The finite arithmetic checks do not replay the external source
theorem or the inherited conditional-kernel/domain proofs.

## Boundary

The result handles every eight-prime core containing $3,5$, including
arbitrarily large later coordinates and arbitrary finite original heights and
residues, provided all other blocks have at most seven vertices. It does not
handle an eight-prime core omitting $3$ or $5$, an arbitrary larger block,
or the unrestricted Erdős #7 problem. The ordinary monotonicity of the source
coupling and the Chapter 23/31 transfer remain explicit mathematical premises.

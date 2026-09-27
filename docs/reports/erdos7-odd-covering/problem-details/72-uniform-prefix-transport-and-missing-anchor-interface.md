[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Uniform finite-prefix transport and the missing-anchor interface

This note isolates the ordinary transport used in Chapter 31 and Chapter 70.
It makes the finite-height statement explicit and records the source-coordinate
maps needed when an eight-prime core omits 3 or 5. It does not supply the
ordinary source survival theorem, the conditional-kernel theorem, or a global
solution of Erdos--Selfridge #7.

## Finite-prefix transport lemma

Let (p\le q) be primes and let (h\ge0). Write a source residue in base
\(p\),

\[
x=\sum_{j<h}d_jp^j,\qquad 0\le d_j<p.
\]

For a shift table

\[
\sigma=(\sigma_0,\ldots,\sigma_{h-1})\in(\mathbb Z/q\mathbb Z)^h
\]

define

\[
F_\sigma(x)=\sum_{j<h}(d_j+\sigma_j\bmod q)q^j.
\tag{T1}
\]

For each fixed \(\sigma\), every digit map \(d\mapsto d+\sigma_j\pmod q\) is
injective because \(p\le q\). Therefore \(F_\sigma\) is injective. More
precisely, the inverse image of a target cylinder

\[
y\equiv a\pmod {q^e},\qquad e\le h,
\]

is either empty or one source cylinder of the same depth \(e\). This follows
digit by digit: the target digit must lie in the \(p\)-element image of the
corresponding shifted source digit map.

If \(\sigma\) is uniform, then for every fixed source \(x\), the random residue
\(F_\sigma(x)\bmod q^h\) is uniform. Consequently, for every target subset
\(D\subseteq\mathbb Z/q^h\mathbb Z\),

\[
\mathbb E_\sigma\,H_{p,h}(F_\sigma^{-1}D)=H_{q,h}(D).
\tag{T2}
\]

Here \(H_{p,h}\) and \(H_{q,h}\) are normalized counting measures. The proof
is finite Fubini:

\[
\mathbb E_\sigma H_{p,h}(F_\sigma^{-1}D)
=\frac1{p^h}\sum_x\Pr_\sigma[F_\sigma(x)\in D]
=\frac{|D|}{q^h}.
\]

The coordinatewise product of (T1)--(T2) gives the same statement for finite
products. No independence assumption on a transported survivor measure is
needed.

## Submeasure form used by source transport

Let (F_\sigma:X\to Y) be the product map above. Suppose that for every
\(\sigma\) there is a submeasure \(\mu_\sigma\) on \(X\) such that

* \(\mu_\sigma(X)\ge m\);
* \(\mu_\sigma\) avoids the pullbacks of all target forbidden cylinders;
* for coordinate \(i\) and every source subset \(A\),
  \(\mu_\sigma(x_i\in A)\le\alpha_iH_{p_i}(A)\).

Define the averaged pushforward

\[
\nu(B)=\mathbb E_\sigma\mu_\sigma(F_\sigma^{-1}B).
\tag{T3}
\]

Then

\[
\nu(Y)\ge m,
\qquad
\nu\text{ avoids every target forbidden cylinder},
\]

and, for every target coordinate subset \(D\),

\[
\nu(y_i\in D)
\le\alpha_i\mathbb E_\sigma H_{p_i}(F_{i,\sigma}^{-1}D)
=\alpha_iH_{q_i}(D).
\tag{T4}
\]

Thus (T3) is a single common transported measure for all attachment estimates;
it is not a product of separately optimized marginal laws. The finite-height
form is sufficient for an original finite covering family: take \(h_i\) at
least the largest original exponent in coordinate \(i\). Projection from an
infinite prime-adic source to these heights preserves both avoidance and the
marginal inequalities.

## Missing-anchor coordinate maps

The source geometry has special coordinates \((3,5)\). The same lemma permits
the following maps, provided the displayed coordinatewise inequalities hold:

| target core profile | source coordinates | target coordinates |
| --- | --- | --- |
| contains \(3,5\) | \((3,5,q_1,\ldots,q_6)\) | \((3,5,r_1,\ldots,r_6)\) |
| contains \(3\), omits \(5\) | \((3,5,q_1,\ldots,q_6)\) | \((3,r_1,\ldots,r_6)\) |
| omits \(3\) | \((3,5,q_1,\ldots,q_6)\) | \((r_0,r_1,\ldots,r_7)\) |

For the first row require \(q_i\le r_i\); for the second require
\(q_i\le r_{i+1}\) and \(5\le r_1\); for the third require
\(q_i\le r_{i+1}\), \(3\le r_0\), and \(5\le r_1\). The first row is the
existing Chapter 31/70 use. The second row transports the source 5-anchor to
an actual first prime \(r_1\ge7\). The third transports both source anchors to
\(r_0\ge5,r_1\ge7\), so it is the missing-3 interface.

The finite checker
[`verify_prefix_transport.py`](../frontier/cover-geometry/verify_prefix_transport.py)
checks fixed-map prefix injectivity and the averaged identity for representative
profiles \((3,5)\to(5,7)\), \((3,5)\to(3,7)\), and a later-coordinate map.
The check is exact finite evidence for (T1)--(T2), not a replacement for the
source theorem or the attachment budget.

## Remaining mathematical gap

The lemma removes the coordinate-map ambiguity from missing-3 and missing-5
cores. It does not close those cores. A new certificate still has to supply,
for every ordered lower-proxy profile, (i) a source mass bound for the pulled
back target family, (ii) the joint marginal cap product, and (iii) a budget for
all possible locations of the omitted small prime and all outside blocks.
The existing Chapter 70 certificate starts its source geometry at an actual
3,5 pair and therefore does not establish these new budgets. In particular,
the finite transport identity cannot be used to transfer a numerical margin
without first proving that the source mass bound is uniform over the pulled
back residue families and that the target attachment decomposition has the
same common realized family.

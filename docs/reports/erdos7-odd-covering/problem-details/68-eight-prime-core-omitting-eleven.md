[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# An eight-prime core omitting 11

This is an ordinary conditional transfer of the Chapter 38 attachment
argument. It is not a Lean theorem and does not claim a solution of
unrestricted Erdős #7. The inherited premises are the actual-domain invariant
(SV2) and conditional-kernel theorem (SV4)--(SV7) of
[Chapter 31](31-seven-vertex-block-noncoverage-with-actual-prime-measures.md),
and the ordinary source construction and transport (SV16)--(SV28), with the
source assumptions recorded in Chapters 30 and 31.

## Conditional core statement

Let a finite family of pairwise distinct odd congruence classes have an
actual prime-interaction block

\[
 S=\{3,5,7,13,17,19,23,29\},
\]

and suppose every other graph block has at most seven vertices. Assume the
inherited Chapter 31 domains for all outside primes and the ordinary source
premises just named. Then the set of complete words on the eight original
core coordinates that avoids every original core class and extends through
all attached blocks has Haar measure greater than
\[
 \frac1{2200000}.
\]

The statement concerns extendible core words. It leaves the unrestricted
problem open.

## Why the Chapter 31 transfer is generic

Root the block-cut tree at `S`. An attached block meets `S` at one parent
prime and has at most six outside children; distinct attached subtrees have
disjoint outside prime sets. This uses only the block-cut decomposition and
the fact that every mixed support is a clique. It does not require 11 to be
in the core.

Every outside prime is at least 11. Since 3 is in `S`, all attached child
domains are in the non-3 induction of Chapter 31. In particular, the child
`q=11` satisfies the same invariant as every `q\ge7`; Chapter 31 does not
use an in-core 11 hypothesis. From (SV2),
\[
 H_q(V_q)\ge1-\frac1{q-1}-\frac{2e_q}{q-1},\qquad e_q<\frac12,
\]
so its cofactor cylinder cap is bounded by \(b_q\le1/(q-3)\), including
`q=11`.

For an attached block with fewer than six children, adjoin fresh independent
dummy coordinates. The Chapter 23 conditional-kernel proof uses only the
actual domain caps and the six-coordinate support polynomial; the real
minimum child is unchanged. Comparison labels are numerical lower proxies,
not labels inserted into the original family. Thus the `s=11` proxy
`(11,13,17,19,23,29)` remains valid even though 13, 17, 19, 23 and 29 are
core vertices. Since all five of those primes are in `S`, an outside minimum
is either 11 or at least 31. After 53, the existing all-large six-child
estimate applies from 59 onward.

The parent comparison is the generic Chapter 23 identity
\[
 K_{p,t}=\frac{2}{p-1}\left(\frac3p\right)^tK_{3,t}.
\]
The source marginal caps below make \(\alpha_pK_{p,t}\le K_{3,t}\) for
every core parent. The attachment costs therefore apply to one transported
measure on the actual family; they are not independently optimized measures.

## Core source row and exact attachment budget

Use the ordinary source row with later proxy primes and integer thresholds
\[
 (q_i)=(7,13,17,19,23,29),\qquad
 (t_i)=(2,4,4,8,8,12).
\]
Each \(q_i>5\) and \(1\le t_i\le q_i-2\), so (SV16) applies. The source
geometry and anchor coordinates remain the same; only these later-prime
parameters change. The exact source calculation gives an unnormalised
survivor measure \(\mu\) with
\[
 m:=\mu(X)=\frac{10237584019}{168750000000},
 \qquad
 \mu\le D H_S,
\]
where
\[
 D=(1)(1)\frac32\frac32\frac43\frac95\frac{11}{7}\frac74
   =\frac{297}{20}.
\]
The eight marginal caps, in the order \((3,5,7,13,17,19,23,29)\), are
\[
 (1,1,3/2,3/2,4/3,9/5,11/7,7/4).
\]

The new conditional-kernel row for an outside minimum 11 uses cutoff
\(t=4\) and the proxy children `(11,13,17,19,23,29)`. Its 64 residuals have
minimum and load numerator
\[
 \min_A Z_A=\frac{9483}{1863680},
 \qquad L=\frac{5801}{116480},
 \qquad k_{11}:=K_{3,4}=\frac{46408}{768123}.
\]
The existing Chapter 38 rows for minima
\(31,37,41,43,47,53\), followed by the all-large tail from 59, give the
shared root budget
\[
 \Delta
 =k_{11}+\sum_{s\in\{31,37,41,43,47,53\}} k_s+2^{-28}
 =0.06041741148121673\ldots .
\]
All displayed residuals are positive. Exact arithmetic gives the convenient
strict bounds
\[
 m>\frac{91}{1500},\qquad
 \Delta<\frac{3021}{50000},\qquad
 m-\Delta>\frac{37}{150000}.
\]

For the new row, the parent ratios \(\alpha_pK_{p,4}/K_{3,4}\), in the
same eight-coordinate order, are
\[
 1,\frac{81}{1250},\frac{81}{4802},\frac{81}{114244},
 \frac{27}{167042},\frac{81}{651605},
 \frac{81}{1958887},\frac{81}{5658248},
\]
all at most one. The ratios for the later rows have the same formula with
larger \(t\), hence are smaller. Distinct attached subtrees have distinct
minimum outside primes, so the union bound on this same \(\mu\) costs at
most \(\Delta\).

After deleting all attached blockers, the surviving source mass is at least
\(m-\Delta\). Since \(\mu\le D H_S\), the extendible core Haar measure is
\[
 \frac{m-\Delta}{D}
 =1.6818388944128326\cdot10^{-5}
 >\frac1{2200000}.
\]
The exact rational computation is reproduced by
[`missing11_core_certificate.py`](../frontier/cover-geometry/missing11_core_certificate.py).
From the repository root, run:

    python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/missing11_core_certificate.py

## Gluing and scope

A surviving core word lies in every actual child domain. Choose an avoiding
extension in each attached subtree at that same word. Their outside prime
sets are disjoint, so the extensions glue; other connected components use
the Chapter 31 root-domain induction. The finite Chinese remainder theorem
then supplies an integer avoiding the original family.

The only non-arithmetic inputs are the inherited Chapter 23/31 conditional
interfaces, the ordinary Schroeder source comparison, and the block-tree
decomposition. No claim is made for arbitrary eight-vertex cores or for the
unrestricted Erdős #7 problem.

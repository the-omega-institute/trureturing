[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Two exact eight-prime cores omitting 7

This is an ordinary conditional transfer using the Chapter 31 actual-domain
invariant and the ordinary source construction. It is not a Lean theorem and
does not claim a solution of unrestricted Erdős #7. The result covers the two
exact core tuples displayed below; a coordinatewise larger tuple can expose a
skipped prime as an outside attachment minimum and requires a separate budget.

The inherited premises are (SV2) and (SV4)--(SV7) of
[Chapter 31](31-seven-vertex-block-noncoverage-with-actual-prime-measures.md),
together with the ordinary source transport (SV16)--(SV28) recorded in
Chapters 30 and 31.

## Conditional core statements

Let all original moduli be pairwise distinct and odd, and suppose every graph
block other than the displayed eight-vertex core has at most seven vertices.
Under the inherited premises, each of the following exact core tuples has
extendible core Haar measure greater than (1/2200000):

\[
 S_7=\{3,5,11,13,17,19,23,29\},
 \qquad
 S_{7,11}=\{3,5,13,17,19,23,29,31\}.
\]

The measure counts core words avoiding all original core classes and admitting
extensions through every attached block.

## Generic transfer and omitted-prime fees

Root the block-cut tree at the selected core. Every attached block has one
core parent and at most six outside children, and distinct attached subtrees
have disjoint outside prime sets. Since 3 is in either core, all child domains
are covered by the non-3 Chapter 31 induction. This remains valid for outside
children 7 and 11; no in-core 7 or 11 assumption is used by (SV2).

Pad an attachment to six children with fresh independent dummy coordinates.
The Chapter 23 kernel uses only actual child-domain caps and numerical proxy
caps. The omitted primes are handled by the Chapter 31 fees rather than by a
new conditional-kernel row. For a core parent \(p\), the transported marginal
cap satisfies \(\alpha_pc_p\le1\) in both rows, where
\(c_3=1, c_5=3/10\), and \(c_p=2/(p-1)\) for \(p\ge7\). Therefore an
outside minimum 7 costs at most \(f(7)=1/8\), and an outside minimum 11 costs
at most \(f(11)=1/24\), on the same transported source measure.

The remaining outside minima are distinct because the attached child sets are
disjoint. Their conditional-kernel costs use the existing rows with minima
31--53 (for \(S_7\)) or 37--53 (for \(S_{7,11}\)), followed by the existing
all-large tail \(2^{-28}\) from 59 onward. No omitted-prime fee is counted as
an independently optimized probability law.

## Source rows and exact budgets

Use thresholds
\[
 (t_i)=(2,4,4,8,8,12).
\]
For \(S_7\), use the exact later-prime row
\[
 (q_i)=(11,13,17,19,23,29).
\]
Its ordinary source gives
\[
 m_7=\frac{7332516433}{56250000000},
 \qquad
 D_7=(1)(1)\frac54\frac32\frac43\frac95\frac{11}{7}\frac74
     =\frac{99}{8}.
\]
The shared deletion budget is
\[
 \Delta_7=\frac18+
 \sum_{s\in\{31,37,41,43,47,53\}}k_s+2^{-28}
 =0.12500000437324055\ldots .
\]
The exact checker gives \(m_7-\Delta_7>0\), and the coarse strict bounds
\[
 m_7>\frac{13}{100},\qquad
 \Delta_7<\frac{63}{500},qquad
 D_7<13
\]
already imply
\[
 \frac{m_7-\Delta_7}{D_7}>\frac1{3250}>\frac1{2200000}.
\]

For \(S_{7,11}\), use the exact later-prime row
\[
 (q_i)=(13,17,19,23,29,31).
\]
Its source gives
\[
 m_{7,11}=\frac{229603051201}{1350000000000},
 \qquad
 D_{7,11}=(1)(1)\frac32\frac43\frac95\frac{11}{7}\frac74\frac53
         =\frac{264}{35}.
\]
The shared budget is
\[
 \Delta_{7,11}=\frac18+\frac1{24}+
 \sum_{s\in\{37,41,43,47,53\}}k_s+2^{-28}
 =0.16666667040378524\ldots .
\]
Here
\[
 m_{7,11}>\frac{17}{100},\qquad
 \Delta_{7,11}<\frac{167}{1000},\qquad D_{7,11}<8,
\]
so
\[
 \frac{m_{7,11}-\Delta_{7,11}}{D_{7,11}}
 >\frac3{8000}>\frac1{2200000}.
\]

The source marginal caps are the products displayed in the two values of
\(D\). Chapter 31's parent comparison
\[
 \alpha_pK_{p,t}/K_{3,t}
 =\frac{2\alpha_p}{p-1}\left(\frac3p\right)^t
\]
is at most one for every displayed conditional-kernel row; the omitted-prime
fees use \(\alpha_pc_p\le1\). Thus each budget is a union bound on one
realized source measure.

The exact rational checks are reproduced by
[`missing7_core_certificates.py`](../frontier/cover-geometry/missing7_core_certificates.py):

    python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/missing7_core_certificates.py

## Gluing and scope

After deleting the attached blockers, a surviving core word lies in every
actual child domain. Disjoint outside prime sets allow the chosen recursive
extensions to glue at that word; other connected components use the Chapter
31 root-domain induction. The finite Chinese remainder theorem then gives an
integer avoiding the original family.

These are exact core results. They do not assert the same budget for a core
whose later primes skip one of the displayed values; such a skip introduces
an additional outside minimum that must be charged explicitly.

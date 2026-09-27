[Index](../../marked_head_profile.md) · [Complete aligned hinges and raw tails](314-complete-aligned-hinges-and-raw-moments-share-one-source.md) · [Eight retained source labels](315-eight-retained-labels-bound-the-aligned-heavy-cost-and-fourth-hinge.md)

# Complete quadratic observations on the actual aligned source

The source is the actual aligned equality endpoint of312, with raw mass1/4,
survivor mass413/2700 and the single late parameter in[1/405,1/270].
Each of the six original observations retains its own independent load,
its own six-label head, and its own two positive-seven profiles. A common
source does not identify their maximizing test choices.

The resulting complete upper bounds, with the full polynomial tails, are:

| Original observation | Exact upper bound | Decimal |
| --- | --- | ---: |
| square | 2565377442951193237/567000000000000000 | 4.524475208026796 |
| factorial2 | 673097/453600 | 1.483899911816579 |
| factorial3 | 1222663/1058400 | 1.155199357520786 |
| factorial5 | 836347/1058400 | 0.790199357520786 |
| cost48 | 14239908700596137297/3969000000000000000 | 3.587782489442212 |
| cost49 | 15450579600948267683/3969000000000000000 | 3.892814210367415 |

## Additional necessary source constraints

The AE3 identity on H is
\[
 \Lambda|_H=\eta\otimes\operatorname{Haar}_H-\zeta,
 \qquad \zeta=I_{27}\times H,\quad |\zeta|=1/135.
\]
For an own quinary descendant of depth b in H, the removed mass is
\(1/(135\,5^{b-1})\). Thus the absolute descendant-five coefficient at
coarse cell(L,H) is2/27, replacing the safe previous1/9 only at that cell.
The five new rows concern the separate own labels25,75,125,225,375.
The own27 and81 caps and every original CRT intersection remain unchanged:
an own ternary descendant can avoid the source's original I27.

AE2 forces every forbidden cofactor5^b or3*5^b with b>=2 to attain its full
raw cap. For pure5^b the nominal normalized coefficient is1/2. Its P,A,B,H
coefficients are at most0,1/6,7/18,25/54, respectively, all strictly smaller.
For3*5^b the nominal coefficient is1/3. The wrong ternary root is at most1/6;
on the correct root its P,A,B,H coefficients are at most0,0,2/9,8/27.
Therefore these forbidden carriers all use Q; the latter family also uses
root1. The complete projected deletion E5, which includes all these forbidden
labels, satisfies
\[
 E_5(c,s)=0\quad(s\ne Q),\qquad
 E_5(c,Q)=\eta_c(1+\operatorname{ROOT}(c))/100.
\]
These20 zero rows supplement the existing five marginal equalities. For
any nonnegative coarse head f, its E5 deletion correction is consequently
\(\sum_c\eta_c(1+\operatorname{ROOT}(c))f(c,Q)/100\), rather than a row minimum.
The five profile rows and20 deletion rows are necessary source constraints;
their relaxation still contains the actual311 limiting-family witness.

## Exact head and assigned tail accounting

Write
\[
 \Phi_k(n)=\tfrac12(n-k)_+(n-k+1)_+,\qquad h_k(n)=(n-k+1)_+.
\]
The unchanged original functions are
\[
\begin{aligned}
 n^2&=1+3(n-1)_++2\Phi_2(n),\\
 F_2&=\Phi_2,\quad F_3=\Phi_3,\quad F_5=\Phi_5,\\
 C_{48}&=5(n-3)_++2\Phi_3(n),\\
 C_{49}&=\tfrac{31}{16}(n-2)_++\tfrac{17}{16}(n-3)_++2\Phi_2(n).
\end{aligned}
\]
Finite transitions and all three coefficients of each infinite quadratic
continuation are checked against the original299 observation definitions.

Let B be the six-label head, K the count of the separate retained labels
25,27,75,81,135,125,225,375, and let Zsel contain pure positive-seven
cofactors at every depth together with cofactors3,5,9,15 at depths1 and2.
The elementary all-integer inequality
\[
 \Phi_k(v+t)\le\Phi_k(v)+h_k(v)t+\binom t2
 \quad(v,t\in\mathbb N)
\]
follows by exact quadratic expansion when v>=k-1, and by monotonicity of
\(\binom t2\) when v<k-1. Apply it after retaining B+K exactly.
For unselected tail factors only, use
\[
 h_k(B+K)\le h_k(B)+K.
\]
The selected term \(h_k(B+K)Z_{\rm sel}\) is retained exactly. Therefore the
new source objective keeps \(\Phi_k(B+K)\) on survivor states and the exact
selected-seven slope on raw states. The only pair-cap payments removed
from the assigned complete series are the28 distinct K-K terms and the72
K-Zsel blocks. No unknown actual moment is subtracted from another bound.
All other old-old, old-positive-seven and positive-seven pairs remain.

Before conditioning PZZ, the complete pair caps from314 are
\[
 P_{OO}=111/800,\qquad P_{OZ}=121/720,\qquad P_{ZZ}=3893/10800.
\]
The selected OO/OZ payments are sums of their explicit survivor/raw LCM caps;
the positive complements are retained in full. The remaining normalized
old-cross weights are
\[
 (1/18,1/20,1/20,1/20,1/72)
 -(1/27+1/81,1/25+1/125,1/25+1/125,1/25,1/135).
\]
After both selected seven depths, each of the four selected base-cofactor
families retains coefficient1/245; the cofactor45 family retains1/5.
All remaining old-cofactor rows also retain their full1/5 series.

## Independent conditional positive-seven pairs

For the own cofactor load at depth e, same-depth pairs have weight
\(a_e=6/(5\,7^e)\). Splitting each unequal-depth product using
\(2uv\le u^2+v^2\) gives the square weight
\[
 b_e=(6e-5)/(10\,7^e).
\]
Thus depths1 and2 have respective pair weights6/35,6/245, and each has
square weight1/70. All higher depths retain pair weight1/245 and square
weight1/210. The checker independently reconstructs all25,000 actual314
raw head endpoints, then conditions each of the first two depths on its
own independent500 four-cofactor profiles, maximizing only the remaining
cofactor45 completion. Their sum plus the complete higher-depth constant
is a necessary PZZ affine bound in the one common late source parameter.
The two profiles need not coincide.

## Full coverage and exact certificates

For each original function, all12,500 head choices and500 choices at each
of the two selected seven depths are retained:3,125,000,000 choices per
observation. The complete head-and-cross affine prefixes include every
infinite exponent tail. A prefix may close only at its own verified whole
function upper. Every remaining choice belongs to exactly one final source
node. A node bounds each physical objective coordinate by its member maximum;
its constant-plus-late-parameter block is bounded at both endpoints, hence
throughout the full interval. Each rational dual is checked against every
one of the12,941 columns of the30,479-inequality,23-equality source model.
The original2,645-step induction re-establishes the4,634 zero columns on this
new matrix before their objective coefficients are omitted.

The delivered certificate keeps only final closed nodes and their used
duals. Its checker regenerates all prefixes and conditional tables, verifies
nonempty original domains and disjoint final subsets, and requires the
covered sets to equal the entire unresolved domain. The final six bounds
are the actual maxima of closed prefix bounds and closed source-node bounds.
Scheduling thresholds do not supply an unchecked conclusion.

These are six complete observations on the aligned equality source. They
do not by themselves assert a403 comparison, an explicit neighborhood,
attainment of a relaxed source maximum, or an unrestricted Erdos7 result.

The [source helper](../../frontier/j-geometry/j_aligned_quadratic_sharp_source.py), [complete checker](../../frontier/j-geometry/j_aligned_quadratic_complete_heads.py), and [certificate](../../certificates/source_norms/j-geometry/j_aligned_quadratic_complete_heads.json) retain1827 final covering nodes and1695 used rational duals. The full check verifies23,643,207 column inequalities. Each of the six observations covers3,125,000,000 original containing choices. The canonical split directory is part of the certificate.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_aligned_quadratic_complete_heads.py --check
```

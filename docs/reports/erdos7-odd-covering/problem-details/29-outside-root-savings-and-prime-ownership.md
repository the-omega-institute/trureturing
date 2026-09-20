[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](28-unique-root-reserve-and-shared-descendant-budget.md)

<a id="outside-root-savings-and-prime-ownership"></a>
# Outside-root savings leave six specified six-vertex cores

Six more of the twelve exceptional child-prime sets in
[Chapter 28](28-unique-root-reserve-and-shared-descendant-budget.md)
are paid by keeping the actual location of a prime outside the core.
If that prime is charged at the root, its whole block has a much smaller
conditional-kernel bound than its nominal fee. If it lies below the core,
its fee belongs to just one actual child subtree. Both facts concern the
same original family and prevent independent worst-case charges.

**Theorem.** Let a finite family have pairwise distinct odd moduli greater
than one, with arbitrary residues and finite prime-power heights. Suppose
**every block of its prime interaction graph has at most six vertices**.
The family is noncovering unless it contains one of the following
six-vertex blocks:
\[
 \{3,5,7,11,13,q\},\quad q\in\{17,19,23,29,31\},
 \qquad \{3,5,7,11,17,19\}.
 \tag{OR1}
\]
Equivalently, excluding these six block sets suffices for noncoverage.
The entries are prime sets, each allowing arbitrary finite original
heights and residues; they are not six finite congruence systems.

This is an ordinary mathematical application of the established
conditional-kernel and coupled first-root inequalities. The exact
arithmetic below does not constitute a new Lean proof or resolve the
remaining six cores or unrestricted Erdős #7.

## 1. A single actual partition of the prime-fee budget

Use the fees and common global majorant from
[Chapter 25](25-six-vertex-block-fees-and-a-finite-prime-core-frontier.md):
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad
 f(11)=\frac1{24},\quad f(13)=\frac1{48},\qquad
 f(q)=2^{-(q-1)/2}\ (q\ge17),\qquad
 \sum_{q\ge5\text{ prime}}f(q)\le F_*:=\frac{1493}{3072}.
 \tag{OR2}
\]
All exceptional blocks in Chapters 25 and 28 contain \(3,5,7\).
Distinct graph blocks share at most one vertex, so at most one such block
can occur. Root its component at 3; let \(K\) be this exceptional block
and \(J\) its five child primes. Put
\[
 C=\sum_{q\in J}f(q),\qquad E=F_*-C,\qquad M=\frac12-E,
 \qquad x=\sum_{q\in J}e_q,\quad
 e_q=\sum_{r\in D_q}f(r),
 \tag{OR3}
\]
where \(D_q\) is the actual strict descendant set of \(q\).
These sets are mutually disjoint and avoid \(J\), hence \(0\le x\le E\).
Every non-3 descendant block already has its certified recursive fee.
Thus the actual child domains satisfy
\[
 H_q(V_q)\ge1-\frac1{q-1}-c_qe_q,
 \qquad c_5=\frac3{10},\quad c_q=\frac2{q-1}\ (q\ge7).
 \tag{OR4}
\]
All coordinates are the original complete prime-power coordinates.
The sets \(V_q\), conditioned product laws, and literal cylinders are
those of [Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md).

Let \(T\) be the sum of nominal fees of all immediate children of the
other blocks at root 3. These children are distinct and avoid both
\(J\) and the core descendants, so
\[
 C+x+T\le F_*,\qquad T\le E-x.
 \tag{OR5}
\]
Writing \(B_K\) for the block-only blocker, the root recursion and the
pure-3 bound give
\[
 H_3(V_3)\ge M+x-H_3(B_K).
 \tag{OR6}
\]
The density and expense bounds refer to one actual family. The root
reserve is not a new general recursive block fee.

## 2. A prime outside the core gives a strict root saving

Choose a prime \(p\ge5\) outside \(J\), and in the six cases below
choose it to be the smallest such prime. Let
\(q_1<\cdots<q_5\) be the five smallest primes at least 5 outside
\(J\), so \(q_1=p\). All these proxies are at least 11. Define
\[
 \bar b_i=\frac1{q_i-2-2E},\quad
 \bar b_S=\prod_{i\in S}\bar b_i,\quad
 w_S=\begin{cases}0,&|S|=1,\\\bar b_S,&|S|\ge2.\end{cases}
\]
For every coordinate subset \(A\), let
\[
 Z_A(v)=\sum_{\mathcal F}(-1)^{|\mathcal F|}
                           \prod_{S\in\mathcal F}v_S,
\]
where \(\mathcal F\) ranges over all families of pairwise-disjoint
nonempty supports inside \(A\), including the empty family.
For a cutoff \(t\), put
\[
 v_t=w+t\bar b,\qquad
 L_t=\sum_{S\ne\varnothing}\bar b_SZ_{[5]\setminus S}(v_t),
 \qquad K_p=\frac{L_t}{2\cdot3^tZ_{[5]}(v_t)}.
 \tag{OR7}
\]
Assume every nonempty coordinate residual is positive and
\(K_p<f(p)\). Write \(s_p=f(p)-K_p>0\).

Suppose \(p\) is not a strict descendant of the core. If \(p\) is not
an immediate child of another root block, its fee does not occur in
\(C+x+T\). Adding it still gives a sum of distinct prime fees bounded
by \(F_*\), even if \(p\) is absent from the original family. Therefore
\(T\le E-x-f(p)\). This case includes \(p\) in another component or
deeper inside an outside subtree.

Otherwise, \(p\) is an immediate child of exactly one other root block
\(L\). This block and \(K\) already share 3, so \(L\) contains no
prime in \(J\). It has at most five children; its sorted children
dominate the corresponding \(q_i\). Every child of \(L\) has strict
descendant fee at most \(E\). The proxy caps therefore dominate the
actual event caps. If there are fewer than five children, unused
coordinates with zero actual events embed the smaller support graph;
positive proxy caps and the full strict residual test still dominate it.
Chapter 23 (CK12), at parent 3, gives \(H_3(B_L)\le K_p\) on the
original root Haar law.

If \(C_L\) is \(L\)'s actual immediate-child fee, then \(C_L\ge f(p)\).
Replacing only this block's nominal charge gives
\[
 \sum_{L'\ne K}H_3(B_{L'})\le T-C_L+K_p
                  \le E-x-f(p)+K_p=E-x-s_p.
 \tag{OR8}
\]
Both cases thus provide
\[
 H_3(V_3)\ge M+x+s_p-H_3(B_K)
       \quad\text{if }p\notin\bigcup_{q\in J}D_q.
 \tag{OR9}
\]
No proxy fee is subtracted: proxies bound coordinate caps, whereas
\(C_L\) contains the real child fees.

If \(p\) is a core descendant, then \(x\ge f(p)>s_p\), and the
unchanged (OR6) applies. Combining the two possibilities shows that
\[
 H_3(B_K)<M+s_p
 \tag{OR10}
\]
is a sufficient criterion without identifying where \(p\) occurs.
This saves the outside fee only when legitimate; when the fee is inside
the core, its actual contribution to \(x\) supplies the alternative gain.

## 3. Five fixed-cap certificates

For coordinate expense bounds \(u_q\ge e_q\), use
\[
 b_5(u_5)=\frac1{3-(6/5)u_5},\qquad
 b_q(u_q)=\frac1{q-2-2u_q}\quad(q\ge7),\qquad
 b_S=\prod_{q\in S}b_q(u_q).
 \tag{OR11}
\]
Let \(w_S=0\) on singletons and \(w_S=b_S\) otherwise, and set
\(L_0=\sum_{S\ne\varnothing}b_SZ_{J\setminus S}(w)\).
For target \(A\in(1/3,2/3)\), the same coupled first-root test as
Chapter 28 is
\[
 \Delta(b,A)=\min_{0\le y\le b}
 \left\{\frac13Z_J(w+y)
       +\left(A-\frac13\right)Z_J(w+b-y)\right\}-\frac{L_0}{6}>0.
 \tag{OR12}
\]
Together with \(Z_U(w+b)>0\) for all nonempty \(U\subseteq J\),
this proves \(H_3(B_K)<A\) on the actual child domains. Its proof only
requires dominating coordinate caps, not a common expense value; it
also applies to the unequal caps in Section 4.

The certificate sets every \(u_q=E\) and \(A=M+s_p\) for these rows:

| Core children \(J\) | Outside proxy children | \(t\) | Certified \(\Delta\) lower bound |
| --- | --- | ---: | ---: |
| \(5,7,11,17,23\) | \(13,19,29,31,37\) | 7 | \(1/3000\) |
| \(5,7,11,19,23\) | \(13,17,29,31,37\) | 7 | \(1/200\) |
| \(5,7,13,17,19\) | \(11,23,29,31,37\) | 6 | \(1/250\) |
| \(5,7,13,17,23\) | \(11,19,29,31,37\) | 6 | \(3/250\) |
| \(5,7,13,19,23\) | \(11,17,29,31,37\) | 6 | \(1/60\) |

Each tabulated inequality is strict. All outside and core residuals
are positive, and every displayed target lies in \((1/3,2/3)\).
For example, the last row has \(E=283/6144\) and
\[
 K_{11}=\frac{8539713821846668274176}{6519544451327078732269935},
 \qquad
 s_{11}=\frac{2104863773200919564563237}{52156355610616629858159480}.
\]
The exact minimum is
\[
 \Delta=\frac{5737020794755207668640503688400626009729842166157}
 {339296990315305372241968437983599306312747731179520}>\frac1{60}.
\]

## 4. The actual owner of prime 17 pays one more core

For \(J=(5,7,11,13,37)\), use
\[
 E=\frac{1791}{262144},\qquad p=17,\qquad f(p)=\frac1{256}.
\]
The outside proxy is \((17,19,23,29,31)\), with cutoff \(t=9\).
Equation (OR7) and the certificate give
\[
 K_{17}=\frac{258807378351277136528552296448}
              {4435795902041787312429934224490695}<f(17).
\]

If 17 is not a core descendant, adding its distinct fee to \(C+x\)
gives \(x\le E-f(17)\). Equation (OR9) applies throughout this branch.
Use \(u_q=E-f(17)\) for all five children and \(A=M+s_{17}\).
The full (OR12) minimum is strictly positive.

If 17 is a core descendant, it belongs to exactly one set \(D_q\).
For this actual owner \(q\),
\[
 f(17)\le x\le E,\qquad e_q\le x,\qquad
 e_r\le x-f(17)\quad(r\ne q).
 \tag{OR13}
\]
For a closed interval \([a,b]\subseteq[f(17),E]\), set the owner
expense cap to \(b\), all other expense caps to \(b-f(17)\), and the
target to \(A=M+a\). These caps dominate the actual domains, while
\(A\le M+x\) is allowed by (OR6). The following subdivisions cover
the whole interval for every possible owner:
\[
 a_0=\frac1{256},\qquad a_1=\frac{4863}{1048576},\qquad
 a_2=\frac{2815}{524288},\qquad a_3=\frac{1791}{262144}.
\]

| Owner | Closed intervals |
| --- | --- |
| 5 | \([a_0,a_1],[a_1,a_2],[a_2,a_3]\) |
| 7 | \([a_0,a_2],[a_2,a_3]\) |
| 11 | \([a_0,a_2],[a_2,a_3]\) |
| 13 | \([a_0,a_2],[a_2,a_3]\) |
| 37 | \([a_0,a_3]\) |

All ten intervals have positive full residuals and \(\Delta>1/25000\).
The no-owner certificate and these five exhaustive ownership cases pay
this sixth additional core. The assignment is a fact about the actual
block tree, not an independently chosen favorable distribution of fees.

## 5. Scope and complete remaining list

Chapter 28 paid 38 of Chapter 25's 50 core types. The five rows in
Section 3 and the distinct row in Section 4 pay six more, leaving exactly
the six sets in (OR1). This proves the stated theorem by the original
root recursion: the positive root surviving set admits avoiding witnesses
through disjoint private block sides, and other components glue by CRT.
All original modulus labels, residues and prime-power coordinates remain
in that construction, so it yields a residue avoiding the original
family, hence positive original Haar uncovered mass on its finite period.

The outside proxy in this chapter uses the hypothesis that every graph
block has at most six vertices. Allowing larger outside blocks requires
a new bound for their additional children; it does not follow merely
because some larger blocks have previously certified nominal fees.
The result does not improve a universal local fee or spend a root
reserve at multiple exceptional blocks. No optimality or covering
construction is claimed for the six remaining core types. Dense larger
blocks and unrestricted Erdős #7 remain unresolved. The additional
literal-residue criteria of
[Chapter 26](26-literal-pure-classes-and-six-vertex-residue-branches.md)
remain available on the same families.

## 6. Standalone exact certificate

The standard-library program
[outside_root_savings_certificate.py](../frontier/cover-geometry/outside_root_savings_certificate.py)
and its [exact data](../frontier/cover-geometry/outside_root_savings_certificate.json)
recompute the six outside-kernel bounds, the five fixed-cap core tests,
the no-owner test, and all ten assigned-owner interval tests. No external
input or imported certificate program is needed.

Each core test records every strict residual and derivative margin,
forced/free support sets, the full corner count, the minimizing allocation,
its two exact residual values, the minimum objective, \(L_0\), and
\(\Delta\). The objective is multi-affine. A positive derivative margin
\(\frac13Z_{J\setminus S}(w+b)-(A-\frac13)Z_{J\setminus S}(w)\)
forces the minimizing coordinate to its upper endpoint; all remaining
corners are evaluated exactly. Disjoint-support expansion uses integer
coefficients after clearing denominators, and each minimizing residual
is independently reevaluated. The program checks interval adjacency,
endpoints, the six additional rows, and the exact 12-to-6 partition.

An independent calculation using elementary-symmetric residuals and
integer subset recurrence reproduces all six outside bounds and all
sixteen core minima, including the ownership intervals. The mathematical
same-family budget, conditional-law and graph-recursion premises remain
ordinary proofs. Python 3.10 or later is required; optimized `-O`
execution is rejected. Reproduce the JSON from the repository root with

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/outside_root_savings_certificate.py --output /tmp/outside-root-savings-certificate.json
```

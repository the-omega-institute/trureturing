[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="conditional-kernels-and-recursive-block-noncoverage"></a>
# Conditional kernels close all five-vertex blocks and an unbounded block regime

Every five-vertex block admits the established descendant-compatible fee,
with no restriction on its original residue choices or finite prime-power
heights. These blocks may occur arbitrarily many times below one another.
There is also a compatible class of blocks of unbounded size: a block with
\(k\ge4\) children is admissible whenever its smallest child prime \(s\)
satisfies
\[
 s\ge k(k+3)+3.
 \tag{CK1}
\]
Every original support, including a modulus involving the entire block,
remains present.

More precisely, consider a finite family of arithmetic progressions with
distinct odd moduli greater than one. Form its original prime-interaction
graph, joining primes which occur together in an original modulus. Root
the block-cut tree of each connected component at prime 3 when that prime
is present, and at any prime otherwise. Then all child primes are at least
5. Suppose every nontrivial block is an edge, a simple cycle, a block on at
most five vertices, or a larger oriented block satisfying (CK1). The
family does not cover the integers.

The number of blocks, their depth, all original exponents, and the number
of distinct primes are unbounded. The condition is on the graph's blocks;
it is not merely a bound on the number of prime factors in an individual
modulus. In particular, the result does not prove unrestricted Erdős #7.
Dense larger blocks with small child primes remain outside the theorem.

The proof uses ordinary mathematics and exact rational certificates. It
is not a Lean-certified result. Its essential local estimate is
\[
 H_p(B)\le\frac{L_t}{p^t(p-1)Z_t},
 \tag{CK2}
\]
where both \(L_t\) and \(Z_t\) are evaluated after the same shallow
cutoff. The conditional child law is the actual law of the shallow
survivors at each complete parent word. Its parent marginal remains the
original Haar law; it is not replaced by a product with a fixed child
marginal.

## 1. The unchanged induction and original block fibres

Use the original full coordinates
\(X_p=\mathbb Z/p^{h_p}\mathbb Z\), with their uniform laws \(H_p\).
For a prime vertex \(p\), let \(V_p\) be the set of words admitting an
avoiding extension through its full descendant subtree, including
avoidance of its original pure prime-power classes. For a block with
parent \(p\) and child set \(J\), its blocker \(B\subseteq X_p\)
consists of words which have no avoiding child tuple in
\(\prod_{q\in J}V_q\). Parent-pure classes are excluded from this
block-only definition and charged separately.

Retain the fees and density invariant of
[the four-vertex-block theorem](06c-four-vertex-blocks-and-cycle-breaking-vertices.md#four-vertex-blocks-with-a-common-descendant-budget):
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad
 f(11)=\frac1{24},\quad f(13)=\frac1{48},\qquad
 f(q)=2^{-(q-1)/2}\quad(q\ge17),
\]
\[
 \sum_{q\ge5\text{ prime}}f(q)\le F:=\frac{187}{384}<\frac12,
 \qquad c_5=\frac3{10},\quad c_p=\frac2{p-1}\quad(p\ge7),
 \tag{CK3}
\]
\[
 H_q(V_q)\ge1-\frac1{q-1}-c_qe_q,
 \qquad e_q=\sum_{r\in D_q}f(r).
 \tag{CK4}
\]
Here \(D_q\) is the actual strict descendant prime set. Child descendant
sets are disjoint and avoid the entire current block. They are not
independently supplied copies of an outside budget.

The local claims below assume (CK4) only for the actual child domains.
They do not assume that these domains were constructed using only older
block types. Section 6 closes the enlarged induction.

For a positive density lower bound \(d_q\le H_q(V_q)\), put
\[
 b_q=\frac1{(q-1)d_q},\qquad b_S=\prod_{q\in S}b_q,
 \qquad \nu=\bigotimes_{q\in J}H_q(\cdot\mid V_q).
\]
For an original literal child cylinder \(C_d\) on support \(S\), where
\(d=\prod_{q\in S}q^{a_q}\),
\[
 \nu(C_d)\le\prod_{q\in S}\frac{q^{-a_q}}{d_q}.
 \tag{CK5}
\]
Summing over its positive child exponent vectors gives \(b_S\).
At each fixed parent exponent \(a\), an original complete child cofactor
occurs at most once globally across all parent residues, because the
original modulus \(p^ad\) occurs at most once. The same cofactor may occur
at different parent exponents, which correspond to different original
moduli.

## 2. A dominating support vector and actual conditional kernels

The following argument also permits any convenient coordinate bounds
\(\bar b_q\ge b_q\). Define
\[
 \bar b_S=\prod_{q\in S}\bar b_q,
 \qquad w_S=\begin{cases}0,&|S|=1,\\\bar b_S,&|S|\ge2.\end{cases}
\]
The old internal mixed classes on a complete support have union
probability at most \(w_S\) under \(\nu\). Old pure child classes are
already avoided inside \(V_q\).

For \(A\subseteq J\), let
\[
 Z_A(v)=\sum_{\substack{\mathcal F\text{ a family of pairwise-disjoint}\\
                        \text{nonempty supports in }A}}
             (-1)^{|\mathcal F|}\prod_{S\in\mathcal F}v_S,
 \qquad Z_\varnothing=1.
 \tag{CK6}
\]
For an integer cutoff \(t\ge0\), set
\[
 v_t=w+t\bar b,\qquad Z_t=Z_J(v_t),\qquad
 L_t=\sum_{S\ne\varnothing}\bar b_SZ_{J\setminus S}(v_t).
 \tag{CK7}
\]
Assume every nonempty coordinate residual is positive:
\[
 Z_A(v_t)>0\quad(\varnothing\ne A\subseteq J).
 \tag{CK8}
\]
This verifies the whole strict Shearer region, not just the top
polynomial. For the support-intersection graph, the atom of an
independent support family \(\mathcal I\) is
\[
 \left(\prod_{S\in\mathcal I}v_{t,S}\right)
 Z_{J\setminus\bigcup\mathcal I}(v_t).
\]
All atoms are nonnegative and the empty atom is positive. Summing the
atoms which avoid a specified graph-vertex set proves strict positivity
of every induced avoidance polynomial. This is the same support argument
used in [the first-root theorem](21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md).

Fix a complete original parent word \(x\). Let \(R_x\) avoid all old
internal classes and all crossing classes at parent exponents
\(1,\ldots,t\) whose parent prefixes match \(x\). If \(t>h_p\), there are no original
labels at exponents above \(h_p\); those shallow levels contribute
empty event families. Thus the construction stays on the original full
parent coordinate and includes every original height.

Group the actual avoided events by their complete child supports. At
each shallow exponent, a fixed cofactor contributes at most once. Thus
the actual group on \(S\) has \(\nu\)-probability at most
\(w_S+t\bar b_S=v_{t,S}\). Groups with disjoint supports depend on
disjoint coordinates under the actual product law \(\nu\).
Scott–Sokal,
[arXiv:cond-mat/0309352v2, Theorem 4.1(a) and conditional inequality (4.3)](https://arxiv.org/html/cond-mat/0309352v2),
therefore applies with this fixed dominating vector. Its conditional
nonneighbor probability hypothesis follows from that product
independence, and its strict-region hypothesis is (CK8).
In particular, \(\nu(R_x)\ge Z_t>0\) for every \(x\).

Let \(R\) avoid only the old internal classes. Since \(R_x\subseteq R\),
\(\nu(R)>0\), and all conditional laws below are actual:
\[
 \mu=\nu(\cdot\mid R),\qquad
 \mu_x=\mu(\cdot\mid R_x)=\nu(\cdot\mid R_x).
 \tag{CK9}
\]
For a literal cylinder \(C\) on support \(S\), let \(R_{x,S}^{\rm out}\)
avoid only the groups with supports disjoint from \(S\). Then
\[
 \nu(C\cap R_x)\le\nu(C)\nu(R_{x,S}^{\rm out}),
\]
by independence under \(\nu\), and the conditional Shearer inequality
at the same dominating vector gives
\[
 \frac{\nu(R_x)}{\nu(R_{x,S}^{\rm out})}
 \ge\frac{Z_t}{Z_{J\setminus S}(v_t)}.
\]
Consequently
\[
 \mu_x(C)\le\nu(C)\frac{Z_{J\setminus S}(v_t)}{Z_t}
 \quad\text{for every original parent word }x.
 \tag{CK10}
\]
This is a ratio of related avoidance events under one actual product law;
it is not a division of unrelated lower bounds.

If \(x\) is fully blocked, every point of \(R_x\) must hit some matching
crossing class of parent exponent greater than \(t\). Thus
\[
 \mathbf1_B(x)\le
 \sum_{\ell:\,a(\ell)>t}
   \mathbf1_{\{x\text{ matches the parent prefix of }\ell\}}\,
   \mu_x(C_\ell).
 \tag{CK11}
\]
Integrate over the original \(H_p\). A parent cylinder of exponent
\(a\) has measure \(p^{-a}\); (CK10) is uniform in \(x\); and the
complete original cofactor sum at that exponent is bounded by
\(\bar b_S\), globally across all its residues. Hence
\[
 H_p(B)\le\frac{L_t}{Z_t}\sum_{a>t}p^{-a}
          =\frac{L_t}{p^t(p-1)Z_t}=:K_{p,t}.
 \tag{CK12}
\]
The actual finite deep sum is bounded by the displayed convergent
infinite sum. No original class is split into prime-divisor substitutes.

The joint law \(H_p(dx)\mu_x(dy)\) need not equal \(H_p\times\mu\).
The proof uses its original parent marginal and the pointwise uniform
cylinder bound (CK10). The bound concerns a full-parent blocker, so this
conditional construction is sufficient; it is not an assertion about the
full surviving Haar density.

Using a larger \(\bar b\) does not require a new monotonicity theorem for
ratios of support polynomials. It is directly a valid dominating event
cap in the conditional probability theorem. This observation will carry
the finite rows over their entire infinite prime ranges.

## 3. All four-child tuples: a complete finite-to-infinite partition

For a common expense bound \(e_q\le E\), (CK4) gives the coordinate caps
\[
 b_5(E)=\frac1{3-(6/5)E},\qquad
 b_q(E)=\frac1{q-2-2E}\quad(q\ge7).
 \tag{CK13}
\]
Take
\[
 P_0=\{5,7,11,13,17,19,23,29\}.
\]
Suppose a four-child tuple has \(j\in\{1,2,3,4\}\) primes in \(P_0\).
Write these actual small primes in increasing order, and put
\[
 C=\sum_{q\in J\cap P_0}f(q),\qquad E=F-C.
 \tag{CK14}
\]
All actual child expenses are at most \(E\). In forming this bound the
fees of every larger child have deliberately been omitted. Thus making
a large child still larger, and thereby reducing its fee, cannot
invalidate the chosen rectangle.

Replace the remaining sorted children by the lower odd-integer proxies
\(31,33,35\), as many as needed. Actual larger primes dominate these
proxies, and the cap formula (CK13) decreases with its prime argument.
The four proxy caps at expense \(E\) therefore provide the dominating
vector \(\bar b\) for every actual tuple in that row. The proxies need
not be prime and are not asserted to be simultaneously realized by an
original AP system.

The exact certificate establishes the following exhaustive partition:

| Small children \(j\) | Boundary rows | Rows paid by (CK12) | Separate KR inputs |
| ---: | ---: | ---: | ---: |
| 4 | 70 | 68 | 2 |
| 3 | 56 | 56 | 0 |
| 2 | 28 | 28 | 0 |
| 1 | 8 | 8 | 0 |

Every one of the 160 kernel rows has a selected cutoff \(t\ge1\), all
fifteen residuals in (CK8) positive, and \(K_{3,t}<C\). The largest
selected cutoff is 7. The greatest cost-to-charge ratio is exactly
\[
 \max\frac{K_{3,t}}C
 =\frac{65157018363904}{65378462038225}<1,
 \tag{CK15}
\]
at the proxy tuple \((11,13,31,33)\), with \(C=1/16\) and \(t=1\).
The data record every row, residual, selected cutoff, and positive fee
margin.

For example, the two tuples treated by
[the two-layer theorem](22-two-layer-profiles-for-two-further-five-prime-blocks.md)
also satisfy the following direct conditional-kernel bounds on the same
descendant rectangles:

| Children | Assigned fee | \(K_{3,1}\) |
| --- | ---: | ---: |
| \(5,11,13,17\) | \(275/768\) | \(1213357059200/4469079776649\) |
| \(7,11,13,17\) | \(49/256\) | \(7799081075968/50716879766737\) |

The kernel bound's positive fee margins in these rows are respectively
\(99046239037625/1144084422822144\) and
\(488562353122305/12983521220284672\). These examples do not replace
the exhaustive partition above.

When all four children are at least 31, Section 5 applies with \(k=4\),
since \(4(4+3)+3=31\). This supplies the only remaining infinite range.

## 4. The two first-root inputs and non-3 parents

The two rows not paid by the parent-3 kernel bound are
\((5,7,11,13)\) and \((5,7,11,17)\). They use the coupled first-root
inequality (KR14) from
[Chapter 21](21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md).
Its proof assumes actual child densities and a shared original
exponent-one allocation. It does not require that the domains were
produced only by older block types.

For completeness, the precise two inputs are:

| Children | Child fee sum \(C\) | Outside bound \(E=F-C\) | Blocker upper threshold \(M\) |
| --- | ---: | ---: | ---: |
| \(5,7,11,13\) | \(23/48\) | \(1/128\) | \(15/32\) |
| \(5,7,11,17\) | \(355/768\) | \(19/768\) | \(355/768\) |

The blocker mass is strictly less than the threshold in either row.
For the second input the caps, in child-prime order, are
\[
 \bar b=\left(\frac{640}{1901},\frac{384}{1901},
              \frac{384}{3437},\frac{384}{5741}\right).
 \tag{CK16}
\]
All residuals at \(w+\bar b\) are positive. The first-root saturation
inequality would require
\[
 \min_{0\le y\le\bar b}
 \left\{\frac13 Z_J(w+y)
       +\left(M-\frac13\right)Z_J(w+\bar b-y)\right\}
 \le\frac{L_0}{6}
 \tag{CK17}
\]
if the blocker had mass at least \(M\). The unused shared budget may be
assigned to the two active roots because every relevant residual is
positive. Write the expression in braces as \(H(y)/d\), where
\[
 (a,c,d)=(32,13,96)\quad\text{or}\quad(256,99,768),
 \qquad H(y)=aZ_J(w+y)+cZ_J(w+\bar b-y)
\]
for the first and second row, respectively. Its support derivative has
the uniform upper bound
\[
 \frac{\partial H}{\partial y_S}
 \le-aZ_{J\setminus S}(w+\bar b)+cZ_{J\setminus S}(w).
\]
For each row, this is strictly negative on thirteen of the fifteen
supports. Precisely the two singleton support masks 4 and 8 remain free,
with masks in increasing child-prime order. The smallest positive values
of \(aZ_{J\setminus S}(w+\bar b)-cZ_{J\setminus S}(w)\) over the
thirteen forced supports are respectively
\[
 \frac{61587}{101761}>0,\qquad
 \frac{30446693}{3613801}>0.
\]
Assigning these thirteen supports to the first root therefore minimizes
the expression. It is separately affine in the two remaining singleton
allocations, so only their four corners remain. The certificate records
all thirteen derivative margins and all four corner values for each row.

The exact positive gaps between the left minimum and \(L_0/6\) are
\[
 \frac{51066292103}{11846689984800}
 \quad\text{for }(5,7,11,13),\qquad
 \frac{831018050567443}{54763668484928256}
 \quad\text{for }(5,7,11,17).
 \tag{CK18}
\]
The first is the stronger \(M=15/32\) certificate of Chapter 21. The
second is a separate numeric input to (CK17). Among the four remaining
corners, the minima occur at support vertices 32631 and 32639 respectively,
when support masks \(1,\ldots,15\) occupy bits \(0,\ldots,14\).
Direct disjoint-family summation evaluates every corner. Thus both
parent-3 rows pay at most their child fee sums.

For the 160 kernel rows, the exact parent comparison is
\[
 K_{p,t}=\frac2{p-1}\left(\frac3p\right)^tK_{3,t}.
 \tag{CK19}
\]
Because every selected \(t\ge1\), this factor is at most \(c_5=3/10\)
when \(p=5\), and at most \(c_p=2/(p-1)\) when \(p\ge7\). Hence
these rows pay at most \(c_pC\) under every permitted non-3 orientation.

The two KR rows have a separate non-3 argument; a parent-3 blocker fee
is not transferred between parent primes. Their valid \(t=1\) kernel
values are
\[
 K_{3,1}=\frac{28317138496}{51430917897}<1,
 \qquad
 K_{3,1}=\frac{16623382411648}{34891795286835}<1,
 \tag{CK20}
\]
respectively. A non-3 parent distinct from the first tuple is at least17;
for the second it is at least13. In both cases \(C>1/3\), so
\[
 \frac{K_{p,1}}{c_p}=\frac3p K_{3,1}
 <\frac3{13}<\frac13<C.
 \tag{CK21}
\]
The parent prime cannot be5 in either row because5 is already a child.
This proves the needed non-3 bounds.

Combining these cases, every oriented five-vertex block under the stated
rooting convention satisfies
\[
 H_p(B)\le
 \begin{cases}
 \sum_{q\in J}f(q),&p=3,\\
 c_p\sum_{q\in J}f(q),&p\ge5.
 \end{cases}
 \tag{CK22}
\]
The child-prime restriction \(q\ge5\) follows from the rooting
convention. No claim about an unnecessary orientation with child3 and
parent different from3 is used.

## 5. A uniform theorem for arbitrarily many children

Let \(k\ge4\), \(s=\min J\ge k(k+3)+3\), and
\[
 t=\frac{s-3}{2}\ge t_0:=\frac{k(k+3)}2.
 \tag{CK23}
\]
Since every child expense is at most \(F<1/2\), (CK13) gives
\[
 b_q\le\frac1{q-3}\le\frac1{2t}.
 \tag{CK24}
\]
All child primes in this section are at least31.

At a fixed complete parent word, first avoid only the shallow crossing
classes of singleton child support. These deletions are coordinatewise.
The resulting actual child law is a product law, and each coordinate has
relative survival at least \(1-tb_q\ge1/2\). Set
\[
 u_q=\frac{b_q}{1-tb_q}\le\frac1t,\qquad
 A=\prod_{q\in J}(1+u_q)-1,\qquad U=\sum_{q\in J}u_q,
 \qquad\Lambda=(t+1)(A-U).
 \tag{CK25}
\]
Under that actual product law, the union of old internal mixed classes
and all shallow mixed crossing classes has probability at most
\(\Lambda\). There is one old copy and at most \(t\) shallow copies
of each complete mixed-support cap. The full \(k\)-child support is
included in \(A-U\).

If \(\Lambda<1\), the actual complete shallow-survivor law exists for
every parent word. Conditioning on the mixed avoidance set increases
each deep cylinder cap by at most \(1/(1-\Lambda)\). Summing the
original cofactor budgets and integrating over original parent Haar,
exactly as in (CK11)–(CK12), gives
\[
 H_p(B)\le\frac{A}{p^t(p-1)(1-\Lambda)}.
 \tag{CK26}
\]
This large-child argument uses only product conditioning and union
bounds; it does not require a Shearer strict-region certificate at this
cutoff.

Put \(D=(1+1/t)^k-1-k/t\). Nonnegative coefficients yield
\[
 A+\Lambda=U+(t+2)(A-U)\le\frac kt+(t+2)D.
\]
Starting with degree2, consecutive binomial terms in \(D\) have ratios
at most \((k-2)/(3t)<1\), so
\[
 D\le\frac{k(k-1)}{2t^2(1-(k-2)/(3t))}.
 \tag{CK27}
\]
The denominator \(2t(3t-k+2)\) is positive. After clearing it, the
resulting upper bound for \(A+\Lambda\) is below1 exactly when
\[
 P_k(t):=6t^2+(4-5k-3k^2)t-4k^2+2k>0.
 \tag{CK28}
\]
At the permitted starting point,
\[
 P_k(t_0)=2k(k^2+2k+4)>0,\qquad
 P_k'(t_0)=3k^2+13k+4>0,\qquad P_k''=12.
 \tag{CK29}
\]
These identities prove (CK28) for every \(k\ge4\) and \(t\ge t_0\).
They are not a finite test in \(k\). Therefore \(A+\Lambda<1\), which
establishes both \(\Lambda<1\) and \(A/(1-\Lambda)<1\). Equation
(CK26) gives
\[
 H_3(B)<\frac1{2\cdot3^t}<2^{-(t+1)}=f(s).
 \tag{CK30}
\]
The same comparison factor as (CK19), with \(t\ge1\), proves
\(H_p(B)<c_pf(s)\) for every non-3 parent. The charge is assigned to
the actual smallest immediate child \(s\).

## 6. The enlarged recursion and full original-Haar noncoverage

Proceed from the leaves upward in the actual finite rooted block-cut
tree, assuming (CK4) for every child domain. The existing local edge,
cycle and four-vertex proofs apply: their hypotheses are the actual child
densities and disjoint descendant budgets, not a restriction on how those
domains were produced. In particular (FB8) follows from (CK4), and supplies
their required uniform child density. For a five-vertex block use (CK22);
for a qualifying larger block use (CK30) and its non-3 comparison.

Each assigned charge uses a subset of that block's actual immediate
child primes. Different outgoing blocks have disjoint child sets, and all
charged primes lie in the parent's strict descendant set \(D_p\).
Let \(P_p\) denote the original pure \(p\)-power forbidden set. For a
child graph block \(K\), write \(\mathcal B_{K\to p}\) for its blocker
on the original parent coordinate. The exact block recursion is
\[
 V_p=X_p\setminus\left(P_p\cup
          \bigcup_{K\text{ child block of }p}\mathcal B_{K\to p}\right),
 \qquad H_p(P_p)\le\frac1{p-1}.
 \tag{CK31}
\]
For a nonroot prime \(p\ge5\), the union bound therefore gives
\[
 H_p(V_p)\ge1-\frac1{p-1}-c_p\sum_{q\in D_p}f(q),
\]
which is exactly (CK4). Leaves give the base case with empty descendant
set. Thus the enlarged block class proves its own density induction;
it does not assume a new-block descendant bound in advance.

At a root3,
\[
 H_3(V_3)\ge1-\frac12-F=\frac5{384}>0.
 \tag{CK32}
\]
At a root at least5, the same density argument and (FB8) give a positive
domain. Choose an actual root word in that domain and glue actual block
and descendant witnesses at that same word. Private block sides are
disjoint; no product of separately averaged extension proportions is used.
Finally combine distinct connected components by CRT.

When prime3 occurs, let
\(Q_{\mathrm{off}}=\prod_{p\ne3}p^{h_p}\) over all prime coordinates of
the original family, including every other connected component. Every
extendable root3 word has at least one avoiding extension in its component;
choose one avoiding witness in each other component. Hence every such
root word has at least one full original extension, so
\[
 U_{\mathrm{full}}\ge\frac{H_3(V_3)}{Q_{\mathrm{off}}}
             \ge\frac5{384Q_{\mathrm{off}}}>0.
 \tag{CK33}
\]
The reserve \(5/384\) concerns the root coordinate. It is not a uniform
lower bound for full uncovered density independent of the period. If
prime3 does not occur, the witness construction still gives at least one
uncovered residue modulo the original common period \(Q\), hence full
uncovered density at least \(1/Q\).

## 7. Exact certificate and the remaining unrestricted problem

The standard-library program
[conditional_kernel_block_certificate.py](../frontier/cover-geometry/conditional_kernel_block_certificate.py)
and its [exact data](../frontier/cover-geometry/conditional_kernel_block_certificate.json)
provide the finite certificate. They check all selected residual
polynomials and fee margins, the thirteen-derivative and four-corner
certificates for each first-root input, and the non-3 orientation
comparisons. For each selected residual, the elementary-symmetric formula
is checked against direct summation over pairwise-disjoint support
families; there are 52 such families on four children. The unbounded-child
inequality is proved by (CK27)–(CK29), independently of this finite
certificate.

For an additional algebraic check, if \(e_i\) denotes the elementary
symmetric polynomial of degree \(i\) in four coordinate caps, then
\[
 \begin{aligned}
 Z_t={}&1-te_1+(t^2-t-1)e_2+(-t^3+3t^2+2t-1)e_3\\
      &+(t^4-6t^3+t^2+9t+2)e_4,\\
 L_t={}&e_1-(2t-1)e_2+(3t^2-6t-2)e_3\\
      &-(4t^3-18t^2+2t+9)e_4.
 \end{aligned}
 \tag{CK34}
\]
The certificate uses these formulas and checks the displayed \(L_t\)
against the support sum in (CK7). The program checks exact arithmetic; it does not replace the conditional probability argument or
elaborate a Lean proof. It uses only the Python standard library and requires
Python 3.10 or later. Optimized `-O` execution is rejected. Reproduce from
the repository root with assertions enabled:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/conditional_kernel_block_certificate.py --output /tmp/conditional-kernel-block-certificate.json
```

Known results have different scopes. The repository's source audits record
Schroeder's [at-most-three-prime-divisors-per-modulus theorem](../../../../Library/Arith/schroeder2026noncoverage.md)
and the separate [at-least-nine-total-prime-divisors theorem](../../../../Library/Arith/schroeder2026nine.md),
with their respective verification boundaries.
Neither stated scope closes the unrestricted problem, and an entire
prime-interaction block is a different object from one modulus's support.
This chapter makes no publication-priority claim.

The result permits arbitrarily large blocks only under (CK1), or under the
separate established simple-cycle rule. It supplies no general fee for a
larger dense block containing small child primes, and no transport of its
conditional survivor kernels into a separate unrestricted continuation
theorem. Those are remaining mathematical obligations. The uniform
five-vertex result and the unbounded large-child regime do not settle the
unrestricted odd-covering problem.

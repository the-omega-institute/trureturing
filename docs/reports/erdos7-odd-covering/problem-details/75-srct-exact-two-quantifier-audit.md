[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# SRCT: the exact-two-9 implication and a repeated-layer counterexample

The SRCT exact-two-9 claim would imply the unrestricted distinct odd-covering
conjecture. However, the universal repeated-layer gain bound in its current
proof fails on an explicit congruence calculation. This audit rejects that
proof step, without deciding whether the claimed nonexistence theorem is true.

## External source and verification scope

The source is the public
[Shunyaya Residual Capacity Theory repository](https://github.com/OMPSHUNYAYA/Shunyaya-Residual-Capacity-Theory)
at revision 95531a4849fdd0a072e5cf943abd96ac7fe136bf. Its theorem manuscript is
[version 1.15.43](https://github.com/OMPSHUNYAYA/Shunyaya-Residual-Capacity-Theory/blob/95531a4849fdd0a072e5cf943abd96ac7fe136bf/01_Theorem_and_Proof/SRCT_Modulus9_Exactly_Twice_Obstruction_Theorem_v1_15_43.md),
with SHA-256

    eb10e4b26afdff144774a3f56e2f060d78319bf228f3fd7f3be30e9aad032d7e

The source states: no finite covering has all moduli odd and greater than
$1$, modulus $9$ exactly twice, and every other modulus at most once.
It explicitly assumes neither irredundancy nor distinct residues for the two
$9$-classes.

Both source checks were reproduced: 556/556 self-test and 565/565 repository
verification, with exit code zero. The source describes its universal lemmas
as not proof-assistant formalized. The passing checks do not validate the
universal gain claim against arbitrary congruence realizations. This audit's
two independent standard-library programs import no SRCT code.

## Exact-two-9 nonexistence would imply Erdős #7

Let $C$ be any finite covering with pairwise distinct odd moduli $m_i>1$.
Since the moduli are distinct, $9$ occurs zero or one time.

- If $9$ is absent, adjoin $0\bmod9$ and $1\bmod9$.
- If $9$ occurs once, with residue $a\bmod9$, adjoin $(a+1)\bmod9$.

Adding classes preserves coverage. Every non-$9$ modulus still occurs at most
once, and $9$ now occurs exactly twice. Thus

\[
\exists C\;\mathrm{DistinctOddCover}(C)
\ \Longrightarrow\
\exists C'\;\mathrm{ExactTwo9OddCover}(C').
\]

Contrapositively, the declared exact-two nonexistence theorem would settle the
unrestricted distinct odd-covering problem. The source README's assertion
that multiplicities zero and one remain outside the conclusion is incompatible
with this implication. Section 13's separate augmentation by the canonical
modulus $K$ does not block augmentation by $9$.

The checker
[verify_srct_exact_two_e7_implication.py](../verify_srct_exact_two_e7_implication.py)
tests all 23,040 residue assignments over subsets of $\{3,5,7,9,11\}$.
Every transformed family satisfies the exact-two class restrictions and retains
every original class. This is a bounded regression of the transformation;
the universal implication follows from the case split above.

## A literal repeated-layer counterexample to Lemma 9.2

Use the source's own core and support constants:

\[
B=51975=3^3\,5^2\,7\,11,\qquad K=221B,\qquad
\theta_0=\frac{221}{192},\qquad R_0=\frac7{48}.
\]

For a residual set $W\subseteq\mathbb Z/M\mathbb Z$, define the actual
divisor capacities and deficit exactly as in Sections 4 and 7 of the source:

\[
C_W(d)=\max_{a\bmod d}|\{x\in W:x\equiv a\pmod d\}|,\qquad
S(W)=\sum_{d\mid M}C_W(d),
\]
\[
D(W)=|W|-\sum_{\substack{d\mid M\\d\notin E}}C_W(d).
\]

Here $E$ contains the forbidden identity label and all already used modulus
labels. The two used $9$-classes leave no further available modulus-$9$ label.

The core parent residual set is

\[
U=\{x\bmod B:x\not\equiv0\pmod p\ (p=3,5,7,11),\
x\not\equiv1,2\pmod9\}.
\]

For the core child, take the class $4\bmod27$:

\[
V=U\setminus\{x:x\equiv4\pmod{27}\}.
\]

The parent exclusion set is $E=\{1,3,5,7,9,11\}$; the child adds $27$.
Direct residue counting gives:

| Core state | Active mass $A$ | Raw capacity sum $S$ | Deficit $D$ |
| --- | ---: | ---: | ---: |
| Parent $U$ | 14,400 | 44,044 | 2,996 |
| Child $V$ | 13,200 | 42,042 | 3,178 |

The source's renewal shape is therefore

\[
(u,X,Y,G)=(0,182,802,1200),
\]

where $G=A-A'$, $u=C_U(27)-G$, $X$ sums the decreases of the other
available capacities, and $Y=S-S'-G$.

Now append two repeated $3$-adic layers. Put $B_2=9B=467775$ and
$L=221B_2=103378275$. Lift the parent constraints to $B_2$, but take the
localized class $4\bmod243$ for the child. This class projects through

\[
4\bmod243\ \longmapsto\ 4\bmod81\ \longmapsto\ 4\bmod27.
\]

Each step fixes one new $3$-adic digit, exactly the top-layer localization in
Lemma 8.1. The high-level child exclusion set adds $243$, not $27$.
Direct counting over $B_2$ gives:

| High-resolution state | Active mass $A$ | Raw capacity sum $S$ | Deficit $D$ |
| --- | ---: | ---: | ---: |
| Parent | 129,600 | 404,404 | 18,956 |
| Child after $4\bmod243$ | 128,400 | 402,402 | 19,138 |

The same renewal shape $(0,182,802,1200)$ is obtained from this table.
In particular, the localized class removes 1,200 points, not nine times
that number.

Restore the normalized zero classes for $13$ and $17$. Their coprime
coordinates give, directly by CRT divisor-capacity summation,

\[
D_{221}=192D+28A-29S.
\]

Indeed, the unrestricted support multiplier is
$(12+1)(16+1)=221$, the active multiplier is $12\cdot16=192$,
and the two newly excluded prime labels have total capacity $28A$.
Consequently,

\[
D_{\rm parent}=-4459364,\qquad
D_{\rm child}=-4399962,\qquad
\boxed{\Delta D_{\rm true}=59402}.
\]

These negative absolute deficits do not assert coverage. They are legitimate
residual-capacity states for testing a universal claim about gain.

Lemma 9.2 asserts $\Delta D_{\rm true}\ge F C_{\rm dec}$ for a renewal
shape and a finite sequence of layers. For the two repeated layers,
$b_1=b_2=3$ and

\[
F=192\cdot9=1728,\quad
U_{\rm model}=\frac{221}{192}\left(\frac43\right)^2-1,\quad
R_{\rm model}=\frac7{48}+\frac23.
\]

Its prescribed decoration charge is

\[
C_{\rm dec}
=182+802\,U_{\rm model}-1200\,R_{\rm model}
=\frac{2491}{54}.
\]

Thus the asserted lower bound becomes

\[
\boxed{59402\ \ge\ 79712},
\]

which fails by exactly 20,310. The source lists no terminal-only, positive-parent-
deficit, or restricted-branch premise in Lemma 9.2. If such a restriction is
intended, it requires a new statement and proof, together with a verified
application to Propositions 10.1 and 11.1.

## Why the envelope argument does not prove a gain bound

A pointwise capacity envelope can give $D_{\rm true}(W)\ge D_{\rm env}(W)$
for each state. Writing the difference as a nonnegative shadow $s(W)$ gives

\[
\Delta D_{\rm true}
=\Delta D_{\rm env}+s(W_{\rm child})-s(W_{\rm parent}).
\]

Nonnegativity of both shadows does not establish the required inequality
between their increments. Lemma 8.2 supplies a single-family nonnegative
shadow, without the needed monotonicity under the same actual TAKE.
There is also a scale mismatch when a fully lifted core TAKE is replaced by
one localized high-digit class, as the active masses above demonstrate.

The source's function named charge_envelope_challenge in its version 1.15.43
referee certificate compares two expressions built from the same abstract
product weights. It does not independently compute the true capacities for
this repeated-layer congruence example. Its passing result therefore does
not contradict this counterexample.

The independent checker
[srct_repeated_layer_counterexample.py](../frontier/cover-geometry/srct_repeated_layer_counterexample.py)
enumerates actual residues and divisor capacities for the core and the
two-layer instance. It also checks a core-supported TAKE under eight repeated
layers, using exact CRT fiber multiplicities; that control distinguishes the
failure from merely choosing the wrong localized interpretation.

For that control the same numerical class $1\bmod15$ is taken before and
after refinement. Its core shape is $(0,30,510,1800)$. At
$L=K\cdot3^8=75362762475$, direct sums of the original numerical labels give
$\Delta D_{\rm true}=146638350$, while $F C_{\rm dec}=404608800$.
The claimed lower bound exceeds the true gain by 257,970,450. In this control
the used label is unchanged, so the failure cannot be attributed to replacing
$27$ by $243$ or to excluding the projected label instead of the actual label.

## Reproduction and boundary

    python3 -I -O docs/reports/erdos7-odd-covering/verify_srct_exact_two_e7_implication.py
    python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/srct_repeated_layer_counterexample.py

Both programs use explicit failures that remain active with Python
optimization enabled. They retain no external source code or finite
covering candidate.

This is an ordinary mathematical audit backed by exact integer/rational
computation, not a Lean-certified theorem. It invalidates the stated universal
gain bound and the present proof's use of that bound. It neither constructs an
odd distinct covering nor proves its impossibility. Unrestricted Erdős #7
remains open; the earlier finite-LCM and conditional source results retain
their previous scopes.

## Exact transport through arbitrary repeated heights

The replacement below uses actual capacities, with every original numerical
modulus counted once. It supplies a correct all-height capacity criterion and
a monotone potential. Its value is negative on the six-prime SRCT initial
state, so it does not repair that proof's unrestricted conclusion.

Let $B=p^aM$, where $p\nmid M$, $a\ge1$, and let $W\subseteq\mathbb Z/B\mathbb Z$.
Write $W_t$ for its full inverse image modulo $Bp^t$. An exclusion set
$E\subseteq\{d:d\mid B\}$ contains the identity and the already used labels.
The same **numerical** labels remain excluded after lifting; exclusion of
$d$ does not exclude any new label $dp^j$.
Put

\[
A=|W|,\quad S=\sum_{d\mid B}C_W(d),\quad
T_p(W)=\sum_{\substack{d\mid B\\v_p(d)=a}}C_W(d),\quad
D_0=A-\sum_{d\mid B,\ d\notin E}C_W(d).
\]

For a divisor $d\mid Bp^t$, set $j=\max(0,v_p(d)-a)$ and $d_0=d/p^j$.
Counting the fibers of reduction modulo $B$ gives the exact identity

\[
C_{W_t}(d)=p^{t-j}C_W(d_0).
\tag{ET1}
\]

For $j=0$, each point in a compatible base residue has $p^t$ lifts. For
$j>0$, the chosen residue fixes $j$ of the additional $p$-adic digits and
leaves $p^{t-j}$ lifts per compatible base point. Maximization over residues
then gives (ET1), including $W=\varnothing$.
Separate the old labels from the distinct new labels $p^{a+j}e$, $e\mid M$:

\[
S_t=p^tS+\frac{p^t-1}{p-1}T_p(W),\qquad
\boxed{D_t=p^tD_0-\frac{p^t-1}{p-1}T_p(W).}
\tag{ET2}
\]

In particular, the repeated-layer factor is a geometric **sum** of new
original labels, not a product of independently reusable label inventories.

If $q\mid B$, $q\notin E$, and $V=W\setminus[a\bmod q]$, use $E\cup\{q\}$
for the child. With $\delta T=T_p(W)-T_p(V)\ge0$ and
$\Delta D_0=D_0(V;E\cup\{q\})-D_0(W;E)$, subtraction gives

\[
\boxed{\Delta D_t=p^t\Delta D_0+
\frac{p^t-1}{p-1}\delta T.}
\tag{ET3}
\]

This transports a base-supported TAKE and its full lift. A single localized
class modulo $qp^t$ is a different operation, as the preceding counterexample
shows. Such a class is nevertheless handled by first using the larger period
as the base and then taking that actual numerical label.

Positive removed mass need not give any strict gain, even for the complete
corrected potential below. Take $B=15$, $E=\{1,3,5\}$ and
$W=(\mathbb Z/15\mathbb Z)^\times$, the actual residual after the classes
$0\bmod3$ and $0\bmod5$. TAKE the unused class $1\bmod15$. The capacity
vectors at labels $(1,3,5,15)$ before and after are
$(8,4,2,1)$ and $(7,4,2,1)$. Both deficits are $7$, while every nonempty
top-shell sum over $\{3,5\}$ is unchanged. Thus $G=1$ but
$\Delta D_t=0$ at every repeated height, and $\Delta J_P=0$ for every
nonempty $P\subseteq\{3,5\}$ in (ET6). This rules out a compulsory
strict gain from positive actual deletion alone; it does not rule out
stronger estimates using additional hypotheses or other functionals.

### Coprime support with its original labels

Let $Q$ be squarefree and coprime to $B$, and retain the nonzero residues in
each coordinate $\ell\mid Q$. Put

\[
h=\varphi(Q),\qquad
\sigma=h\sum_{\ell\mid Q}\frac1{\ell-1}.
\]

At every height exclude precisely the labels in $E$ and the prime labels
$\ell\mid Q$. Under CRT, the support has active size $h$, raw divisor-capacity
sum $Q$, and capacity $h/(\ell-1)$ at label $\ell$. Thus

\[
D_0^Q=hD_0-(Q-h)S+\sigma A,
\]
\[
\boxed{D_t^Q=p^tD_0^Q-Q\frac{p^t-1}{p-1}T_p(W),\qquad
\Delta D_t^Q=p^t\Delta D_0^Q+
Q\frac{p^t-1}{p-1}\delta T.}
\tag{ET4}
\]

These identities concern support depths fixed at one. Higher support depths
must be included among the refinements in the next formula.

### Simultaneous refinements and the exact positivity threshold

Let $P$ be a nonempty set of primes dividing $B$, and let $t_p\ge0$ be
arbitrary integers. Put $F=\prod_{p\in P}p^{t_p}$ and let $W_{\mathbf t}$ be
the full lift modulo $BF$. For each nonempty $J\subseteq P$, define

\[
T_J(W)=\sum_{\substack{d\mid B\\
v_p(d)=v_p(B)\ (p\in J)}}C_W(d),\qquad
w_p(t)=\frac{1-p^{-t}}{p-1}.
\]

Clamping all increased exponents in (ET1), each original label has a unique
base label and a unique set of coordinates whose exponents exceeded the
base heights. Summing the geometric series for those coordinates gives

\[
\boxed{\frac{D_{\mathbf t}}F
=D_0-\sum_{\varnothing\ne J\subseteq P}
\left(\prod_{p\in J}w_p(t_p)\right)T_J(W).}
\tag{ET5}
\]

Define its limiting coefficient

\[
J_P(W,E)=D_0-
\sum_{\varnothing\ne J\subseteq P}
\frac{T_J(W)}{\prod_{p\in J}(p-1)}.
\tag{ET6}
\]

For **nonempty** $W$ and **nonempty** $P$,

\[
\boxed{D_{\mathbf t}>0\text{ for every finite }\mathbf t
\quad\Longleftrightarrow\quad J_P(W,E)\ge0.}
\tag{ET7}
\]

For sufficiency, every $T_{\{p\}}(W)>0$: a nonempty set has positive capacity
at the top label $B$. At every finite height, $w_p(t_p)<1/(p-1)$, so (ET5)
is strictly greater than $J_P$. This includes the equality boundary $J_P=0$.
For necessity, let all heights increase together. The right side of (ET5)
converges to $J_P$; a negative limit makes it negative at a finite height.
If $P=\varnothing$, the criterion instead is just $D_0>0$. If $W$ is empty,
all capacities and deficits are zero, so the strict-positivity conclusion
does not hold.

### The same potential is invariant under refinement and monotone under TAKE

For a Haar formulation, now take $P$ to be **all** primes dividing $B$ and
let $\widetilde W$ be the corresponding clopen subset of
$\prod_{p\in P}\mathbb Z_p$. Write

\[
c_W(m)=\max_{a\bmod m}\mu(\widetilde W\cap[a\bmod m])
\]

for each positive $P$-smooth integer $m$, retaining $m$ as an original
numerical label. Since $c_W(m)\le1/m$ and
$\sum_{m\text{ $P$-smooth}}1/m=\prod_{p\in P}p/(p-1)<\infty$, the potential

\[
\Phi_P(W,E)=\mu(\widetilde W)-
\sum_{\substack{m\text{ $P$-smooth}\\m\notin E}}c_W(m)
=\frac{J_P(W,E)}B
\tag{ET8}
\]

is well-defined. The last equality follows by the same clamping and
geometric summation as (ET5). Refining the finite period changes neither
the clopen set nor the actual original-label capacities, so it changes
neither side of (ET8).

For any unused original $P$-smooth label $q$, take
$\widetilde V=\widetilde W\setminus[a\bmod q]$ and $E'=E\cup\{q\}$.
If necessary first refine the period to $\operatorname{lcm}(B,q)$.
Let $g=\mu(\widetilde W\setminus\widetilde V)$. Absolute convergence permits
termwise subtraction:

\[
\boxed{\Phi_P(V,E')-\Phi_P(W,E)
=c_W(q)-g+
\sum_{\substack{m\text{ $P$-smooth}\\m\notin E'}}
[c_W(m)-c_V(m)]\ge0.}
\tag{ET9}
\]

The inequality uses $g\le c_W(q)$ and $V\subseteq W$, for the same actual
parent and child sets. It does not assume simultaneous attainment of the
separate capacity maxima. Consequently a nonnegative potential for a
nonempty residual set is preserved by all actual TAKE operations and
arbitrary increases of the heights of this fixed prime support.

It also directly excludes a finite completion: for any finite set $F$ of
remaining distinct labels, the union bound gives
$\mu(\widetilde W\setminus\bigcup_{m\in F}[a_m\bmod m])
\ge\mu(\widetilde W)-\sum_{m\in F}c_W(m)$.
This is positive when $\Phi_P\ge0$, because infinitely many unused
$P$-smooth labels lie outside $E\cup F$, and each has strictly positive
capacity when $W$ is nonempty. Thus the equality boundary is also valid.
No assertion here permits an unlimited set of new primes: enlarging $P$
adds original labels to the sum and can make the potential negative.

### Fresh-prime extensions necessarily defeat this scalar potential

This limitation holds for every nonempty seed, not only the SRCT initial
state. Keep a finite old support $P$, a nonempty clopen residual
$\widetilde W$, and finitely many excluded original labels $E$. Set

\[
A=\mu(\widetilde W)>0,\qquad
S=\sum_{m\text{ $P$-smooth}}c_W(m),\qquad
\Phi=\Phi_P(W,E).
\]

Let $R$ be a finite set of genuinely new odd primes. Add just the original
classes $0\bmod q$, one for each $q\in R$. The actual residual set is
$\widetilde W\times\prod_{q\in R}\mathbb Z_q^\times$, of measure $h_RA>0$,
where

\[
h_R=\prod_{q\in R}\frac{q-1}{q},\quad
Y_R=\sum_{q\in R}\frac1{q-1},\quad
F_R=\prod_{q\in R}\left(1+\frac{q}{(q-1)^2}\right).
\]

For one fresh coordinate, the capacities are $(q-1)/q$ at exponent zero
and $q^{-e}$ at each positive exponent $e$. Its complete raw capacity sum
is $(q-1)/q+1/(q-1)$, while the newly excluded original label $q$ has
capacity $A/q$. Tensoring these actual independent coordinates therefore
gives

\[
\Phi_{P\cup\{q\}}'
=\frac{q-1}{q}\Phi-\frac{S}{q-1}+\frac Aq,
\]
\[
\boxed{\Phi_{P\cup R}'
=h_R\,[\Phi-(F_R-1)S+AY_R].}
\tag{ET10}
\]

All new labels are their original numerical products. In particular, the
mixed new-prime and old-prime capacities are included rather than discarded.

If $Y_R\ge2$, then this potential is strictly negative for **every** such
seed. Indeed, $S\ge A$ (the identity-label term) and $\Phi\le A$. Write
$y_q=1/(q-1)\le1/2$. Positivity of all expansion terms gives

\[
F_R=\prod_q(1+y_q+y_q^2)
\ge1+Y_R+\sum_{q<r}y_qy_r
\ge1+Y_R+\frac{Y_R^2-Y_R/2}{2}.
\]

For $Y_R\ge2$ the last quadratic term is at least $3/2$, so

\[
\Phi-(F_R-1)S+AY_R
\le A(2+Y_R-F_R)\le-\frac A2,
\qquad
\boxed{\Phi_{P\cup R}'\le-\frac{h_RA}{2}<0.}
\tag{ET11}
\]

Euler's divergence of the prime reciprocal sum ensures such a finite $R$
exists outside every fixed finite old support. The pinned Mathlib already
contains this result as `Nat.Primes.not_summable_one_div` in
`Mathlib/NumberTheory/SumPrimeReciprocals.lean`; no new wrapper is needed.
Removing finitely many primes preserves divergence, and $1/(q-1)\ge1/q$.
The finite smooth Euler sum used in (ET8) is likewise an established
geometric-product identity, available in `Mathlib/NumberTheory/EulerProduct/Basic.lean`.

Consequently the exact potential has a useful fixed-support invariant but
cannot remain nonnegative across every actual fresh-prime extension.
The extension is an explicit noncovering family with positive residual
measure; the failure is in this certificate, not in the original conjecture.
It also does not rule out a different potential, a later recovery under
additional constraints, or a proof using joint capacities.

As a finite regression of (ET11), take old support $\{1229\}$, the full
residual set, and $E=\{1\}$. Then $A=1$, $S=1229/1228$, and
$\Phi=1227/1228>0$. The 199 odd primes from $3$ through $1223$ are genuinely
fresh and satisfy $Y_R\ge2$ by exact rational summation. Adding their zero
classes leaves positive Haar mass, yet gives the strictly negative bound
in (ET11). This is a counterexample to positivity preservation of the
scalar certificate, not a covering counterexample.

The repository's
[fresh-prime descendant-budget result](../profile-notes/321-384/351-multiple-descendants-fresh-prime-budget-and-local-repair.md)
uses a related Euler-product capacity budget for a different constrained
transport. It does not state (ET10) or the every-seed sign failure (ET11).
The present searched-scope comparison makes no claim of research originality.

### Bounded clusters retain joint information but have the same fresh-prime barrier

There is a joint refinement of the scalar certificate. Its scope and its
failure can both be stated for the same actual Haar law, without choosing
independent laws for different labels.

Fix an integer $k\ge1$ and write $\mathcal I$ for the unused original
$P$-smooth numerical labels. For each nonempty finite
$A\subseteq\mathcal I$, $|A|\le k$, define the actual union capacity

\[
U_A(W)=\max_{(a_m\bmod m)_{m\in A}}
\mu\left(\widetilde W\cap\bigcup_{m\in A}[a_m\bmod m]\right).
\tag{ET12}
\]

Every residue in this maximum belongs to its original label, and all
intersections use the same $\widetilde W$ and Haar measure. Each maximum is
over a finite set. A fractional cluster cover is a nonnegative assignment
$\lambda_A$ to these clusters such that
$\sum_{A\ni m}\lambda_A\ge1$ for every $m\in\mathcal I$. Define

\[
B_k(W,E)=\inf_\lambda\sum_A\lambda_AU_A(W),\qquad
\Psi_k(W,E)=\mu(\widetilde W)-B_k(W,E).
\tag{ET13}
\]

Countably many clusters and weights are allowed. The singleton cover is
feasible and has finite cost $\sum_{m\in\mathcal I}c_W(m)$; thus the
infimum is finite. All sums are nonnegative. For any fixed actual finite
completion, its union indicator is bounded pointwise by the corresponding
weighted cluster-union indicators. Every active original label receives
total weight at least one. Consequently $B_k$ is an upper bound on every
such union, and $\Psi_k>0$ certifies noncoverage. Also
$B_k\le B_1=\sum_{m\in\mathcal I}c_W(m)$, so $\Psi_k\ge\Phi_P$.
No claim is made here that the equality boundary $\Psi_k=0$ by itself is a
noncoverage certificate.

For a pair, the gain over the two singleton capacities is exactly

\[
\kappa_{m,n}=c_W(m)+c_W(n)-U_{\{m,n\}}(W)\ge0.
\]

The separate unary maxima can always be attained simultaneously, because
each label has its own free residue. What the unary sum loses is their
overlap in the union. Shared-label pair or cluster factors can additionally
have mutually incompatible maximizers; that is a different constraint.
The gain above accounts for the actual union rather than assuming that
separate maxima imply disjoint covered regions.

The improved potential still respects actual TAKE operations. Let $q$ be
an unused label, delete its actual class, and write $V$ for the child and
$g=\mu(\widetilde W\setminus\widetilde V)$. If $q\in A$, fixing that label
to the deleted class and optimizing the other labels on $V$ gives

\[
U_A(W)\ge g+U_{A\setminus\{q\}}(V),
\]

with $U_\varnothing=0$. If $q\notin A$, set inclusion gives
$U_A(W)\ge U_A(V)$. Remove $q$ from every cluster of a feasible cover and
combine identical resulting clusters. The remaining labels retain their
coverage weights. Since the old weight through $q$ is at least one,

\[
B_k(W,E)\ge g+B_k(V,E\cup\{q\}),\qquad
\boxed{\Psi_k(V,E\cup\{q\})\ge\Psi_k(W,E).}
\tag{ET14}
\]

To handle a nonattained infimum, use covers within an arbitrary positive
error of it and then let the error decrease to zero. Finite-cost covers
suffice; nonnegative summation justifies the removal operation. Refinement
invariance follows directly from the unchanged Haar sets and original-label
capacities. Thus this is a genuine fixed-support joint improvement, not a
change of probability law.

Nevertheless **every fixed $k$ fails on an actual finite fresh-prime
extension of every nonempty seed**. For any cluster,

\[
U_A(W)\ge\max_{m\in A}c_W(m)
\ge\frac1k\sum_{m\in A}c_W(m).
\]

Tonelli summation and the fractional coverage inequalities imply

\[
B_k(W,E)\ge\frac1k\sum_{m\in\mathcal I}c_W(m).
\tag{ET15}
\]

Apply the exact fresh-prime extension (ET10). Let $S_E$ denote the old
excluded-capacity sum, so $S_E\le S$, and put
$Z_R=\sum_{q\in R}(q-1)^{-2}>0$. The new available-capacity sum and mass
satisfy

\[
\frac{S_{\rm available}'}{A'}
=\frac{F_RS-S_E-AY_R}{A}
\ge F_R-1-Y_R
\ge\frac{Y_R^2+Z_R}{2}.
\tag{ET16}
\]

For the last bound, expand $\prod_q(1+y_q+y_q^2)$ and keep its constant,
linear, single-square and distinct-pair terms. Therefore, whenever
$Y_R^2\ge2k$,

\[
\boxed{\Psi_k(W',E')
\le-\frac{A'Z_R}{2k}<0,\qquad A'=h_RA>0.}
\tag{ET17}
\]

Prime reciprocal divergence supplies such a finite fresh set for every
fixed $k$ and finite old support. Every added class is an actual
$0\bmod q$, with a distinct odd numerical modulus. The same 199-prime
regression above already has $Y_R\ge2$, so it defeats $k=2$ even after
granting **all** exact pair-union capacities and their best fractional
cover. Pair gains need not vanish: for two distinct fresh primes $q,r$,
the still-unused original labels $q^2,r^2$ have pair gain exactly
$A'/[q(q-1)r(r-1)]>0$ on this residual product. The taken labels $q,r$
are excluded and supply no available pair credit. The barrier shows the
actual available gains are insufficient for
this bounded-cluster certificate, not that joint information is absent.

The scope is nonnegative fractional covers of raw actual union capacities
of at most $k$ original labels. It does not include arbitrary signed
messages, additional global consistency constraints, or clusters whose
size grows with the new prime support. Thus it is not an impossibility
theorem for every method called a finite-order relaxation.
The repository already has an
[exact subset-union DP](../profile-notes/001-064/01-survivor-reduction.md)
and [fractionally packed shared-factor losses with signed messages](../profile-notes/001-064/27-actual-mask-weights-and-an-all-height-square-certificate.md).
Those provide established local joint tools; they do not supply a
positive every-seed bound across this fresh-root family. No new general
cluster technique or Lean theorem is claimed here.

### Actual initial and successor values

For the literal SRCT parent $U$ above, $T_3(U)=2002$. The exact coefficients
are:

| State and allowed later refinements | Limiting coefficient $J$ |
| --- | ---: |
| Period $B$, only further powers of $3$ | $1995$ |
| Period $B$, arbitrary heights at $3,5,7,11$ | $1785/32$ |
| Period $221B$, only further powers of $3$ | $-520065$ |
| Period $221B$, arbitrary heights at $3,5,7,11$, fixed depths at $13,17$ | $-30356235/32$ |
| Period $221B$, arbitrary heights at all six primes | $-2157798825/2048$ |

The two base-supported TAKE operations retain the same top-$3$ capacity
sum despite removing positive mass:

| Actual TAKE | $T_3(U)-T_3(V)$ | Child $J_{\{3\}}$ at $B$ | Child coefficient with fixed support $13\cdot17$ |
| --- | ---: | ---: | ---: |
| $1\bmod15$ | $0$ | $2025$ | $-497715$ |
| $4\bmod27$ | $0$ | $2177$ | $-460663$ |

Thus there are actual nonempty positive cases on the four-prime parent and
its successors, uniformly over arbitrary later heights and actual TAKE
sequences. They are a conditional fixed-support result for this explicit
head, not a universal residue classification. Existing
[four-prime-head results](10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md)
already cover distinct families on that support by different estimates;
the table does not claim a new bound for unrestricted Erdős #7.
The six-prime parent and these two successors remain outside the criterion.
The zero top-capacity drops also rule out a uniformly positive top-drop
bonus merely from positive removed mass. Monotonicity alone does not prove
that a negative initial potential must eventually become nonnegative.

The existing `compressed_uniform_pair` in the repeated-layer counterexample
checker already implements the one-prime capacity identity for $p=3$.
Searches of the covering reports and capacity-related D5 modules did not
locate the general simultaneous-depth statement or this smooth-label
potential; this is a searched-scope statement, not a novelty claim. The
argument above is ordinary mathematics, without new Lean declarations.

Independent direct-count regressions and the actual values are reproduced by

    python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/verify_repeated_prime_transport.py

The checker performs 925 checks: 120 parent/child/height cases for one-prime
transport and coprime support, 144 simultaneous-height cases, invariance and
TAKE monotonicity and exact zero-gain checks, the displayed SRCT readings, and the fresh-prime
sign-failure regression including the fractional pair-capacity obstruction.
It computes real
residue populations and counts each original divisor label once. These
bounded checks supplement the derivations above; they do not quantify over
all coverings or provide Lean certification. The repaired transport is not
a proof of the external SRCT theorem or of Erdős #7.

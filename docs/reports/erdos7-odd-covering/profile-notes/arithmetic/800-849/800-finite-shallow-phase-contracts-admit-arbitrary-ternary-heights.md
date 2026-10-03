# 800: 103 shallow mixed slots admit arbitrary ternary heights and the complete large-prime tail

A common-source condition on 103 specified shallow mixed numerical labels is sufficient for noncoverage on the old head

$$P_8=\{3,5,7,11,13,17,19,23\},$$

followed by arbitrary originals involving 29 and any finite set of support primes strictly above 3000. Every unlisted shallow old label, every old ternary height at least three, every pure nonternary original, and all later original phases and heights are unrestricted. The final distorted survivor mass is greater than $19/1000$.

The 103 conditions concern one common source: each listed original, if present, must be null on the same reference-core survivor defined below. They are not permission to choose a different source or reference for each label. This is a restricted-family theorem, not a uniform noncoverage theorem for arbitrary shallow phases or unrestricted Erdős #7.

An easier sufficient condition uses all shallow mixed labels whose nonternary cofactor is at most 437. It constrains 111 numerical slots and leaves final mass greater than $1/100$. The optimized 103-slot count is minimal only for the fixed source, individual-cap union bound, query comparison and 3000-tail certificate used here.

All arguments are ordinary mathematics with exact rational arithmetic. No Lean verification or external novelty claim is made.

## 1. One source, with arbitrary actual pure-q phases and heights

Write

$$Q=(5,7,11,13,17,19,23),\qquad C_q=\frac{q-1}{q-2},\qquad b_q=\frac1{q-2}.$$

For each $q\in Q$, let $\lambda_q$ be Haar measure conditioned on avoiding all actual pure $q$-power originals. Their finite number and heights are arbitrary. Distinct numerical labels give total excluded Haar mass at most $\sum_{j\ge1}q^{-j}=1/(q-1)$, so the conditional probability law exists and satisfies

$$\lambda_q([a]_{q^j})\le C_q/q^j.$$

Handle the actual 3 and 9 originals in one common frame as in [Report 719](../700-749/719-actual-phase-unions-and-common-affine-reference-enlarge-the-certified-families.md). If they are nonredundant, a single simultaneous affine transport puts them at $0\bmod3$ and $1\bmod9$. Missing or redundant slots permit the same auxiliary source restrictions. This does not create a second actual original at either numerical label. All other actual phases are transported by that one map.

Use the live mod-9 leaves $(4,7,2,5,8)$ with weights

$$w=(1/3,1/3,1/9,1/9,1/9),$$

and independent Haar digits above ternary depth two. The one initial product law is

$$\lambda=\lambda_3\otimes\bigotimes_{q\in Q}\lambda_q.$$

Its ternary root and leaf caps are $r=2/3$ and $v=1/3$. Higher pure ternary originals have not been discarded; they will be charged with all other higher ternary labels.

## 2. The 28-class mixed core and its actual joint event

Set $E_q=\{x_q\equiv2\pmod q\}$. Define a fixed reference mixed core consisting of:

- the $3\cdot5$ cylinder whose ternary root is 1 and whose 5-coordinate is 2;
- for every other $q\in Q$, the $3q$ cylinder whose ternary root is 2 and whose q-coordinate is 2;
- for every unordered pair $p,q\in Q$, the single class $2\bmod pq$.

There are seven root-star classes and 21 pair classes, all with distinct numerical moduli and one globally fixed phase. The first star is $7\bmod15$; the other six are $2\bmod3q$.

Let $S$ be the survivor of these 28 reference classes inside the support of $\lambda$. They are auxiliary exclusions defining a common source test; the actual family need not contain them. For an original class $A_m$, the null condition means

$$\lambda(S\cap A_m)=0.\tag{A1}$$

Containment of $A_m$ in the reference forbidden union, or incompatibility with the actual pure survivors or live ternary leaves, is sufficient. More generally A1 can be checked on the actual common finite resolving period. The same $S$ is used for every selected label.

On either root-A leaf 4 or 7, survival is exactly

$$\neg E_5\quad\text{and at most one of }E_7,E_{11},E_{13},E_{17},E_{19},E_{23}.$$

On a root-B leaf 2, 5 or 8, survival is exactly that all six $E_q$ with $q\ne5$ fail; $E_5$ is free. Both events are coordinatewise decreasing in the seven indicators.

The actual $E_q$ are independent under the original nonternary product, with probabilities at most

$$t_q=C_q/q.$$

A decreasing event has its smallest probability when every Bernoulli parameter is increased to its cap. Thus, writing

$$
R_B=\prod_{q\ne5}(1-t_q),\qquad
R_A=(1-t_5)\prod_{q\ne5}(1-t_q)
       \left(1+\sum_{q\ne5}\frac{t_q}{1-t_q}\right),
$$

one obtains

$$
\lambda(S)\ge M:=\frac23R_A+\frac13R_B
=\frac{33324292966457}{52178633632125}
=0.6386578307397478\ldots.\tag{A2}
$$

The exact checker independently enumerates all $128$ Boolean profiles on each of the five leaves and compares the actual 28-class event with this closed form. Independence is used only for the declared product $\lambda$, not for its later survivor restriction.

This calculation extracts the useful core exposed by the containment pruning in [Report 799](../750-799/799-whole-class-containment-repairs-a-finite-raw-cap-source-certificate.md). It does not retain that example's 21 fixed pure-power phases or its depth-three cutoff: here the actual pure-q inventories are arbitrary.

## 3. Every higher ternary original is paid, with the full tail

Every old numerical modulus is uniquely $3^a n$ with $n$ Q-smooth. Define

$$c(n)=\frac{\prod_{q\mid n}C_q}{n},\qquad c(1)=1,$$

and

$$Z=\sum_{n\ Q\text{-smooth}}c(n)=\prod_{q\in Q}(1+b_q)=\frac{4096}{1785}.$$

For every original with $a\ge3$, whatever its actual phase,

$$\lambda(A_{3^an})\le v3^{2-a}c(n).$$

There is at most one original at each full numerical label. Summing over all labels, including every finite height and every Q-smooth cofactor, bounds the actual higher-ternary deletion union by

$$
D_{\ge3}\le\sum_{a\ge3}v3^{2-a}\sum_n c(n)
=\frac v2Z
=\frac{2048}{5355}
=0.38244631185807654\ldots.\tag{A3}
$$

In particular the pure labels 27, 81, and all higher powers of 3 are included through $n=1$. No exponent tail has been set to zero. The sum concerns the same law $\lambda$ and the actual fixed phase of each label.

Before paying unconstrained shallow mixed labels, A2 minus A3 leaves

$$\alpha_{\mathrm{core}}=\frac{13368766976057}{52178633632125}
=0.2562115188816712\ldots.\tag{A4}$$

If every shallow mixed original is null on $S$, this already suffices for the continuation below, with final 3000-tail mass greater than $3/5$.

## 4. Release every shallow label outside a finite list

The pure q-power originals have already been avoided by $\lambda_q$. The remaining shallow old inventory consists of:

- $a=0$ and $n$ having at least two different prime factors;
- $a=1,2$ and $n>1$.

For these numerical labels use the individual caps

$$
u(3^a n)=
\begin{cases}
c(n),&a=0,\\
(2/3)c(n),&a=1,\\
(1/3)c(n),&a=2.
\end{cases}\tag{A5}
$$

The notation $u(m)$ here denotes only a scalar slot cap, not a separately chosen probability law. Their full infinite sum is

$$
D_{\mathrm{shallow}}
=\sum_q b_q+2\left[Z-1-\sum_qb_q\right]
=\frac{99013}{58905}.\tag{A6}
$$

For a finite set $F$ of these shallow mixed labels, require A1 whenever a label in $F$ is actually present. Every other shallow phase is arbitrary. Their union loss on $S$ is bounded by

$$D_F=D_{\mathrm{shallow}}-\sum_{m\in F}u(m).$$

Consequently the actual old survivor $U_8$ satisfies

$$
\lambda(U_8)\ge\lambda(S\cap U_8)
\ge\alpha_F:=M-D_{\ge3}-D_F.\tag{A7}
$$

This is the explicit obligation that replaces a false assumption that the small reference core automatically avoids every later shallow original. Unlisted originals can meet $S$ and are charged. Overlap between paid events only makes this union bound more conservative.

### The concrete 103-slot set

Take the 103 largest caps A5, breaking equal-cap ties by increasing full numerical modulus. The list below gives the nonternary cofactors; the full modulus is $3^a n$ in row $a$.

| $a$ | Number | Cofactors $n$ |
|---:|---:|---|
|0|36|35,55,65,77,85,91,95,115,119,133,143,161,175,187,209,221,245,247,253,275,299,323,325,385,391,425,437,455,475,539,575,595,605,665,715,805|
|1|40|5,7,11,13,17,19,23,25,35,49,55,65,77,85,91,95,115,119,121,125,133,143,161,169,175,187,209,221,245,247,253,275,289,299,323,325,343,385,425,455|
|2|27|5,7,11,13,17,19,23,25,35,49,55,65,77,85,91,95,115,119,121,125,133,143,161,169,175,187,245|

For this literal set,

$$D_F=\frac{26234722426961}{119585698116885},$$

and

$$
\alpha_F=\frac{2973044873761504}{80720346228897375}
=0.03683141875198217\ldots.\tag{A8}
$$

The conditions impose no bound on the number of other originals. All pure-q phases and heights, every old ternary height at least three, and every unlisted shallow mixed phase and height remain unrestricted.

A concrete released slot is $3496\bmod3933$, where $3933=9\cdot19\cdot23$. It is absent from the list and can meet the common core survivor. For this scope control choose empty pure-q inventories; the single CRT witness $x=37182145$ satisfies $x\equiv4\bmod9$, $x\equiv0\bmod q$ for every q, lies in that released class, and avoids all 28 core classes. The witness is checked against the entire union. It is not claimed to survive an arbitrary different pure-q inventory.

## 5. Arbitrary-phase queries and 29 use the same source

Set $\mu=\lambda|U_8/\lambda(U_8)$, with $\lambda(U_8)\ge\alpha_F$. This actual normalized source is chosen before any query. It is not a source optimized separately for each cylinder.

Use [Report 790](../750-799/790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md) PC9--PC11's conditional weighted-indicator rearrangement. It allows one independently fixed phase for each numerical cofactor in a complete query. It does not assume that those phases come from one common reference path. The auxiliary comparison variable is

$$N=N_3\prod_{q\in Q}N_q,$$

with tails

$$
\Pr(N_3\ge2)=r,\quad
\Pr(N_3\ge k)=v3^{3-k}\ (k\ge3),\quad
\Pr(N_q\ge k)=C_q q^{-(k-1)}\ (k\ge2).
$$

Its complete mean is $(1+r+3v/2)Z$. For every complete arbitrary-phase query load $L$,

$$\int(L-h)_+\,d\lambda\le H(h):=\mathbb E(N-h)_+,$$

so the same actual $\mu$ has complete first-query bound

$$B(\mu)\le h+H(h)/\alpha_F.$$

The full mean and all subthreshold atoms are recomputed exactly; no upper-height mass is truncated. Comparing the 28 integer breakpoints $0,\ldots,27$ gives, at $h=16$,

$$B(\mu)\le27.062569890093297\ldots<28.\tag{A9}$$

Take the actual pure-29 survivor law, with cap $28/27$. Restrict its product with this same $\mu$ by every remaining actual 29-ending original. Each has a nonunit old cofactor, with arbitrary ternary depth and arbitrary fixed phase. The unchanged argument of Report 790 gives an unnormalized supported measure with mass at least

$$m_{29}=\frac{28-B_*}{27}=0.03471963370024832\ldots.\tag{A10}$$

These higher old cofactors are queried at their actual phases; they are not inserted as extra old-only forbidden originals.

## 6. The complete tail above 3000

For $s=1/(p-1)$ put

$$A_4(p)=15s+50s^2+60s^3+24s^4.$$

The original full product law gives the simultaneous fourth-query envelope

$$K_0=(1+15r+216v)\prod_{q\in Q}[1+C_qA_4(q)].$$

All further restrictions are of the same measure. Hence the unnormalized post-29 source has mixed fourth-query bound

$$K_{29}=\frac{K_0}{\alpha_F}\left[1+\frac{28}{27}A_4(29)\right].$$

Apply [Report 734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md)'s complete prime-tail construction at $B=3000$, $\ell=7$, $\delta=2/7$ and growth exponent 21. Its analytic prime-product premise and attribution are inherited unchanged. The exact coefficient/range checks include $B\ge286$, $3^\ell\le B$, $4\ell\ge21$, and the required fourth-moment coefficient domination. The complete factor is

$$
\tau=\frac{21609}{10240}\left(\frac{99}{97}\right)^{21}
\frac{3000}{2999^4}
\sum_{j=0}^{21}\frac{21!}{(21-j)!21^j}.
$$

Every tail original is charged once at its largest outside prime, retaining its full earlier cofactor and fixed phase. Arbitrarily many finite outside support primes above 3000 and arbitrary joint supports and exponent heights are permitted.

Exact arithmetic gives

$$m_{29}-K_{29}\tau=0.019659734375340573\ldots>\frac{19}{1000}.\tag{A11}$$

This is a distorted supported mass. It is not a Haar-density assertion of the same size. Since the actual family is finite, positive supported mass gives an uncovered residue in its finite CRT period and therefore an uncovered integer.

Primes 31 through 3000 remain outside the support scope. No condition has been added on the old phases of originals involving 29 or larger permitted primes.

## 7. Exact, limited minimality and the simple cutoff version

The sorting proof retains the infinite inventory. It enumerates all 134 nonunit Q-smooth cofactors $n\le5000$, giving 380 shallow mixed numerical labels. Every unenumerated label has

$$u(3^an)\le Z/n<Z/5000=\frac{512}{1115625}.$$

The 103rd selected cap is $176/84525$, which is strictly larger. Thus the retained list is the largest-cap prefix of the entire infinite shallow inventory, not merely of a finite search table.

For this fixed source and fixed query/tail mechanism, a scalar source lower bound must exceed

$$
\alpha_{\mathrm{tail}}=\min_{0\le h\le27}
\frac{H(h)+27K_0[1+(28/27)A_4(29)]\tau}{28-h}
=0.03520220295598763\ldots
$$

to make the displayed final bound positive. The largest A7 certificate value obtainable by declaring any 102 shallow labels null is attained by the 102 largest caps and equals

$$\alpha_{102}=\frac{2804967015893584}{80720346228897375}
=0.034749194557956734\ldots<\alpha_{\mathrm{tail}}.$$

The 103-label value A8 exceeds this threshold. Thus 103 is minimal among these finite label-null contracts when evaluated by precisely A2--A7 and the unchanged hinge/quartic continuation. This is a limitation on that certificate value, not an upper bound on the actual survivor mass. It excludes neither other source laws nor sharper actual-union or query estimates. The first 102 labels separately suffice for the 29-only gate; the complete 3000 tail requires the extra slot in this mechanism.

For a simpler description, require A1 on every shallow mixed label $3^a n$ with $n\le437$. There are 42 nonunit cofactors, 15 with singleton support and 27 with larger support, hence $2\cdot15+3\cdot27=111$ constrained slots. The same full-tail subtraction gives

$$\alpha_{437}=\frac{55499567246375488}{1533686578349050125}
=0.03618703327645891\ldots,$$

and final 3000-tail mass $0.012095558132936174\ldots>1/100$.

At cutoff 436, the certificate value is $0.03111040308204705\ldots$, below even the 29-only hinge threshold $0.033954178674591294\ldots$. Monotonicity in the cutoff proves that 437 is the first numerical cutoff admitted by this same certificate. It is not an absolute lower bound on finite-prefix complexity.

## 8. Relation to existing work and exact evidence

Report 719 already supplies common affine transport, actual-null phase menus and actual-union repair on one source. Its stated global hypothesis is $v_3\le2$; A3 explicitly removes that hypothesis here. [Report 480](../450-499/480-arbitrary-old-phases-after-a-finite-common-prefix.md) releases deeper digits through a different common-prefix condition on later 23/29 labels; it does not provide this arbitrary-phase 29 continuation from the eight-prime common core. [Report 797](../750-799/797-numerical-slot-boundaries-retain-complete-cap-tails-with-explicit-error.md) provides complete sparse numerical-tail control for the signed source template. Here a direct actual-core event and one same-law union bound replace sensitivity of that signed polynomial; the pure-q inventory is removed before charging the shallow tail. No unconditional comparison with every previous restricted family is claimed.

The portable standard-library consumer [pruned_core_allheight.py](../../../frontier/cover-geometry/refined-capped-source/pruned_core_allheight.py) reads the fixed [pruned_core_allheight_certificate.json](../../../frontier/cover-geometry/refined-capped-source/pruned_core_allheight_certificate.json). It reuses the adjacent existing full-hinge and quartic-tail implementations. It reconstructs the actual core event, the exact Bernoulli formula, both complete exponent tails, all 103 numerical slots and their caps, the global omitted-tail sorting bound, the common-source 29/3000 continuation, the 437 cutoff comparison and the single released-slot CRT witness. The exact output is [pruned_core_allheight.json](../../../frontier/cover-geometry/refined-capped-source/pruned_core_allheight.json).

Normal and `-O` execution agree, with 702 explicit checks. An independent adjacent-directory replay passes. Seven altered inputs are rejected: a missing selected slot, a false numerical label, a forged cap, deletion of the higher-ternary tail, deletion of the remaining shallow tail, an unearned outside-prime cutoff and a forged final reserve. Independent root arithmetic agrees on the source masses, 103-label selection, mass gates and complete continuation fractions. These finite checks support the arithmetic; the conditional domination, common-source null contract and inherited analytic prime-tail estimate remain the ordinary proof inputs stated above.

# Pure-union savings control all four later rows under one law

Let Q={5,7,11,13,17,19}. For any finite family of nonunit Q-smooth
moduli with at most two original occurrences per numerical label, keep
all original residues globally fixed. The existing actual PA law has
complete nonunit query norm strictly below T=257/51 whenever ANY of
the following conditions holds:

1. Numerical modulus11 has at most one original occurrence.
2. Numerical modulus13 has at most one original occurrence.
3. Numerical moduli17 and19 each have at most one original occurrence.

Every other label may occur twice, at arbitrary finite heights and with
arbitrary phases. No old5/7 window or old-coordinate factorization is
required. In particular, an actual all-laws lower witness above T must
have two occurrences at11 and13, and two at at least one of17 and19.
These are necessary conditions on such a lower witness, not an exhibited
witness or a resolution of unrestricted Erdős #7.

The proof bounds the ACTUAL row loss by separating the pure-prime union
from the nonpure old-cofactor count. Savings from all four rows add in
one actual mass identity. This extends the first11 inequality of
[report558](558-first-eleven-inventory-and-an-actual-phase-counterexample.md);
it is ordinary mathematics and exact rational computation, not new Lean
verification.

## 1. The actual process and the fixed comparison

Use the PA construction of
[report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#retaining-the-actual-pure-anchor-masses).
Let x>=1/2 and y>=2/3 be the complete pure5 and pure7 survivor masses.
Start with lambda0, Haar restricted to the full actual5/7 survivor.
Its mass is xy-m, where0<=m<=1/12 is the mixed5/7 union mass inside the
pure product. The raw pure-product restriction is denoted sigma.

At each q=11,13,17,19 and complete old history h, let g_q(h) be the Haar
fraction avoiding exactly the original classes assigned to that row.
The actual kernel has density min(C_q,1/g_q(h)) on this allowed set,
and is zero if it is empty. Its row mass is s_q=min(1,C_q*g_q). Use

| q | Threshold t_q | Density cap C_q | Charge coefficient a_q |
| --- | ---: | ---: | ---: |
|11|2|5/3|1/3|
|13|2|3/2|1/4|
|17|4|2|1/4|
|19|4|9/5|1/5|

These satisfy a_q=2C_q/(q-1) and C_q-1=a_q*t_q. Let ell_q=1-s_q
be the local row loss, and Loss_q its integral against the actual prefix
subprobability. Each kernel is fixed by the same original family; it is
never changed to fit a comparison query.

The existing completed-kernel comparison gives absolute prefix hinge
bounds F_q(x,y), baseline mass alpha(x,y), and final hinge Phi(x,y),
with

    alpha=xy-1/12-sum_q a_q*F_q,
    lambda(1)=alpha+(1/12-m)+sum_q S_q,
    S_q=a_q*F_q-Loss_q>=0,                              (PU1)
    lambda(L-1)<=2*lambda(1)+Phi

for every finite complete final query L including the unit. The actual
lambda is supported on the full survivor, has positive mass, and has
mass at most one. Normalize it ONCE to nu=lambda/lambda(1). This law
need not be uniform Haar on the survivor.

## 2. Keep the actual pure-q forbidden union separate

Fix one q row. Let r_q be the Haar mass of the actual union of its
pure-q originals. This set depends only on the q-coordinate. Define

    theta_q=(q-1)*r_q/2,  delta_q=1-theta_q.

At most two originals per pure numerical label give0<=theta_q<=1 by
the complete geometric sum. Overlap of pure cylinders only reduces this
actual union mass.

At current exponent e>=1, assign each numerical label's at most two
originals to slots j=1,2 once, keeping its full residue fixed. Let
n_(e,j)(h) count the active NONPURE old cofactors in this slot. Define

    beta_(e,j)=(q-1)/(2*q^e), sum_(e>=1,j=1,2) beta_(e,j)=1,
    G_q(h)=sum_(e,j) beta_(e,j)*(n_(e,j)(h)-(t_q-1))_+,
    b_q(h)=sum_(e,j) beta_(e,j)*min(n_(e,j)(h),t_q-1).

Here0<=b_q<=t_q-1. Only finitely many n_(e,j) are nonzero, but the
weight identity retains the whole absent-exponent tail. No missing
original is inserted into the actual forbidden union.

The union bound for NONPURE current cylinders, together with the actual
pure union, gives

    1-g_q(h)<=r_q+(2/(q-1))*(G_q(h)+b_q(h)).             (PU2)

This does not assume any disjointness of different nonpure cylinders,
or of their intersection with the pure union.

Where ell_q>0, the exact kernel identity and PU2 yield

    ell_q=C_q*(1-g_q)-(C_q-1)
          <=a_q*(theta_q+G_q+b_q-t_q)
          <=a_q*(G_q-delta_q).

On this positive-loss set, ell_q<=1 and delta_q>=0 give

    (1+a_q*delta_q)*ell_q
       <=a_q*G_q-a_q*delta_q*(1-ell_q)
       <=a_q*G_q.

The ENDPOINT inequality also holds on the zero-loss set by nonnegativity:

    (1+a_q*delta_q)*ell_q<=a_q*G_q.                    (PU3)

This local inequality
is the same for every permitted old history and every actual residue
assignment. It retains the cost of the pure union before the old-query
comparison.

## 3. Integrate against the same actual prefix

For a fixed slot,1+n_(e,j) is a legal old query with one unit term and
at most one cylinder per occupied nonunit old numerical cofactor. Add
arbitrary fixed query phases at missing labels only when applying the
comparison. Its threshold-t_q hinge dominates
(n_(e,j)-(t_q-1))_+.

The actual prefix is dominated by the same completed-kernel process
started from sigma. The PA comparison therefore bounds every such
integral by F_q(x,y), irrespective of that slot's full-label phases.
Weighting by beta, whose complete sum is one, gives

    integral G_q d lambda_<q <=F_q(x,y).

Integrating PU3 now proves

    Loss_q<=a_q*F_q(x,y)/(1+a_q*delta_q),
    S_q>=a_q^2*F_q(x,y)*delta_q/(1+a_q*delta_q).         (PU4)

The integral uses the actual prefix at this q. Later rows use their own
actual prefixes from the same sequential process. Adding their absolute
savings in PU1 is valid; multiplying unrelated optimized conditional
probabilities or switching the final law would not be justified.

The pure union can be replaced by an explicit numerical inventory upper
bound. If c_(q,e) in{0,1,2} is the number of pure-q originals at exponent
e, then

    theta_q<=p_q=sum_(e>=1)(q-1)*c_(q,e)/(2*q^e)<=1.

The lower bound in PU4 decreases as theta_q increases. Thus p_q gives
a possibly weaker but fully numerical sufficient condition. Using the
actual union is stronger when pure cylinders overlap.

## 4. One joint sufficient region

The raw auxiliary old-prime count law has mass x-1/5 or y-1/7 at count1
and weights(p-1)/p^n at counts n>=2. Increasing x or y adds positive
mass at count1. Every F_q is an integral of a nonnegative hinge against
the tensor product with the fixed later auxiliary laws. Hence it is
nondecreasing in x and y, and its minimum occurs at x=1/2,y=2/3.
The exact minima are

| q | f_q=F_q(1/2,2/3) |
| --- | ---: |
|11|97/840|
|13|47/240|
|17|202266823897/1875745872000|
|19|807126826607839/4914954383539200|

Write

    Gamma=sum_q a_q^2*f_q*(1-theta_q)/(1+a_q*(1-theta_q)),
    kreq=6168733163201163811/1650097635185615616000.

The existing NC4 identity, with d5=x-1/2 and d7=y-2/3, is

    (T-2)*alpha-Phi=-c0+A5*d5+A7*d7+A57*d5*d7,
    c0=(T-2)*kreq,

where all three A coefficients are positive. Combining it with PU1 and
PU4, and retaining the nonnegative packing credit1/12-m, proves

    (T-2)*lambda(1)-Phi >=(T-2)*(Gamma-kreq).            (PU5)

Consequently Gamma>=kreq implies R_Q(nu)<=T. If Gamma>kreq, set
Delta=(T-2)*(Gamma-kreq)>0. Finite labelwise maximizing queries under
this SAME nu, followed by increasing query boxes, give

    R_Q(nu)<=T-Delta/lambda(1)<=T-Delta<T,               (PU6)

since lambda(1)<=1. The infinite-height completion is the existing PA
comparison; no query tail is discarded. This criterion does not require
calculating, or knowing in advance, which query attains any supremum.

## 5. Missing one root occurrence gives uniform margins

If numerical modulus q itself occurs at most once, every deeper pure
label may still occur twice. Thus

    theta_q<=((q-1)/2)*(1/q+2/[q*(q-1)])
            =(q+1)/(2*q).

The resulting lower bounds for S_q are

| Restricted root label | Guaranteed absolute saving |
| --- | ---: |
|11|97/19152|
|13|47/9280|
|17|202266823897/71278343136000|
|19|2421380479823517/851925426480128000|

Either of the first two alone exceeds kreq. The sum of the last two
also exceeds it; neither of those two lower bounds alone does. PU6
therefore supplies these explicit same-law bounds:

| Sufficient root condition | Uniform query upper bound |
| --- | ---: |
|At most one occurrence at11|2733779746141627138211/542935350932041267200|
|At most one occurrence at13|79279616946006192818519/15745125177029196748800|
|At most one at17 and at most one at19|451123045202905459499/89627423011003637760|

All three are strictly below257/51. Missing all occurrences of a root
is included. No condition is imposed on higher powers of that prime or
on mixed labels containing it. The shared union condition in Section4
also applies when these simple root criteria do not.

If repeated identical classes are retained as two occurrences, two
root-q copies with the SAME residue have union mass1/q and satisfy the
same bound on theta_q. The necessary condition for a lower witness can
therefore be sharpened to two DISTINCT root residues at11 and13, and
two distinct root residues at at least one of17 and19.

## 6. Exact computation and open boundary

The [standalone calculation](../../frontier/cover-geometry/pure_union_pa_savings.py)
reconstructs every F_q, alpha and Phi from their raw auxiliary atom
weights and COMPLETE means, using finite corrections at products below
each threshold. Its [exact data](../../frontier/cover-geometry/pure_union_pa_savings.json)
include all four anchor corners, the positive NC4 coefficients, the
joint-saving requirement, all four root savings and all three final
query bounds. It imports no old producer or result table.

All30 checks pass. The retained JSON SHA256 is
`b4a04e443b5563c06b30b1dfd8480103225a8e4e338cae2c1e1d50c27435291c`.
A separate calculation reconstructs the four prefix hinges and the
NC4 constants and matches every displayed corner and final bound.
Executing a copied script at a path containing spaces from another
working directory gives identical JSON bytes on the tested macOS host.
Other operating systems were not tested.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_union_pa_savings.py
```

The program requires only Python3 and accepts `--output`. The finite
arithmetic does not substitute for PU2--PU5's ordinary proof for arbitrary
families. No Lean was added or built.

If all four pure unions approach their full two-copy geometric masses,
theta_q approaches1 and this particular saving tends to zero. Finiteness
does not give a uniform positive deficit. The dense regime still needs
a joint estimate involving actual nonpure unions, transported source
deletions or final-query response. The two-copy problem without the
stated sufficient conditions, and its separate connection to unrestricted
Erdős #7, remain unresolved.

[Report560](560-reordered-pa-pure-union-savings.md) applies the same local pure-union estimate to the fixed order13,11,19,17. It certifies root17 scarcity by itself, with all other two-copy labels unrestricted. Its sufficient region and this report's region are alternatives under their respective complete laws; their union is strictly larger, and savings from the two laws are not added.

## 7. A joint row-loss and query-cap inequality

Keep the actual process, fixed slots and weights of Sections1--3. At a
current prime q, suppress the q subscript and write

    A=q-1-2t>0, C=(q-1)/A, a=2/A,
    delta=1-(q-1)r/2, G=sum_(e,j) beta_(e,j)*(n_(e,j)-(t-1))_+.

Let g be the actual allowed Haar fraction. For g>0 define
kappa=min(C,1/g), the density on the allowed part of the actual row.
For g=0 the actual kernel is zero; define kappa=C only as its comparison
cap. This convention avoids an undefined reciprocal and admits the
usual normalized row completion. With ell=1-min(1,Cg), PU2 and
b<=t-1 give the simultaneous bounds

    Cg>=1+a(delta-G),
    ell<=a(G-delta)_+,
    kappa<=C/[1+a(delta-G)_+].                         (PU7)

For the last bound, G>=delta gives kappa<=C. If G<delta, the first
bound implies Cg>1, so kappa=1/g and the result follows. At g=0 the
first bound forces G>=delta+1/a, and all three statements remain valid.
The second bound also follows directly from ell=(1-Cg)_+. Thus PU7
is a direct consequence of PU2; the additional information retained
here is the query cap together with its joint consumption in PU8.

For any fixed Lambda,D>=0 these bounds yield

    Lambda*ell+D*kappa
      <=Lambda*a*G+D*C
        -a*delta*min(Lambda,D*C/(1+a*delta)).           (PU8)

If G>=delta, the saving from Lambda*a*G+D*C is at least
Lambda*a*delta. Otherwise put z=delta-G in[0,delta]. The saving is at
least

    a[Lambda*(delta-z)+D*C*z/(1+a*z)].

The bracket is concave in z, and its endpoint values are Lambda*delta
and D*C*delta/(1+a*delta). This proves PU8. In a target-gap application
Lambda=T-2=155/51; D must come from an independently justified,
nonnegative downstream coefficient under the same actual construction.

The auxiliary comparison law with cap kappa has atoms

    Pr(N=1)=1-kappa/q,
    Pr(N=n)=kappa*(q-1)/q^n, n>=2.

Here kappa<=C<q for the stated thresholds. Integrating a fixed payoff
against this law, with every other comparison factor fixed, is affine
in kappa whenever finite. This observation does not make later actual
kernels, normalization or a changing payoff affine in kappa. PU8 is a
joint row estimate, not yet a new complete-query certificate.

The retained truncated load b in PU2 gives a stronger pointwise form.
Set v=delta+(t-1)-b, so v>=delta>=0. Then PU2 gives

    Cg>=1+a(v-G).

Every bound in PU7 and PU8 remains valid with delta replaced by this
actual-row v, by the same proof. This retains shortages of active old
cofactors even when delta is small. The quantity v depends on the whole
old history. Its integral or correlation with a downstream coefficient
cannot be replaced by an independent auxiliary average without a further
comparison theorem. No uniform positive integrated credit is claimed.

### Local sharpness and the remaining integral

A finite arithmetic construction shows why a uniformly positive local
saving cannot be inferred merely from dense pure unions. Fix one of
the displayed q,t pairs, an integer pure height H>=2, and an integer
mixed height K>=1. At depth1 take pure
q-words0,1; at each depth e=2,...,H take

    2+q^(e-1), 2+2*q^(e-1) modulo q^e.

Use nonpure old cofactors5^i, i=1,...,t-1, all with old residue0.
For each cofactor take q-words2i+1,2i+2 at depth1, and at depths
2<=e<=K take

    2t+1+(2i-1)*q^(e-1), 2t+1+2i*q^(e-1) modulo q^e.

Within this q-coordinate these words are mutually disjoint. There are
at most two original classes per numerical label. If distinct full
labels are required before taking a parent fiber, lift the two copies
to3d q^e and9d q^e, with root residue0 and the displayed old and q
residues fixed by CRT, then take the parent fiber0 modulo9.

On the actual old cell0 modulo5^(t-1), all t-1 cofactors are active.
Writing delta=q^(-H) and epsilon=q^(-K), one obtains

    G=0,
    g=[A+2(delta+(t-1)*epsilon)]/(q-1)>1/C,
    ell=0,
    kappa=(q-1)/[A+2(delta+(t-1)*epsilon)].

The root q-1 is untouched. For the normalized conditional q-row, each
clean cylinder q-1 modulo q^e therefore has mass kappa/q^e. Its complete
clean-chain deficit from the cap-C comparison is

    Delta_(H,K)=(C-kappa)/(q-1)
      =2(delta+(t-1)*epsilon)
         /[A*(A+2(delta+(t-1)*epsilon))].              (PU9)

For K=H, Delta_(H,H)/delta tends to2t/A^2 as H grows. Letting K grow
first gives Delta_(H,K)/delta tending to2/A^2 as H grows. Thus the
G=0 reciprocal-cap bound in PU7 can be approached by finite actual
families. The corresponding pure unions have theta=1-q^(-H) tending
to one. No positive constant saving, uniform in height, follows from
these row quantities alone; a saving proportional to delta is fully
consistent with the construction.

These are genuine conditional rows, but a selected row is not the
common prefix integral. A complete old query can have count exactly t
at a selected old point, by choosing its other cylinders away from that
point. It cannot thereby have count t throughout a cell that restricts
only the5-coordinate and leaves7 Haar. For example, keeping N5=t and
using a nested7-query gives

    integral (M_old-t)_+ d rho=t*sum_(e>=1)7^(-e)=t/6

when the other old query factors equal one. Concentrating the5-law on
0 modulo125 has density125 and does not satisfy the PA anchor caps;
it cannot be substituted for the actual PA prefix. In fact the displayed
family has no5/7 anchor exclusions and is covered by the existing
u=v=0 PA certificate.

To consume PU8 globally one must identify a downstream payoff for the
same actual process, justify its coefficient D and its dependence on
the full old history, and integrate without discarding the measure of
the relevant old cells or changing the anchor law. Current loss savings
and future-query credits must belong to this same payoff before they
are added. Report560's alternative coordinate orders remain separate
complete constructions. PU7--PU9 establish a local joint bound and its
sharpness; they do not exclude a stronger integrated estimate or settle
the arbitrary two-copy target.

## 8. Vanishing actual-prefix credits can leave a positive comparison saving

For the actual PA order 5,7,11,13,17,19, a finite, explicitly fixed
two-copy family can make all three first11 local credits tend to zero:
the integrated effective shortage v, the integrated reciprocal-cap
improvement C-kappa, and the improvement of actual loss over aG.
Nevertheless these same families have a uniform positive PA baseline
slack S11>=31/1260, enough for the full nonunit query target. Thus they
obstruct a uniform additive credit from the local ledger alone, not a
joint theorem using old-query comparison slack.

This is an ordinary exact construction, with the finite verification
described at the end. No claim of Lean formalization is made.

### Explicit actual old anchor and fixed cofactor inventory

Fix K>=1. For p=5,7 and c in {1,...,p-1}, write

    A_(p,c) = union_(1<=i<=K) [c*p^(i-1)]_(p^i),
    l_p=(1-p^(-K))/(p-1),  z_p=p^(-K).

All p-classes occurring here are pairwise disjoint across depths and
colors: their first nonzero base-p digit differs. Each A_(p,c) has Haar
mass l_p; the remaining all-zero depth-K cylinder has mass z_p.

For the pure5 and pure7 original classes use colors1,2 at every depth.
For each mixed original numerical label 5^i7^j use the two CRT classes
with colors (4,4) and (4,5). Thus every used numerical anchor label has
exactly two originals. Their mixed union has Haar mass

    m=2*l5*l7.

Let lambda0 be UNNORMALIZED Haar restricted to the actual joint
survivor of these originals. This is exactly a PA anchor, not a
concentrated substitute law. Its mass is

    L=(1-2*l5)*(1-2*l7)-2*l5*l7
     =1-2*l5-2*l7+2*l5*l7.

At each future11 exponent and each of its two copy slots, use these
same fixed old cofactors and CRT residues:

* numerical cofactor 5^i: color3 in5;
* numerical cofactor 7^j: color3 in7;
* numerical cofactor 5^i7^j: colors(4,6).

The literal active nonpure cofactor count is consequently

    n=1_(A_(5,3))+1_(A_(7,3))+1_(A_(5,4))*1_(A_(7,6)).

On the actual anchor, n belongs to {0,1,2}. This description concerns
the explicitly chosen original family; it does not factor an arbitrary
query or replace any query by independently chosen marginals.

Its exact unnormalized category masses are

    P2=lambda0(n=2)=l5*l7,
    Z=lambda0(n=0)=z5*(1-3*l7)+l5*z7,
    P1=lambda0(n=1)=L-Z-P2.

Indeed n=2 is exactly the color3/color3 rectangle. An n=0 survivor
either has5 in the all-zero tail and7 outside color3, or has5 in color4
and7 in its all-zero tail. All other survivors have n=1.

Writing u=5^(-K), w=7^(-K) gives

    L=(3+5u+3w+uw)/12,
    Z=u/2+w/4+uw/4,
    P2=(1-u)*(1-w)/24.

Hence L->1/4, m->1/12, Z->0, and P2->1/24. This reaches the actual
worst anchor corner x=1/2,y=2/3,m=1/12; it is not the no-anchor case.

### Three fixed and disjoint current11 channels

Fix H>=1 and epsilon=11^(-H). Define two words per exponent in each of
three11 channels:

| channel | exponent1 words | exponent e>=2 words |
| --- | --- | --- |
| P | 0,1 modulo11 | 2+11^(e-1), 2+2*11^(e-1) modulo11^e |
| X | 3,4 modulo11 | 5+11^(e-1), 5+2*11^(e-1) modulo11^e |
| Y | 6,7 modulo11 | 8+11^(e-1), 8+2*11^(e-1) modulo11^e |

All words across these channels are mutually disjoint cylinders.
Different channels use disjoint root digits. Within a channel, the
deep words use a separate root and their first nonzero higher digit
specifies their exponent and copy.

Use P for pure11 originals. Use X for every pure5 and mixed5/7 cofactor
above; use Y for every pure7 cofactor. For each such cofactor and11
exponent, its two actual original residues are fixed by CRT with the
two words in the assigned channel. Every numerical label has exactly
two copies; there are no extra labels or query-dependent choices.

At n=1 exactly one channel X or Y is active. At n=2 both are active.
The mixed5/7 channel never overlaps either pure5 or pure7 cofactor
event. Each active channel excludes the Haar fraction

    r=2*sum_(e=1)^H 11^(-e)=(1-epsilon)/5.

Consequently the literal current allowed fractions are

    g_n=1-(1+n)*(1-epsilon)/5
       =(4-n+(n+1)*epsilon)/5.

The pure-current deficit is delta=epsilon. Since every exponent-slot
has the same old count n and the beta weights sum to1-epsilon,

    b=(1-epsilon)*1_(n>=1),
    G=(1-epsilon)*1_(n=2),
    v=delta+1-b.

Thus v=1+epsilon at n=0 and v=2epsilon at n>=1. With a=1/3,C=5/3,
the retained PU2 inequality is in fact equality:

    C*g=1+a*(v-G).

### All three local-ledger credits vanish

The actual row cap and loss are kappa=min(C,1/g), ell=(1-Cg)_+.
Because H>=1, epsilon<=1/11<1/3, so their values are

| n | g | kappa | ell |
| --- | --- | --- | --- |
|0|(4+epsilon)/5|5/(4+epsilon)|0|
|1|(3+2epsilon)/5|5/(3+2epsilon)|0|
|2|(2+3epsilon)/5|5/3|1/3-epsilon|

Integrating against the same actual lambda0 gives the exact identities

    integral v = Z+epsilon*(2L-Z),

    integral (C-kappa)
      =Z*5*(1+epsilon)/(3*(4+epsilon))
        +P1*10*epsilon/(3*(3+2epsilon)),

    integral G=(1-epsilon)*P2,
    Loss11=(1/3-epsilon)*P2,

    a*integral G-Loss11=(2*epsilon/3)*P2.

All three nonnegative credits tend to zero as K,H tend to infinity.
In particular, for fixed Lambda>=0 and ANY nonnegative old payoff D
uniformly bounded by one finite M independently of K,H,

    integral [Lambda*a*G+D*C-Lambda*ell-D*kappa]
      <=Lambda*(2*epsilon/3)*P2+M*integral(C-kappa)
      ->0.

There can therefore be no uniform strictly positive additive gain
relative to this actual count-and-cap ledger across all actual PA
anchors and fixed two-copy families. This statement does not cover a
payoff with unbounded family-dependent D, or an estimate retaining a
separate old-query comparison gap.

### The same family already crosses the complete-query target

The latter distinction has a useful exact consumer. At the limit,

    F11(1/2,2/3)-integral G
      ->97/840-1/24=31/420>0.

More strongly, at EVERY finite K,H,

    Loss11=(1/3-epsilon)*l5*l7 <=1/72,
    F11(x,y)>=F11(1/2,2/3)=97/840.

Hence the ACTUAL PA baseline slack obeys

    S11=a*F11-Loss11 >=97/2520-1/72=31/1260.

Later13/17/19 rows may be arbitrary under the existing two-copy PA
hypotheses: their corresponding S_q and the packing credit remain
nonnegative. The existing NC4 identity and PU1 therefore imply

    (T-2)*lambda(1)-Phi
      >=(T-2)*(31/1260-kreq)>0,

where T=257/51 and

    kreq=6168733163201163811/1650097635185615616000.

The same complete-query comparison and one final normalization give

    R_Q(nu)<=T-(T-2)*(31/1260-kreq)
      =100057015925264522393/20108716701186713600
      =4.975803151046415... <257/51.

This uniform strict certificate applies to the explicit first11 family
with arbitrary permitted later rows; it does not solve arbitrary
first11 inventories. It demonstrates that vanishing local credits
need not identify a genuinely difficult full construction. A productive
remaining theorem could trade cap/loss credit against old-query
comparison slack, within one actual law.

The [actual-family calculation](../../frontier/cover-geometry/actual_anchor_v_cap_obstruction.py)
and [data](../../frontier/cover-geometry/actual_anchor_v_cap_obstruction.json)
check all nine K,H pairs in{1,2,3}^2 using actual CRT originals, the
old survivor histogram and current allowed sets. All12112 checks pass,
including the exact full-query bound above. The formulas, rather than
this finite sample, prove the all-height limits and uniform consumer.

## 9. Actual cap slack gives an additive complete-query debit

For the fixed PA order and caps of this report, Section7's conditional
cap improvement has a complete-query consumer. Let `lambda_<q` be the
actual unnormalized prefix before row `q`, and retain its actual allowed
fraction `g_q(h)` and `kappa_q(h)=min(C_q,1/g_q(h))`, with `kappa_q=C_q`
when `g_q=0`. Define

\[
K_q=\int(C_q-\kappa_q(h))\,d\lambda_{<q}(h),\qquad
D_{\rm cap}=\sum_{q=11,13,17,19}\eta_q K_q.
\tag{CS1}
\]

The four positive coefficients are

| `q` | `C_q` | `eta_q` |
|---|---|---|
|11|`5/3`|`641451990131/13653911814400`|
|13|`3/2`|`130632977/5642112320`|
|17|`2`|`118307/16692640`|
|19|`9/5`|`1/6498`|

For every finite query with one globally fixed phase per numerical
label and its unit included once, the same final actual measure obeys

\[
\int(L-3)_+\,d\lambda_{\rm final}
\le\Phi(x,y)-D_{\rm cap}.
\tag{CS2}
\]

Consequently, writing `s=lambda_final(1)>0` and normalizing this law
only once,

\[
R_Q(\lambda_{\rm final}/s)
\le 2+\frac{\Phi(x,y)-D_{\rm cap}}s.
\tag{CS3}
\]

This strictly improves the previous numerator whenever `Dcap>0`.
No uniform positive lower bound for `Dcap` is asserted. The result
allows arbitrary finite original inventories, phases and heights under
the two-copy rule on `Q={5,7,11,13,17,19}`.

### A compulsory part of the complete query controls the cap slope

First fix a complete finite exponent box and every query phase. Use the
conditional convex comparison of Report348, processing the last
coordinate first. At row `q`, the later coordinates have already been
replaced in the main term by their full-cap auxiliary uniforms.
Condition on these uniforms and on the actual earlier history.

Let `S_e` count the active labels in current exponent layer `e`, after
all earlier and later tests except the current `q` test. Put
`A_e=S_0+...+S_e` and `phi(n)=(n-3)_+`. Comparing the current cylinders
to one common nested uniform with cap `c<q` gives the affine envelope

\[
B(c)=\phi(A_0)+c\sum_{e=1}^{H_q}q^{-e}
                            [\phi(A_e)-\phi(A_{e-1})].
\tag{CS4}
\]

This comparison permits arbitrary original query-phase overlaps; it
does not choose new actual residues conditional on the history.
The complete box contains every label with zero exponents on earlier
primes. Thus, in every current layer including layer zero,

\[
S_e\ge Z_H:=\prod_{r>q}\left(1+
                \sum_{f=1}^{H_r}\mathbf1_{\{U_r\le C_r/r^f\}}\right).
\]

Convexity and monotonicity of `phi` give

\[
\phi(A_e)-\phi(A_{e-1})
\ge\phi((e+1)Z_H)-\phi(eZ_H).
\]

In particular `B(C_q)-B(kappa_q)` is at least
`(C_q-kappa_q) beta_(q,H_q)(Z_H)`, where

\[
\beta_{q,H}(z)=\sum_{e=1}^H q^{-e}
                     [\phi((e+1)z)-\phi(ez)].
\tag{CS5}
\]

Averaging the already replaced later uniforms gives a coefficient
`eta_(q,H)=E beta_(q,H_q)(Z_H)` independent of the actual earlier
history. Its geometric-sum limit is

\[
\beta_q(z)=
\begin{cases}
1/[q^2(q-1)]&z=1,\\
(q+1)/[q(q-1)]&z=2,\\
z/(q-1)&z\ge3.
\end{cases}
\]

For `Z=product_(r>q) N_(r,C_r)`, this yields

\[
\eta_q=\frac{\mathbb EZ}{q-1}
       -\frac{q+1}{q^2}\Pr(Z=1)-\frac1q\Pr(Z=2).
\tag{CS6}
\]

The necessary exact moments are

| `q` | `E Z` | `Pr(Z=1)` | `Pr(Z=2)` |
|---|---|---|---|
|11|`891/640`|`2967/4199`|`21492961/88158005`|
|13|`99/80`|`258/323`|`93598/521645`|
|17|`11/10`|`86/95`|`162/1805`|
|19|1|1|0|

### Backward extraction preserves the actual source of every debit

Where `g_q>1/C_q`, the actual row is already normalized, with density
`kappa_q=1/g_q` on its allowed set. Therefore CS4--CS5 subtract the
stated cap debit from the full-cap comparison. Where `g_q<=1/C_q`,
the debit is zero; the ordinary normalized completion dominates the
subprobability row for this nonnegative payoff. This includes `g_q=0`.

Integrating the conditional inequality against the actual `lambda_<q`
extracts the scalar `eta_(q,H)K_q`. Keep it outside subsequent backward
comparisons. Only the remaining main term is compared at the preceding
row. This gives, successively for19,17,13,11,

\[
\int\phi(L_H)\,d\lambda_{\rm final}
\le\Phi_H(x,y)-\sum_q\eta_{q,H}K_q.
\tag{CS7}
\]

At the last step the actual old survivor is dominated by the product
of its actual pure5/7 restrictions, as in the original PA argument.
Each `K_q` still uses its own actual unnormalized prefix; no debit has
been transported to an auxiliary law or multiplied by another prefix
mass.

Complete any prescribed finite query to larger boxes with arbitrary
globally fixed phases. Its hinge can only increase. Independently,
`Phi_H` increases to `Phi`, and `eta_(q,H)` increases to `eta_q`;
CS5 is increasing both in its height and in `z`, and is bounded by
`z/(q-1)`. The full future product has finite first moment. Taking the
two limits in CS7 proves CS2, without assuming that their difference
is monotone. Simultaneous phase maximization on each finite inventory
and exhaustion under this one final law then prove CS3.

### A same-law consumer and its remaining quantitative condition

Since the cap slack is supported on rows of mass exactly one,

\[
K_q=\int_{1/C_q}^1
        \lambda_{<q}\{g_q>t\}\,\frac{dt}{t^2}.
\tag{CS8}
\]

An actual bin of prefix mass `b` with `g_q>=r>1/C_q` contributes at
least `b(C_q-1/r)`. Several disjoint bins can be added. This uses no
claim about query/original intersection and no killed mass.

For `T=257/51`, the precise sufficient condition from CS3 is

\[
D_{\rm cap}\ge\Phi-(T-2)s \quad\Longrightarrow\quad R_Q\le T.
\tag{CS9}
\]

A strict premise gives `R_Q<T`. In particular, using only the old
lower bound `s>=alpha(x,y)`, write
`Gamma(x,y)=Phi-(T-2)alpha`. Then `Dcap>=Gamma` suffices.
The full actual mass identity gives the sharper condition

\[
D_{\rm cap}+(T-2)
 \left(\tfrac1{12}-m_{\rm mixed}+\sum_qS_q\right)
\ge\Gamma(x,y).
\tag{CS10}
\]

Every term here comes from the same actual process. At the formal
corner `x=1/2,y=2/3`, `Gamma` equals
`c=6168733163201163811/542935350932041267200`. The sufficient numerical
assumptions `K11>=1/6`, `K13>=1/8`, `K17>=1/10` give

\[
D_{\rm cap}-c\ge
\frac{3502514252639023}{49357759175640115200}>0.
\]

These are arithmetic assumptions, not claimed universal or jointly
attained slack values. The first11 slack alone cannot supply this
corner deficit using the old mass lower bound: `K11<=2/9` and

\[
c-\tfrac29\eta_{11}
=\frac{26345565509485633}{28575544785896908800}>0.
\]

For Report348's all-supported-laws witness with strict query lower
bound above `T`, CS9 imposes the additional necessary strict inequality
`Dcap<Phi-(T-2)s`. Proving this impossible for every remaining family
requires a further actual joint estimate. CS2 also supplies the
previously missing nonnegative coefficient `D=eta_q` for PU8 within
this fixed complete-query construction. It neither settles arbitrary
two-copy families nor unrestricted Erdős #7.

The [exact coefficient producer](../../frontier/cover-geometry/pa_cap_slack_numerator.py)
and [rational data](../../frontier/cover-geometry/pa_cap_slack_numerator.json)
verify CS6, finite-height coefficients and the stated consumer margins.
The arbitrary-phase and all-height conclusions follow from CS4--CS7's
proof, not from finite samples. No Lean was added or run.

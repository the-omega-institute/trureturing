[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="sparse-tail-extensions-of-conditioned-heads"></a>
# Sparse tails preserve strict fees under the actual conditioned head law

A strict conditional-kernel fee on a head set of child primes extends
to a finite tail with sufficiently small reciprocal mass. The head
need not be a separate graph block. The results below give explicit
extensions for the 160 kernel heads and two coupled first-root heads of
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md),
four large head primes, and the literal-sensitive five-child core of
[Chapter 26](26-literal-pure-classes-and-six-vertex-residue-branches.md).

The original congruence family is finite, with pairwise distinct odd
moduli greater than 1. All complete prime-power coordinates, original
residues, and supports are retained, including supports meeting every
head and tail coordinate. Components containing 3 are rooted at 3, so
all children are at least 5. **Every tail prime in this chapter is at
least 7.** The tail bounds below concern the particular finite set of
added primes. They give no unrestricted dense-small-prime continuation
and do not settle unrestricted noncoverage.

Use the unchanged fees and descendant-density invariant of Chapter 23,
with total fee bound \(F=187/384<1/2\), \(c_5=3/10\), and
\(c_q=2/(q-1)\) for \(q\ge7\). All child domains are the actual
domains admitting an avoiding extension through their strict descendants,
including avoidance of their original pure classes.
The probability and recursive arguments are ordinary mathematical
proofs; the accompanying exact calculations are not Lean verification.

## 1. Continue one actual conditioned head kernel

Let the children of a block with parent prime \(p\) be the disjoint
union \(J=H\sqcup T\). Write
\[
 \nu=\bigotimes_{q\in J}H_q(\,\cdot\mid V_q)
\]
for the product of the actual nonempty child-domain laws. At each
complete parent word \(x\), let \(R_x^H\) avoid exactly the old
head-only internal classes and the head-only crossing classes at parent
exponents \(1,\ldots,t\) matching \(x\). Assume an integer
\(t\ge1\), \(\nu_H(R_x^H)>0\) for every \(x\), and put
\[
 \kappa_x=\nu_H(\,\cdot\mid R_x^H).
\]
Suppose there is a nonnegative cap \(g(d)\) for each nonunit numerical
head cofactor, valid simultaneously for every \(x\) and every literal
residue \(r\bmod d\), such that
\[
 \kappa_x(C_{d,r})\le g(d),\qquad
 \sum_{d>1}g(d)\le R.
\]
The sum ranges over distinct products of head prime powers within the
original complete-coordinate heights, not repeated occurrences at
different parent exponents. Set \(g(1)=1\). Infinite geometric sums
may majorize these finite sums without adding original labels. The
strict-region kernel in Chapter 23 supplies these uniform caps with
\(R=L_t/Z_t\); other independently proved head kernels may supply
their own caps.

For the tail choose positive actual density lower bounds
\(d_q\le H_q(V_q)\), and define
\[
 b_q=\frac1{(q-1)d_q},\qquad
 \Delta=\prod_{q\in T}(1+b_q)-1,\qquad
 \Lambda=(t+1)(1+R)\Delta.
\]
If \(\Lambda<1\), the full block's blocker \(B\), before deleting
pure-parent classes, satisfies
\[
 H_p(B)\le
 \frac{R+(1+R)\Delta}
 {p^t(p-1)\bigl[1-(t+1)(1+R)\Delta\bigr]}.
 \tag{HT1}
\]

To prove this, fix \(x\) and use the actual law
\[
 \lambda_x=\kappa_x\otimes
                   \bigotimes_{q\in T}H_q(\,\cdot\mid V_q).
\]
It is precisely \(\nu\) conditioned on head-only old and shallow
avoidance. Under this law, the sum of literal cylinder caps for all
cofactors touching \(T\) is at most \((1+R)\Delta\): the head and
tail factors are independent, the head factor may be the unit cofactor,
and every nonempty tail support is included. There is at most one old
layer and at most \(t\) shallow layers, with each numerical cofactor
occurring at most once in each layer. Their remaining forbidden union
has \(\lambda_x\)-mass at most \(\Lambda\). Conditioning on its
actual complement gives exactly the full shallow-survivor law \(\mu_x\),
at a normalization cost at most \(1/(1-\Lambda)\).

If \(x\) is blocked, each point remaining under \(\mu_x\) meets a
matching deep crossing class. Before the final normalization, the sum
of their cofactor caps is at most \(R+(1+R)\Delta\). At a fixed
parent exponent \(a\), every complete numerical child cofactor occurs
at most once globally over parent residues, by original modulus
distinctness. Integration over the original parent Haar marginal
therefore incurs at most
\[
 \sum_{a>t}p^{-a}=\frac1{p^t(p-1)},
\]
which proves (HT1). Cutoffs above the actual parent height are allowed:
absent layers contribute no events. All child heights likewise remain
arbitrary and finite. The joint law \(H_p(dx)\mu_x(dy)\) preserves
the original parent marginal; it is not asserted to be a product law.

## 2. A strict fee has an explicit continuation radius

Suppose the head's parent-3 benchmark has a strict fee \(C\), so that
\(R<X\), where \(X=2\cdot3^t C\). The right side of (HT1) at
parent 3 is strictly below \(C\) whenever
\[
 \Delta<\frac{X-R}{(1+R)\bigl[1+(t+1)X\bigr]}.
 \tag{HT2}
\]
Indeed, this is exactly
\[
 R+(1+R)\Delta
 <X\bigl[1-(t+1)(1+R)\Delta\bigr],
\]
and it also forces the bracket to be positive. Half the right side of
(HT2) is an explicit allowable non-strict upper bound on \(\Delta\).

For the reciprocal-tail specializations, choose the density lower
bound from the descendant invariant, or a proved stronger bound. For
every tail prime \(q\ge7\), actual expense \(e_q\le F<1/2\) then gives
\[
 b_q\le\frac1{q-2-2e_q}\le\frac1{q-3}.
\]
Consequently, for
\(\sigma(T)=\sum_{q\in T}1/(q-3)<1\),
\[
 \Delta\le\frac{\sigma(T)}{1-\sigma(T)}.
 \tag{HT3}
\]
Expand the product into elementary symmetric sums and bound its
degree-\(j\) sum by \(\sigma(T)^j\). This is a restriction on the
chosen finite tail, not a claim that the prime reciprocal series
converges. Arbitrarily large finite tails satisfying any fixed positive
bound exist by choosing distinct sufficiently large primes.

With the same head and tail caps, the ratio of the right side of (HT1)
at parent \(p\) to its value at parent 3 is
\[
 \frac2{p-1}\left(\frac3p\right)^t.
\]
For \(p\ge7\) this is at most \(c_p=2/(p-1)\). For \(p=5\)
and \(t\ge1\), it is at most \(3/10=c_5\). Thus a strict
parent-3 benchmark supplies the unchanged scaled fees in all legal
non-3 orientations of that same head, provided the head caps apply
there. The literal-sensitive core below uses a separate baseline for
its non-3 orientations.

## 3. One tail bound extends all 160 inherited kernel rows

The Chapter 23 kernel certificate gives
\[
 \frac RX\le r_*:=\frac{65157018363904}{65378462038225}<1,
 \qquad 1\le t\le7,\qquad \frac3{8192}\le X<2200.
\]
Set \(\varepsilon=1-r_*\). The quadratic
\[
 10^7\varepsilon X-(1+X)(1+8X)
\]
is concave and positive at both endpoints \(3/8192\) and \(2200\).
It is therefore positive throughout the interval. Since
\(R\le r_*X\) and \(t+1\le8\), the bound
\(\Delta\le10^{-7}\) satisfies (HT2) for every one of the 160 rows.
By (HT3), it suffices that
\[
 \sigma(T)=\sum_{q\in T}\frac1{q-3}\le\frac1{10000001}.
 \tag{HT4}
\]

Each inherited row uses fixed dominating head caps and charges only
its actual small head primes. These charges remain valid after adding
the tail: the actual descendant sets avoid the entire current block,
so the original outside-budget upper bounds still apply. Tail primes
need not receive an additional charge, and their actual descendant
expenses remain bounded by \(F\). The parent comparison in Section 2
pays all legal non-3 orientations.

## 4. Extend the two coupled first-root heads

For \(H=(5,7,11,13)\) or \((5,7,11,17)\), retain the inherited
old-head quantities
\[
 Z=Z_H(w)>0,\qquad
 L=\sum_{\varnothing\ne S\subseteq H}b_S Z_{H\setminus S}(w).
\]
Here singleton entries of \(w\) vanish and the other entries are
\(b_S\). The coupled first-root certificate supplies a target blocker
mass \(M\) and a strict gap \(g\) between the minimum weighted
first-root avoidance polynomial and \(L/6\).

At parent 3, a hypothetical blocker of mass at least \(M\) admits a
weight \(0\le h\le\mathbf1_B\) with \(\int h\,dH_3=M\).
Use the single actual old-head law
\[
 \lambda=\nu(\,\cdot\mid\text{old head avoidance})
         =\mu_H\otimes\nu_T.
\]
At a blocked parent word, every point avoiding the head first-root
classes must hit a tail-touching old class, a tail-touching crossing
class, or a head-only class at parent depth at least two. Their
integrated costs are at most, respectively,
\[
 M(1+L/Z)\Delta,\qquad
 \frac12(1+L/Z)\Delta,\qquad \frac{L}{6Z}.
\]
The first bound uses \(\int h=M\); the other two use \(h\le1\)
and original parent-prefix Haar masses. If \(\beta_j\) is the
\(h\)-mass of first-root branch \(j\) and \(y_j\) its head
support-load vector, multiplication by \(Z\) gives
\[
 \sum_j\beta_j Z_H(w+y_j)
 \le\frac L6+(Z+L)\Delta\left(M+\frac12\right).
 \tag{HT5}
\]
The original allocation constraints used by the inherited first-root
argument are retained. Thus
\((Z+L)\Delta(M+1/2)<g\) preserves its contradiction.

Both heads satisfy this strict inequality at \(\Delta=1/400\).
The target and the assigned full head fee have the following distinct
roles:

| Head | Target \(M\) | Assigned head fee \(C\) | Remaining first-root gap |
| --- | ---: | ---: | ---: |
| \(5,7,11,13\) | \(15/32\) | \(23/48\) | \(1196487308249/4738675993920000\) |
| \(5,7,11,17\) | \(355/768\) | \(355/768\) | \(48931618037787833/4381093478794260480\) |

Therefore \(\sigma(T)\le1/401\) suffices. For legal non-3
parents, use the inherited \(t=1\) kernels and (HT1) separately.
Their smallest legal parent primes are 17 and 13, respectively. The
normalized bounds \(H_p(B)/c_p\) at those primes are at most
\[
 \frac{22727488713091}{228136596158612}<\frac{23}{48},\qquad
 \frac{4447861097523547}{39541533590637156}<\frac{355}{768}.
\]
Larger legal parents decrease these bounds. No coupled parent-3
certificate is transferred between parent primes.

## 5. Four large head primes

For any four-child head with \(s=\min H\ge31\), the elementary
product-conditioning proof in Chapter 23, Section 5, supplies head
cylinder caps with \(R<1\) at \(t=(s-3)/2\). This uses that proof;
it does not assume Shearer positivity at the same cutoff. The tail
condition
\[
 \sigma(T)\le\frac1{2s-1}
\]
gives \(\Delta\le1/[4(t+1)]\), hence \(\Lambda<1/2\). The
aggregate ratio in (HT1) consequently satisfies
\[
 \frac{R+(1+R)\Delta}{1-(t+1)(1+R)\Delta}
 <2+\frac1{t+1}<\frac94\le\left(\frac32\right)^t.
\]
The parent-3 bound is strictly below
\(2^{-(t+1)}=f(s)\). Charge the actual smallest head prime \(s\).
Every legal non-3 orientation follows from the ratio in Section 2.

## 6. The literal-sensitive five-child core

Let \(H=\{5,7,11,13,17\}\), with head charge \(C=371/768\),
and impose
\[
 \sigma(T)\le\frac1{129},\qquad\text{so}\qquad
 \Delta\le\frac1{128}.
\]
At parent 3, assume one of Chapter 26's three literal conditions: the
original modulus 5 is absent; the original modulus 15 is absent; or
both are present with the same residue modulo 5. Its actual-pure
conditional head kernel has cutoff \(t=1\) and
\[
 R=6K_*,\qquad K_*=\frac{328823862662848}{743415381507325}.
\]
Equation (HT1) gives
\[
 H_3(B)\le\frac{255253085082551677}{538346710307812644}
          <\frac{371}{768},
\]
with fee margin
\[
 \frac{307688348399900249}{34454189459700009216}>0.
\]
The added tail preserves the actual-pure argument: only the five head
fees are charged, so every head descendant expense remains at most
\(F-C=1/256\). Equation (HT1) includes every tail-touching original
label and retains all original finite heights.

For a non-3 parent use a separate head kernel, with no literal-5/15
condition. The baseline five-child vector is strict at \(t=1\) and has
\[
 R=\frac{1601702426740864}{265038168341245}<7.
\]
At \(\Delta\le1/128\), the aggregate ratio in (HT1) is below
\(113/14\). A legal non-3 parent is at least 19, so
\[
 \frac{H_p(B)}{c_p}<\frac{113}{28p}
 \le\frac{113}{532}<\frac{371}{768}.
\]
This argument uses neither the parent-3 literal condition nor its
improved \(R\). The exact baseline calculation at \(p=19\) gives
the sharper normalized bound
\[
 \frac{206884651217912701}{1147273365585575396},
\]
with positive fee margin
\(66687751624222879387/220276486192430476032\).

## 7. Recursive scope and exact certificate

Only a subset of each new block's actual immediate child primes is
charged. Across outgoing blocks at a common parent, these assigned
sets are disjoint subsets of its strict descendant set. The existing
finite bottom-up induction therefore closes with unchanged fees and
actual child domains; pure classes remain separately charged. Chapter
26 supplies the strengthened actual-pure invariant when its core
branch is used. The local condition is imposed wherever that branch
is needed. All mixed supports spanning \(H\) and \(T\) are present
in (HT1) and (HT5).

These permitted dense blocks can be used wherever their local
hypotheses hold in the same recursive construction, with arbitrary
finite original heights and residues. The reciprocal-tail restrictions
remain substantive. In particular, the core extension does not pay
its parent-3 branch when both literal moduli 5 and 15 are present with
different mod-5 residues.

The standard-library program
[head_tail_extension_certificate.py](../frontier/cover-geometry/head_tail_extension_certificate.py)
and its [exact data](../frontier/cover-geometry/head_tail_extension_certificate.json)
consume the explicitly supplied
[Chapter 23 certificate](../frontier/cover-geometry/conditional_kernel_block_certificate.json).
The program records that input's SHA256, checks both endpoints of the
uniform-radius quadratic, and verifies the extension inequality at each
of the 160 inherited cutoffs. It retains every resulting fee margin.
For the two coupled heads it evaluates the old and cutoff-1 residuals
by coordinate recurrence and direct disjoint-support summation, then
checks the remaining first-root gaps and separate non-3 comparisons.
It also checks the literal-sensitive core continuation and its separate
baseline non-3 bound.

The value \(K_*\) is a fixed rational input from Chapter 26, equation
(LP12); this program does not reprove that input's literal premise.
The probability transport, actual-pure premise, unbounded large-head
argument, and recursive assembly remain the ordinary proofs above and
in Chapters 23 and 26. The inherited conditional inequality is the
Scott--Sokal result cited in Chapter 23,
[arXiv:cond-mat/0309352v2](https://arxiv.org/abs/cond-mat/0309352v2).
These applications claim no new probability theorem or Lean result.

Python 3.10 or later is required. Both input and output paths are
explicit arguments; optimized `-O` execution is rejected. From the
repository root run:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/head_tail_extension_certificate.py --inherited docs/reports/erdos7-odd-covering/frontier/cover-geometry/conditional_kernel_block_certificate.json --output /tmp/head-tail-extension-certificate.json
```

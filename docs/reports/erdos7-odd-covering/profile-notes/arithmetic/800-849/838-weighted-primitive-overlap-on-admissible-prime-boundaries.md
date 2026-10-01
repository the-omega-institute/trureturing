# Periodic query weights preserve maximal-label Fourier isolation

A nonnegative query weight can preserve the original maximal-label
Fourier identity exactly. The sufficient condition is arithmetic: the
weight's period must not supply every prime-power layer missing from any
other original modulus. This gives a positive joint-incidence interface
for arbitrary original supports, heights and phases, with an explicit
restriction on the weight. It supplies the signed moment missing from
[report 336](../../321-384/336-maximal-label-fourier-overlap-and-uncovered-density.md#the-missing-transport-is-a-signed-joint-moment),
rather than replacing one measure by another.

The criterion is necessary and sufficient for the termwise character
annihilation used in the proof, uniformly over all nonnegative weights
of the stated period. It is not asserted necessary for cancellation of
the total expression for one fixed family. A hitting-set description
identifies the largest admissible period for each chosen set of retained
prime-power cutoffs. The noncovering inequality keeps the actual weighted
uncovered mass; its whole-cover specialization can force overlap with a
specified partner family only after paying the other partners and their
multiplicity. No unconditional positive debit or resolution of Erdős #7
is claimed.

The all-family results below are ordinary finite Fourier and CRT proofs.
Section 9 gives bounded exact controls of the stated interfaces and
examples. There is no new Lean declaration or Lean verification.

## 1. One actual family, one Haar carrier and one periodic weight

Let

$$
A_i=[a_i]_{d_i},\qquad L=\sum_i\mathbf1_{A_i},
$$

be a finite family of distinct original moduli $d_i>1$. Choose one
original $C=[a]_d$ whose modulus is maximal under divisibility. Thus
no other $d_i$ is a multiple of $d$. Let $N$ be any common
multiple of the original moduli and the finite query periods used below,
and let $\mu$ be uniform probability on $\mathbb Z/N\mathbb Z$.
Enlarging this carrier by independent Haar digits changes none of these
finite-cylinder expectations.

For $q\mid N$, a $q$-measurable weight means an arbitrary function
$w:\mathbb Z/N\mathbb Z\to\mathbb R_{\ge0}$ depending only on
$x\bmod q$. Consider the conditions

$$
d\nmid q,\qquad
d\nmid\operatorname{lcm}(q,d_i)\quad(i\ne *),       \tag{WI1}
$$

where $*$ denotes the chosen original $C$.

For every $k$ coprime to $d$, define

$$
\chi_k(x)=\exp(2\pi i k(x-a)/d).
$$

Then WI1 implies the exact identities

$$
\mu(w\chi_k)=0,\qquad
\mu(w\mathbf1_{A_i}\chi_k)=0\ (i\ne *),\qquad
\mu(w\mathbf1_C\chi_k)=\mu(w\mathbf1_C).
$$

Consequently, with $\beta_w=\mu(w\mathbf1_C)$,

$$
\boxed{\mu\bigl(w(L-1)\chi_k\bigr)=\beta_w.}       \tag{WI2}
$$

**Proof.** A function of period $\ell\mid N$ has zero inner product
with a character of order $d$ unless $d\mid\ell$. Indeed, on
each residue class modulo $\ell$, sum the geometric progression with
ratio $\exp(2\pi i k\ell/d)$. Its sum is zero when this ratio is
not one, because $d\mid N$. Apply this with periods $q$ and
$\operatorname{lcm}(q,d_i)$. On $C$, the character equals one.
Linearity gives WI2. This proof retains the actual original residues and
uses no independence assertion about the original events. $\square$

Averaging WI2 over primitive characters gives

$$
R_d(t)=\frac1{\varphi(d)}\sum_{(k,d)=1}e^{2\pi i kt/d},
\qquad
\boxed{\mu\bigl(w(L-1)R_d(x-a)\bigr)=\beta_w.}     \tag{WI3}
$$

The right side is the actual query-weighted mass on the selected
original class. It is generally neither $1/d$ nor $\mu(w)/d$.

## 2. The termwise criterion is exact

For a fixed primitive $\chi_k$,

$$
\begin{aligned}
&\mu(w\chi_k)=0\text{ for every nonnegative }q\text{-measurable }w
&&\Longleftrightarrow d\nmid q,\\
&\mu(w\mathbf1_{A_i}\chi_k)=0\text{ for every such }w
&&\Longleftrightarrow d\nmid\operatorname{lcm}(q,d_i).       \tag{WI4}
\end{aligned}
$$

The reverse implications are the period argument above. For necessity
in the first line, if $d\mid q$, take $w$ to be the indicator of
any nonempty residue class modulo $q$. The character is constant and
nonzero there, so its weighted average is nonzero. For the second line,
take $w=\mathbf1_{[a_i]_q}$. Its intersection with $A_i$ is the
nonempty class $[a_i]_{\ell}$, where
$\ell=\operatorname{lcm}(q,d_i)$. If $d\mid\ell$, the average
equals $\chi_k(a_i)/\ell\ne0$.

Thus WI1 is exactly the criterion for all the separate cancellations
used by WI2, uniformly over the weight algebra. A particular weight can
have additional cancellations. Contributions from different original
labels or from the constant term can also cancel after summation; WI4
does not exclude that possibility or claim a necessary condition for
every such total cancellation.

## 3. Missing prime-power layers give a hitting-set boundary

For each other original label set

$$
D_i=\{p\mid d:v_p(d_i)<v_p(d)\},\qquad
T(q)=\{p\mid d:v_p(q)<v_p(d)\}.
$$

Maximality of $d$ makes every $D_i$ nonempty. Direct comparison
of prime valuations gives

$$
d\nmid\operatorname{lcm}(q,d_i)
\quad\Longleftrightarrow\quad T(q)\cap D_i\ne\varnothing.
$$

The additional condition $d\nmid q$ is exactly $T(q)\ne\varnothing$.
It must still be included for a one-label family. Hence WI1 holds exactly
when the nonempty set $T(q)$ meets all the $D_i$.

For any nonempty hitting set $T\subseteq\{p:p\mid d\}$, the largest
admissible divisor of $N$ with this exact set of cut coordinates is

$$
q_T=
\prod_{p\in T}p^{v_p(d)-1}
\prod_{p\mid N,\ p\notin T}p^{v_p(N)}.             \tag{WI5}
$$

It cuts only the selected axes just below the selected original's
highest requested digit, and retains the complete carrier on every
uncut axis. Every admissible $q$ divides $q_{T(q)}$, which is
itself admissible. Inclusion-minimal nonempty hitting sets give the
maximal admissible periods under divisibility. There is no assertion
that minimizing the number of cuts maximizes the useful query debit;
different axes and heights can have different costs for the task.

For example, take original moduli $45,21,35$ and select $d=45$.
The two missing-layer sets are $\{3,5\}$ and $\{3\}$. With
$N=315$, choosing $T=\{3\}$ gives $q_T=105$. Arbitrary weights
depending jointly on $x\bmod3$, $x\bmod5$ and $x\bmod7$
preserve the identity; only the second ternary digit is hidden. This
statement holds for every choice of the three original residues.

The construction permits arbitrary original support sizes and heights.
It restricts the weight, not the original family. A usable nonconstant
weight need not exist at the query threshold required by an application.

There is an equivalent residual-label formulation. Put
$e=d/\gcd(d,q)$ and $e_i=d_i/\gcd(d_i,q)$. Prime by prime,
$$
d\mid\operatorname{lcm}(q,d_i)\quad\Longleftrightarrow\quad e\mid e_i.
$$
Thus WI1 says $e>1$ and no other original tag has residual modulus
divisible by $e$. The selected residual is divisibility-maximal and
is not repeated by another tag; other incomparable maximal residuals
are allowed. Distinct original moduli need not remain distinct after
projection, so their tags and active residues must be retained.

## 4. Weighted uncovered mass and weighted overlap

As in report 336, put

$$
v=\mathbf1_{\{L=0\}},\quad e_{\rm exc}=(L-1)_+,\quad
S_w=\mu(wv),\quad E_w=\mu(we_{\rm exc}),\quad
H_w=\mu\bigl(w(L-1)\bigr)=E_w-S_w.
$$

Since $L\ge1$ on $C$,

$$
X_w=\mu(we_{\rm exc}\mathbf1_C)
    =\sum_{i\ne *}\mu(w\mathbf1_C\mathbf1_{A_i}).
$$

Let $p_1<p_2<\cdots$ be the distinct prime factors of $d$, and set

$$
\kappa_d=\frac1{p_1-1},\qquad
\rho_d=\begin{cases}
0,&d\text{ is a prime power},\\
\displaystyle\frac1{(p_1-1)(p_2-1)},&\text{otherwise}.
\end{cases}
$$

The Ramanujan kernel satisfies $R_d=1$ on $C$,
$R_d\le\rho_d$ off $C$, and $R_d\ge-\kappa_d$ everywhere.
These are the prime-power/CRT estimates already proved in report 336.
Using WI3 and $L-1=e_{\rm exc}-v$,

$$
\begin{aligned}
\beta_w
 &=\mu(we_{\rm exc}R_d)-\mu(wvR_d)\\
 &\le(1-\rho_d)X_w+\rho_d E_w+\kappa_d S_w\\
 &=(1-\rho_d)X_w+\rho_d H_w+(\rho_d+\kappa_d)S_w.  \tag{WI6}
\end{aligned}
$$

In particular,

$$
\boxed{S_w\ge
\left[\frac{\beta_w-\rho_dH_w-(1-\rho_d)X_w}
{\rho_d+\kappa_d}\right]_+.}                       \tag{WI7}
$$

Here $H_w$ may be negative. No covering assumption has been used.
Any certified upper bounds on $H_w$ and $X_w$ can be substituted
in WI7. Positive $S_w$ gives an actual uncovered residue in the same
carrier; if $0\le w\le B$, $B>0$, then
$\mu(L=0)\ge S_w/B$.

Under the additional hypothesis that the whole original family covers,
$S_w=0$, $H_w=E_w\ge0$, and

$$
\boxed{X_w\ge
\left[\frac{\beta_w-\rho_dH_w}{1-\rho_d}\right]_+.} \tag{WI8}
$$

Thus a positive weighted overlap is forced whenever
$\beta_w>\rho_dH_w$. For a prime-power selected modulus this reduces
to $X_w\ge\beta_w$, a weighted form of the existing sibling argument.
For odd composite $d$, $\rho_d\le1/8$. The size of $\beta_w$
is not bounded below independently of heights or the chosen weight.

## 5. Sharp failures when a missing layer is supplied by the weight

Consider the two actual distinct odd originals

$$
C=[0]_{15},\qquad A=[0]_{21},\qquad N=105,
$$

and take $q=5$, $w=\mathbf1_{[0]_5}$. Both moduli are
divisibility-maximal, and both classes have private points. The constant
term vanishes because $15\nmid5$. However,

$$
15\mid\operatorname{lcm}(5,21)=105.
$$

On $C$, $w=1$; on $A\cap[0]_5=[0]_{105}$, every primitive
character of order 15 also equals one. Therefore

$$
\beta_w=\frac1{15}=\frac7{105},\qquad
\mu\bigl(w(L-1)\chi_k\bigr)=\frac8{105}.
$$

The same failure holds after averaging to $R_{15}$. Here
$D_A=\{5\}$, but $T(q)=\{3\}$: cutting an unrelated axis does
not protect the missing layer. This is an exact identity failure in an
irredundant noncover, not a claimed counterexample to a cover-only bound.

The constant-term condition has an independent failure. With the single
original $C=[0]_3$, choose $q=3$ and $w=\mathbf1_C$. Then
$w(L-1)=0$, whereas $\beta_w=1/3$. Thus even without another
original label the premise $d\nmid q$ cannot be dropped from the
termwise construction.

## 6. Active-fibre masks and the sharper residual kernel

A period can also be used on a restricted collection of actual fibres
when WI1 fails globally. Assume $d\nmid q$, and put
$$
I_q=\{i\ne *:d\mid\operatorname{lcm}(q,d_i)\},\qquad
\mathcal B_i=\{r\bmod q:r\equiv a_i\pmod{\gcd(q,d_i)}\}.
$$
The original $A_i$ meets the $q$-fibre $r$ exactly when
$r\in\mathcal B_i$. Define
$$
\mathcal R_{\rm safe}=(\mathbb Z/q\mathbb Z)
 \setminus\bigcup_{i\in I_q}\mathcal B_i.                  \tag{WI11}
$$
Every nonnegative $q$-measurable weight supported over
$\mathcal R_{\rm safe}$ satisfies WI2--WI9. The offending labels
are absent on its support, and all other character terms still vanish
by periodicity. Conversely, this is the largest set of $q$-fibres
on which those separate cancellations hold for every supported
nonnegative weight: an active offending label on a retained fibre gives
the nonzero indicator-weight witness from WI4. This maximality concerns
termwise cancellation, not total fixed-family cancellation.

This criterion preserves actual phases. A safe fibre with no point of
$C$ supplies no target mass. Let
$$
g=\gcd(d,q),\qquad e=d/g>1,\qquad
\mathcal B_C=\{r\bmod q:r\equiv a\pmod g\}.
$$
For any allowed weight $w$, replace it by
$\widetilde w=w\mathbf1_{\{x\bmod q\in\mathcal B_C\}}$.
Its target mass $\beta_{\widetilde w}=\beta_w$ is unchanged, while
all its other weighted quantities are now restricted to target-active
fibres. If masking was needed, also retain $\mathcal R_{\rm safe}$.

On this support the original Ramanujan kernel already has a sharper
form. The prime-power formula gives
$$
R_d(x-a)=R_e((x-a)/g)\qquad(g\mid x-a).                  \tag{WI12a}
$$
At a prime where $v_p(g)=v_p(d)$, the factor on the left is one.
At every remaining prime, division by its part of $g$ lowers both
the modulus exponent and the argument valuation by the same amount;
the other prime factors of $g$ are units and do not change the
Ramanujan value. Multiplying the prime-power formulas proves WI12a.
The residual kernel equals one exactly on $C$ within this support.

Thus the same WI3 identity and pointwise proof give WI6--WI9, now with
$$
\boxed{\rho_e,\ \kappa_e\text{ in place of }\rho_d,\ \kappa_d,}
\qquad \beta_{\widetilde w}=\mu(\widetilde w)/e.           \tag{WI12}
$$
All the other moments must likewise use $\widetilde w$; one cannot
keep the old $H_w$ or $S_w$ while changing only the coefficients.
The argument of the smaller kernel is $(x-a)/g$, not an
untransported $x-a$. The mass formula follows because every active
$q$-fibre meets $C$ in relative Haar proportion $1/e$.
Equivalently, the exact affine pullback from
[report 341](../../321-384/341-conditional-future-avoidance-controls-the-current-prefix.md)
has one selected residual class modulo $e$, and no other active
original tag of residual modulus divisible by $e$. Original tags
remain attached even when other residual labels collide.

Since $e\mid d$, these coefficients are no larger than their
full-conductor counterparts. For the maximal period $q_T$,
$e=\prod_{p\in T}p$. A one-prime cut has $\rho_e=0$, giving
the existing sibling/private-mass mechanism on each actual fibre.
Several selected primes can also improve the coefficient by omitting
small uncut prime axes. This is a conditional application of the
existing Ramanujan argument, not a separately claimed literature theorem.

For an exact strict comparison, use the same two originals
$C=[0]_{15}$, $A=[0]_{21}$, now with $q=21$ and
$w=\mathbf1_{[3]_{21}}$. This period is admissible. The chosen
fibre meets $C$ and misses $A$; its residual selected modulus
is $e=5$. Direct counts on the 105-point carrier give
$$
\mu(w)=1/21,\quad \beta_w=1/105,\quad H_w=-4/105,
\quad X_w=0,\quad S_w=4/105.
$$
The full-conductor WI7 bound is $4/175$, whereas the residual
prime-power bound gives $4\beta_w=4/105$, the exact weighted
uncovered mass. This is one explicit noncovering application on its
actual fibre, not a uniform guarantee that such a fibre exists.

## 7. From an actual query payoff to a specified deleted partner family

Fix one simultaneous layout of numerical query labels and phases,

$$
N_Q=\sum_{j\in Q}\mathbf1_{B_j},\qquad
h=(N_Q-\tau)_+,\qquad \tau\ge0.
$$

Choose an admissible $q$, and retain any query subset $Q_0$
whose moduli divide $q$, with their phases unchanged. Then

$$
w=\left(\sum_{j\in Q_0}\mathbf1_{B_j}-\tau\right)_+
$$

is nonnegative, $q$-measurable, and satisfies $w\le h$ pointwise.
WI2--WI8 apply to this actual shared query layout. Replacing $h$ by
its conditional average given $x\bmod q$ would not in general give
a pointwise minorant; that replacement is not used.

Let $J$ be a specified subset of the original partners other than
$C$, and $W_J=\bigcup_{i\in J}A_i$. Suppose one has an upper bound

$$
U_{\rm other}\ge
\sum_{i\ne *,\ i\notin J}\mu(w\mathbf1_C\mathbf1_{A_i}),
$$

and a positive multiplicity cap $M_J$ satisfying

$$
\sum_{i\in J}\mathbf1_{A_i}(x)\le M_J
\quad\text{whenever }x\in C\text{ and }w(x)>0.
$$

All quantities concern the same original source. WI6 gives the explicit
deleted-hinge lower bound

$$
\boxed{\mu(h\mathbf1_{W_J})\ge\frac1{M_J}
\left[
\frac{\beta_w-\rho_dH_w-(\rho_d+\kappa_d)S_w}
{1-\rho_d}-U_{\rm other}
\right]_+.}                                           \tag{WI9}
$$

Indeed WI6 first lower-bounds all weighted partners of $C$. Subtract
the allowed upper bound for partners outside $J$, then use the
multiplicity cap to pass from their sum to the union on $C$.
Finally $w\le h$ and $C\cap W_J\subseteq W_J$.
Under whole coverage, the term in $S_w$ vanishes. A uniform bound on
ordinary unweighted original intersections is not a substitute for this
same-source subtraction unless an explicit weight bound is supplied.

The two-original fixture also makes this partner bound positive without
assuming global coverage. Keep $C=[0]_{15}$, $A=[0]_{21}$,
$q=21$, but use $h=w=\mathbf1_{[0]_{21}}$ and $J=\{A\}$.
Then $\beta_w=H_w=X_w=1/105$, $S_w=0$,
$U_{\rm other}=0$, and $M_J=1$. WI9 gives
$\delta=1/105>0$, while the actual deleted hinge is $1/21$.
The weight here is a one-query payoff at threshold 0; the example does
not assert positivity at the threshold or source required by unrestricted
Erdős #7.

For the final-law interface of
[report 562](../550-599/562-joint-deletion-certificates-and-an-actual-query-antichain.md),
let $\nu$ be a probability measure supported on $W_J^c$, with
$d\nu/d\mu\le K$, and let $\mu(h)\le B$. Any lower bound
$\delta$ furnished by WI9 then gives

$$
\mathbb E_\nu N_Q\le\tau+K(B-\delta).                \tag{WI10}
$$

To bound the sum of maximal query-cylinder probabilities, the chosen
phases must maximize for this same final $\nu$, or their total regret
must be added as in report 562. A positive certificate from one fixed
finite query subset persists on larger boxes retaining its phases, but
the complete-query raw bound and final-law requirements still apply.

The active-fibre mask and target projection from Section 6 may further
multiply this query minorant; they remain $q$-measurable and preserve
the inequality with $h$. The remaining arithmetic obligations are
precise: an admissible
period must retain a query subload with useful weight on $C$;
$H_w$, the excluded partners and $M_J$ must admit bounds making
WI9 positive and sufficiently large. Neither distinct odd moduli nor
the hitting-set criterion alone proves these estimates. In particular,
$Q_0$ can be too small to make $w$ nonzero, and all forced overlap
can be paid by partners outside the desired bucket.

There is also a source-law obligation. The reference throughout is
full-period Haar. For a different measure $\xi=f\mu$, applying
the result requires the **entire product weight** $fw$ to satisfy
the declared periodicity and support conditions. A shallow query payoff
does not make a deep or correlated density shallow. In particular, a
pure-survivor conditioning can depend on the top digits hidden by a
chosen cutoff, so multiplying its density into the payoff can destroy
the cancellation. If the selected $C$ is one of the killed pure
classes, its mass under that conditioned law is zero anyway. An identity
before pure killing therefore does not supply a positive target term
after pure killing. To use WI10 with full Haar instead, its density cap
and raw query bound must be established for that same reference; values
already proved for a conditioned pure source cannot be substituted.

## 8. Relation to existing results

Report 336 supplies the unweighted primitive-character identity and the
pointwise Ramanujan bounds. Its FO8 already shows that arbitrary weight
transport requires a signed joint moment. WI1--WI5 identify and
characterize an explicit arithmetic algebra of actual weights for which
that moment is known exactly. This is additional to FO8's conditional
inequality. The weighted inequalities then follow from its established
pointwise argument.

[Report 344](../../321-384/344-original-fourier-moments-and-finite-probe-obstructions.md)
retains original-label Fourier coefficients on conditional fibres and
multiple maximal-conductor constraints. It does not supply the periodic
weight/hitting-set criterion used here. Report 562 gives a general Gram
projection once query-weighted intersections are available; WI9 instead
forces a particular weighted intersection from the isolated original
character and explicitly pays the unwanted partners. The two interfaces
can be used together but have different premises.

The substantive bridge here is the direct finite proof in Sections 1–3
and its actual-fibre refinement. It is not a claim of a newly discovered
published theorem or of an exhaustive novelty search. The unresolved
application is quantitative: find such an actual weighted boundary
whose target mass survives the required masks and exceeds the costs of
the excess, unwanted partners and multiplicity under the same source.

## 9. Bounded exact controls

The standalone standard-library
[checker](../../../frontier/moments-survival/weighted_primitive_boundary.py)
and [result](../../../frontier/moments-survival/weighted_primitive_boundary.json)
use only the four declared original families with carriers 3, 105, 315, 315.
They examine 34 periods and 102 termwise vanishing criteria. Cancellation
is computed by integer polynomial reduction modulo a cyclotomic
polynomial, independently of the divisibility predicate being tested;
no floating complex arithmetic is used. The actual-fibre comparisons
also check 457 safe fibres and 2,481 residual-kernel values, the maximal
period/hitting-set correspondence, and the exact failures and positive
fixtures above.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/moments-survival/weighted_primitive_boundary.py
```

The command emits deterministic JSON; `--output` selects a result file.
These finite controls test the implementation and the stated examples.
The unbounded quantifiers and sharp termwise criterion rest on the
proofs above, not on enumeration.

# The AH9 interface does not bound the uncapped coherent hinge below one

The three displayed source properties in report473(AH9) do not, by themselves,
imply an uncapped additive cofactor hinge below one, even for an irredundant
family of actual distinct odd moduli with one common OLD-coordinate centre.
One explicit law satisfying all three properties supports an additive hinge
strictly above one. Rank colouring the2186 original moduli gives a private
integer for every class while preserving that same law and additive load.

A separate zero-current-phase construction has exactly the same actual
forbidden union as a seven-label family whose additive hinge is zero. These
same-union and irredundancy conclusions concern two different assignments of
current phases; the zero-current-phase family remains redundant.

This is an interface counterexample. It does not produce an odd cover, refute
report473, or identify its law with report467's particular source-selection
mechanism. The irredundant example has different current phases. If the old
cofactors instead form an antichain at each current height, the existing
antichain mechanism gives H_(1/2)(f)<=R_M(mu)/(q-1), hence below one at
q=23 under AH9. Full CRT coherence with irredundancy is one sufficient
source of this structure; it is not required by the bound itself.
For the fixed rank-coloured head, actual-union updating also controls the
complete next query budget: any additional finite family of distinct
29-bearing moduli supported on these old primes and23 leaves strictly
positive survivor probability. This continuation forbids additional old-only
or23-only blockers.
A second, ternary-coloured irredundant head defeats the uniform cylinder
majorant at every clipping threshold. Keeping its actual joint cylinder
masks instead gives the exact complete query value5.508155054540077...
and a positive arbitrary29 continuation. These two fixed-head repairs
identify the missing joint information; they do not settle arbitrary heads.
All deductions here are ordinary mathematics with exact finite checks, not
new Lean verification.

## The interface and the two different quantities

Use the old primes

    P=(3,5,7,11,13,17,19),
    A=70871/3375,
    Lambda=6075000000000/7235955529.

Report473(AH9), citing report467, records a single law on a sufficiently fine
old period M with

    supp(mu)=U,
    R_M(mu)=sum_(1<d|M) max_a mu(x=a mod d)<=A,
    mu<=Lambda H_M.

Here U is the actual survivor set of the old-only original family, and H_M is
uniform probability. The laws below are compatible across all deeper periods,
so one can take M divisible by p^21 for every p in P as required there.

At current prime23, a collection C of originals a_lambda mod(23 d_lambda)
has additive cofactor load

    f_C(x)=(1/23)sum_lambda 1_(x=a_lambda mod d_lambda).

Its actual forbidden union fraction alpha_C(x), measured in the23-coordinate,
is at most f_C(x) and at most one. Define the UNCAPPED additive hinge by

    H_(1/2)(f_C)=E_mu[(f_C-1/2)_+]/(1/2)
                =E_mu[(2 f_C-1)_+].

A survivor bound for the actual union controls alpha_C, not an upper bound for
the generally larger f_C. This distinction survives all three AH9 properties.

## One full-support law with exact all-height control

Let H be product Haar on the old prime coordinates. Equivalently, use finite
uniform old periods and compatible uniform extensions at higher digits. Put

    v_p(x)=the p-adic valuation of x relative to centre0,
    D2(x)=product_(p in P)(min(v_p(x),2)+1),
    E={x:D2(x)>=32},
    e=H(E)=8435891267/7840332174675,
    mu=(3/5)H+(2/5)H(.|E).                         (CU1)

The density depends on only two digits at each old prime. It is everywhere at
least3/5, so its support at every finite period is the entire period. Choose
an empty old-only original family; its full survivor set U is exactly that
support. No assumption about missing a prescribed nonempty old family is
being made.

The maximum density is

    3/5+2/(5e)=15705972023151/42179456335
              =372.3607032392775...<Lambda.         (CU2)

The density is nondecreasing in each truncated valuation. This proves that
for every P-supported modulus d, its zero cylinder is a maximizing cylinder:

    max_a mu(x=a mod d)=mu(x=0 mod d).              (CU3)

For completeness, fix all other prime coordinates and compare cylinders at
one prime p^j. A nonzero residue whose valuation is r<j has that fixed
valuation throughout its cylinder. The zero cylinder has valuation at least
j throughout. Both cylinders have the same Haar mass, and replacing the former
by the latter cannot decrease the conditional density. An already zero
residue needs no change. Apply these replacements one coordinate at a time.
This also applies when j>2; the density then only sees the saturated value2.

Consequently the complete all-height query sum is

    1+R_infty(mu)
       =E_mu product_(p in P)(v_p(x)+1).            (CU4)

This follows by summing the nonnegative zero-cylinder indicators for every
P-supported divisor label. For every finite M, R_M<=R_infty. There is no
exchange of separately chosen maximizing laws in this identity.

Only3^7=2187 truncated valuation cells are needed to evaluate CU4 exactly.
For a coordinate value r in{0,1,2}, their Haar probabilities are respectively

    (p-1)/p, (p-1)/p^2, 1/p^2.

The conditional factor E(v_p+1) is r+1 for r<2, and

    E(v_p+1 | v_p>=2)=2+p/(p-1)

for r=2. The unsummed deeper tail is therefore evaluated by a convergent
geometric identity, not discarded. The exact results are

    E_H product_p(v_p+1)=323323/110592,
    E_H[1_E product_p(v_p+1)]
       =680845452801113263/13006170237924864000,
    R_infty(mu)=1414458544322632571/69970656525004800
               =20.21502461988705...<A,
    A-R_infty(mu)=274211572584785561/349853282625024000>0. (CU5)

Thus the displayed support, query and density conditions in AH9 all hold,
including every greater finite query depth.

## Actual original labels with the same union but different hinges

Let

    Q2=product_(p in P)p^2=23520996524025.

The full original family is

    C_full={0 mod(23d): d|Q2, d>1}.                (CU6)

There are exactly3^7-1=2186 labels. All numerical moduli are pairwise distinct,
odd, and greater than one. All old phases and all current phases are zero;
there is no pure23 class. Every label has old height at most2 and current
height1. This family is genuinely an original congruence family, not a set of
independently selected query maximizers.

Its active old cofactor count is D2(x)-1, so

    f_full(x)=(D2(x)-1)/23.                        (CU7)

Compare it with the seven-label original family

    C_short={0 mod(23p):p in P}.

Every short label is present in the full family. Conversely, every nonunit
divisor d of Q2 has a prime factor p in P, so

    {0 mod(23d)} subset {0 mod(23p)}.

The two actual forbidden unions are therefore equal, as literal subsets of
their common full CRT period. On each old x their shared current union
fraction is

    alpha_full(x)=alpha_short(x)
       =(1/23)1_(some p in P divides x).           (CU8)

Its actual union hinge is zero. Also

    f_short(x)=(1/23)#{p in P:p|x}<=7/23<1/2,

so the short family's uncapped additive hinge is zero.

In contrast, exact integration of CU7 under CU1 gives

    H_(1/2)(f_full)
       =2581992950434626793746299/2535373939370931457423625
       =1.018387430090593...>1,                    (CU9)

with strict excess

    46619011063695336322674/2535373939370931457423625>0.

For reproduction, the two unnormalized Haar contributions are

    E_H[(2f_full-1)_+]=452456464149/60109213339175,
    E_H[1_E(2f_full-1)_+]=1701702799/623971072725.

Multiplying the first by3/5 and the second by2/(5e) gives CU9.

## Rank colouring makes the obstruction irredundant

The redundancy of CU6 is not necessary for the AH9-interface obstruction.
Keep the SAME old source CU1 and the same2186 numerical moduli23d. For

    d=product_(p in P)p^e_p,  0<=e_p<=2, d>1,
    r(d)=sum_p e_p in{1,...,14},

give the original class its unique normalized CRT phase

    a_d=0 mod d,
    a_d=r(d) mod23,
    a_d=d*[r(d)*(d^(-1) mod23) mod23].             (CU10)

The bracket denotes the representative in{0,...,22}. Each numerical d receives
exactly one current colour; the colours are fixed before drawing the common
old law. There is no independent optimization of a colour group or change of
source. Every old phase is still the common centre0, but the current phases
are different. This is OLD-coordinate coherence, not full CRT coherence.

Within one colour, old cofactors form a divisibility antichain. Indeed,
d'|d means e'_p<=e_p at every p, and equality of r(d') and r(d) forces equality
of every exponent. All colours are below23, so colour equality modulo23 is
literal equality of ranks, without wraparound.

More strongly, every original has an actual private integer. For the exponent
tuple of d, choose x_d by CRT with

    x_d=p^e_p mod p^3 for every p in P,
    x_d=r(d) mod23.                               (CU11)

The old valuations of this integer are exactly e_p. If x_d lies in another
original a_(d') mod23d', then d'|x_d gives e'_p<=e_p, while the current
coordinate gives r(d')=r(d). Thus d'=d. Each x_d belongs to its own original
and no other one. The family is irredundant; deleting any class changes the
actual union. The witness period is

    23 product_p p^3=2623683309902380600875.

The colour-class sizes, for ranks1 through14, are

    7,28,77,161,266,357,393,357,266,161,77,28,7,1.

Changing the current phases does not alter which old cofactor indicators are
active. Thus this irredundant family's additive load and hinge remain exactly

    f_rank(x)=(D2(x)-1)/23,
    H_(1/2)(f_rank)=H_(1/2)(f_full)>1.             (CU12)

The same all-height query and density bounds CU2--CU5 continue to hold. They
are properties of the unchanged old law, which is supported on the full
survivor of the unchanged empty old-only family.

The ACTUAL union is different from CU8 and can also be computed exactly.
Write v_p=min(v_p(x),2) and s=sum_p v_p. The active exponent vectors are
precisely the nonzero e with0<=e_p<=v_p. Their possible ranks are every
integer1,...,s: sums of the integer intervals{0,...,v_p} form the full interval
{0,...,s}. As s<=14<23, their current colours are all distinct. Hence

    alpha_rank(x)=s/23,
    alpha_rank(x)<=14/23,
    (2 alpha_rank(x)-1)_+<=5/23.                  (CU13)

The actual current fibre always has at least9/23 surviving mass. In particular,
this is not a whole cover or a counterexample to report473.

Exact integration gives

    H_(1/2)(alpha_rank)
      =1219830493798061/585086293700984182482375
      =0.0000000020848727904425514... .             (CU14)

For reproduction, its Haar value is233/41614070773275. A positive actual
hinge requires s>=12. For v in{0,1,2}, (v+1)^2>=2^v, so
D2^2>=2^s>=2^12 and hence D2>=64>32. Its positive set lies in E.
Multiplying that Haar value by the density3/5+2/(5e) from CU2 gives CU14.
The uncapped hinge above one and the small actual-union hinge therefore refer
to exactly the same source and exactly the same irredundant original family.

This rules out the proposed implication using AH9 together with
OLD-coordinate coherence and actual irredundancy. CU10 has no common
current centre and its whole single-height cofactor set is not an
antichain. The layered-antichain case has the different bound below;
the particular source-selection mechanism of report467 and the extra
consequences of a minimal whole covering family are not reconstructed
by this counterexample. A conflict/coherence extraction must state
exactly which common-centre or antichain conditions it establishes.

## Same-old-centre layered cofactor antichains control the uncapped load

The existing comparable-class and antichain mechanisms in
[Chapter16](../../../problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#congruence-and-complete-layout-specialization),
[Chapter40](../../../problem-details/40-fixed-order-scalar-threshold-barrier-and-cofactor-colors.md#3-existing-actual-label-colors-and-their-boundary)
and [Report535](../500-549/535-mixed-chain-moments-retain-shared-prime-correlations.md)
have a direct application to the AH9 interface. This is an ordinary
application of those mechanisms, not a new generic antichain theorem or
formal-library declaration.

Let q>=3 be prime, let M be any finite old period coprime to q, and let mu
be one probability law on Z/MZ. Consider a finite block of actual original
classes with distinct numerical moduli d*q^k, where d|M and k>=1. Assume:

* Every old residue is one common t: a_(d,k)=t mod d.
* At each fixed current height k, the set A_k of present old cofactors d is
  a divisibility antichain.

The current residues modulo q^k may differ between d and between heights.
Each original still has its one fixed global CRT phase. No global irredundancy
or common current centre is required in addition to these two hypotheses.
Define the unconditioned-Haar cofactor load

    f(x)=sum_(original(d,k)) q^(-k)1_(x=t mod d),
    R_M(mu)=sum_(1<d|M) max_b mu(x=b mod d).

Then, allowing arbitrary finite old and current heights,

    H_(1/2)(f)=E_mu(2f-1)_+<=R_M(mu)/(q-1).       (CU15)

To prove this, put

    D(x)=#{d|M:x=t mod d}
        =product_(p|M)(min(v_p(x-t),v_p(M))+1),
    N_k(x)=#{d in A_k:x=t mod d}.

The product uses truncated valuations, so it is finite even when x=t
mod M. When D(x)>=2, choose any old coordinate with positive truncated
valuation v>=1. Holding all other exponents fixed partitions the D(x) active
divisors into D(x)/(v+1) chains. At most one member of A_k lies on each
chain, so

    N_k(x)<=D(x)/(v+1)<=D(x)/2,
    f(x)<=D(x)/[2(q-1)].

The geometric sum bounds the entire finite inventory of current heights;
no height is dropped and no independently favorable laws are selected.
When D(x)=1, only d=1 can be active, at most once at each height. Hence
f(x)<=1/(q-1)<=1/2. In both cases,

    (2f(x)-1)_+<=(D(x)-1)/(q-1).

Finally, under the SAME mu,

    E_mu(D-1)=sum_(1<d|M) mu(x=t mod d)<=R_M(mu),

which proves CU15. The support and density clauses of AH9 are not needed
for this implication. M need only resolve the actual old cofactors; it can
also contain all the extra query labels required by AH9.

At q=23, every AH9 law therefore gives, under the stated layered-antichain
hypothesis,

    H_(1/2)(f)<=70871/74250
                =0.9544915824915825...<1.          (CU16)

If all current exponents equal1, the same argument uses f=N_1/q and yields
the stronger bound R_M(mu)/q, here70871/77625<1. These conclusions are not
restricted to the particular mixture CU1. The actual current union fraction
alpha(x) satisfies alpha(x)<=f(x), so its hinge obeys the same bound.
The load here uses weights q^(-k); a load normalized by a pure-survivor
measure needs its own normalization comparison.

FULL CRT coherence plus actual irredundancy is one SUFFICIENT way to obtain
the hypothesis on every A_k: comparable old cofactors at the same k would
make the corresponding common-centre original classes nested. It is not a
necessary condition for CU15. Another sufficient special case has one common
current residue separately at each k, together with old coherence and
irredundancy; those current residues need not lie on one nested path.

General irredundancy plus old coherence gives only an antichain within each
current-residue colour at a fixed height. It need not make the entire A_k
an antichain. CU10 retains many comparable cofactors at its single current
height by assigning different colours, so CU15 does not apply to it.

The distinction also affects actual unions. A full-centre block is contained
in the single current root and has alpha<=1/q. A block with one current
residue per height has alpha<=sum_(k>=1)q^(-k)=1/(q-1). Neither bound follows
merely from CU15's weaker layered-antichain hypothesis, which allows many
current residues within a layer. These special-case union observations are
not new noncoverage results; CU15 supplies an uncapped additive consumer under
a stated structural hypothesis, without solving unrestricted Erdős#7.

There remains a precise extraction obligation. A procedure which enforces
only old-coordinate coherence has not established the layered-antichain
hypothesis. Moreover, disagreement of current q-phases does not make the old
indicators1_(x=a_lambda mod d_lambda) and1_(x=a_kappa mod d_kappa) disjoint.
Their product can remain positive in E_mu f^2. Current-phase conflicts cannot
simply be subtracted from that old-cofactor square budget. A paid extraction
must either establish the actual layered-antichain condition, or reach a
sufficient stronger form of coherence through an additional same-source
comparison accounting for those current-phase conflicts. CU15 supplies no
such missing deletion comparison.

## The actual rank union also preserves the next complete-query budget

Keep the SAME old law CU1 and all2186 rank-coloured23 originals CU10.
One may add any finite family of originals of the form

    c mod d*29^k,  k>=1,

where d is supported on P union{23}, all numerical moduli are distinct,
and all residues and finite exponents are arbitrary. This permits pure29
powers and arbitrary mixed old/23/29 labels. It does not permit adding
further old-only or23-only forbidden classes. For every such29 family,
one fixed supported23 law gives joint survivor probability at least

    26186121710409348975590651753
    /150980347602176747057609859072
      =0.17344059757636837...>0.                   (CU17)

This is an application of the actual killed row in
[report327](../../321-384/327-actual-two-prime-survival-needs-a-masked-moment.md),
TS7, and the complete-query accounting in
[report463](../450-499/463-two-actual-prime-extensions-preserve-a-common-core-law.md),
PE5. [Report546](../500-549/546-dense-irredundant-families-separate-stage-debits-from-actual-unions.md),
DU9--DU10, uses the same cylinder-cap and one-normalization mechanism for
a different fixed family. No new generic transfer theorem or Lean result
is asserted here.

Use Haar on the23-coordinate and retain its higher digits for all later
queries. Let B_x be the actual rank-coloured forbidden union, let
alpha=alpha_rank from CU13, and put theta=min(alpha,1/2). Define the
unnormalized live measure and its one normalization by

    xi(dx,dy)=mu(dx) H23(dy) 1_(y notin B_x)/(1-theta(x)),
    h=H_(1/2)(alpha),  s=xi(1)=1-h,  mu'=xi/s.     (CU18)

The identity for s is the actual killed-row formula: at each x its row
mass is (1-alpha)/(1-theta)=1-(2alpha-1)_+. The old marginal of xi is
at most mu, whereas every old cylinder C and every23-prefix J of depth e
satisfy

    xi(C times J)<=2*23^-e*mu(C).                 (CU19)

The old-only nonunit query labels therefore contribute at most R=R_infty(mu).
At each positive23 exponent e, all old query labels INCLUDING1 contribute
at most2*23^-e*(R+1). Sum every positive exponent and then normalize once:

    R_(P union{23})(mu')
       <=[R+(R+1)/11]/(1-h).                      (CU20)

Every maximum here concerns the same xi or mu'. There is no independent
choice of source for different queries. The higher-digit extension of CU1
and CU18 supplies these bounds at arbitrary depths; equivalently one can
project that law to a finite period resolving the entire chosen29 family
and its query depths. No unresolved old or23 exponent is discarded.

Insert CU5 and CU14. Exact arithmetic gives

    R+(R+1)/11=1420289432366382971/64139768481254400,

    R_(P union{23})(mu')
       <=119402070620261085687104569495
          /5392155271506312394914637824
        =22.143663267861687...<27.                 (CU21)

In particular the small ACTUAL union hinge controls a complete subsequent
query budget, although the uncapped additive hinge exceeds one. The next
step is not inferred merely from positive23 survival.

To process the additional29 originals, use this fixed mu' times Haar29.
For a fixed k>=1, numerical-modulus distinctness gives at most one original
per old label d; its actual phase has mu'-mass at most that label's query
maximum. Include d=1. Consequently the actual29 forbidden union has mass
at most

    sum_(k>=1)29^-k*[1+R_(P union{23})(mu')]
      =[1+R_(P union{23})(mu')]/28<1.              (CU22)

The complement lower bound obtained from CU21 is exactly CU17. The same probability law and the same numerical lower bound apply to
each finite29 family in the stated scope, with its one original phase
fixed at each numerical label; no branch reselects an original residue.
Positive mass on that family's resolved finite CRT carrier yields an
uncovered integer, which may depend on the family. No one integer is
asserted to survive every such family at once.

Without the normalization in CU18, the same combined survivors have mass
under xi times Haar29 at least

    26186121710409348975590651753
    /150980347916951566321211904000
      =0.17344059721476679...>0.                   (CU23)

CU17 is a probability under mu' times Haar29; CU23 is an unnormalized
distorted-measure bound. Neither number is asserted to be the full Haar
survivor density.

For reuse with the scalar AH9 value A alone, the very same accounting
shows exactly what extra actual-union estimate would suffice:

    h<1-[A+(A+1)/11]/27
      =49516/334125=0.14819603441825663...          (CU24)

implies the strict query target in CU21. CU14 satisfies this threshold
for the fixed rank head. AH9 itself does not assert CU24 for an arbitrary
actual23 family. Thus this application does not remove the quantitative
actual-union obligation, identify CU1 with report467's selected source,
allow extra old/23-only blockers, or prove unrestricted Erdős #7.

The existing verifier's `rank_colored.continuation23_29` output applies
the checked CU5/CU14 values to CU18--CU24, checks the15 possible rank-row
mass and density identities, and verifies all displayed rational gaps.
The arbitrary-height and all29-family assertions rely on the ordinary
cylinder and original-label argument above, not finite enumeration of
those families. No Lean verification is claimed.

## Another irredundant colouring defeats this entire cylinder-cap comparison

The uniform-cylinder estimate used in the rank-coloured continuation does
not certify every old-coherent irredundant head from the same numerical
AH9 interface. The SAME old law
CU1 supports the following finite example, without any pure23 original.
Its actual half-threshold hinge exceeds CU24, and even optimizing the
clipping threshold over every0<=delta<1 leaves the particular uniform-
cylinder query majorant above27. This is a failure of that upper estimate,
not a lower bound on the actual new query norm and not a covering example.
The following joint-cylinder calculation repairs this same example: its
actual complete query norm is only5.508155054540077...<27.

Index the old primes increasingly as p_0,...,p_6. For every nonzero
e in{0,1,2}^7 put

    d(e)=product_(i=0..6)p_i^e_i,
    c(e)=sum_(i=0..6)3^i*e_i mod23,
    A_e={x=0 mod d(e), y=c(e) mod23}.              (CU25)

These are2186 distinct numerical labels23*d(e), all with old centre0.
Retain only exponent vectors which are coordinatewise minimal among the
nonzero vectors of their own colour. Exactly536 labels remain.

This reduction preserves the entire actual union. Every removed vector e
has a same-colour minimal f<=e; then A_e is contained in A_f. Conversely
the retained family is a subfamily. It is irredundant: for each retained e,
take the integer CRT point

    x=p_i^e_i mod p_i^3 for every i, y=c(e) mod23. (CU26)

Its old valuations are exactly e. Another retained original A_f could
contain that point only if f<=e and c(f)=c(e), which would contradict
minimality unless f=e. Thus every retained original has an actual private
integer. No class with d=1 was introduced, and the old-only original
family remains empty, so CU1 retains the same full old survivor support.

For v_i=min(v_(p_i)(x),2), the actual current union is

    alpha(v)=|{c(e):0<e<=v}|/23.                  (CU27)

The finite source-cell calculation is explicit. Let Q2=product_i p_i^2
and let n(v) be the product of p_i(p_i-1), p_i-1 or1 according as v_i is
0,1 or2. If E_count sums n(v) over product_i(v_i+1)>=32, then

    mu(v)=(3/5)n(v)/Q2
          +(2/5)1_(product_i(v_i+1)>=32)n(v)/E_count.

Summing these exact masses over the attainable-colour counts gives

    h_(1/2)(alpha)
      =898342963018123305464329/2535373939370931457423625
      =0.354323655800066...>49516/334125,          (CU28)

with positive gap

    126994375662937750830895063/616095867267136344153940875.

The retained result stores every one of the24 exact masses
w_j=mu{alpha=j/23}; it also records all536 retained exponent/colour tuples.
The bound is for the same CU1 law before and after removing the redundant
labels, since the actual union is unchanged.

The failure is not confined to delta=1/2. To test this comparison over a
larger parameter range, define its live measure directly for0<=delta<1:

    xi_delta(dx,dy)
      =mu(dx) H23(dy)1_(y notin B_x)/(1-min(alpha(x),delta)),
    s_delta=E_mu[(1-alpha)/(1-min(alpha,delta))].

The same old-marginal and cylinder estimates as CU19--CU20 give

    R_(P union{23})(xi_delta/s_delta)<=B_delta,
    B_delta=[R+(R+1)/(22(1-delta))]/s_delta,       (CU29)

where R is the exact old query value CU5. Allowing delta>1/2 here needs
no extrapolation of a quadratic clipping estimate: both inequalities
follow directly from the displayed live density. The delta=0 endpoint
is ordinary restriction of mu times Haar23. Rows with alpha=1 have zero
live mass for every delta<1.

It suffices to compare the23 thresholds delta=j/23, j=0,...,22. To see
this for the whole continuum, write t=1-delta, beta=1-alpha and
C=(R+1)/22. On an interval between consecutive alpha breakpoints, put

    a=mu{beta>=t}, b=E_mu[beta*1_(beta<t)].

These coefficients are constant in that open interval, and

    s_delta=a+b/t,
    B_delta=(R*t+C)/(a*t+b),
    dB_delta/dt=(R*b-C*a)/(a*t+b)^2.              (CU30)

The denominator is positive because mu{alpha=0}>0. The derivative has
constant sign, so each interval's minimum lies at an endpoint or the
whole interval is constant. The expressions are continuous at the
breakpoints. For delta>22/23 all nondead rows already have live mass one;
s_delta=1-w_23 is constant and B_delta increases strictly. Consequently
the finite endpoint minimum is the minimum over every0<=delta<1.

The exact endpoint calculation gives its minimum at delta=11/23:

    s_(11/23)=394841535459971666944/613545359208904926375,
    min_(0<=delta<1) B_delta
      =35929581952530320495737057385/1047991562150140478176100352
      =34.28422828024914...>27.                   (CU31)

Its excess over27 is

    7633809774476527584982347881/1047991562150140478176100352.

Here w_23=21597899555960513066847/110233649537866585105375>0:
some old fibres are completely forbidden, although the old law is positive
on them. The family also has genuinely surviving fibres, including the
old valuation-zero cell; no whole-cover conclusion follows.

Thus actual old coherence, irredundancy and the same AH9 law do not ensure
CU24 or make CU29 strong enough to certify the next query target, even
with its best threshold. The inequality R_new<=B_delta does NOT imply
R_new>=27 when B_delta>27. The exact joint-cylinder calculation below supplies the needed improvement
for this very law and this very head; it does not prove an arbitrary-head
continuation theorem. The
rank-coloured positive conclusion CU17--CU24 is unchanged.

The existing verifier's `ternary_coloured` result reconstructs CU25,
checks union equality on all2187 old valuation cells, and checks287296
literal private-point/class memberships for the536 retained originals.
It stores the exact alpha histogram and all23 endpoint values, and checks
the rational gaps CU28/CU31. The continuum conclusion uses CU30, not a
sampled numerical optimization. This is ordinary mathematics with exact
finite verification, not new Lean certification.

## Exact all-height query accounting for the same ternary-coloured live law

For the ternary-coloured family, fix delta=11/23 and keep the SAME live
measure xi_delta from CU29. The following finite calculation computes its
complete query norm exactly. It does not replace that law by separately
chosen query laws. Here the complete query norm sums the maximum cylinder
mass over every nonunit modulus supported on P union{23}. Any resolved
finite-period query norm is bounded by this complete compatible-law value.

For v in{0,1,2}^7 and c in{0,...,22}, let C(v)={c(e):0<e<=v} and write

    r(v,c)=mu(v)*1_(c notin C(v))/(23-min(|C(v)|,11)). (CU32)

This is the xi_delta mass of the joint old valuation cell and23 first-digit
cylinder. Its sum is the s_(11/23) already computed in CU31.

At one old prime p, every cylinder through depth two has one of six types.
Its conditional masses across the valuation cells0,1,2 are the rows

    T_p = [1,             1,         1]
          [1/(p-1),       0,         0]
          [0,             1,         1]
          [1/(p*(p-1)),   0,         0]
          [0,             1/(p-1),   0]
          [0,             0,         1].

The rows respectively mean the unit query, a nonzero or zero residue
modulo p, and a unit, exact-valuation-one or zero residue modulo p^2.
All residues of a stated type have equal mass because the density depends
only on the truncated valuations and on the23 first digit.

For a joint row choice j=(j_0,...,j_6), set

    A_j(c)=sum_v r(v,c)*product_i T_(p_i)[j_i,v_i].

These are actual joint cylinder masses, retaining every old/current
correlation. For e in{0,1,2}^7, let J(e) allow row0 when e_i=0, rows1--2
when e_i=1, and rows3--5 when e_i=2. Define

    a_e=max_(j in J(e)) sum_c A_j(c),
    b_e=max_(j in J(e),c) A_j(c),
    w_e=product_(i:e_i=2) p_i/(p_i-1).             (CU33)

For a query without23, its current coordinate is summed BEFORE maximizing
the old phase, giving a_e. For a query containing23, both the old phase
and current first digit are maximized, giving b_e. These finite maxima
are over one jointly selected cylinder, not products of marginal maxima.

The density is constant inside each full old depth-two/current-depth-one
atom. Raising an old exponent from2 to h>=2 therefore multiplies the
corresponding maximal cylinder mass by p_i^(-(h-2)); all deeper choices
are equally distributed inside their depth-two ancestor. The full old
tail sums to p_i/(p_i-1). Raising the23 exponent from1 to h>=1 similarly
contributes23^(-(h-1)), whose complete sum is23/22. Hence the exact
all-height identity is

    R_(P union{23})(xi_delta/s_delta)
      = [sum_e w_e*(a_e+(23/22)*b_e)]/s_delta -1.   (CU34)

The subtraction removes only the old full-unit query, of unnormalized
mass s_delta, which occurs in the a_(0,...,0) term. The b term retains
the old unit for every positive23 exponent. All terms are nonnegative
before this single subtraction, so increasing finite exponent boxes and
geometric sums justify the complete-height equality.

For exact integer evaluation, let M=product_i p_i^2,
E_count=sum_(event cells)n(v), and L=lcm(12,13,...,23). A common denominator
for all r(v,c) is D=5*M*E_count*L. The numerator of an allowed cell is

    n(v)*(3*E_count+2*M*1_event(v))*L/(23-min(|C(v)|,11)).

At every transform axis, division by p-1 or p(p-1) is exact: all terms
with that coordinate fixed in valuation cell1 or0 retain the respective
factor p-1 or p(p-1) from n(v). Transforming and summing other coordinates
preserves that common factor. The remaining geometric tail factors may
be summed with a common denominator product_i(p_i-1).

Thus one old sum over23 roots and one transform for each of the23 roots
suffice, each with6^7 joint cylinder types. Taking the current-root maximum
pointwise before the old type-group maxima gives exactly b_e; no floating
point maximum or equality decision is needed. The all-height justification
above is ordinary mathematics; a successful exact finite computation is
not a Lean proof.

Exact integer evaluation gives

    R_(P union{23})(xi_(11/23)/s_(11/23))
      =48819613325418098388618839835627526373
        /8863151607393243786151717247542886400
      =5.508155054540077...<27.                    (CU35)

Thus the same law whose uniform-cylinder majorant is at least34.2842 has
an actual complete query value below5.509. The difference comes from
retaining the actual joint survival masks inside each cylinder before
maximization; no law is reselected for a different query.

The original-label union bound CU22 now applies with CU35. After this
fixed536-class ternary-coloured23 head, any finite distinct29-bearing
family d*29^k, k>=1, d supported on P union{23}, arbitrary finite exponents
and fixed residues, leaves survivor probability at least

    190485480074199483837477525848030406427
      /248168245007010826012248082931200819200
      =0.767565890909283...>0.                    (CU36)

This probability is under the ONE normalized law xi_(11/23)/s_(11/23)
times Haar29. The unnormalized reserve under xi_(11/23) times Haar29 is

    190485480074199483837477525848030406427
      /385629325571564855781271020855705600000
      =0.49396004775277214...>0.

Neither number is a full Haar density. No additional old-only or23-only
blockers are allowed in this continuation. The same law and lower bound
work for each finite29 family; its surviving set and uncovered integer
may depend on that family. Neither this fixed-head computation nor the
failure of the coarser comparison resolves unrestricted Erdős#7.

The existing verifier's `ternary_coloured.actual_complete_query` block
performs the24 integer transforms, checks every division and the one
unit subtraction, and evaluates the rational quantities in CU35--CU36.
An independent implementation processes the prime axes in reverse order
and reproduces both raw query blocks, the live mass and the final query
value. The finite checks implement CU34; its all-height and arbitrary-
family quantifiers use the ordinary cylinder and original-label proofs.

## Precisely which proposed bridge fails

There cannot be a theorem using only the three displayed AH9 properties,
old-coordinate coherence and actual irredundancy to bound the uncapped
additive hinge by a uniform H0<1. CU1 and CU10 are a counterexample to that
statement. The zero-current family CU6 separately shows that identical actual
unions can have different additive hinges. Both actual-union calculations
remain compatible with report473's fibre-survival conclusion.

The source law in CU1 has not been obtained from report467's prescribed source
construction. Extra structure of that chosen law could still be useful. To
use such structure, an application must state it and prove the bridge; it
cannot substitute the three numerical/support summaries for it. The law has
full support from an actual empty old family, so the sparse-support/density
failure in report474 is not the issue here.

Removing redundant originals fixes the zero-current family CU6 but cannot
remove a class from the rank-coloured family CU10. Full CRT coherence would
impose a stronger condition: irredundancy then forces one divisibility
antichain. Old-coordinate coherence alone gives a separate antichain within
each current-residue group at height1, and CU10 satisfies exactly those
conditions. At greater current heights, current prefix compatibility must also be
preserved. CU15 assumes an antichain of old cofactors in each entire
height layer, a property implied by full coherence and irredundancy but
not by arbitrary old-only coherent irredundant inputs such as CU10.

A separate repair is to work with the clipped majorant min(1,f_C). Its hinge
is bounded by one, and report473's good set can bound it strictly below one
in the specified seven-old-prime/23 coherent case. That is a different
quantity from the uncapped H in the proposed Nyx interpolation. It needs an
explicit rewritten consumer and quantitative tail budget. CU18--CU24
instead use the actual union for the fixed rank head; CU32--CU36 retain
joint query masks for the fixed ternary head. Neither establishes a
continuation from the clipped majorant alone. No unrestricted support,
arbitrary-head or all-stage gain is established by this note.

## Reproduction and references

The [standalone verifier](../../../frontier/cover-geometry/coherent-uncapped-hinge-obstruction/coherent_uncapped_hinge_obstruction.py)
uses the standard library and writes [exact result data](../../../frontier/cover-geometry/coherent-uncapped-hinge-obstruction/coherent_uncapped_hinge_obstruction.json).
From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/coherent-uncapped-hinge-obstruction/coherent_uncapped_hinge_obstruction.py \
  --output docs/reports/erdos7-odd-covering/frontier/cover-geometry/coherent-uncapped-hinge-obstruction/coherent_uncapped_hinge_obstruction.json
```

Checks use explicit exceptions and remain active under Python optimization.
They cover all2187 valuation types, the2186/7 original-label inventories,
literal divisibility certificates for the common union, the rational sums,
and all three strict comparisons. For CU10 the verifier additionally checks
all2186 normalized CRT phases,4,778,596 private-point/class memberships,
307020 same-colour antichain pairs and every valuation type's actual colour
union. The result's original `exact.actual_union_hinge` belongs to the
zero-current family; its `rank_colored` block records the irredundant family.
A separate exact implementation reproduced the source quantities and both
families' hinge integrals, independently constructing and checking every
rank-coloured private point against all2186 originals.
The monotone-cylinder proof and all-height geometric-tail deduction above
are ordinary proof inputs; the finite check does not enumerate infinitely
many cylinders or reconstruct the source selector.

[Report467](../450-499/467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md)
supplies the source construction not reconstructed here.
[Report473](../450-499/473-a-finite-query-certificate-removes-the-coherent-cofactor-height-bound.md),
AH9--AH14, supplies the scalar/support interface and actual-union fibre result.
[Report474](../450-499/474-arbitrary-fixed-phases-admit-high-load-below-the-query-cap.md)
gives a different fixed-phase obstruction that fails the density cap.
[Report340](../../321-384/340-whole-cover-completion-constrains-original-prefix-loads.md),
CP7--CP7a, already distinguishes label incidence from union incidence and
requires a same-law multiplicity bridge.
[Report562](../550-599/562-joint-deletion-certificates-and-an-actual-query-antichain.md)
retains actual-original, query-weighted losses; these data are not supplied
by a clipped union bound alone.

The irredundant examples in
[Report564](../550-599/564-integrated-actual-profiles-permit-empty-root-fibres.md),
[Report609](../600-649/609-linear-schedule-credit-fails-on-an-actual-irredundant-core.md)
and [Report615](../600-649/615-nested-actual-incidences-force-unbounded-fixed-law-credit.md)
concern integrated support-profile or linear-schedule certificates.
[Report622](../600-649/622-full-capacity-unique-maxima-refute-the-universal-hinge-bound.md)
uses a different full-capacity entropy-selected law and its stated family is
redundant. Those results do not supply the same AH9/old-coherence/current-
height1 interface of CU10--CU14. The rank-antichain and CRT reasoning here
use elementary existing structures; no new generic antichain theorem or
formal-library declaration is claimed.

[Chapter40](../../../problem-details/40-fixed-order-scalar-threshold-barrier-and-cofactor-colors.md#3-existing-actual-label-colors-and-their-boundary)
already gives fixed current-residue colours, rank-coloured actual families
and symmetric-chain counting. CU10 is a same-AH9-law quantitative
application of that existing mechanism. Chapter16 and Report535, cited
above, supply the comparable-class exclusion used to derive a sufficient
instance of CU15. No new generic antichain theorem is claimed.

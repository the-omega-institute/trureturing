# Two levels of shared pair interfaces preserve a common survivor

Keep the head-only restrictions of
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md)
and the ordinary private blocks of
[Report601](601-staged-payment-admits-every-two-parent-entry-from37.md).
A first-level two-parent entry q>=37, on any two head primes p,r,
may now have arbitrarily many second-level entries s>q. Each such
entry is attached along either pair(p,q) or pair(r,q), and has its
own ordinary private block tree. Then the proportion of complete
head words with a simultaneous avoiding extension is greater than
1/260000.

There is no additional second-level prime cutoff, no bound on the
finite number of branches or the depth of their ordinary block
trees, and no bound on original finite heights. Numerical moduli
remain distinct, and every original has one arbitrary globally
fixed residue. This is a complete restricted-family noncoverage
result. It admits another shared two-coordinate separator below a
Report601 entry; it does not admit arbitrary recursive shared-pair
separators or settle unrestricted Erdős #7. The proof is ordinary
mathematics with exact rational arithmetic, not new Lean verification.

## The original family and its declared decomposition

Let P be the ten smallest primes in the family. Initially work with
P={3,5,7,11,13,17,19,23,29,31}; the final transport handles arbitrary
ordered odd head primes. Write P0={3,5,7,11,13,17,19} and
P1={23,29,31}. Pure head originals and head originals touching P1
are unrestricted. A mixed original on P0 must have some exponent
at least three, exponents at most one at3 and5, or at least five
prime divisors. These are Report598's conditions.

Ordinary Type I attachments to one head prime and separate ordinary
components remain permitted exactly as in Report601. Every enlarged
Type II branch has the following declared structure.

1. It has a primary entry q>=37 and distinct head parents p,r. Its
   primary triangle originals are

       p^i r^j q^e, i,j>=0, i+j>0, e>=1.

2. It has an ordinary private block tree rooted at q. This tree
   includes the pure-q originals and excludes all secondary branches.

3. Each secondary entry s is a distinct prime s>q. Choose one
   a_s in{p,r}. Its triangle originals are

       a_s^i q^j s^e, i,j>=0, i+j>0, e>=1.

   Behind s there is an ordinary private block tree, including its
   pure-s originals. This tree has no further head contact or shared
   two-coordinate interface.

Each original is assigned once. In particular q^j s^e originals are
assigned to the secondary triangle, and a_s^i s^e originals are
allowed there. Primary and secondary entries are globally distinct. Away from the
named attachment roots, ordinary private interiors are pairwise
disjoint and contain no other primary or secondary entry. Pieces
intersect only at their declared head vertices and attachment roots.
There are no additional originals joining private interiors. Siblings may use the
same a_s or different members of{p,r}.

Every ordinary nontrivial block is on at most twelve vertices, is a
simple cycle, or has the Report599 orientation with k>=4 children
and minimum child at least k(k+3)+3. Ordinary descendants need not
increase numerically along every edge; s>q is required only for the
new shared-pair attachment. All outside primes are at least37.

This class contains Report601 by taking no secondary entries. For
example, primary original3*5*37 and secondary original3*37*41, with
the remaining head primes present through pure originals, use the
shared pair(3,37) below entry37. Their two triangles share the exterior
prime37 and a head prime; they cannot be split into Report601 branches
with disjoint private interiors and no deeper head contact. No original
here is replaced by an abstract event or independently chosen phase.

## Actual domains and one joint dead-fibre relation

Resolve every original at its full finite prime-power height and
write X_t for its complete t-coordinate, with normalized counting
measure H_t. All sets below come from this one original family.

Let V_q^0 be the actual entry domain of q's ordinary private tree,
including pure-q originals. Let V_s be the corresponding domain of
a secondary entry's ordinary private tree. Report599's actual-domain
induction gives

    H_q(V_q^0)>=1-2/(q-1),
    H_s(V_s)>=1-2/(s-1).                         (TL1)

For every secondary entry s, define the complete pair relation

    B_s={(u,t) in X_(a_s) times X_q:
          no word in V_s avoids all actual s-triangle originals
          at this same pair(u,t)}.

Report600's complete-parent-label estimate applies to this branch,
with parents(a_s,q). They are coordinatewise at least(3,37), so

    H_(a_s,q)(B_s)<=F_(3,37)(s).                  (TL2)

Here, for any reference prime pair a<b,

    C_(a,b)=a/(a-1) b/(b-1),
    T_(a,b)(N)=C_(a,b)-1-sum_(j<=N)1/d_j,
    F_(a,b)(t)=min_(0<=N<t-3)T_(a,b)(N)/(t-3-N), (TL3)

where d_j are the increasing nonunit a,b-smooth numerical labels.
The estimate keeps all actual parent residues and every original
s-height. It bounds the pair relation itself, not its projections.

At a complete primary head pair x=(x_p,x_r), let B_q^+ be the event
that no q-word in V_q^0 both avoids the primary triangle and lies
outside B_s(x_(a_s),.) for every secondary child s. This event is
exactly nonextension through the entire enlarged primary branch:
conditional on one q-word, the ordinary and secondary private
interiors are disjoint, so their actual witnesses glue. Although a
secondary branch touches a head coordinate again, B_q^+ still depends
only on the original pair(p,r).

## The amplified pair bound, without independence assumptions

Choose N<q-3 distinct nonunit primary parent labels, retaining the
whole q-tower of each selected label. At x let R_x be their actual
complement inside V_q^0. Distinct numerical originals allow at most
one original d q^e for each pair(d,e). Consequently, uniformly in x,

    H_q(R_x)>=1-(N+2)/(q-1)
              =(q-3-N)/(q-1)=r_q>0.            (TL4)

R_x can depend arbitrarily on both parent coordinates and can be
correlated with every child relation. No independence is asserted.

For x in B_q^+, every t in R_x must meet an unselected primary
original or an actual secondary blocker. Therefore, on the single
product space X_p times X_r times X_q,

    1_(B_q^+)(x) 1_(R_x)(t)
      <=sum_(actual d q^e, d unselected)
           1_(actual parent cylinder)(x) 1_(actual q-cylinder)(t)
        +sum_s 1_(B_s)(x_(a_s),t).              (TL5)

The inequality for x outside B_q^+ follows because its left side is
zero. Integrate against H_p times H_r times H_q. Its left side is
at least r_q H_(p,r)(B_q^+). Each primary summand has integral
1/(d q^e). Each secondary summand has integral exactly H_(a_s,q)(B_s):
the unused head coordinate integrates to one. This is marginalization
of one fixed product measure; no conditional law of R_x is substituted.
Dropping the indicators of R_x and B_q^+ on the upper side merely
enlarges the integral, even when these events are correlated.

If T(S) is the reciprocal sum of the unselected primary parent labels,
summing all positive q-heights gives

    H_(p,r)(B_q^+)
      <=[T(S)+(q-1)sum_s H_(a_s,q)(B_s)]/(q-3-N).
                                                       (TL6)

Thus a joint child obstruction is propagated to the previous joint
interface with a controlled loss. The factor(q-1) is necessary: the
child terms were measured under q-Haar, whereas the surviving q-domain
has only the uniform lower mass in TL4.

Call a primary entry early if p,r both belong to P0, and late otherwise.
For an early entry, use the minimizing reference patterns for(3,5)
in TL3; for a late entry use(3,23). The actual reciprocal remainder
is bounded by the reference remainder. With t=E or L accordingly,
write N_t(q) for that minimizer and

    A_t(q)=(q-1)/(q-3-N_t(q)),
    F_E(q)=F_(3,5)(q), F_L(q)=F_(3,23)(q).

Then TL2 and TL6 yield

    H_(p,r)(B_q^+)<=F_t(q)+epsilon_q,
    epsilon_q=A_t(q)sum_(s child of q)F_(3,37)(s). (TL7)

The denominator is a positive integer, hence

    A_t(q)<=q-1<s for every child s.             (TL8)

## A complete budget for all secondary primes

For prime41<=s<=967 define

    A_*(s)=max_(t in{E,L}, prime37<=q<s)A_t(q).

Every relevant primary minimizer here is already certified by
Report601. The new producer computes F_(3,37)(s) exactly at all151
primes41<=s<=967, retaining the full reciprocal tail of literal
3,37-smooth labels. It checks the ordered label prefix independently
by an exponent grid.

A secondary prime belongs to only one primary branch. Thus, even
with arbitrary overlapping head pairs and arbitrary numbers of
children, their total additional fee is at most

    sum_q epsilon_q
      <=sum_(41<=s<=967 prime)A_*(s)F_(3,37)(s)
        +sum_(s>=971 prime)sF_(3,37)(s)=:W.     (TL9)

For clarity, W on the right is henceforth replaced by its explicit
upper bound below. No independence or simultaneous worst-case
attainment is required.

For n>=22 and odd s in[2n^2+3,2(n+1)^2+1], the rectangle
0<=i,j<n excluding the unit has N=n^2-1 labels. With C=37/24,

    F_(3,37)(s)<=2 C 3^(-n)/(n^2+1).

The interval contains2n+1 odd integers and each s is at most
2n^2+4n+3. Its weighted contribution is therefore at most

    2 C 3^(-n)(2n+1)(2n^2+4n+3)/(n^2+1)
      <=2 C(4n+11)3^(-n),                       (TL10)

because the difference of the numerator products is
(n-2)(n-4)>=0. All primes s>=971 lie in these intervals. Summing
the geometric first moment proves

    sum_(s>=971 prime)sF_(3,37)(s)
      <=C(12*22+39)3^(-22)
       =3737/251048476872.                       (TL11)

The exact finite sum plus this entire infinite tail is

    W_bound=
      3429563111986983047669811975140668350494433104168844559551995660731651367996576293
      /291904356281363149742315282589811678638243496117144277796517978380256975760755526966400
      <1/85000.                                 (TL12)

Its decimal value is approximately0.000011748927476372664. The
fraction and strict rational comparison are the proof inputs; the
decimal is only for scale. In particular the small children41 and43
are paid explicitly, rather than hidden in an assumed large-prime tail.

## Restrict one source, continue it, and pay the remaining blockers

Use Report601's same seven-coordinate submeasure eta, with

    eta<=rho, eta(1)-c Gamma_Q(eta)>=K,
    c=1084133/201247200,
    D=3458/405, alpha=33/(200D)=2673/138320.

All early enlarged blockers B_q^+ are determined by P0 alone.
The early pair marginal of rho is dominated by(10/3) times pair Haar.
If epsilon_E is the sum of epsilon_q over early entries, deletion
therefore costs at most

    delta_E<=(10/3)[S35+epsilon_E],
    S35=sum_(q>=37 prime)F_(3,5)(q)<1/2600.

Restrict eta by the union of those actual enlarged blockers. The
unchanged unit-query argument gives

    eta'(1)-c Gamma_Q(eta')
       >=K-(1-c)(10/3)[S35+epsilon_E].           (TL13)

Apply the23,29,31 continuation afresh to this same restricted source.
It retains its P0 word and hence every early avoidance condition.
On the resulting actual head set U_*, restrict head Haar, as in
Report601, and pay all late enlarged blockers using their full pair
relations and pair-Haar domination. Write epsilon_L for their
additional total fee. Ordinary Type I attachments still cost at
most2^-17. Their private primes are disjoint from the already used
primary and secondary interiors.

The original Report601 simple reserve was31991/2048000000. The only
additional loss in final head-Haar units is bounded by

    beta epsilon_E+epsilon_L,
    beta=alpha(1-c)(10/3)
        =46191477/720966400<1.                  (TL14)

Since epsilon_E+epsilon_L<=W_bound, charging every additional fee
at full head-Haar cost is conservative. In particular,

    H_P(U_ext)
      >31991/2048000000-W_bound
      >31991/2048000000-1/85000
       =134247/34816000000
      >1/260000>0.                              (TL15)

The early gate is positive before continuation: its resulting
head lower bound is greater than1/32000-beta W_bound>0. Thus the
continuation was not applied to a negative or merely hypothetical
source. Early source domination and continuation normalization have
both been included in beta.

Choose one complete head word in U_ext. For every primary entry its
actual B_q^+ exclusion supplies one q-word simultaneously avoiding
its primary originals and all its secondary relations. That same
q-word extends through V_q^0. For each child s, the same pair
(x_(a_s),q-word) lies outside B_s, so one s-word in V_s extends
through its ordinary private tree and avoids all child originals.
All these witnesses glue, since the declared private interiors are
disjoint and every original was assigned to one of these pieces.
Type I branches and separate components use their old domain induction.
CRT gives an integer avoiding the entire original family.

If Q_off is the product of the complete outside prime powers, the
full survivor density is greater than1/(260000 Q_off). The head
bound is not a uniform height-independent full-density bound.

## Transport and scope

For arbitrary ten ordered odd head primes, use Report601's shifted
digit injections on the head only. Leave every outside coordinate
fixed. For each injection, retain nonempty original pullbacks exactly
and pad empty pullbacks with one fixed auxiliary source cylinder at
the same exponent/support vector. Distinct numerical originals,
head occurrences and the entire declared two-level decomposition
are preserved. Every private-only original is unchanged; V_q^0 and
V_s and all ordinary block conditions are therefore unchanged.
The inequalities q>=37 and s>q are unchanged as well.

An avoiding extension of the padded source maps to an avoiding
extension of the target with its same outside witness. Apply TL15
to every padded source and average the head injections. Their pointwise
average is target head Haar, giving the same extendible-head bound.
This transports the actual extension predicate, without asserting
invariance of an optimized query law.

The original unrestricted target quantifies over every finite family
of distinct odd moduli, with no support decomposition or head-label
restriction. This result quantifies over every such family satisfying
the explicit two-level decomposition above, with arbitrary heights
and globally fixed phases. Further shared-pair levels, originals
joining sibling interiors, and the remaining restricted head labels
are not covered. Those gaps do not invalidate the attained complete
subclass or turn a failure of a fee bound into a covering example.

The [producer](../../frontier/cover-geometry/two_level_triangle_attachment.py)
and [data](../../frontier/cover-geometry/two_level_triangle_attachment.json)
verify621 named checks, including all151 child-prime rows, both old
parent-amplification tables, the entire analytic tail, the early
continuation coefficient and the positive simultaneous reserve.
The producer uses only the inherited Report601 certificate, checking
its fingerprint; it does not repeat the old full head scan.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_level_triangle_attachment.py

The domain, same-source integral, all-height majorants and witness
gluing above supply the mathematical scope beyond these finite checks.

[Report610](610-normalized-kernels-close-increasing-two-parent-networks.md)
replaces the two-level restriction by an arbitrary finite increasing
two-parent network behind each primary. It permits connections between
earlier branches and unbounded co-occurrence treewidth, while retaining
the head restrictions and disjoint outside coordinates between primary
components. One normalized whole-network law gives the stronger
extendible-head lower bound1/200000.

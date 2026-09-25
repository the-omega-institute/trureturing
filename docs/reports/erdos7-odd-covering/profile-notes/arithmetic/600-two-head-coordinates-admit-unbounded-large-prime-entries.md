# Two head coordinates can share arbitrarily many large-prime entries

Let a finite family have pairwise distinct odd numerical moduli greater
than one and arbitrary globally fixed residues. Suppose at least ten
primes occur, and let P be its ten smallest primes. Head-only originals
must satisfy
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md):
pure powers and originals touching the last three head coordinates are
unrestricted; a mixed original on the first seven must have some
exponent at least three, or exponents at most one on the first two
coordinates, or at least five prime divisors.

In addition to the single-parent attachments of
[Report599](599-the-ten-prime-head-admits-arbitrary-twelve-vertex-attachments.md),
permit the following two-parent branches. Each has one distinct entry
prime q>=53 and two distinct head primes p_q,r_q. Its head-touching
originals have exactly the form

    d q^e,  d=p_q^a r_q^b>1,  a,b>=0, e>=1.

All these original labels, heights and phases are unrestricted. Behind
q there may be arbitrarily many levels of the single-parent block trees
allowed by Report599. The branch's private primes, including q, are
disjoint from every other branch's private primes. The parent pair may
vary between branches and may overlap or coincide with another pair.

Then the original family is noncovering. More precisely, the proportion
of complete head configurations admitting a simultaneous avoiding
extension is greater than1/90000. There is no bound on the number of
entry primes, the number or depth of private blocks, or the original
finite heights. A further version also admits entries37,41,43,47 whose
parent pair avoids the actual prime3; its weaker positive bound is given below.

This removes the requirement that every exterior branch meet the head
in one prime. It still requires the stated branch decomposition; it
does not prove an arbitrary recursive two-coordinate separator theorem
or unrestricted Erdős #7. The proof is ordinary mathematics with exact
rational certificates, not new Lean verification.

## The original-label decomposition

There are two allowed kinds of branch, both with pairwise disjoint
private interiors and no additional originals joining those interiors.

- Type I meets the head in one prime and is a rooted block tree of the
  kind in Report599.
- Type II meets the head only in its declared pair. Every original
  containing a head prime and a private prime is supported in
  {p_q,r_q,q} and contains q. After removing the head-touching originals,
  its private part is a block tree rooted at q, with no other link to
  the head.

Every private nontrivial block is on at most twelve vertices, is a
simple cycle, or, in its orientation away from the head or entry,
has k>=4 children with smallest child s>=k(k+3)+3. Other connected
components may have these same allowed block trees, with a chosen
root for their orientation. All primes outside P are at least37.

Original head-only labels belong to the head once. Pure private-prime
labels belong to their private coordinates once, including pure q
labels at an entry. A Type II head-touching class belongs to its unique
entry q. Every remaining mixed original belongs to its one private
block. These conditions keep every actual numerical modulus, residue
and full exponent vector. No class or phase is added by the
decomposition.

Different Type II branches can create a large common graph block with
the head, so Report599's whole-head-block hypothesis is no longer
required. Only their private interiors must separate as stated here.

## One joint head law and actual entry domains

Resolve all original exponents on full coordinates X_p=Z/p^h_p Z,
including heights used by outside classes. Let U be the head-only
survivor and set mu=H_P restricted to U. Report598 gives

    mu(X_P)>=h,
    h=26345885990886052732242307711
       /468579418066477236879360000000000.          (TP1)

The measure remains unnormalized and satisfies mu<=H_P. Hence every
joint marginal on a head pair obeys

    (pi_(p,r))_*mu<=H_p times H_r.                 (TP2)

The pair marginal of mu need not be a product. Inequality TP2 is enough
to pay a bad set measured under product Haar on the same pair.

For a Type II entry q, let V_q be its actual set of words admitting an
avoiding extension through its entire private block tree, including
its pure-q classes, but excluding its head-touching classes. The
actual-domain induction of Report599 gives

    H_q(V_q)>=1-1/(q-1)-2e_q/(q-1),
    e_q=sum_(strict private descendants r) f(r)<1/2,
    f(r)=2^(-(r-1)/2), r>=37.                     (TP3)

These are domains from the same original family. There are no hidden
joint constraints with another branch. In particular V_q is nonempty.
Under nu_q=H_q(.|V_q), the sum of literal cylinder caps over all
positive q-exponents is at most

    b_actual=1/[(q-1)H_q(V_q)]<=1/(q-3)=b.        (TP4)

The finite original sum is bounded by the full geometric series.
This introduces no extra original labels and truncates no original
height.

## Finite parent-label conditioning controls a joint blocker

Fix one entry q and its parent pair p<r. Choose any finite set S of
N distinct nonunit labels p^a r^b, with N<q-3, and let T(S) be the
sum of reciprocals of all unselected nonunit p,r-smooth labels.
At a complete parent
word x in X_p times X_r, avoid all actual head-touching classes whose
parent label belongs to S, retaining every original q-height. Let R_x
be their actual complement inside V_q.

For each fixed parent label d, numerical distinctness permits at most
one class d q^e at each e. Thus, even though its parent residue may
vary with e,

    nu_q(R_x)>=1-Nb>0 for every x.                (TP5)

The law nu_(q,x)=nu_q(.|R_x) is consequently actual and well-defined.
It is selected by conditioning on the original classes at this one
parent word, not by choosing a separate optimum for each query.

Let B_q be the full joint blocker: parent pairs with no avoiding
entry word in V_q after all head-touching originals are imposed. If
x belongs to B_q, every point remaining in R_x must meet an original
whose parent label lies outside S. Therefore

    1_(B_q)(x)<=sum_(actual d q^e, d notin S)
          1_(x in actual parent cylinder of d q^e)
          nu_(q,x)(actual q^e cylinder).          (TP6)

For every summand the last factor is at most
q^(-e)/[H_q(V_q)(1-Nb)]. Its parent cylinder has product Haar
probability1/d. Integrating TP6 over the original complete parent
pair and summing the full positive q-height series gives

    (H_p times H_r)(B_q)
      <=[b_actual/(1-Nb)]
           sum_(d=p^a r^b>1, d notin S)1/d
      <=T(S)/(q-3-N).                            (TP7)

This is a bound for one joint bad set on two full coordinates. It
does not replace the set by the product of its projections. The
conditioning uses every original selected d-tower, and the remaining
labels are charged globally once each; absent labels contribute zero
before the harmless infinite majorant.

This extends the actual-parent conditional-kernel method of
[Chapter23](../../problem-details/23-conditional-kernels-and-recursive-block-noncoverage.md)
from finitely many parent exponent layers to finitely many complete
parent labels. The exact joint interface and same-boundary-law union
bound already appear in
[Chapter17](../../problem-details/17-two-prime-separator-interfaces-and-exact-count-probes.md).
Neither existing interface alone supplies the numerical fee below.

## One uniform two-prime fee and its infinite sum

List the nonunit3,5-smooth labels in increasing numerical order as
d_1,d_2,... . Their complete reciprocal sum is7/8. Put

    T_N=7/8-sum_(j=1..N)1/d_j,
    F(q)=min_(0<=N<q-3) T_N/(q-3-N).              (TP8)

Use the exponent patterns of the selected reference labels on the
actual ordered pair p,r. Since p>=3 and r>=5, every unselected
reciprocal decreases, so its actual tail is at most T_N. There are
still exactly N distinct selected parent labels. Thus TP7 implies

    (H_p times H_r)(B_q)<=F(q)                    (TP9)

uniformly over every allowed head pair, all heights and all original
phases. The same reference pattern set is used throughout each
application; selecting the actual N smallest labels is optional and
can only improve this upper bound.

The exact producer enumerates the148 primes53<=q<=967 and minimizes
TP8 with rational arithmetic. Their simultaneous fee sum is

    F_finite=
      26367566679970603998162514215695685748991796027092345257
      /715166192625059001701426870634865611791610717773437500000000.
                                                        (TP10)

For the infinite tail no search over primes or parent labels is
needed. For n>=22 and odd q in

    2n^2+3<=q<=2(n+1)^2+1,

select the complete parent rectangle0<=a,b<n, excluding the unit.
It has N=n^2-1 and reciprocal remainder

    T<=15/8(3^(-n)+5^(-n)-15^(-n))
       <=15/4*3^(-n),
    q-3-N>=n^2+1.                                (TP11)

The N smallest reference labels minimize the reciprocal remainder
among all N-label sets, so the same bound also majorizes F(q).
There are2n+1 odd integers in the interval. All primes q>=971 are
covered, because971=2*22^2+3. Consequently

    sum_(q>=971 prime)F(q)
      <=sum_(n>=22)(2n+1)/(n^2+1)*(15/4)*3^(-n)
      <=135/(8*22)*3^(-22)
       =5/204558018192.                           (TP12)

The second bound uses(2n+1)/(n^2+1)<=3/n<=3/22 and one convergent
geometric series. Set F_total=F_finite+5/204558018192.

## Pay all branches on the same head and glue actual witnesses

By TP2 and TP9, the cost of deleting a Type II blocker from mu is
at most F(q). Entry primes are distinct, so the sum over all such
actual branches is at most F_total, even when their parent pairs
overlap. No independence among these bad events is assumed.

Type I branches retain Report599's original-parent-Haar fees. Their
immediate charged child sets are disjoint, giving a simultaneous loss
at most

    sum_(r>=37 prime)f(r)<=2^(-17).                (TP13)

Private blocks behind Type II entries have already been used to form
V_q. They are not charged again as Type I branches at the head.
Combining the two kinds of actual bad set by one union bound yields

    H_P(U_ext)>=h-F_total-2^(-17)>1/90000>0.      (TP14)

Choose one surviving complete head word. Each Type I branch has an
avoiding private extension at its one parent word. Each Type II
branch has an entry word in V_q avoiding every original at the same
fixed parent pair; that word has an avoiding private extension by
definition of V_q. The private interiors are disjoint and there are
no additional cross-branch originals, so all these witnesses glue.
Other components are handled by their actual block-domain induction.
CRT then supplies an integer avoiding the full original family.

For Q_off equal to the product of all original prime powers outside
P, including other components, this also gives

    H_full(U_full)>1/(90000 Q_off).               (TP15)

The constant1/90000 concerns extendible head configurations. A
height-independent full-density constant is not asserted.

## Lower entries whose parent pair does not contain3

The same theorem admits one further simultaneous extension. Permit
Type II entries q in{37,41,43,47} whenever neither parent is the
actual prime3. Keep every q>=53 entry already allowed, with arbitrary
head pairs, and every Type I attachment. Then the extendible head
proportion is greater than1/2500000, and full survivor density is
greater than1/(2500000 Q_off).

For such a lower entry, order its actual parents p<r. They satisfy
p>=5 and r>=7. Apply TP7 using the exponent patterns of the N smallest
nonunit5,7-smooth labels. Their full reciprocal sum is

    (5/4)(7/6)-1=11/24.

Every actual unselected reciprocal is at most its5,7 reference value.
The same condition N<q-3 therefore gives these exact fees:

|Entry q|Selected parent labels N|Joint blocker upper fee|
|---:|---:|---:|
|37|30|5290879/882367500000|
|41|32|3526879/1323551250000|
|43|34|12185819/6617756250000|
|47|39|31395653/38603578125000|

Each entry prime appears in at most one Type II branch. The sum of all
four additional charges is

    F_low=5241874291/463242937500000.

One union bound on the same original head measure now gives

    H_P(U_ext)>=h-F_total-2^(-17)-F_low
      =62332722242758081115138250112167978469716233789601849512803125699409139
       /151717507333311971414691529009750383198896514375000000000000000000000000000000
      >1/2500000>0.

The original conclusion>1/90000 remains valid when these four
additional entry types are absent. This corollary does not admit a
q<53 two-parent entry involving3. It retains the same private-interior
separation and single-parent private block-tree conditions; it makes
no new assumption of independence on overlapping head pairs.

## Boundary of the result

The proof retains the two-parent relation at every entry. It does
not permit a Type II private subtree to acquire another two-parent
separator, nor permit originals joining two entry primes or their
private interiors. Those changes would require new joint-domain
invariants; the single-coordinate V_q used in TP3 would not provide
them.

The cutoff53 is a proved sufficient threshold for the stated fee
calculation. Failure of this particular bound at smaller entries is
not a covering example or a proof that their branches cannot be
included by sharper joint estimates. Unrestricted dense support and
the remaining low-support head labels remain unresolved.

## Reproducible arithmetic

The [producer](../../frontier/cover-geometry/two_parent_entry_attachment.py)
and [data](../../frontier/cover-geometry/two_parent_entry_attachment.json)
retain every selected parent-label count, the common ordered prefix of
literal3,5 labels with exponent pairs, all148 finite prime fees and the
analytic remainder. A priority-queue enumeration agrees with an independent
bounded exponent grid; trial division agrees with a separate sieve.
All324 named checks pass, including the four additional low-entry fees. The inherited Report599 producer fingerprint,
head density and ordinary-attachment reserve are checked before the new
simultaneous reserve is computed.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_parent_entry_attachment.py

The infinite bounds and the original-family interpretation are the ordinary
proof above. The finite program verifies the arithmetic inputs and strict
reserve; it is not a substitute for those arguments or new Lean verification.

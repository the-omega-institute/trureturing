# The ten-prime head admits arbitrary twelve-vertex attachments

Let a finite family have pairwise distinct odd numerical moduli greater
than one and arbitrary globally fixed residues. Suppose at least ten
primes occur, and let P be its ten smallest primes, in increasing order.
Every original supported entirely on P must satisfy
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md): pure
powers and originals touching the last three coordinates are unrestricted;
a mixed original on the first seven coordinates must have some exponent
at least three, or exponents at most one on the first two coordinates,
or at least five prime divisors.

Form the original prime-interaction graph and add every edge between
the ten vertices in P. Require that P is exactly the vertex set of its
distinguished block. Root that component's block-cut tree at this block;
root every other component at an arbitrary prime. Every other block must
be one of:

- a block on at most twelve vertices;
- a simple cycle;
- an oriented block with k>=4 children whose smallest child s satisfies
  s>=k(k+3)+3.

Then the original family is noncovering. The number of outside primes,
number and depth of blocks, and all original finite prime-power heights
are unbounded. The Haar proportion of head configurations that avoid
all head originals and extend through the whole component is greater
than1/21000.

This applies the existing Haar-core restriction and gluing argument in
[Chapter35](../../problem-details/35-eight-prime-core-with-seven-vertex-attachments.md)
to the stronger head of Report598, with a new eleven-child
conditional-kernel certificate. The local kernel theorem and analytic
large-block argument are reused from
[Chapter23](../../problem-details/23-conditional-kernels-and-recursive-block-noncoverage.md). It is ordinary
mathematics with an exact arithmetic certificate, not a new Lean theorem
or a resolution of unrestricted Erdős #7. The positive constant concerns
extendible head configurations; a full-density lower bound includes the
outside period as described below.

## One actual head set on complete original coordinates

For each actual prime p, take X_p=Z/p^h_p Z, where h_p is its maximum
exponent anywhere in the complete original family, including attached
classes. Let H_P be product Haar probability, and let U be the complete
survivor of head-only originals in X_P. The ordered-prime transport in
Report598 gives

    H_P(U)>=h,
    h=26345885990886052732242307711
       /468579418066477236879360000000000>1/18000.   (HB1)

Lifting a head coordinate to the height required by an attachment does
not change this proportion. Use the actual unnormalized measure

    mu=H_P restricted to U.

Then mu<=H_P and every complete-coordinate marginal of mu is bounded
by the corresponding H_p. This is the same interface used in Chapter35,
Section1. No product structure for the correlated head-survivor law is
asserted or needed.

Adding graph edges within P changes no original cylinder. Requiring P
to remain its entire block excludes paths through outside vertices that
join two different head vertices. Thus every immediate attached block
meets P in exactly one parent p, and its private descendant prime set is
disjoint from those of all other immediate attachments. Every original
mixed support is a clique, hence belongs to one block; pure originals
are assigned once to their own prime. The added edges introduce no
extra original constraints.

## Actual descendant domains and an eleven-child local fee

All exterior primes are at least37. Retain the fees of Chapter23,
in particular

    f(q)=2^(-(q-1)/2) for q>=17,
    d_3=1, d_5=3/10, d_p=2/(p-1) for p>=7.       (HB2)

For an exterior prime q let V_q be its actual domain of words admitting
an avoiding extension through its descendant subtree, including its
own pure originals. Write e_q=sum_(r in actual strict descendants)f(r).
The existing invariant is

    H_q(V_q)>=1-1/(q-1)-d_q e_q.                  (HB3)

For a block K attached at parent p, its full-parent blocker B_(K->p)
consists of complete p-words having no avoiding tuple of its actual
child domains. It excludes the parent's pure originals. The local
estimate used below is

    H_p(B_(K->p))<=d_p sum_(q in C_K)f(q),         (HB4)

where C_K is a specified subset of that block's actual immediate child
primes. For the new at-most-twelve-vertex blocks below, C_K contains only
the actual minimum child. Chapter23's analytic large-block theorem also
charges that actual minimum; its existing cycle theorem uses a subset
of the actual child fees.

Here is the new local certificate. Consider a block with one to eleven
actual children, of minimum s>=37. Under HB3 its actual child-domain
product law has complete positive-depth cofactor caps bounded by

    b_q=1/[(q-1)H_q(V_q)]
        <=1/[q-2-2e_q]<=1/(q-3)<=1/(s-3)=b,       (HB5)

because e_q<1/2. The term "complete" means the sum over all positive
exponents on that child coordinate, not a height cutoff. If fewer than
eleven children occur, pad with fresh independent dummy prime
coordinates larger than every original prime. Their domains are full,
their positive-depth caps are also at most b, and no original uses them.
The minimum s stays a real child. No fee or descendant expense is
assigned to a dummy; a surviving padded tuple projects to a real one.

Take k=11 and a shallow parent cutoff t>=1. For every nonempty child
support A, the actual union of internal classes and shallow crossing
classes has cap

    v_t(A)=(t+1_(|A|>=2))b^|A|.                  (HB6)

Internal singleton classes are already avoided by the child domains.
At each positive parent exponent a complete child cofactor occurs at
most once globally across residues, by original numerical distinctness.
Actual unions with disjoint child supports depend on disjoint product
coordinates. Thus these are exactly the source and event hypotheses
of Chapter23 CK6--CK12.

All comparison coordinates have the same cap b, so every coordinate
residual depends only on its size n. Let Z_n be that residual. It has
the exact support-deletion recurrence

    Z_0=1,
    Z_n=Z_(n-1)-sum_(j=1..n)
        binom(n-1,j-1)(t+1_(j>=2))b^j Z_(n-j).    (HB7)

For an independent evaluation, signed partitions of the occupied
coordinates give

    c_0=1,
    c_n=-t c_(n-1)
        -(t+1)sum_(j=2..n)binom(n-1,j-1)c_(n-j),
    Z_n=sum_(j=0..n)binom(n,j)c_j b^j,
    L=sum_(j=1..11)binom(11,j)b^j Z_(11-j).       (HB8)

Positivity of all twelve numbers Z_0,...,Z_11 establishes all2048
coordinate residual conditions. The support-intersection argument in
Chapter23 then supplies the whole strict region, not just its top
polynomial. Its same-law conditional avoidance ratio yields

    H_p(B_(K->p))<=K_(p,t)
       =L/[p^t(p-1)Z_11].                       (HB9)

The exact finite certificate checks every odd integer

    s=37,39,...,155,                             (HB10)

including composites only as numerical cap proxies. Each of these60
rows has a selected integer t with Z_n>0 for all0<=n<=11 and

    K_(3,t)<f(s)=2^(-(s-1)/2).

The largest certified ratio K_(3,t)/f(s) occurs at s=37,t=12:

    K_(3,12)=49074500591689/17621384873374478358,
    K_(3,12)/f(37)
       =6432292941553860608/8810692436687239179<1. (HB11)

For every actual minimum s>=157, Chapter23's analytic eleven-child
theorem applies because157=11(11+3)+3. These two ranges exhaust all
possible prime minima. If the actual block has fewer children, the
same padded argument still charges only its real minimum.

For a non-3 parent the same kernel and comparison give

    K_(p,t)/d_p=(3/p)^t K_(3,t) for p>=7,
    K_(5,t)/d_5=(5/3)(3/5)^t K_(3,t)<=K_(3,t).   (HB12)

Thus HB4 holds for every possible head parent as well as all exterior
parents. The p=5 formula uses d_5=3/10 and t>=1. Chapter23 already
provides the corresponding non-3 comparison for its analytic range.

Every local estimate assumes only HB3 for actual child domains and
disjoint descendant budgets, not that descendants use the same block
type. The induction therefore mixes at-most-twelve-vertex blocks,
cycles and qualifying larger blocks, from leaves upward. Outgoing
blocks charge disjoint actual child primes, so their union costs at
most d_q e_q. Adding the pure-q cost1/(q-1) proves HB3 at that parent.
This closes the induction and does not assume the new local fee for
its own descendants in advance.

Every p-blocker in HB4 is measured against original parent Haar H_p,
not a freshly normalized survivor marginal. Its proof keeps one full
parent word throughout and includes all original heights. Parent-pure
classes at a head prime have already been charged in U; at an exterior
prime they enter HB3 once.

## A summable interface loss

Distinct immediate attachments have disjoint actual child sets, so
their C_K are disjoint even when they share a head parent. Since d_p<=1,
HB4 and the marginal bound on mu give the simultaneous loss bound

    mu(union_K pi_parent(K)^(-1)(B_(K->parent(K))))
      <=sum_K H_parent(K)(B_(K->parent(K)))
      <=sum_(q>=37 prime) f(q)
      <=sum_(n>=18)2^(-n)=2^(-17).                (HB13)

The final majorant sums over every odd integer at least37, so it does
not bound the number of blocks or primes. Descendant primes affect the
local domains HB3; they are not charged again as independent immediate
attachments at the head.

Consequently one actual set of simultaneously extendible head words has

    H_P(U_ext)>=h-2^(-17)>1/21000>0.              (HB14)

This does not combine separately optimized marginals. It subtracts a
union of actual blockers from one fixed original head set.

Fix any word in U_ext. Every attached block has an avoiding child tuple
at this same parent word, and each child word has an avoiding descendant
extension by definition of V_q. Private sides are disjoint, so these
finite witnesses glue. Other connected components use the same non-3
actual-domain induction and have avoiding tuples. CRT then produces an
integer outside every original class.

If Q_off=product_(q outside P)q^h_q, each extendible head word has at
least one complete outside tuple. Thus the full survivor density obeys

    H_full(U_full)>1/(21000 Q_off).               (HB15)

This last bound depends on the original outside period. No uniform
full-density bound of1/21000 is claimed.

## Scope and the remaining obstruction

The head may have arbitrary interaction among its ten primes, subject
to Report598's numerical-label condition. The exterior may have
arbitrarily many vertices and arbitrarily many levels, but it must meet
the stated block conditions. In particular an exterior path joining
two different head vertices is not covered by this theorem; neither
is an arbitrary large dense exterior block.

The generic Haar-head argument is already in Chapter35 Sections1/4,
and Chapter38 applies it to further eight-prime cores. The new input
here is Report598's ten-prime family and its margin, together with the
fact that every outside prime is at least37, and the new local
eleven-child estimate HB5--HB12. No new generic gluing lemma is required.

The [producer](../../frontier/cover-geometry/twelve_vertex_attachment_kernel.py)
and [data](../../frontier/cover-geometry/twelve_vertex_attachment_kernel.json)
read the completed Report598 data, verify its producer fingerprint and
inherited density, and check the geometric loss and positive reserve
in HB14. All310 named checks pass. Every selected row is verified by
both recurrences HB7--HB8, retaining all twelve residuals per row. These finite calculations support the constants;
the analytic large-minimum theorem and the preceding decomposition and
actual-domain induction establish the unbounded quantifiers. No
template scan or original-residue enumeration is repeated.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/twelve_vertex_attachment_kernel.py

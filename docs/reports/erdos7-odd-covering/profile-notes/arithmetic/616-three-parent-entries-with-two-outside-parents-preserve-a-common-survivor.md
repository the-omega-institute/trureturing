# Three-parent entries with two outside parents preserve a common survivor

Keep the head restrictions and the global outside network of
[Report614](614-one-global-two-parent-network-preserves-a-common-survivor.md).
An outside owner may now have THREE fixed smaller parents, provided at
least two are outside the ten-prime head. It may carry every actual mixed
label on that parent triple, at arbitrary finite original heights and
with arbitrary globally fixed phases. All previous two-parent entries
and arbitrary crossings between their roots remain allowed.

The proportion of complete head configurations with an avoiding extension
is greater than1/170000. This is a new family of actual four-prime mixed
originals, not merely an improvement in Report614's displayed constant.
It remains an ordinary mathematical proof with exact rational checks,
not new Lean verification or a resolution of unrestricted Erdős #7.

## Complete actual family

Use the ten smallest primes of the family as the head. First take the
reference primes

    P0={3,5,7,11,13,17,19}, P1={23,29,31}, P=P0 union P1.

The head-only conditions are those of Report598: pure head originals
and originals touching P1 are unrestricted; a mixed original on P0
must have an exponent at least three, exponents at most one at3 and5,
or at least five prime divisors. All numerical original moduli are
distinct, with one fixed residue at each actual modulus.

Outside entries are globally distinct primes v>=37. Every entry owns
ONE fixed tuple of distinct smaller parents from the head and the other
outside entries. There are two permitted types:

* Two parents: exactly Report614's type. A root has two head parents;
  a nonroot has at least one outside parent.
* Three parents: at least two must be outside the head. It owns any
  subset of the actual originals

      a^i b^j c^k v^e,
      i,j,k>=0, i+j+k>0, e>=1.                 (TP1)

The tuple is fixed for its owner even when some original exponents are
zero. Several different parent tuples are not granted to one owner.
Every parent is numerically smaller than its owner. The positive exponent
on the unique largest introduced prime preserves numerical ownership.
Three-parent entries are at least43; their two distinct outside parents
are at least37 and41. There is no bound on finite network size, width,
depth or co-occurrence treewidth, and no separation by root, head pair
or early/late root type.

At each entry, Report599 ordinary private block trees remain allowed,
including pure powers of that entry. Their interiors are disjoint from
all network entries and from each other away from their attachment roots.
The permitted ordinary blocks, ordinary Type I attachments to a single
head prime, and separate ordinary components retain exactly Report614's
conditions. No new crossing through such private interiors is introduced.
Each original is assigned once to the head, one fixed owner inventory,
or an ordinary block. All original heights are arbitrary finite quantities.

## The same global joint law, with more precise head marginals

Retain Report614's actual seven-coordinate submeasure eta and constants

    eta<=rho=product_(p in P0)rho_p,
    eta(1)-c_head Gamma(eta)>=K,
    K=26345885990886052732242307711
          /9055182074115772514304000000000,
    c_head=1084133/201247200,
    D=3458/405,
    C=D*(200/33)=138320/2673, alpha=1/C.         (TP2)

Rho is a probability, eta(1)<=1, and its coordinate density caps are
2 at3 and p/(p-2) at every other P0 prime. Its pair caps are at most10/3.

First sample every two-head-parent root whose parents both belong to P0,
using the same normalized selected-complement Haar rows as Report614.
Then apply the existing head-only normalized kernels at23,29,31, which
have conditional ORIGINAL-Haar density caps

    kappa_23=5/3, kappa_29=20/11, kappa_31=2.    (TP3)

They ignore the sampled outside roots. If x0,x1 are the first-seven and
last-three head coordinates, the exact enlarged law at this stage is

    eta(dx0) K_head(dx1|x0)
                     product_(early roots q)nu_q(dz_q|x0).      (TP4)

Thus its head marginal mu is exactly the existing physical head law.
It has mass eta(1), satisfies mu<=C H_P, and charges head-bad mass at
most c_head Gamma(eta). Conditioned on the full head, the early roots
retain their product kernel and their original conditional prefix caps.

In addition to the global density C, this SAME mu has the sharper bounds

    mu's marginal on any one head prime <=2H,
    mu's marginal on any two head primes <=4(H times H).        (TP5)

For a P0 coordinate use eta<=rho and the probability of the other rho
coordinates. For a new head coordinate use its conditional cap in TP3
and eta(1)<=1. For a P0 pair use the original product-rho bound10/3.
For a P0/new pair, eliminate the new coordinate first and then use the
P0 cap, giving at most2*kappa_q<=4. For two new coordinates, eliminate
the later sampled one first, giving kappa_q*kappa_r<=40/11<4.
Every omitted intervening normalized kernel integrates out. This proves
TP5 jointly; it is not a product of unrelated marginal inequalities.

Now sample every remaining outside entry in increasing numerical order.
Every parent is available: all heads and early roots are already present,
and every other outside parent is smaller. These normalized rows define
one unnormalized joint law Pi by Report614's construction; Pi is not
conditioned on survival. Its head marginal and conditional early-root law
remain those above. All later normalized rows preserve that head marginal
and the masses of earlier events.

## Ordinary domains, root costs and two-parent costs remain valid

Let V_v^0 be the actual ordinary private extension domain at entry v.
It includes its pure powers and satisfies H_v(V_v^0)>=1-2/(v-1).
Deleting all actual owner-height towers in N_v selected nonunit parent
patterns leaves a set R_v with

    H_v(R_v)>=D_v/(v-1), D_v=v-3-N_v.           (TP6)

This bound applies to either two or three declared parents. A selected
pattern has at most one original at every positive owner height, and the
full geometric owner-height sum is1/(v-1). No actual phase is discarded.

Roots keep Report612's choices: finite minimizing patterns through967
and rectangle patterns in the entire remaining tail. They have D_q>=4,
use only H_q(.|R_q), and have conditional density A(q)=(q-1)/D_q.
Their complete series satisfy S_E<1/2600 and S_L<1/125000. Early root
violation mass is at most(10/3)G_E(q), as before. TP5 now bounds a late
root's violation mass by4G_L(q), rather than the full-density factor C.
Thus the total root payment in Pi is at most

    (10/3)S_E+4S_L<1/780+4/125000.             (TP7)

All nonroots use the selected-complement base and a normalized capped
kernel, as in Reports612/614. Its density relative to original owner Haar
is at most6 at every full sampling history. Completely forbidden remaining
fibres retain a normalized row; no hidden positive survivor fibre is assumed.

For two-parent nonroots the old reference(3,37), caps(1,37/4), still applies.
When one parent is a head prime, TP5 contributes factor2; with both outside,
the total input mass is at most1. The raw violation fee is therefore at
most2J_2(v), using the existing Report612 choices. Its whole-prime bound is

    W_2=sum J_2(v)<1/250000.                    (TP8)

Ordinary Type I blockers depend on one head coordinate. Their Haar fee
is at most2^-17, so TP5 pays their pullback to Pi by at most2^-16. They
are deleted as head bad sets once and need not be sampled into the network.

## Three actual parents enter one joint square moment

Order a three-parent tuple as a<b<c. At least two are outside, so
b>=37,c>=41. For every root q>=r and exponent j>=1,

    A(q)/q^j <=(1/4)q^(1-j)<=(r/4)r^(-j).      (TP9)

Every generated nonroot has density at most6 and is at least41; hence
the same comparisons with r=37 or41 hold whenever its prime is at least r.
Every outside coordinate also satisfies the smaller-role bound3^(-j),
as in Report614. These conditional bounds are uniform over the complete
prior history. Preloaded early roots have them conditional on the full
head and the other early roots by TP4.

Eliminate queried outside parents in reverse ACTUAL SAMPLING order,
not necessarily reverse numerical order. Integrate unqueried normalized
rows without a factor. At the preloaded-root stage use TP4's conditional
product. A remaining head query has cap2 from TP5; if no head is queried,
the total initial mass is at most1. Since a three-parent tuple contains
at most one head coordinate, the resulting joint bound is at most2 times
the reference product kernel with

    reference primes (3,37,41),
    coordinate caps (1,37/4,41/4).              (TP10)

Explicitly, if z,z' are nonnegative exponent triples, define

    k(z,z')=product_(r=1..3)
       p_r^(-max(z_r,z'_r))
          *[1 if max(z_r,z'_r)=0, otherwise c_r].       (TP11)

Repeated cylinders on one coordinate intersect at the maximum exponent,
so that coordinate pays its cap once. Incompatible original phases give
zero. This is a joint conditional argument, not assumed independence of
the actual parents.

Let S_N contain the unit and the N smallest nonunit3,37,41-smooth labels,
retaining their complete exponent patterns. Put

    M_3(N)=sum_(z notin S_N,z' notin S_N)k(z,z').

Use those patterns on the actual ordered parents. Expanding the remaining
actual owner-fibre load L_v and summing all positive owner-height pairs gives

    integral L_v^2 dPi<=2M_3(N_v)/(v-1)^2.

The selected-complement bound TP6 and the capped-row inequality
(z-delta)_+<=z^2/(4delta) therefore give

    Pi(E_v)<=2J_3(v),
    J_3(v)=M_3(N_v)/[4delta_v(1-delta_v)D_v^2]. (TP12)

The factor2 is global for the one possible head coordinate, not repeated
for each outside parent or each original. Original numerical labels,
heights and phases are kept before these nonnegative infinite majorants.

## Exact finite triple fees and the entire cubic tail

For a reference coordinate p with cap c define

    T_p=1+c[3/(p-1)+2/(p-1)^2],
    R_p(0)=1+c/(p-1),
    R_p(i)=c*p^(-i)[i+1+1/(p-1)] for i>=1.

The complete kernel sum is product_p T_p. Thus the finite complement
identity is

    M_3(N)=product_p T_p
       -2 sum_(z in S_N)product_p R_p(z_p)
       +sum_(z,z' in S_N)k(z,z').              (TP13)

For every prime43<=v<=967 minimize TP12 over N>=0 satisfying
6(v-3-N)>v-1, with

    D=v-3-N,
    delta=min{1/2,1-(v-1)/(6D)}.                (TP14)

All150 exact rows satisfy the original-Haar cap6. Their exact fee sum is
approximately0.000590101737819991 and is strictly less than3/5000.
The rational sum is the proof input, not the displayed decimal.

For v>=971 choose n>=7 with

    2n^3+3<=v<=2(n+1)^3+1.

Select the cube0<=i,j,k<n excluding the unit, so N=n^3-1, and set
delta=1/2. Then D>=n^3+1 and2(v-1)/D<=4, so the cap6 still holds.
The first cube interval begins at689. Only its part from971 is needed;
bounding the WHOLE n=7 interval below is a permissible overestimate of
the prime tail, not an assertion that971 is the cube-interval boundary.

For each reference coordinate put

    A_p(n)=c*p^(-n)*p(p+1)/(p-1)^2,
    B_p(n)=c*p^(1-n)/(p-1)*[n+1+2/(p-1)].

Here A_p sums the coordinate kernel with BOTH exponents at least n;
B_p sums it with one exponent at least n and the other unrestricted.
If both exponent triples lie outside the cube, choose an exceeding
coordinate in each. They are the same coordinate or two different ones.
Summing this nonnegative union of cases gives

    M_cube(n)<=sum_i A_i(n)T_jT_k
                     +2 sum_(i<j)B_i(n)B_j(n)T_k.      (TP15)

The factor2 accounts for which triple exceeds which of the two coordinates.
No assertion of disjoint cases or independent parent probabilities is used.

After multiplication by3^n, every term in TP15 is nonincreasing for n>=7.
For an A_p term the ratio is3/p<=1. For B_pB_q terms the ratio is at most

    3*(9/8)^2/(pq)=243/(64pq)<1,

since p,q are distinct reference primes and pq>=3*37. At n=7 the exact
scaled sum is

    211923214881494131358891/22212202531721076633600<10.

It follows that M_cube(n)<10*3^(-n) for EVERY n>=7. The entire integer
interval has at most6(n+1)^2 members, hence its contribution to J_3 is at
most60(n+1)^2*3^(-n)/n^6. Therefore

    sum_(v>=971 prime)J_3(v)
      <=[60(8/7)^2/7^4]sum_(n>=7)3^(-n)
       =640/28588707<1/40000.                  (TP16)

This pays all larger primes and all actual owner heights. Combining the
finite and analytic pieces gives

    W_3=sum_(three-parent eligible primes)J_3(v)
       <3/5000+1/40000=1/1600.                 (TP17)

An actual owner has only one tuple type. Paying BOTH complete positive
series W_2 and W_3 is a conservative joint bound and needs no claim that
their separate worst inventories can occur simultaneously.

## A positive common witness and its exact scope

On the single joint law Pi remove head-bad, all root and nonroot mixed
violations, and the ordinary Type I head blockers. By TP2 and TP7--TP17,

    Pi(good)
      >=K-(10/3)S_E-4S_L-2^-16-2(W_2+W_3)
      >K-1/780-4/125000-1/65536
                  -2(1/250000+1/1600)>0.

Every good joint configuration avoids all mixed originals, including
the new four-prime originals, in ONE assignment. Its entry words extend
through their actual ordinary private domains; the disjoint private
witnesses, Type I witnesses and separate ordinary components then glue.
Every numerical original is paid once in that same actual family.

The head marginal still satisfies mu<=C H_P. Projecting good therefore
gives an actual extendible head set with

    H_P(U_ext)>=alpha Pi(good)
      >37925188791845275633871920243
          /6091532434864204079431680000000000
       >1/170000.                              (TP18)

The sharper one- and two-coordinate caps are used only for event payment;
the projection still uses the justified FULL head density C. CRT yields
an integer avoiding the entire family. With Q_off the product of all
outside resolving prime powers, full survivor density is greater than
1/(170000 Q_off). The uniform head fraction is not a full density bound
independent of outside heights.

For any ten ordered odd head primes, apply the same head-only shifted
injections and padded pullbacks as Report614. They preserve full exponent
and support vectors and fixed parent tuples, with an injective correspondence
between original and transformed numerical labels. Outside primes, owner
order and the count of outside parents are unchanged. Empty pullbacks are
padded at their same vectors. Padded-source extensions map to target
extensions with the same outside witnesses; averaging the head injections
transfers TP18. The small reference-head marginal constants are used in
the source theorem, not asserted unchanged for an arbitrary target law.

## A new actual four-prime original

Use roots37 and41 with head parents(3,5), and owner43 with parent triple
(3,37,41). Take the actual squarefree originals

    3*5*37, 3*5*41, 3*37*41*43,

with all phases zero, and include the remaining eight head primes through
pure-prime originals. Ordinary interiors may be empty. This family meets
the new hypotheses. The two first originals force37 and41 to be network
roots: a private ordinary or Type I component cannot supply their two
head interfaces. The last original needs THREE distinct parents at its
largest owner43, so it cannot belong to a fixed two-parent owner inventory
in Report614. Putting a forced root into an ordinary private interior
would also violate that report's disjointness condition. The fixed ten
smallest primes prevent changing the head to absorb37 or41. Thus no
alternative Report614 decomposition admits these same originals.

The remaining restrictions include Report598's missing head labels,
three-parent tuples with TWO head parents and only one outside parent,
more than three declared parents, several parent inventories per owner,
non-increasing parent assignments and extra crossings through ordinary
private interiors. The present three-parent moment does not certify
those omitted cases. In particular the requirement of at least two
outside parents supplies the37 and41 reference directions and is essential
to the budget actually proved here.


## Retained exact certificate

The [producer](../../frontier/cover-geometry/three_parent_forward_kernels.py)
and [data](../../frontier/cover-geometry/three_parent_forward_kernels.json)
check 1449 named conditions. They verify the input producer fingerprints,
the sharper head constants, complete cofactor-tail moments, the 150 finite
owner rows from 43 through 967, the analytic bound for every remaining prime,
and the positive common-law reserve. All inequalities use exact rational
arithmetic. TP4--TP5, the reverse-actual-sampling-order argument and the
ordinary-domain gluing supply the mathematical law and witness obligations;
the finite arithmetic checks do not replace those proofs or constitute
Lean verification.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/three_parent_forward_kernels.py

## A different head source with the same network interface

[Report617](617-all-central-star-phases-admit-root-one-continuation.md)
constructs a stronger gate for a restricted head phase class admitting
all central star and pair phases and the additional9q/25q slots. Its actual
source satisfies the same density and query interfaces, so this report's
network attaches there with extendible reference-head Haar mass greater
than1/2100. The two head classes must not be identified.

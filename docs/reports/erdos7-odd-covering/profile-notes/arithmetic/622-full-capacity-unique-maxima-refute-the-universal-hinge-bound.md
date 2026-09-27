# Full-capacity unique maxima refute the universal hinge bound

There is an actual finite family of distinct odd numerical moduli, with
one globally fixed residue at each modulus, for which the full-unused-capacity
entropy minimizer has

    Phi_4(mu_a)>=4608/323323
        >alpha7*320713/392000,
    alpha7=7235955529/6075000000000.                 (UH1)

Five occupied labels have unique maximizing phases under this SAME law,
and their maximizing cylinders all contain the displayed positive-mass
survivor set. Allowing arbitrary fractional choices among all maximizing
phases does not remove the obstruction.

Nevertheless, this same minimizer has complete all-height query norm

    R_P(mu_a)<650481/110592<6<566/49.                (UH2)

Thus UH1 refutes the universal sufficient hinge target, not the desired
query-norm conclusion or unrestricted Erdős #7. The family is redundant.
An irredundant-only assertion, a criterion restricted to a high-query-norm
regime, or a different criterion accounting for jointly removable originals
is not settled. These are ordinary proofs and exact rational checks, not
new Lean verification.

## 1. The precise selected law and rejected target

Use the actual-family and common-law framework of
[Report530](530-one-supported-law-controls-unused-and-deep-occupied-labels.md)
and the finite free-energy formulation of
[Report609](609-linear-schedule-credit-fails-on-an-actual-irredundant-core.md).
Let P={3,5,7,11,13,17,19}, H be product Haar, M the occupied numerical
labels, L their complete resolving period, U the complete survivor, h=H(U)
and rho=H(.|U). All laws below have Haar digits above L. For nonunit g|L set

    q_g(nu)=max_r nu([r]_g),
    b_g=product_(p:v_p(g)=v_p(L))p/(p-1),
    a_g=b_g-1_(g in M),
    mu_a=argmin_nu [D(nu||rho)+sum_(1<g|L)a_g q_g(nu)]. (UH3)

The minimization is on the finite probability simplex over U mod L.
Relative entropy is strictly convex there, while the penalty is convex;
there is one minimizer. Write Q_d for its entire set of maximizing phases.
The proposed sufficient target was

    Phi_4(mu_a)
      :=min_(eta_d in Delta(Q_d),d in M)
         integral_U (sum_(d in M)eta_d(x mod d)-4)_+ dH
      <=alpha7*320713/392000.                       (UH4)

All sets Q_d refer to the same mu_a, and every eta_d has mass one.
No selected canonical representative of a tie is imposed.

## 2. A finite original inventory with an explicit complete survivor

Take L=(product P)^64=4849845^64 and occupy EVERY nonunit divisor of L.
For the following ordered list of the 23 units modulo45 other than1,

    (r_1,...,r_23)=
    (2,8,14,4,7,13,11,16,17,19,22,23,
     26,28,29,31,32,34,37,38,41,43,44),

assign the exceptional original

    d_i=45*3^i=5*3^(i+2),  a_(d_i)=r_i,  1<=i<=23. (UH5)

Every other occupied divisor has original phase0. These are distinct
numerical labels dividing L, and all phases are fixed once globally.
The family is specified by this finite divisor rule; the proof does not
enumerate its65^7-1 labels or its full resolving period.

Every prime p in P is occupied at phase0. All other phase0 originals
are redundant because their cylinders lie in a prime phase0 cylinder.
Set

    W={x:x not=0 modp for every p in P},
    C_i=[r_i]_(45*3^i),
    U=W minus union_(i=1..23)C_i.                   (UH6)

The exceptional cylinders are pairwise disjoint: their mod45 residues
are distinct. Put

    kappa=product_(p in P minus{3,5})(p-1)/p
         =207360/323323.

The exact masses, with all high digits integrated, are

    H(W)=24*kappa/45,
    H(W intersect C_i)=kappa/(45*3^i),
    h=(kappa/90)(47+3^(-23))
      =(2304/323323)(47+3^(-23))>1/3.              (UH7)

The last inequality follows from3*2304*47=324864>323323.
The set E=W intersect[1]_45 is untouched by every exceptional cut, so

    E subset U,   H(E)=kappa/45=4608/323323.        (UH8)

The five decisive occupied labels are D={3,5,9,15,45}. Every x in E
is1 modulo every g in D.

## 3. Strict phase gaps for the normalized Haar survivor

For any g in D and any unit residue s modg, complete cylinder masses are

    H(U intersect[s]_g)
      =(kappa/45)[24/phi(g)-sum_(i:r_i=s modg)3^(-i)]. (UH9)

Nonunit residues have mass zero. Before the exceptional cuts every unit
residue has the same mass. The ordering in UH5 gives:

| Label g | First cut meeting1 modg | First-hit indices of the other unit residues |
| --- | --- | --- |
| 3 | 4 | 1 |
| 5 | 7 | 1,2,3 |
| 9 | 10 | 1,2,3,4,5 |
| 15 | 8 | 1,2,3,4,5,6,7 |
| 45 | Never | 1,...,23 |

For g<45, if a competing unit phase is first hit at index j, every cut
at the preferred phase1 comes later. Thus its cut loss exceeds that at1 by

    3^(-j)-sum_(i=j+1..23)3^(-i)>(1/2)3^(-j)>3^(-23),

since j<=7. For g=45 the minimum gap is exactly3^(-23). Nonunit
residues have a still larger gap since the preferred cylinder contains E.
After dividing by h, uniformly over all five labels,

    rho([1]_g)-rho([s]_g)>=gamma,  s not=1 modg,
    gamma=H(E)*3^(-23)/h=2/(47*3^23+1)
          >1/(24*3^23).                            (UH10)

This is a gap for the comparison law rho. The next step transfers it
to the exact full-capacity minimizer, rather than changing the selected law.

## 4. Every unused query height is paid before the entropy comparison

Because every nonunit divisor of L is occupied, a_g=b_g-1. For any
nonunit P-smooth numerical query e let g=gcd(e,L). Haar higher digits give

    q_e(nu)=(g/e)q_g(nu),
    sum_(e:gcd(e,L)=g)g/e=b_g.                    (UH11)

The second identity sums a geometric series precisely at coordinates
whose g-exponent equals64. Removing the occupied e=g gives

    sum_(1<g|L)a_g q_g(nu)
      =sum_(e P-smooth,e not dividing L)q_e(nu)
      =R_unused(nu).                              (UH12)

There is no query-height cutoff. The complete unused reciprocal tail is

    E_P=product_(p in P)p/(p-1)=323323/110592<3,
    T=sum_(e P-smooth,e not dividing L)1/e
      =E_P[1-product_(p in P)(1-p^(-65))]
      <3 sum_(p in P)p^(-65)<=21*3^(-65).          (UH13)

Each cylinder of rho has mass at most1/(eh), so
R_unused(rho)<=T/h<63*3^(-65). Minimality in UH3 and nonnegativity
of the unused penalty imply

    D(mu_a||rho)<=D(mu_a||rho)+R_unused(mu_a)
       <=R_unused(rho)<63*3^(-65).                (UH14)

For total variation delta=sup_B|mu_a(B)-rho(B)|, Pinsker's inequality
gives delta^2<=D(mu_a||rho)/2 and hence delta<3^(-30).
In this finite setting the inequality follows directly by applying
the log-sum inequality to a binary partition: binary relative entropy
as a function of its first probability has second derivative
1/[t(1-t)]>=4, giving D>=2delta^2. Endpoint cases follow by continuity.

Since48<3^7,

    2delta<2*3^(-30)<1/(24*3^23)<gamma.             (UH15)

The probabilities of each preferred and competing cylinder change by
at most delta. Therefore UH10 proves, for the ACTUAL minimizer,

    Q_g(mu_a)={1 modg} for every g in D.           (UH16)

The supporting Gibbs normalizer also satisfies its required lower bound.
If F(a) is the minimum objective, its identity is Z_a=h exp(-F(a)).
Here F(a)<1/2 by UH14, exp(1/2)<2 by its positive power series, and
h>1/3. Consequently Z_a>1/6>alpha7. No approximate minimizer or
numerical entropy optimization is used anywhere in the proof.

## 5. A forced joint overlap despite fractional phase selection

For every allowed collection eta_d in UH4, each of the five distributions
at g in D is forced by UH16 to be the point mass at1. On E their sum
is5, and all other summands are nonnegative. Thus pointwise on E

    (sum_(d in M)eta_d(x mod d)-4)_+>=1.

Integrating and then minimizing gives Phi_4(mu_a)>=H(E), proving UH1,
because

    alpha7*320713/392000<alpha7<1/800<1/100<H(E).    (UH17)

Equivalently, z=1_E is an explicit witness in the hinge dual: the five
decisive occupied terms each contribute H(E), every other term is
nonnegative, and the subtraction is4H(E). The direct primal argument
already proves the lower bound and does not require invoking a minimax
identity as a black box.

The hinge counterexample holds for every inventory height K>=64 if64
is replaced by K in L and M. The complete survivor and all gaps remain
unchanged, while T<21*3^(-(K+1)) only decreases. The following query-norm
bound is stated for the explicit K=64 instance.

## 6. The same selected law still has a small full query norm

Let A=E_P-1=212731/110592. For rho, summing all nonunit numerical
query labels gives

    R_P(rho)<=A/h<3A.                             (UH18)

For each g|L, the maximum of the cylinder probabilities changes by
at most delta. The exact gcd representation from UH11 now gives

    R_P(mu_a)<=R_P(rho)+delta*sum_(1<g|L)b_g,
    sum_(1<g|L)b_g=product_(p in P)(64+p/(p-1))-1
                   <66^7<81^7=3^28.              (UH19)

Together with delta<3^(-30), this yields

    R_P(mu_a)<3A+1/9=650481/110592<6,              (UH20)

as claimed. Both the large hinge and the small query norm concern the
same full-capacity mu_a with all heights retained.

Redundant occupation makes the unused penalty small without making U
small. The strict phase gaps then survive the entropy perturbation and
force the five-fold overlap. Removing redundant originals and recomputing
the capacities and minimizer changes the assertion. Such a repair remains
available as a research direction, but is not a choice of eta within UH4.

Unlike the tied nested example in
[Report615](615-nested-actual-incidences-force-unbounded-fixed-law-credit.md),
this obstruction cannot be repaired just by selecting different maximizing
ties for its five decisive labels. It also does not inherit that report's
irredundancy. No conclusion about arbitrary irredundant full-capacity
families follows.

## Exact certificate and source

The [producer](../../frontier/cover-geometry/full_capacity_unique_maximizer_obstruction.py)
and [data](../../frontier/cover-geometry/full_capacity_unique_maximizer_obstruction.json)
check the actual exceptional numerical labels and disjointness, complete
survivor and decisive cylinder masses, strict normalized gaps, the exact
all-height reciprocal tail, entropy-to-variation comparisons, hinge margin
and complete query coefficient sum. The finite divisor rule defines the
remaining originals; no exhaustive enumeration of65^7-1 labels is claimed.
The entropy and universal-height arguments are the ordinary proof above.

The construction was proposed by the authorized Nyx research oracle and
independently reconstructed and checked against the actual-label contract.
No oracle assertion of execution is used as evidence. The proof uses
elementary geometric sums, convexity and Pinsker's inequality; it does not
depend on the oracle's additional literature suggestions.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/full_capacity_unique_maximizer_obstruction.py

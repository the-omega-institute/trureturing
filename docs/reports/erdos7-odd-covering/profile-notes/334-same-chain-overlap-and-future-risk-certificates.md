[Index](../marked_head_profile.md) · [Two-prime mask](327-actual-two-prime-survival-needs-a-masked-moment.md) · [Cell capacities](332-common-mask-capacity-and-the-kakeya-interface.md) · [Full-Haar schedule](333-variable-full-haar-thresholds-retain-more-survivor-mass.md)

# Same-chain overlap and future-risk certificates

Two established methods preserve relations discarded by a sum of physical
bad-charge bounds: a Hunter--Worsley overlap tree and a backward future-risk
supersolution. Both apply to the same actual finite original family and
its prescribed physical/killed kernels. On the twelve-label extension of
327 below, both methods recover the exact surviving mass; this example
claims no strict comparison between the two methods.

For333's full-Haar schedule, the outstanding quantitative target is a
same-family margin-plus-overlap gain strictly greater than
0.0141227935202177856578... . A sharp abstract relaxation below proves that
marginal bounds and a common probability space alone cannot close this
target. No positive mass through47 or unrestricted-prime result is claimed.

## One physical chain and its actual bad events

Resolve every original prime-power height of the given finite family,
including old powers appearing in later-ending moduli. Let nu0 be a
probability supported on the complete old survivors, and let K_i be its
prescribed normalized physical kernels, in increasing prime order. Set

    R_i=K_i 1_(B_i^c), D_i=K_i 1_(B_i), beta_i=D_i(1),
    mu_<i=nu0 K_1...K_(i-1), eta_i=nu0 R_1...R_i.

All kernels retain the old coordinates. On the normalized physical law
of complete histories, let E_i be the actual p_i-ending bad event B_i.
Every original label and its own residue remain unchanged. Then

    b_i=P(E_i)=mu_<i beta_i,
    s_n=P(no E_i)=eta_n(1),
    I_ij=P(E_i intersect E_j)
        =mu_<i D_i K_(i+1)...K_(j-1) beta_j, i<j.     (JC1)

Later normalized kernels integrate out. The middle product in I_ij uses
physical kernels, since other bad events are allowed in the intersection.
It does not use killed kernels or a product of marginal probabilities.
An empty middle product is the identity.

## A tree combines same-family marginal margins and overlaps

For every spanning tree T on the n event indices, the Hunter--Worsley
inequality gives

    s_n>=1-sum_i b_i+sum_({i,j} in T)I_ij.            (JC2)

Indeed, for a history with active set A={i:E_i occurs}, T[A] is a forest.
For nonempty A it has at most |A|-1 edges. Thus the pointwise union
indicator is at most sum_i1_Ei minus the sum of edge intersection
indicators. Its slack is the number of components of T[A] minus1;
for empty A the slack is zero. Integration proves(JC2), which is exact
when the nonempty active set is connected in T almost surely.

Suppose the SAME family's data certify

    b_i<=u_i, 0<=Delta_i<=u_i-b_i, 0<=L_ij<=I_ij.

With W(L) the maximum spanning-tree weight for L, it follows that

    s_n>=1-sum_i u_i+sum_i Delta_i+W(L).              (JC3)

Unknown edges may be assigned zero. A certified forest can be completed
to a tree, so partial pair information is usable. A tree has n-1 edges;
subtracting all pair intersections instead would have the wrong direction
on histories with sufficiently many simultaneous bad events.

The useful obligation is a joint alternative: either the actual charges
have enough margin below u_i, or enough overlap is forced, or the two
gains combine. It is unnecessary to force a positive overlap on every
family. Margins from one family cannot be combined with another family's
intersections or independently attained optimizers.

For333 take nu0 to be its SAME supported AP11/13 probability, with guards
qJ>=1-1/4000 and rho>=1/10. Every later kernel is full-Haar, with

    (p_i)=(17,19,23,29,31,37,41,43,47),
    (t_i)=(6,6,8,12,12,16,18,24,24),
    delta_i=t_i/(p_i-1).

The exact333 certificate gives

    D47=sum_i u_i-1
       =0.0141227935202177856578242639630354777368247... .

Here D47 is the certificate's rational
`overlap_correction47_required_strictly_greater_than`, not the decimal
rounded down. Thus

    sum_i Delta_i+W(L)>D47 implies s47>0.             (JC4)

For example a certified gain at least0.014122794 suffices by exact
rational comparison. Equality at D47 gives only nonnegative mass.
These u_i and D47 belong to333's full-Haar kernels.331's pure-base17/19
schedule has another physical law and cannot supply their intersections;
neither J nor the old KC13 consequence is a replacement for these data.

## Local capacities can provide the pair inputs

For i<j, set

    mu_i=mu_<i K_i, xi_i=mu_<i R_i,
    psi_ij=K_(i+1)...K_(j-1) beta_j.

Then I_ij=(mu_i-xi_i)(psi_ij),0<=xi_i<=mu_i, and0<=psi_ij<=1.
The measure xi_i removes ONLY E_i from the full physical prefix; eta_i
would additionally remove earlier events and is not interchangeable.
On a common finite partition, exact energies E_C=mu_i(1_C psi_ij),
cell masses s_C=xi_i(C), and caps psi_ij<=M_C give332's bound

    I_ij>=sum_C(E_C-M_C s_C)_+.                       (JC5)

Verified lower energies also suffice. An upper energy cannot replace E_C
here. Exact or bounded cellwise hinges give332's sharper dominated-measure
envelope. This specifies a new input obligation; it does not derive
intersections from separate scalar stage readings.

## A backward supersolution retains the future relation instead

A second certificate bounds future failure directly on actual histories.
Supply nonnegative functions r_i after stage i, with r_n=0, such that

    r_(i-1)>=beta_i+R_i r_i, i=1,...,n.              (JC6)

Since R_i is positive, backward induction shows that r_i bounds the
conditional probability of a later failure for histories surviving
through i. Hence

    s_n>=1-nu0(r_0),
    s_n>=eta_j(1)-eta_j(r_j), at any prefix j.        (JC7)

This uses the killed kernel inside the future-risk recursion, unlike the
physical middle kernels in(JC1). They answer different questions.
A rational supersolution is checked through local inequalities; supplying
the unknown exact future failure probability would merely restate the
problem. A Doob transform that assumes a positive exact survival function
also presupposes the desired positivity.

For the23/29/31 case, write mu=sigma K23, xi=sigma R23, m=sigma(1)
and b23=sigma(beta23).
A table u29,u23 satisfying

    beta31<=u29, beta29+R29 u29<=u23

gives s31>=m-b23-xi(u23). On cells C of this same through23 space,
332's envelope H_C^u(s)=inf_(t>=0){t s+mu[1_C(u23-t)_+]} gives

    s31>=m-b23-sum_C H_C^u(xi(C)).                   (JC8)

A sufficient finite state retains, for each remaining original label,
whether all its processed-prime conditions match, together with its
remaining powers and actual residues. Each next coordinate updates its
OWN label tests, and labels ending there determine the forbidden union.
For the fixed full-Haar clipping kernels used here this determines physical and killed
transition masses. Any additional information used by an adaptive
threshold must also be retained. On states a,b with killed transition
mass P_i(a,b),(JC6) reads

    r_(i-1)(a)>=1-sum_b P_i(a,b)+sum_b P_i(a,b)r_i(b).

The transition inputs come from the complete original family. This state
can still be exponentially large; neither a Markov assumption for a
coarser feature nor uniform source-family bounds follow from its existence.
This is the standard finite-horizon dynamic-programming supersolution
principle, with a cemetery state charging one on first death.

## Both certificates are exact on an actual three-prime extension

Keep327's eleven original labels in Family A or B, sigma=delta_0 on old19,
delta23=1/23 and delta29=1/58. Add the original label13*29*31 with CRT
residue (x13,z29,w31)=(0,0,0), and choose delta31=1/62. The twelve moduli
are distinct and odd. The source's zero old coordinates avoid its seven
old pure forbidden residues1. These are general supported19 fixtures,
not asserted effective9 or aligned-J sources.

The31 hazard is beta31=1/61 at z29=0 and zero elsewhere. At a29-active
row, beta29=1/57 and R29 puts zero mass at z29=0. At an inactive row,
beta29=0 and R29 is uniform. Thus the verified two-value future-risk table

    u23=1/57 on29-active rows,
    u23=1/(29*61)=1/1769 on29-inactive rows

satisfies(JC6) with equality for u29=beta31. Partitioning into these two
row types and retaining the actual23 mask makes(JC8) exact. The same
physical chain has the following tree data:

| Quantity | Family A | Family B |
|---|---:|---:|
| b23 |1/22|1/22|
| b29 |1/1254|1/1254|
| b31 |613/1109163|613/1109163|
| I23,29 |1/1254|0|
| I23,31 |1/76494|1/38918|
| I29,31 |1/76494|1/76494|
| A maximum tree |23--29,29--31|23--31,29--31|
| Exact s31 from either method |18564/19459|1057292/1109163|
| Gain over exact s29 minus physical b31 |1/76494|43/1109163|

Every positive-probability active event set is connected in the indicated
tree. This is strict improvement over paying the physical31 charge after
the exact through29 result, and equality between the two methods on these
fixtures. The exact helper checks normalized/killed rows, local risk
inequalities, complete terminal histories, pair intersections and tree
weights with rational arithmetic. It does not search families.

## A sharp limit of the information supplied only by marginal bounds

There is a universal nonzero algebraic correction, but it is insufficient.
For n>=2, suppose U=sum_i u_i=1+D with D>0 and write

    G=sum_i(u_i-b_i)+max_T sum_({i,j} in T)I_ij.

Let N be the number of active events and S=sum_i b_i. The average weight
of the n star trees is (2/n)sum_(i<j)I_ij. Also
sum_(i<j)I_ij=E choose(N,2)>=E[N-1]=S-1. Therefore

    G>=(U-S)+(2/n)(S-1)
      =(2D/n)+(1-2/n)(U-S)>=2D/n.                  (JC9)

This bound is sharp whenever u_i>=2D/n for every i. Construct an abstract
finite probability space with one atom for each singleton i of mass
u_i-2D/n, and one atom for each unordered pair{i,j} of mass
D/binom(n,2). Event E_i contains exactly atoms whose labels contain i.
The total mass is U-2D+D=1; all event marginals equal u_i. Every outcome
belongs to one or two events, so the events cover this probability space.
Every edge has intersection mass D/binom(n,2); every spanning tree has
weight2D/n. Thus G=2D/n and actual survival is zero.

333's nine exact upper charges satisfy the required nonnegativity; the
smallest singleton mass is0.0670021287743762892... . For its exact D47,

    2D47/9=0.003138398560048396812849836436...,
    -D47+2D47/9=-0.010984394960169388844974427527... .

The same construction satisfies every333 prefix survivor floor: for a
prefix of k events its surviving mass is
1-sum_(i<=k)u_i+binom(k,2)D47/binom(9,2). At43 this equals
0.0670021287743762892...; at47 it is zero. Thus the existing positive
finite-prefix floors do not eliminate this marginal relaxation either.

Hence the generic common-space correction improves the negative union
estimate but still gives no positive survival; after the trivial clipping
s>=0 it gains nothing. The45-atom construction is a sharp abstract
relaxation matching these marginal bounds, NOT an actual odd-modulus
cover. It proves that marginal constraints and the common-space axiom
alone cannot force(JC4). Additional original-label, cell or transition
relations must exclude such abstract configurations. This is the missing
same-source margin-plus-overlap obligation, not a request for more scalar
optimization or a claim that every family needs positive overlap.

## Sources and reproducibility

The Hunter--Worsley theorem is given for arbitrary events by József
Bukszár, *Hypermultitrees and sharp Bonferroni inequalities*, Mathematical
Inequalities & Applications6(4),727--743(2003), Theorem5 and Definition4,
p.728. Its m=1 case is the usual tree with pair-intersection edge weights;
p.739 identifies the heaviest-tree bound.
[Full article](https://files.ele-math.com/articles/mia-06-66.pdf),
[DOI10.7153/mia-06-66](https://doi.org/10.7153/mia-06-66).
Original sources are Hunter1976,
[DOI10.2307/3212481](https://doi.org/10.2307/3212481), and Worsley1982,
[DOI10.1093/biomet/69.2.297](https://doi.org/10.1093/biomet/69.2.297).

Backward conditional expectation and state augmentation are explained in
[Bertsekas, MIT6.231 Lecture2, pp.6--7 and9](https://ocw.mit.edu/courses/6-231-dynamic-programming-and-stochastic-control-fall-2015/resources/mit6_231f15_lec2/).
The supersolution proof above is the elementary finite positive-kernel
induction; profile16's killed-chain product is already its Feynman--Kac
identity. These arguments reuse established mathematics and do not add a
Lean declaration or claim general continuation.

The actual fixture helper is
[actual_327_three_prime_risk.py](../frontier/actual_327_three_prime_risk.py).
The source charges and exact47 deficit are in333's
[certificate](../certificates/source_norms/high_rho_full_haar_thresholds.json).

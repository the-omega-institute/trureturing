# Thirteen height-one support primes leave positive survivor density

Every finite family of distinct odd nonunit numerical moduli with at
most thirteen actual support primes and v3(m)<=1 for every original
leaves survivor Haar density greater than1/11000. This is ordinary
mathematics with exact rational verification, not new Lean verification.

The proof extends the shared support response of
[Report707](707-shared-support-avoidance-closes-twelve-height-one-primes.md).
A new probability lemma is needed: low-dimensional positivity by itself
no longer supplies all the strict Shearer conditions.

## A bad seven-coordinate response forces a negative top

In this lemma Q=(5,7,11,13,17,19,23,29,31) is the nonternary coordinate set.
The support comparison weights satisfy

    t_D <= c_D <= 2t_D,   t_D=product_{q in D}t_q,
    1/(q-2) <= t_q <= 1/(q-3),   |D|>=2.              (NB1)

These are bounds on COMPLETED COMPARISON CAPS, not lower bounds on actual
event probabilities. In Report707's source construction, set
t_q=b_q/(1-beta_qr), complete the no3 support budget to b_D, and complete
the two roots' shared3d budget to b_D. The actual group probability is at
most c_D=(1+x_Dr)t_D. Thus NB1 holds without adding an original, changing
any phase, duplicating a numerical label, or claiming that a missing
event has positive probability. No event has singleton support because
the star events were already excluded.

Let Z_A(c) be the same signed sum over disjoint support families. At the
uniform maximum c_D=2 product_D1/(q-3), all466 coordinate residuals of
size<=6 are positive, their minimum being3251/71680. Weight monotonicity
at these dimensions proves their positivity for every cap vector in NB1.
They also satisfy Z_A<=1, by their positive-residual coordinate recurrence.

There are exactly five seven-coordinate subsets whose maximum-cap
response is nonpositive; their complementary pairs are

    {29,31}, {23,31}, {19,31}, {23,29}, {19,29}.

Every other seven-coordinate residual is positive throughout NB1:
its weight derivatives involve only residuals of size<=5.

Fix a seven-set A with Z_A<=0, and write Q=A union{j,k}. Classify a
disjoint support family by the support containing j and the one
containing k. This gives the EXACT identity

    Z_Q=(1-c_{jk})Z_A
        -sum_{empty != D subset A}(c_{Dj}+c_{Dk}+c_{Djk})Z_{A minus D}
        +sum_{D,E nonempty disjoint subsets A}c_{Dj}c_{Ek}Z_{A minus(D union E)}.
                                                                  (NB2)

The last sum is ordered: D is attached to j, E to k. The first term
accounts for neither outside coordinate occurring, or the support{j,k}
occurring. The middle term covers just one outside support; the last
term covers two distinct disjoint outside supports. These cases exhaust
all disjoint families and count each once.

Put

    S1=sum_{D nonempty subset A}t_D Z_{A minus D},
    S2=sum_{D nonempty subset A}(2^|D|-2)t_D Z_{A minus D}.

NB1 and positivity of the proper residuals give

    Z_Q <= (1-c_{jk})Z_A
           +t_j t_k[4S2-(1/t_j+1/t_k+1)S1].          (NB3)

Indeed the positive terms in NB2 have cap4t_jt_k t_Dt_E. For fixed
union U, the number of ordered nonempty bipartitions(D,E) is2^|U|-2.
The negative terms have the cap LOWER bound
(t_j+t_k+t_jt_k)t_D, and their residuals are positive. Since
1/t_j+1/t_k+1>=j+k-5, one may use the uniform estimates

    S1 >= sum_{D nonempty subset A}b_D Z^{max}_{A minus D} = L_A,
    S2 <= sum_{D nonempty subset A}(2^|D|-2)bar_b_D = U_A,
    b_q=1/(q-2), bar_b_q=1/(q-3).                     (NB4)

For all five potentially bad seven-sets, exact arithmetic gives

    (j+k-5)L_A-4U_A >0.

The five margins are approximately26.2833990,23.6196192,22.0293172,
22.5999271,20.9557323. The same finite certificate checks c_{jk}<1.
Thus Z_A<=0 forces Z_Q<0 by NB3.

We can now justify the signed lower bound globally. If Z_Q<=0, actual
avoidance probability is trivially at least Z_Q. If Z_Q>0, NB3 rules out
all nonpositive seven-coordinate residuals. The coordinate recurrence

    Z_Q=Z_{Q minus i}-sum_{D containing i}c_D Z_{Q minus D}

then has positive residuals of size<=7, proving all eight-coordinate
residuals positive as well. All coordinate residuals are now positive;
lowering omitted support weights to zero supplies every event-induced
subgraph, exactly as in Report707. The existing support Shearer theorem
applies and again gives actual avoidance probability>=Z_Q.

Setting omitted weights to zero need not retain NB1's positive lower
caps. This is harmless: NB1 was used to establish positivity for the
completed vector. The subsequent general downward-closure argument
starts from that positive vector and no longer uses any lower cap.

Thus Report707's SIGNED response and its joint-root coefficient bounds
remain valid on these nine coordinates. No clipped-response convexity
or unproved top-only Shearer criterion is used.


## One actual source and the new joint-root response

Take the ten-core3,5,7,11,13,17,19,23,29,31. Use the actual pure-power
survivor product lambda and the actual two-root star masks of Report707.
Retain every numerical label and exponent vector. On each support D,
complete the no3 cap to b_D and the shared3d budget to b_D, exactly as
in Report707, with one assignment variable x_D shared by both roots.
The completed normalized caps satisfy NB1; their lower bounds are cap
bookkeeping, not lower bounds on actual event probabilities.

NB1--NB4 makes the signed root response valid on these nine nonternary
coordinates. The rest of the response is Report707's same construction:

    G(beta)=(g1(empty)+g2(empty))/2
       +(1/2)sum_{k=1}^4(-1)^k sum_U N(|U|,k)b_U E_k(g1(U),g2(U)),

where E_k is min_{0<=j<=k}(2^j g1+2^(k-j)g2) for even k and the maximum
for odd k; N counts partitions into blocks of size>=2. Its separate
concavity in each actual beta pair follows from positive minima of
affine functions and negative maxima of affine functions.

The exact minimum over all19683 vertices of the ACTUAL triangles
beta_q1,beta_q2>=0, beta_q1+beta_q2<=b_q is

    alpha13=213341593/2490621210=.08565798449937717... . (TH1)

Only beta_5=(b5,0), beta_q=(0,bq) for all other q, and its root exchange
minimize. The256 saturated corners independently give the same value.
Thus there is no need to change the actual source or enlarge masks:

    alpha=lambda(U_actual)>=alpha13,
    mu=lambda restricted to U_actual / alpha.

If the original pure3 label is absent, as before choose one extra
avoidance class at that unused label; survivors of this fixed enlarged
family remain survivors of the given family. No arbitrary higher
ternary original is truncated. All original exponents are preserved.

## The scalar query and actual pure-outside continuation

The whole-height-one condition permits the same ternary-truncated
comparison law

    M=(1+B3) product_{q=5,...,31}(1+J_q),
    B3~Bernoulli(1/2), Pr(J_q>=e)=((q-1)/(q-2))q^-e.

At threshold8 the full first moment and small atoms give

    H13=E(M-8)_+
       =3012006036358254380805213652237644965724836482183382598542856635170684840645349
        /6619317806701440471602539645918396385988189732561371318277541508887884652968750.

The probability tails straddle alpha13 strictly, so8 is also the
unique real optimum for this scalar source comparison. Every required
finite query layout on the SAME law mu satisfies

    R(mu)<=7+H13/alpha13=12.312204110723385... .         (TH2)

Now append actual pure-conditioned coordinates37,41,43, using the
existing Report463 PE3--PE5 / Report464 FQ2--FQ4 continuation. Its values are

    Q=43/533, s=4399/55965, A8=1+s-8Q=24244/55965,
    required R < (1+s)/Q-1 =55849/4515
                               =12.369656699889259... .

Thus the same source leaves unnormalized mass

    J=A8 alpha13-Q H13=.00039702577610776157... >0.

The product-source density cap is1048576/262769. Consequently the full
survivor Haar density is at least

    4202235623425795417859037358437686294597081908438735317073468072016957798762479
    /42236457130708537387126397231796318917853663511218696702439298368500745666560000000
    =.00009949308983045616... >1/11000.                 (TH3)

No actual phases were optimized separately and no separately chosen
source laws were joined. All-height nonternary query moments have their
full tails; the first-moment calculation is not a finite-depth cutoff.

## Arbitrary actual primes, including the no3 branch

For actual prime lists containing3, Reports460/462's existing finite
prefix transport fixes3 and injects benchmark prefixes into actual
prime prefixes, pairing the remaining prime coordinates in increasing
order. Pullback of the one actual family preserves complete exponent
vectors and numerical distinctness. Averaging unnormalized survivor
pushforwards preserves the Haar lower bound. Padding unused benchmark
coordinates introduces no extra original. Thus TH3 holds for any actual
set of at most13 support primes containing3.

For a set not containing3, apply the existing empty-core pure-product
instance to the first13 nonternary primes5 through47. Its exact product
cap is96468992/35473815; its mixed-deletion reserve is987063241/2731483755.
The Haar lower bound is

    987063241/7428112384=.13288210920530952... >1/11000.

Larger actual primes only improve this bound. This avoids imposing the
ternary-height condition on some unrelated actual prime.

## Verification scope

The [exact checker](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_support_thirteen.py)
verifies the512 maximal-cap coordinate polynomials, all466 low-dimensional
positives and the complete five-case list with its exact margins. It
then evaluates all19683 actual triangle vertices, the complete scalar
hinge and the same-source continuation. Its [compact result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_support_thirteen.json)
retains the exact coefficients, vertex-list digest, minimizing vertices,
query tails and final density bound. Default replay checks that result;
explicit output mode regenerates it. Only the standard library is used.

Independent checks reconstruct the residuals from signed set-partition
coefficients and the positive remainder from its product formula. A
separate enumerator lists all disjoint support families: by family size
k=0,...,4 their counts are1,502,7071,11368,2205. Evaluating the256
saturated source partitions gives the same minimum as the full triangle
calculation. Independent complete-tail query arithmetic also agrees.
Normal, optimized and different-directory canonical replay agree.

These finite checks support the probability, shared-source and concavity
proofs displayed above; they are not end-to-end Lean verification. The
remaining whole-family ternary-height-one restriction and the bound of
thirteen actual support primes are part of the theorem, and unrestricted
Erdős#7 remains unresolved.

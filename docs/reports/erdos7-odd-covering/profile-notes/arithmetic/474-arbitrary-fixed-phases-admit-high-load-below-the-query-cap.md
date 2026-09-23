# Arbitrary fixed phases admit high load below the complete query cap

There is an actual finite divisor query on the first seven odd primes, with one fixed residue for each distinct numerical divisor and with the unit included, and one compatible probability law over every greater query depth such that

    L(x)>=20 throughout the support,
    R_infinity(mu)<70871/3375<21.                  (AP1)

Here R_infinity sums the maximum cylinder probability over every nonunit modulus supported on those seven primes, at all heights. Thus the complete query budget alone cannot extend [report473](473-a-finite-query-certificate-removes-the-coherent-cofactor-height-bound.md)'s escape from coherent load twenty to arbitrary independently chosen label phases. The failure persists after allowing all deeper queries.

This law has a very sparse support and violates report467's density cap. It is not identified with the source-selected law, and its support is not shown to be the full survivor set of an original family with distinct moduli. The construction does not refute the complete source interface, produce an original nine-prime cover, or settle unrestricted Erdős #7. It isolates a failed implication using the query budget alone.

## Distinct large labels can address many different residues

Take

    P=(3,5,7,11,13,17,19), H=1000,
    M=product_(p in P) p^H,
    T=(H+1)^7=1007021035035021007001,
    C=binomial(51,7)=115775100,
    N=floor((T-C)/19)=53001107107100275363.          (AP2)

There are exactly T numerical divisors of M. If d=product p_i^e_i divides M and d<N, then

    3^(sum_i e_i)<=d<N<3^45,
    sum_i e_i<=44.

The number of nonnegative seven-tuples with coordinate sum at most44 is C. Dropping the coordinate bounds e_i<=H can only increase this count. Therefore at most C divisors are smaller than N, and at least T-C divisors are at least N. The exact inventory leaves

    T-C-19N=4.                                    (AP3)

List all divisors d of M with d>=N in increasing numerical order. Give the first nineteen labels to i=0, the next nineteen to i=1, and continue through i=N-1. Set b_d=i at each label assigned to i. Set b_d=0 at every unused label, including the unit. This specifies a finite complete query

    L(x)=sum_(d|M) 1_(x=b_d mod d).                (AP4)

Every assigned residue is normalized, because 0<=i<N<=d. Each numerical divisor is used only once; no phase depends on the sampled point.

Let E be the union of the M-cylinders represented by 0,1,...,N-1. A point with residue i modulo M hits its nineteen assigned labels and the unit. Hence L>=20 on E. In fact, the assigned labels alone contribute exactly nineteen there: a divisor d>=N cannot identify two different integers in this interval. Unused labels can add further hits. This is not a claim that the complete query is constant twenty.

## One law controls every deeper query

Let mu be normalized Haar restricted to E. On the finite carrier modulo M it gives mass 1/N to each of the indicated residues; all digits beyond H are completed with Haar. These are compatible projections of one probability law.

For any P-supported numerical modulus f, put g=gcd(f,M). A fixed residue modulo g occurs among 0,...,N-1 at most ceil(N/g) times, and this maximum is attained. Splitting each M-cylinder at the additional digits gives exactly

    m_f(mu):=max_b mu(x=b mod f)
           =(g/f) ceil(N/g)/N.                    (AP5)

This formula covers moduli below M, above M, and those finer in only some coordinates. It does not optimize a different law for each query.

Write d_e=product p_i^e_i for 0<=e_i<=H. Group all f by the exponent tuple of gcd(f,M). The fine exponents at a coordinate e_i=H contribute the complete geometric sum 1+1/p_i+1/p_i^2+..., so define

    beta_e=product_(i:e_i=H) p_i/(p_i-1).

The complete all-depth query sum, including the unit, is

    1+R_infinity(mu)
      =sum_(0<=e<=H) beta_e ceil(N/d_e)/N.          (AP6)

All terms are nonnegative and the grouped geometric sums converge. Define

    B=product_(p in P) p/(p-1)=323323/110592,
    W=product_(p in P) (H+1+1/(p-1)).

The two finite product identities are

    sum_e beta_e/d_e=B,
    sum_e beta_e=W.

Using ceil(u)<=u+1 in AP6 yields

    1+R_infinity(mu)<=B+W/N
      =32160131737868864198395243
       /1465374609297108413236224
      <22.                                        (AP7)

The resulting nonunit upper bound is

    R_infinity(mu)
      <=30694757128571755785159019
        /1465374609297108413236224
      <70871/3375<21.                              (AP8)

Thus every finite query period, however deep, also satisfies the source's numerical R bound. The conclusion does not rest on checking only the period used to define L.

## The same construction gives a general boundary

Fix any nonempty finite set of distinct primes P, put r=|P| and B=product p/(p-1), and fix an integer k>=2. There are finite fixed-phase divisor queries and compatible all-depth laws with L>=k on their supports for which

    R_infinity <= B+k-2+o(1) as H tends to infinity. (AP9)

To see this, let T_H=(H+1)^r, let D_H=floor(log_(min P) T_H), and put

    C_H=binomial(D_H+r,r),
    N_H=floor((T_H-C_H)/(k-1)).

For all sufficiently large H, 0<N_H<M_H=product p^H. A divisor below N_H has exponent sum at most D_H, so there are at most C_H such labels. Assign k-1 distinct large labels to each of the first N_H residues, exactly as above. The query then has load at least k throughout this support.

Here C_H=O((log H)^r)=o(T_H), and consequently N_H is asymptotic to T_H/(k-1). Meanwhile

    W_H=product_(p in P) (H+1+1/(p-1))

is asymptotic to T_H. The same exact cylinder calculation gives R_infinity<=B+W_H/N_H-1, proving AP9. In particular, if B<3, then for sufficiently large H one obtains L>=k throughout the support while R_infinity<k+1. The explicit seven-prime construction above crosses the sharper retained source cap at k=20.

The mechanism is the assignment of different large numerical labels to different residues. Independence of label phases allows this assignment. A common old centre would forbid it, which is why the example does not contradict report473.

## What the source conditions still exclude

The density of mu relative to full Haar is M/N on E and zero outside E. In this example

    M/N >=3^1000/N >6075000000000/7235955529.        (AP10)

Thus the upper density condition from [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) fails. We have also not supplied a distinct-modulus original family whose full survivor set is E, or shown that its construction selects mu. Taking an empty old family would give the whole carrier as its survivor set, so it would not supply the missing support condition. Mixing in a positive multiple of full Haar does not preserve support on {L>=20}: the Haar mean of L is at most B<3, so some points outside the heavy region have L<20.

The implication disproved here has only two premises: an actual fixed-phase query is heavy throughout the support, and the same law is tested at all query depths. Whether the additional density, original-survivor and source-construction information forces a positive actual 23/29 joint fibre remains unresolved. No original later phases or new-coordinate fibre are supplied by this counterexample.

## Exact arithmetic and verification boundary

The [standard-library checker](../../frontier/cover-geometry/arbitrary_phase_high_load_obstruction.py) verifies the exact label-count inequalities, rational all-depth upper bound, strict comparison with the source query cap, and failure of the density cap. Its [result data](../../frontier/cover-geometry/arbitrary_phase_high_load_obstruction.json) include the finite indexing rule for the original numerical query labels and phases.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_phase_high_load_obstruction.py
```

Optional `--output PATH` writes JSON. Explicit checks remain active under Python optimization. The checker does not enumerate the enormous carrier or its divisors. The counting argument, construction of the fixed query, compatible Haar extension and exact maximum formula AP5 are the ordinary mathematical proof above; no optimization result, source producer or new Lean certification is used.

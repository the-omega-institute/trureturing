# A finite query certificate removes the coherent cofactor height bound

A finite family of residue classes with pairwise distinct odd numerical moduli greater than one cannot cover the integers under the following conditions:

* Every support prime belongs to {3,5,7,11,13,17,19,23,29}.
* There is one integer a such that every original class c mod m touching 23 or 29, written m=d·23^j·29^k with j+k>0 and d supported on the first seven primes, satisfies c=a mod d.

All original heights are arbitrary finite. Old-only original residues are arbitrary, as are the 23- and 29-coordinate residues of every later class. The actual full survivor set has normalized Haar mass at least

    449287056937/6056623125000000000 >0.             (AH1)

This removes the bound on the old cofactors in [report472](472-deeper-boundary-queries-give-a-coherent-nine-prime-noncoverage-class.md). Its simpler restricted-height proof and stronger Haar bound on that subclass remain valid. The common old reference residue remains a hypothesis here. Neither arbitrary independent old phases of the later classes nor additional support primes are included.

The new ingredient is a finite nonnegative query certificate. It forces one source law to give positive mass to actual old survivors having at most nineteen active coherent old cofactors, regardless of their allowed heights. At each such point the original 23/29 fibre retains at least 1/77 Haar mass. The argument is an ordinary mathematical deduction with a standard-library exact certificate verifier, not Lean certification or a solution of unrestricted Erdős #7.

## Prefix partitions supply valid query resources

Write P=(3,5,7,11,13,17,19), and d_e=product_i p_i^e_i for an exponent tuple e. For a finite positive measure lambda, let

    m_e(lambda)=max_b lambda(x=b mod d_e).

If 0<=t<=e coordinatewise, the cylinder x=a mod d_t splits into d_e/d_t cylinders modulo d_e. Consequently

    m_e(lambda)>=(d_t/d_e)lambda(x=a mod d_t).       (AH2)

There is no product-law or independence premise. Different labels may choose their maximizing residues independently, but all their probabilities refer to this same lambda.

Take coarse exponents 0<=e_i<=19. Define the finite family F_e of fine exponent tuples f by the following coordinate rule:

    f_i=e_i                         if e_i<19,
    f_i in {19,20,21}               if e_i=19.

Different coarse tuples have disjoint fine families, because e_i=min(f_i,19). Partitioning a maximizing e-cylinder into fine descendants gives

    sum_(f in F_e) m_f(lambda) >= beta_e m_e(lambda),
    beta_e=product_(i:e_i=19)(1+1/p_i+1/p_i^2).     (AH3)

Thus beta_e is paid for by distinct actual fine divisor labels. It is not an extra weight assigned to one original label or an assumption that unused digits are uniform.

Suppose nonnegative rational coefficients w_(e,t) satisfy

    0<=t<=e<=19,
    sum_t w_(e,t)<=beta_e                           (AH4)

for each used e. Define a pointwise nonnegative potential

    Phi(v)=sum_(e,t) w_(e,t)(d_t/d_e)1_(t<=v).      (AH5)

For v_i(x)=min(v_(p_i)(x-a),19), AH2--AH4 imply, on any period M resolving the used fine labels,

    lambda(1)+R_M(lambda) >= integral Phi(v(x)) dlambda,
    R_M(lambda)=sum_(1<d|M) max_b lambda(x=b mod d). (AH6)

Indeed, the complete divisor sum contains the disjoint fine families; each family pays beta_e m_e; AH4 allocates no more than that resource to prefix inequalities AH2. Unused labels are nonnegative. This works for restricted, unnormalized measures as well as probabilities.

## The finite certificate covers every high coherent load

The [rational coefficient data](../../frontier/cover-geometry/all_height_coherent_query_weights.json) give an instance of AH4 for which

    product_i(v_i+1)>=20  ==>  Phi(v)>=221/10.       (AH7)

All coefficients are nonnegative, so Phi is coordinatewise nondecreasing. It is enough to check the coordinatewise minimal vectors satisfying product_i(v_i+1)>=20.

These minimal vectors have every coordinate at most nineteen. They also have product at most thirty-eight: if a positive coordinate has v_i+1=2, minimality gives product/2<20 and the even product is at most38; if all positive coordinates have v_i+1>=3, minimality gives product<30. Enumerating positive factor tuples of product at most38 and testing minimality therefore finds every such vector. There are exactly644. Every high-load vector dominates one of them, by repeatedly reducing coordinates while preserving load at least twenty.

The exact certificate has the following finite dimensions:

| Certificate component | Count or bound |
| --- | ---: |
| Nonzero rational weights | 9190 |
| Distinct coarse divisor labels | 8857 |
| Distinct fine divisor labels funding them | 8987 |
| Combined prefix terms in Phi | 1102 |
| Minimal high-load profiles | 644 |
| Largest query exponent at any prime | 21 |

After clearing denominators, the verifier checks each profile using integer arithmetic. The exact minimum is

    518208786071716091117232249582461032144788982430014637
    /23426987120022440188673034618298581948465087890625000
    >221/10.                                      (AH8)

All per-label resource inequalities AH4 and the disjointness of the expanded fine families are checked exactly. The input stores rational coefficients and exponent tuples, not floating-point optimization conclusions. No optimality of the certificate is needed or claimed.

To apply AH7 at arbitrary original heights, only truncate actual valuations at nineteen. If an untruncated coherent divisor load is at least twenty, this truncation remains high: a coordinate lost by truncation alone already contributes a factor twenty. Thus the finite monotone test controls the high-load condition at every greater depth. This is a finite certificate for an unbounded-height implication, not enumeration of all original families.

## Positive source mass must have at most nineteen active cofactors

Let U be the full survivor set of the old-only original family. Choose one finite old-prime period M resolving all old parts of all original moduli and containing p^21 for every p in P. The common source law from [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) has

    supp(mu)=U,
    R_M(mu)<=A=70871/3375,
    mu<=Lambda7 H_M,   Lambda7=6075000000000/7235955529. (AH9)

Including old cofactors from later original classes in M does not add those classes to the old-only family. They only determine how far the same source law must be resolved.

Let B_a={x: product_i(v_i(x)+1)>=20}, and alpha=mu(B_a). Apply AH6 and AH7 to lambda=mu|B_a. The unit cylinder contributes alpha; every nonunit cylinder maximum of mu dominates that of lambda. Hence

    A>=R_M(mu)>=(221/10-1)alpha=(211/10)alpha,
    mu(B_a^c)>=1-A/(211/10)=683/142425=:eps.        (AH10)

For x outside B_a, every truncated valuation is at most eighteen. Since M resolves at least twenty-one digits at every old prime, these are the actual valuations at x, not saturated truncations. Therefore the total number of old-prime moduli d with x=a mod d, including d=1, is

    product_i(v_i(x)+1)<=19.                       (AH11)

In particular, at most nineteen possible old cofactors of later original moduli are active at x, even though those moduli have no height bound. The density cap on the same law gives

    H_M(U intersect B_a^c)>=eps/Lambda7.            (AH12)

All tests, restrictions and densities concern this one finite-period probability. There is no exchange of independently favorable laws or choice of a different reference centre for different original classes.

## Original two-prime fibres have positive common capacity

Fix x in U intersect B_a^c. The shared old reference hypothesis and AH11 bound the active old cofactors by nineteen. For each fixed pair of new exponents and each old cofactor there is at most one original class, since numerical moduli are distinct.

All 23-only classes at x therefore remove Haar mass at most19/(23-1)=19/22, by summing the actual distinct exponent labels and bounding their geometric sum. All 29-only classes remove at most19/28. Pure new-prime powers are included through the unit old cofactor.

The axis-avoiding set is a product, with Haar mass at least(3/22)(9/28). Cross classes with both new exponents positive remove mass at most19/(22·28), including those with unit old cofactor. Thus the actual fibre for these fixed original phases satisfies

    H(fibre survivors at x)
      >=(3/22)(9/28)-19/616
      =(27-19)/616=1/77.                          (AH13)

The argument uses upper bounds on unions, so overlaps between original classes do not need to be controlled separately. Infinite geometric sums bound finite exponent inventories; they do not replace the given finite family.

Integrating AH13 over the Haar set in AH12 proves

    H(full original survivors)
      >=eps/(77 Lambda7)
      =449287056937/6056623125000000000>0,          (AH14)

which supplies an uncovered integer. No later residue is optimized separately on different old fibres.

## Verification and scope

The [standard-library verifier](../../frontier/cover-geometry/all_height_coherent_query_certificate.py) reads the rational coefficient data, checks the resources and profile bound, and computes the source escape and full-fibre constants. Its [result data](../../frontier/cover-geometry/all_height_coherent_query_certificate.json) record the exact outputs. The profile generator uses the product bound and minimality test above rather than a manually supplied list of644 profiles. The analytic source theorem AH9 and the general prefix-partition reasoning remain ordinary mathematical inputs; the verifier does not rerun source geometry or Lean.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_height_coherent_query_certificate.py \
  --certificate docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_height_coherent_query_weights.json
```

Optional `--output PATH` writes JSON. Explicit checks remain enabled under Python optimization. Neither an LP solver nor third-party numerical packages are needed to verify the retained certificate.

Compared with report472, the payoff certificate supplies a uniform finite query interface for all old heights; it sacrifices that report's stronger quantitative bound on its narrower subclass. The remaining condition is compatibility with one common old centre. For arbitrary independent old residues, the number of active later classes need not be a coherent divisor load, so AH11 does not follow. Establishing a positive original joint fibre without that restriction remains unresolved, and unrestricted Erdős #7 remains open.

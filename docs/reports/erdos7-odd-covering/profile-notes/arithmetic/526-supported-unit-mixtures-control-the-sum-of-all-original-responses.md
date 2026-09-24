# Unit survivors have a supported product approximation with aggregate response control

For any finite family of actual unit originals on23,29,31, with distinct numerical moduli, arbitrary phases and arbitrary finite exponents, their joint survivor contains a product restriction of Haar mass greater than0.8133. A second construction retains all but less than10^-15 of that survivor using at most2017 disjoint cross-group products. On one finite nonnegative old measure dominated by(27/2)H_P, the same supported approximation loses less than10^-10 in the weighted sum of all distinct original-label responses, for any weights between0 and616, without a factor equal to the number of labels.

These conclusions concern representation of the unit survivor. They do not prove noncoverage of a complete family, automatically feasible ancestor transports, a positive unit reserve, or a separator for arbitrary old residues. The approximation theorem itself does not impose the finite old-reference templates.

The projection assignment and laminar partition are ordinary finite constructions. The LCM intersection bound reuses the arithmetic principle already used in [report439](439-actual-residual-lifting-and-exact-free-coordinate-cost.md) and related source comparisons; [report452](452-exponent-assignment-controls-arbitrary-two-prime-tail-graphs.md) has a different original-endpoint projection assignment for a tail-lifting problem. The result here combines a supported cross-group mixture with a summed response error independent of test-inventory size. This is an independently derived audit of the external proposal, not an imported theorem, Lean verification, source reconstruction or literature-priority claim.


Qualitative nonemptiness of the unit survivor on any finite set of odd outside primes disjoint from P already follows from [Hough--Nielsen, Theorem1](https://arxiv.org/html/1703.02133v2): every distinct covering has a modulus divisible by2 or3, whereas these unit originals have neither divisor. This uses their published theorem as an input, not a new proof of it. The additional results below are quantitative product support and one simultaneous approximation of the original responses. For the three specified outside primes, the elementary union bound also gives the explicit mass bound displayed below.

## Actual unit input and fixed laws

Let P={3,5,7,11,13,17,19}, Q={23,29,31}, R={23}, S={29,31}. Every unit original has one actual residue modulo

    u=23^j29^k31^ell>1, j,k,ell>=0.

The unit family U is finite and has at most one original for each numerical modulus. All residues are fixed. Write H_Q=H_R times H_S, and define its exact joint survivor

    K=Omega_Q minus union_(u in U) C_u.

All probabilities can be evaluated in any common finite CRT refinement resolving the unit and test exponents. The masks below are cylinder sets fixed solely by U and the chosen cutoff; uniform refinement leaves their laws and component count unchanged. No complete infinite covering family is introduced.

## Retain the low joint boundary and mask the actual tail

Choose an integer H>=0. A unit label is low if j,k,ell<=H. First delete the low pure-R and pure-S originals in their own groups, leaving X,Y. There are at most

    N_H=H((H+1)^2-1)

low mixed originals:1<=j<=H and(k,ell) in{0,...,H}^2 excluding(0,0). Their R projections are23-adic prefix cylinders, hence form a laminar family: two are nested or disjoint.

Partition X by membership in these cylinders. A finite laminar family of N distinct sets has at mostN+1 nonempty membership atoms. To see this, its inclusion forest gives at most one residual atom per set, namely that set minus its maximal proper children, and one outside atom; intersecting with X can only remove atoms. Therefore at most1+N_H atoms A_v are needed.

On an atom A_v every low mixed R-condition is constant. Let I_v be the corresponding fixed set of active low mixed originals and put

    Y_v=Y minus union_(u in I_v) D_u,

where D_u is the actual S projection. The low-unit survivor is exactly

    K_H=disjoint union_v A_v times Y_v.                (M1)

Now handle each actual non-low unit label once. Write h=k+ell. Pure originals are masked in their own group. A mixed original is assigned to R when j>=h+1, and to S when1<=j<=h. Delete the assigned actual projection. Let V_R,V_S be the two common surviving tail masks, and set

    Kstar=K_H intersect(V_R times V_S)
         =disjoint union_v(A_v intersect V_R)
                              times(Y_v intersect V_S). (M2)

Every low original is avoided by(M1); each remaining actual original is avoided by its assigned projection. Thus Kstar is a subset of K. The same tail masks and same component laws are used for every old point and every test label. Projection masking can delete extra points, but never creates a point outside K.

## A uniformly positive single product

Set H=0. There are no low nontrivial labels, so(M2) consists of one product. Pure-R originals have total Haar cost at most1/22. For mixed R-assigned labels, a fixed h>=1 has h+1 pairs(k,ell), and j ranges from h+1 upward. Hence their complete-inventory projection cost is

    sum_(h>=1)(h+1)sum_(j>=h+1)23^-j=45/10648.

Consequently

    H_R(V_R)>=1-1/22-45/10648=10119/10648.

Pure-S originals have total cost at most

    (29/28)(31/30)-1=59/840.

For a fixed nontrivial S modulus29^k31^ell, exactly h=k+ell positive values j<=h are available for mixed S assignments. Their complete cost is bounded by

    sum_(k,ell>=0)(k+ell)29^-k31^-ell=26071/352800.

Therefore

    H_S(V_S)>=1-59/840-26071/352800=301949/352800,
    H_Q(V_R times V_S)>=1018473977/1252204800
                         >8133/10000.                 (M3)

These are union bounds over actual projections, majorized by all allowable exponent labels. They insert no absent original and make no claim that the separate maximum costs are jointly attained. Both lower bounds are positive, for every permitted finite unit inventory.

## Uniform mass loss at a finite cutoff

For a fixed R depth j, the number of labels assigned there is at most

    1+sum_(h=1..j-1)(h+1)=j(j+1)/2.

The first term is the pure label. An R-assigned non-low label necessarily has j>H, because j>k+ell dominates both S exponents. For a fixed S exponent pair with h=k+ell>=1, at mosth+1 labels are assigned to S, including the pure label j=0. An S-assigned non-low label necessarily has h>H: if h<=H then j,k,ell<=H.

The loss K minus Kstar lies in the union of these assigned projections. Using31^-ell<=29^-ell and counting h+1 exponent pairs at total h gives

    H_Q(K minus Kstar)<=E_H,
    E_H=sum_(j>H)j(j+1)/2 *23^-j
          +sum_(h>H)(h+1)^2*29^-h.                     (M4)

At H=12 there are at most1+12(13^2-1)=2017 components and

    E_12=23783384346518607201768945/
         113274501820735534684513538211585699450016
        <10^-15.

Its decimal value is approximately2.099623830979844*10^-16. Numerical distinctness also gives

    H_Q(K)>=1-[ (23/22)(29/28)(31/30)-1 ]
            =16283/18480,

so the retained mixture has positive mass at least16283/18480-E_12. The component bound concerns cross-group products; it does not bound the length of within-S masks or the cost of reading the original inventory.

## Summed original responses without a label-count factor

Fix ONE finite nonnegative old measure nu with nu<=(27/2)H_P. Normalization is not required: every estimate below uses only this domination. In particular, the same argument applies directly to the unnormalized charged source of reports517/523, without changing its mass or choosing a new law. Take any finite family F of pairwise distinct full numerical moduli supported on P union Q, with arbitrary actual old and outside phases. Write each original cylinder uniquely as A_(m,P) times C_(m,Q), with modulus m=d*n, and define the UNNORMALIZED response

    R_m(E)=nu(A_(m,P))*H_Q(C_(m,Q) intersect E).

Let0<=c_m<=616. Since Kstar is a subset of K, every response loss is nonnegative. The required bound is on their one simultaneous weighted sum, not on normalized conditional component accounts.

For a fixed depth-a cylinder at a prime q and a test cylinder of depth b, their intersection is empty or has mass q^-max(a,b), irrespective of phases. Summing these phase-independent upper bounds over test depths gives

    sum_(b>=0)q^-max(a,b)
       =q^-a[a+1+1/(q-1)].                            (M5)

The first a+1 terms have b<=a and the remaining geometric tail is q^-a/(q-1). For old queries,

    nu(A_(m,P))<=27/(2d),
    Z_P=sum_(d>=1,P-smooth)1/d
       =product_(p in P)p/(p-1)=323323/110592.          (M6)

Distinct full numerical moduli correspond to distinct pairs(d,n). Hence an upper sum over all such pairs counts each actual original at most once even when many share their old cofactor or outside cylinder. Combining(M5)--(M6), one deleted R projection of depth j costs at most

    616*(27/2)*Z_P*(899/840)
                   *23^-j(j+1+1/22)

in the summed response. Here899/840=(29/28)(31/30) sums all S test depths. The analogous cost for a deleted S projection of depths k,ell is at most

    616*(27/2)*Z_P*(23/22)
       *29^-k31^-ell(k+1+1/28)(ell+1+1/30).

Apply the finite union bound for the actual tail projections, then their complete-inventory counting bounds from(M4). With

    A_H=sum_(j>H)j(j+1)/2*(j+1+1/22)*23^-j,
    B_H=sum_(h>H)(h+1)^2(h+3)(h+8)/6*29^-h,

the resulting simultaneous estimate is

    0<=sum_(m in F)c_m[R_m(K)-R_m(Kstar)]
       <=616*(27/2)*Z_P[(899/840)A_H+(23/22)B_H].      (M7)

For the S bound, use k+1+1/28<=k+2, ell+1+1/30<=ell+2,31^-ell<=29^-ell and

    sum_(k=0..h)(k+2)(h-k+2)=(h+1)(h+3)(h+8)/6.

The additional factor h+1 in B_H is the maximum number of actual labels assigned to each S projection. No factor|F| occurs in(M7); its replacement is the convergent arithmetic sum(M5)--(M6). The same fixed nu is used for every old phase, and no old-reference template enters this proof.

At H=12 the right side is exactly

    8281287768781970749138378383436567/
    84358610810496863648684991366300913626775552
       <10^-10,                                      (M8)

approximately9.816766408570965*10^-11. This does not assert a comparable error for each old fibre, for the normalization of every product component, or for a separate family of measures chosen for different tests.

## One supported mixture for all queries

Discard empty components and write(M2) as a disjoint union E_v times F_v. Set

    w_v=H_R(E_v)H_S(F_v),
    rho_v=(H_R|E_v) times(H_S|F_v).

Then the exact submeasure identity is

    1_Kstar H_Q=sum_v w_v rho_v.                      (M9)

Dividing by sum_v w_v=H_Q(Kstar)>0 gives a probability mixture. Every original mixed query simultaneously satisfies

    H_Q(C_(m,Q) intersect Kstar)
       =sum_v w_v q_(R,v)(m)q_(S,v)(m).               (M10)

Actual unions are evaluated under the same measure identity. Neither(M9) nor(M10) replaces a union probability by a raw sum of its possibly overlapping original labels. The mixture provides a supported common boundary with controlled unnormalized response loss; further survivor gains and transport capacities must still be proved for the same law and actual old activations.

## Exact evaluation and verification scope

All displayed infinite sums are polynomial-geometric tails. For a polynomial f of degree r, put a=H+1,t=1/q. Its finite-difference expansion gives the exact identity

    sum_(j>H)f(j)q^-j
      =t^a sum_(k=0..r) Delta^k f(a)*t^k/(1-t)^(k+1).

This follows by expanding f(a+n) in the binomial basis and summing sum_(n>=0)binomial(n,k)t^n=t^k/(1-t)^(k+1). It produces the exact rational values in(M4) and(M8), without truncating an infinite tail. A portable consumer also checks the resulting values through the geometric-tail recurrence and verifies a finite actual phase inventory, supported laminar decomposition and its simultaneous query responses by exact CRT inclusion-exclusion.

The finite control does not prove the universal statements; their ordinary derivations above retain every quantifier and original-label assumption. No source construction, geometric row certificate, optimizer or Lean build is rerun. In particular, positive product restrictions and short supported mixtures do not imply automatically feasible raw ancestor inventories.


## Portable finite control

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/supported_unit_mixture.py
```

The [standard-library consumer](../../frontier/cover-geometry/supported_unit_mixture.py) reads [12 actual unit originals and 21 distinct test labels](../../frontier/cover-geometry/supported_unit_mixture_input.json), using one normalized old law on45 points throughout. Exact CRT inclusion-exclusion evaluates the same supported mixture and direct supported-set responses for every query. The low inventory contains both nested and disjoint R cylinders; the high inventory exercises projection assignments to both groups. At cutoff12 the control retains five nonempty components. The tests of moduli5*29^13 and9*23^13 have positive exact response and zero supported response, so both tail-loss directions are exercised.

The [retained result](../../frontier/cover-geometry/supported_unit_mixture.json) also contains the exact infinite-tail constants, calculated independently through closed geometric moments and finite differences. Default execution compares this result; `--output` writes it and `--input-dir` selects the input directory. The program never enumerates the full outside period and does not reconstruct the old source used by the covering-system separator. Its literal45-point source is a finite control for the declared domination assumption, not a substitute for that separate source construction.

The raw-account obstruction in [report525](525-phase-balanced-originals-defeat-all-outside-laws-and-groupings.md) applies to every outside probability law and every two-group assignment for its explicit family. A supported product mixture therefore provides a common representation and quantitative error control; it does not make every component's original-label transport feasible. The remaining estimate must use actual old activation or another justified source-sensitive account.

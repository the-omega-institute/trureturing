# Independent ternary centre choices need no shallow-anchor hypothesis

Let P={3,5,7,11,13,17,19}. Consider a finite original family of classes c mod m
with pairwise distinct odd numerical moduli m>1 supported on P union{23,29}.
For every later modulus write m=d23^j29^k with d P-supported and j+k>0.
Suppose there are two fixed integer centres a,b such that:

* at every p in P other than3, a,b agree through the greatest p-exponent
  appearing in any later old cofactor d;
* for every full original later numerical label m, its old residue is either
  a mod d or b mod d. This choice is fixed independently for each m.

There is no restriction on the ternary positions of a,b. Old-only original
classes have arbitrary residues and arbitrary finite heights, with no
required shallow anchors and no missing-pure-power assumption. All original
23/29 residues and finite exponents are arbitrary. Then the full original
survivor set has normalized Haar mass greater than1/80000000000.

The same noncoverage conclusion permits any finite set of further support
primes greater than10000000000000. The two-centre hypothesis is imposed only
on the head-only subfamily. Tail-touching classes have arbitrary fixed
residues, finite heights and joint support; the continuation retains
distorted mass greater than1/125000000000, not a Haar bound of that size.

In particular this family does not cover the integers. The result removes
[report482](482-a-fixed-anchor-allows-independent-opposite-root-choices.md)'s
eight-original-anchor premise. It retains the two-centre and common
nonternary-prefix conditions, and does not resolve unrestricted Erdős #7.
These are ordinary mathematical deductions with exact rational checks,
not a new Lean certification or a claim of literature priority.

## One actual completed source and its eight coarse types

Apply the attributed old-only completion and source construction of
[reports466](466-randomized-completion-retains-full-original-survivor-support.md)--
[467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md).
Its source is Michael Schroeder's *Nine Prime Divisors in Odd Distinct
Covering Systems*, edition1.0.1; source identity and arbitrary-height
verification limits remain in the [library entry](../../../../../Library/Arith/schroeder2026nine.md).

The original family stays fixed. Completion may add a missing selected label
or move a redundant selected class, but retains an already legal selected
class. The completed old covered union contains the original old covered
union. Every later original class and its fixed centre choice remains
unchanged. Consequently an uncovered point for the completed family is
uncovered for the original family, with the same direction for Haar mass.
This does not assert equality of these two survivor sets.

Use one actual completed source supplied by those reports, with its existing
complete pure-prime exclusions. Its live old measure nu satisfies

    nu <= (27/2)H,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).

Every cap is conditional on the full earlier history of this very process.
The retained32 source vertices split into eight coarse types of four. On
seven types, excluding(2,4,1), the same-process live mass is at least

    m_other=5891133457/225000000000.

On the remaining type it is at least

    m7=7235955529/450000000000.

The four-vertex comparison for each type extends to its continuous budget
by the inherited reserve/loss concavity, as in report478. These source and
interpolation results are ordinary inputs, not consequences of matching a
few numerical constants in a file.

For the seven nonworst types keep this same source and its mass lower bound.
Only on the upper-comparison side retain the first H3>=12 and H5>=8 disjoint
pure exclusions, and release the deeper exclusions. Their released mass is
paid explicitly below. This does not construct a different finite source
or assert that a finite truncation inherits the completed source's lower
bound. The original family remains finite; its auxiliary completed source
may have countably many pure exclusions.

The next argument handles every pair of centres differing at only one old
coordinate q, including arbitrary first-digit disagreement. Its use here is
q=3; it also identifies the remaining q=5 boundary.

## The physical union inventory

Fix q in P and assume the two centres agree at all required old precisions
outside q. Extend those finite prefixes to one common reference path at
every p!=q, once for the whole family. At an old point x let

    Vq=max(vq(xq-aq),vq(xq-bq)),
    L=(Vq+1) product_(p in P,p!=q) (vp(xp-ap)+1).

Outside the null reference paths, L counts the union of old numerical cofactors matching one of the two centres: the union of two initial q-exponent intervals is their longer interval, and all other coordinate intervals agree. The unit is included. This counting uses one fixed selector for each complete later label, never a selector chosen after seeing x.

For L<=19, at every new exponent pair there are at most19 active old cofactors. Hence the23-only and29-only axis complements have masses at least1-19/22 and1-19/28. Their conjunction is a product because they concern different new coordinates. All cross classes together have Haar mass at most19/(22*28), retaining the unit cofactor. Every such original fibre therefore has survivor mass at least

    (1-19/22)(1-19/28)-19/616 = 1/77.

It suffices to upper-bound nu(BAD), BAD={L>=20}.

## Pure exclusion by tail domination, without changing any phase

Let n_p=2 at p=q and n_p=1 elsewhere. Use Vp for the maximum of both reference valuations at q and for the single common reference valuation elsewhere. The union bound gives, for every j>=1,

    Hp(Vp>=j) <= min(1,n_p/p^j).

Distinct first digits at the exceptional coordinate achieve equality at every positive tail. Any deeper separation has smaller tails. No position of the centres relative to the actual deleted pure roots is assumed.

If an actual retained p-coordinate set has mass alpha_p, its restricted valuation tail is at most

    min(alpha_p,n_p/p^j).

For the ideal complete pure masses alpha3=1/2 and alpha5=3/4, these tails define positive dominating measures. Their atom values are:

| Coordinate | Centre paths | mass at V=0 | mass at V=1 | mass at V=j>=2 |
| --- | --- | --- | --- | --- |
| 3 | single | 1/6 | 2/9 | 2/3^(j+1) |
| 3 | double | 0 | 5/18 | 4/3^(j+1) |
| 5 | single | 11/20 | 4/25 | 4/5^(j+1) |
| 5 | double | 7/20 | 8/25 | 8/5^(j+1) |

Their total masses are1/2 at3 and3/4 at5. They dominate the restricted integral of every nonnegative increasing function. To prove this, write an increasing step function as its baseline plus nonnegative increments times tail indicators; bounded increasing functions follow by truncation. This uses actual set masses and union-tail bounds; it does not relocate any original deleted cylinder.

Pure3 and pure5 deletions concern separate coordinates, so their actual survivors form a product before mixed deletions. Any mixed deletion is dropped only on the upper BAD side. The ideal comparison product has mass3/8.

In the chosen complete source, let D_(p,e) be the selected class modulo p^e.
The completion rule makes classes at comparable selected moduli disjoint;
thus D_(p,e) are pairwise disjoint. This property concerns the completed
selection, not arbitrary original pure classes. The first Hp such exclusions
have mass

    sum_(e=1,...,Hp) p^(-e) = (1-p^(-Hp))/(p-1).

Put epsilon3=1/(2*3^H3), epsilon5=1/(4*5^H5). The enlarged coordinate sets that retain only these prefixes have masses1/2+epsilon3 and3/4+epsilon5. A positive dominating measure is obtained by adding epsilon3 at V3=1 when q=3, and at V3=0 otherwise; add epsilon5 at V5=0 for every q. For q=3, its j=1 tail becomes1/2+epsilon3 and all j>=2 tails remain2/3^j. All other positive tails stay unchanged. The prescribed finite heights keep these measures positive with total mass at most1.

Retain the same normalized full-history kernels when enlarging the initial
measure; they can be defined on deleted histories as in the inherited source
construction, or extended there by Haar under the same caps. Positivity makes
the enlarged process an upper comparison after its later deletion indicators
are released. No lower source-mass bound is transferred to this comparison.

For every payoff in[0,1], this finite-prefix upper comparison exceeds the ideal one by at most

    (3/4)epsilon3+(1/2)epsilon5+epsilon3*epsilon5
      <=epsilon3+epsilon5.

Every released pure tail is therefore explicitly paid. The lower mass and
full-history caps still belong to the original completed source nu; only
its upper BAD comparison has been enlarged.

## Later normalized conditional kernels and exact convolution

At p in{7,11,13,17,19}, the actual normalized kernel at every full earlier history has density at most Cp. For its one or two reference valuations,

    Pr(Vp>=j | full earlier history) <= Cp*n_p/p^j, j>=1.

Hence the positive probability with mass1-Cp*n_p/p at Vp=0 and mass Cp*n_p*(p-1)/p^(j+1) at Vp=j>=1 dominates every increasing payoff. Each baseline is nonnegative. Reverse integration through the one actual source is legitimate because the terminal BAD indicator is increasing in every factor Vp+1 and positive averaging preserves this property. Later actual deletions are released only on the upper side. This does not assert that the actual source coordinates are independent; independence belongs only to the auxiliary comparison product.

The standalone checker convolves the factors Vp+1 with exact rational arithmetic. Product20 is absorbing, and all omitted larger valuations retain their full tail mass in that state. The seven ideal comparison BAD bounds are:

| Exceptional q | BAD upper, decimal for orientation |
| --- | ---: |
| 3 | 0.02009691092038631... |
| 5 | 0.019159965911146114... |
| 7 | 0.017915114061185847... |
| 11 | 0.016373553330669467... |
| 13 | 0.015458947410406789... |
| 17 | 0.015440496495082506... |
| 19 | 0.014835340861489243... |

The checker computes all seven independently from their tail laws, with no imported numeric bound from report478. The maximum occurs at q=3 and is

    B = 3327584991507538462402462818879857311152571720958903957279651
        /165576938898208242787587584507966922934711827488892566071875000
      = 0.02009691092038631... .

With H3>=12 and H5>=8,

    epsilon3+epsilon5 <= 1312691/830376562500,
    B+epsilon3+epsilon5 < 201/10000.

The checker validates this strict inequality without decimals. It also checks all32 retained source vertices, every local comparison mass and tail, and exact mass conservation of the absorbing convolution.

## Seven types give an original single-fibre margin

Every one of the seven nonworst coarse source types therefore has

    nu(L<=19) > m_other-201/10000
      =1368633457/225000000000 >3/500.

Dividing by the joint density cap and integrating the original fibre floor gives

    H(full original survivors)
      >1368633457/233887500000000 >1/171000.

This estimate handles every legal45/75 placement and every reference
position on these seven types. The additional premise is the availability
of this particular nonworst source; the construction does not claim that
every original family has such a completion.

## The worst type reduces to arbitrary legal45/75 positions

For type(2,4,1), use the simultaneous normalization established in
[report477](477-two-arbitrary-centers-share-a-positive-original-fibre.md).
The actual completed source avoids the six classes

    0 mod3,1 mod9,4 mod27,0 mod5,1 mod25,2 mod15.       (AT1)

Transport the whole completed family, both centres, and the source together.
Rooted prime-prefix permutations send every congruence cylinder to a cylinder
of the same numerical modulus, preserve Haar measure, and preserve all
full-history caps. At any required finite period they are finite bijections;
CRT supplies ordinary integer representatives. No global preservation of
ordinary integers by an infinite path map is needed.

The selected45 and75 classes exist after legal source completion. Their
phases r,s need not be31,16. Proper-divisor legality says exactly

    F45={r mod45:r%3!=0,r%9!=1,r%5!=0,r%15!=2},
    F75={s mod75:s%3!=0,s%5!=0,s%25!=1,s%15!=2}.       (AT2)

There are17 and33 phases respectively, hence561 possible pairs. Existing
legal original phases cannot be reset to a preferred pair. The comparison
below covers all of AT2 directly.

Let A(r,s) be the complement modulo675 of the six classes AT1 and these
actual45/75 classes. The actual completed initial3--5 anchor is contained
in A(r,s). Drop other initial exclusions and later deletion indicators only
on the upper-bound side, retaining the same normalized capped kernels and
extending them by Haar on new histories. This gives an upper comparison for
nu. No higher pure3/5 exclusion is credited in this step, so its original
phase and depth are unrestricted and no infinite completion limit is needed.

## A single extended support certificate for all shallow positions

First assume a and b occupy the two surviving ternary roots, oriented as
root2 and root1. Their reference prefixes modulo27 have9 choices each;
the common5 prefix modulo25 has25 choices. All561*9*9*25=1136025 literal
anchor/reference combinations are enumerated. No orbit representative list
is a premise of the final checker.

Use the profile definitions, normalized-row maximization and exact tail
partition from report482. A profile has matching ternary factor u and six
nonternary factors f. For profiles in opposite roots,

    Qx=u*product(f), Qy=v*product(g),
    N=Qx+Qy-min(u-1,v-1)*product_i min(f_i,g_i).

The fixed-label inequality of [report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md)
gives s(x)+s(y)>=K(Qx,Qy,N)/616 for the actual original later-fibre masses.
All later centre choices remain fixed for each full numerical modulus.

The support certificate is the report482 tree with two terminal cases
further divided by complete bipartite groups of certified edges. Each split
retains both exhaustive alternatives: omit the left group or omit the right
group. Every edge used has K>=4/3. Thus T={s<1/924} avoids all those edges;
T also has no profile of load<=19, whose individual fibre floor is1/77.
The upper comparison treats higher ternary factors and every load overflow
as freely surviving, with their full exact tails.

The extended certificate has3505 nodes and1753 terminal support cases.
The literal anchor/reference enumeration gives912 exact initial weight
vectors, and every terminal case is checked against every vector. Its
largest upper bound is the same U as in report482,

    U=13530362084729802525722239237409731006113773442855176051085643442
      /841453987724678813030011126035327051417778569660355684928876953125,
    U<16079741/1000000000<m7.                         (AT3)

It follows for the same actual source that nu(T)<=U. The source density cap
and actual original fibre then give

    H(full original survivors)>=(m7-U)/12474
                              >1/80000000000.        (AT4)

The reference prefixes exhaust every position relevant to the shallow
anchor. Deeper reference digits only determine valuation shells within a
prefix cell; their exact Haar masses do not depend on those digits. The
profile enumeration covers every retained possibility, and all omitted
higher values remain in explicitly paid tails.

## Remaining ternary roots and the original-family conclusion

If a=b mod3, the seven nonworst types are already covered above. For the
worst type, use only report478's six-anchor same-root comparison (IC8),
which bounds nu(BAD) by a number strictly less than19/1200. It releases
all additional initial exclusions and requires no infinite pure-tail
subtraction. The original fibre floor1/77 and density cap give

    H(full original survivors)>(m7-19/1200)*2/(27*77)
      =110955529/467775000000000 >1/15592500.

Otherwise inspect the selected pure3 root of the completed source. If one
centre, say a, lies there, augment the original finite family only by that
selected class modulo3, if it is absent. If the original modulus3 is
present, its class was retained by completion and no addition is needed.
Every later class choosing a with3|d is now redundant; remove those classes.
For3 not dividing d both centres have the same old residue, and every
remaining later class with3|d uses b. This augmented family is finite and
still has pairwise distinct numerical moduli. Report473's coherent theorem
applies and gives Haar mass at least449287056937/6056623125000000000.
Removing the redundant later classes preserves the augmented covered union,
so its survivors remain contained in the original survivor set. This proves
the required original lower bound without treating the full auxiliary
completion as a finite original family.

The remaining case has the two centres in the two surviving ternary roots.
The seven nonworst types are handled by the single-fibre argument, and the
worst type by AT1--AT4. Every possible source type and ternary-root position
has therefore been accounted for. Positive Haar mass is a union of nonempty
cells on the original finite CRT period and supplies an uncovered integer.

The common nonternary-prefix and two-centre hypotheses remain essential to
this statement. For single-coordinate disagreement at5, the argument above
closes the seven nonworst source types; the worst type with distinct first
quinary digits still requires a separate estimate. Simultaneous arbitrary
coordinate disagreements and arbitrary original old residues are not
settled by this theorem.

## Arbitrary large-prime continuation

For the head subfamily, switch to Haar restricted to its full original
survivor set, of mass greater than1/80000000000 and density at most1. Resolve
every head digit queried by tail classes, without adding their projections
as head exclusions. Apply the correlated-head continuation of
[Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md),
with its inherited analytic prime-product premise, using

    M2=product_(p in P union{23,29}) p(p+1)/(p-1)^2
      =14003665/540672,
    B=10000000000000, ell=27, c=(2ell^2+1)/(2ell^2-1),
    tau7=(c^7/B)(B/(B-3))^2 sum_(j=0,...,7) 7!/((7-j)!ell^j).

The required B>=286, ell>=4 and3^ell<=B hold. Exact arithmetic gives

    M2 tau7=0.00000000000347619953081120...,
    1/80000000000-M2 tau7>1/125000000000.

Assign every tail-touching original class once to its last exposed outside
prime, retaining its complete numerical label and fixed residue. The positive
remaining distorted mass proves noncoverage for any finite number of those
additional primes. It is not asserted to be the Haar mass of the enlarged
original survivor set. No restriction on centre choices is imposed on these
tail-touching classes.

## Exact verification and inherited boundaries

The [nonworst-source checker](../../frontier/cover-geometry/single_coordinate_nonworst_source.py)
reproduces its [exact rational data](../../frontier/cover-geometry/single_coordinate_nonworst_source.json).
The [all-position checker](../../frontier/cover-geometry/all_ternary_two_fibre.py)
replays the report482 support tree together with the
[two-leaf extension](../../frontier/cover-geometry/all_ternary_two_fibre_patch.json),
and reproduces the [all-position result](../../frontier/cover-geometry/all_ternary_two_fibre.json).
Both use only the Python standard library. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/single_coordinate_nonworst_source.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_ternary_two_fibre.py
```

Default execution checks the retained result without writing it; `--output
PATH` writes the reconstructed exact result. The source comparison inputs
remain pinned to:

* query_stoploss_completion.json:44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d;
* common_law_mass_tail.json:3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4.

The finite checks establish the displayed arithmetic, source-vertex minima,
remaining-root constants, tail constants, complete shallow enumeration and
support-tree inequalities. The attributed
source construction and its arbitrary-height validity, the normalized
conditional-kernel bridge, the existing fixed-label pair theorem and the
analytic large-prime continuation remain
ordinary mathematical proof inputs. They are not proved merely by checking
their input numbers. No source producer or Lean build is rerun for this
increment, and no unrestricted Erdős #7 conclusion is claimed.

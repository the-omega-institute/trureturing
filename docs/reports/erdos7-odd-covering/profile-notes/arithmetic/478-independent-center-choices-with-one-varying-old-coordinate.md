# Independent center choices with one varying old coordinate

Let P={3,5,7,11,13,17,19}. Consider a finite family of original residue classes c mod m with pairwise distinct odd numerical moduli m>1, supported on P union {23,29}. Every later modulus has the form d·23^j·29^k, where d is P-supported and j+k>0.

Suppose there are two fixed integers a,b and one q in P such that:

* every later original class satisfies either c=a mod d or c=b mod d, with the choice made independently for each full numerical modulus;
* at every p in P other than q, a and b agree through the largest p-exponent occurring in these later old cofactors d;
* if q=3 or q=5, also a=b mod q. No first-digit agreement is required when q is 7,11,13,17 or19.

Old-only original residues, all finite exponents, and every23/29-coordinate residue are arbitrary. The actual full survivor set U satisfies

    H(U)>4493647/66825000000000>1/15592500.       (IC1)

In particular this family cannot cover the integers. This removes category-wide center assignment: different classes with the same old cofactor, including23-only,29-only and cross classes, may independently use either center. It does not require one choice per old cofactor.

One may additionally allow any finite set of support primes greater than1000000000. Only the head-only subfamily must satisfy the displayed center conditions. All tail-touching original classes may have arbitrary residues, exponents and joint prime support. The retained tail construction leaves distorted mass greater than1/50000000; this last quantity is not a Haar-density bound for the enlarged family.

This is a different extension from [report477](477-two-arbitrary-centers-share-a-positive-original-fibre.md): that result permits arbitrary disagreement in all old coordinates but assigns centers by category. Here choices are independent across all original labels, while disagreement is confined to one old coordinate. Neither theorem contains the other. The proofs below use the attributed source construction and exact rational checks, not a new Lean certification. Unrestricted Erdős #7 remains unresolved.

## Fixed original choices are controlled by a union of divisor inventories

Choose two P-adic reference paths extending the required finite prefixes of a,b. At p other than q choose a common continuation; no assertion that the two distinct integers have identical infinite p-adic expansions is needed. At q choose any continuations respecting the required prefixes and, for q=3,5, their common first digit. If all relevant q-prefixes coincide, the paths can be chosen identical there too.

Put

    V_q(x)=max(v_q(x_q-a_q),v_q(x_q-b_q)),
    L_q(x)=(V_q(x)+1) product_(p in P,p!=q)(v_p(x_p-a_p)+1). (IC2)

Away from the null reference paths, L_q is exactly the number of distinct P-supported numerical cofactors that match at least one center, including the unit. At the exceptional coordinate the two sets of matching exponents are initial intervals, whose union has length V_q+1; every other coordinate has the same matching interval for both centers. This establishes IC2 without counting a cofactor twice when both centers match it.

For every fixed pair (j,k), each numerical d·23^j·29^k occurs at most once. Regardless of that label's fixed center choice, its active old cofactor belongs to this union. Consequently, whenever L_q<=19, the fixed original23-only and29-only unions have Haar masses at most19/22 and19/28. Their simultaneous complement is a product. Cross classes have total Haar mass at most19/616, including d=1. Therefore

    H23,29(original fibre survivors at x)
      >=(1-19/22)(1-19/28)-19/616=1/77.           (IC3)

The infinite geometric sums only bound the given finite inventories. No original residue or center choice depends on x. It remains to find positive actual old-survivor mass on GOOD={L_q<=19}.

## One actual source process and a scalar positive comparison

Use the same completed old-only source process nu as in reports467 and477. It has

    nu(1)>=m7=7235955529/450000000000,
    nu<=(27/2)H,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).    (IC4)

The conditional kernel caps hold at every complete earlier history. The stronger source lower bounds remain attached to the eight coarse types (alpha,beta,gamma). The worst type is(2,4,1); every other type has lower mass at least5891133457/225000000000. Each type's continuous pure5 budget is controlled by its own four retained vertices: reserve is affine, loss bounds are convex, and the resulting mass lower bound is concave. No independently favorable source is selected for different references or queries.

For two paths on a p-coordinate with separation h, the Haar distribution of their maximum valuation V has atoms

    j<h: (p-1)/p^(j+1),
    j=h: (p-2)/p^(h+1),
    j>h: 2(p-1)/p^(j+1).                         (IC5)

For coincident paths only the ordinary geometric law remains. At all coordinates except q there is only one path. For a kernel of density at most C and any increasing payoff f, subtract f(0) before applying the density cap. The resulting positive comparison law multiplies all nonzero valuation atoms by C and puts the remaining mass at valuation zero. Positivity follows from2C/p<1 at all five later coordinates; with one path the weaker C/p<1 suffices.

Apply this comparison by reverse integration through the one actual source process, dropping later deletion indicators only on the upper-bound side. Independent variables occur solely in the auxiliary comparison. Track products below20 exactly, placing all larger products in an absorbing BAD state. If h>=19, all differences from coincident paths occur at V>=19 and are already BAD. Thus h=0,...,18 and one coincident option cover every separation depth exactly. At q=3,5 omit h=0 as required by the statement.

## The full pure anchor covers seven of the eight coarse source types

The completed pure3 union has Haar mass1/2 and the pure5 union mass1/4. For the allowed reference configurations their joint baselines have masses2/3 and4/5 respectively. Removing the corresponding pure mass from each baseline gives positive upper comparison measures of masses1/2 and3/4. Other anchor exclusions may be dropped because the payoff is nonnegative. This retains monotonicity at every integration step.

Exact finite convolution gives the following maxima. Decimal values are displayed only for orientation; the verifier compares full rational numbers.

| Exceptional coordinate q | Allowed separations | Full-pure BAD upper maximum |
| --- | --- | ---: |
| 3 | h>=1 | 0.017691015529075028... |
| 5 | h>=1 | 0.013926553056101200... |
| 7 | h>=0 | 0.017915114061185847... |
| 11 | h>=0 | 0.016373553330669467... |
| 13 | h>=0 | 0.015458947410406789... |
| 17 | h>=0 | 0.015440496495082506... |
| 19 | h>=0 | 0.014835340861489243... |

Every entry is below9/500. Therefore all seven nonworst coarse types retain more than1/15000 good mass. The full-pure bound also handles q=5,13,17,19 in the worst type. The remaining coordinates3,7,11 require the actual mixed anchor.

## The worst source type and its mandatory deep pure exclusions

Normalize the actual(2,4,1) source exactly as in report477, transporting the whole family and both reference paths together. In particular the selected25 class is sent to1 mod25 by a permutation of second-digit children. Equality of reference prefixes, their shared first digit when required, and all original numerical exponent labels are preserved. The anchor avoids

    0 mod3, 1 mod9, 4 mod27,
    0 mod5, 1 mod25, 2 mod15.                    (IC6)

Let R1,R2,V5,W5 be as in report477. The complement of these six classes is the positive disjoint union

    A0=(R1 times V5) union (R2 times W5),         (IC7)

with coordinate masses5/27,1/3,19/25,14/25. Integrate the finite later-coordinate BAD payoff against the exact root distributions in IC7. For q=3, enumerate the two ternary reference prefixes and all deeper separation types consistent with a common first digit. For q=11, both anchor coordinates have one common reference and the split occurs in the later11-kernel. The exact upper maxima are respectively

    q=3:  0.015830413129456140... <19/1200,
    q=11: 0.014709522869687727... <1601/100000.    (IC8)

For q=7, the six classes alone give0.016093927048863477..., which exceeds m7. An actual exclusion omitted from A0 repairs this estimate. The completed pure3 classes at depths e>=4 are pairwise disjoint, avoid the selected3,9,27 classes, and have total Haar mass

    sum_(e>=4)3^(-e)=1/54.                       (IC9)

Write their union as D3, so D3 is contained in R1 union R2. For each fixed pair of common anchor references let f(t) be the increasing BAD payoff after integrating7,11,13,17,19, including the chosen7 separation. Define

    c1=min_(x3 in R1) integral_V5 f((v3(x3)+1)(v5(x5)+1)) dH5,
    c2=min_(x3 in R2) integral_W5 f((v3(x3)+1)(v5(x5)+1)) dH5.

Monotonicity allows each minimum to be evaluated at the least valuation actually possible in its specified ternary region. Every x3 in D3 belongs to one such region. Since the actual anchor excludes D3 at every quinary coordinate, the integral over the same enlarged anchor obeys

    nu(BAD)<=integral_A0 f((v3+1)(v5+1)) dH3dH5
                 -(1/54)min(c1,c2).              (IC10)

This is subtraction of a lower bound on a real excluded part of that very integral. It does not subtract a credit from an unrelated upper bound, and it does not require D3 to be independent of its root or reference valuation. The15 restriction is retained in V5 versus W5. Other pure5 tails and45/75 exclusions are not needed for this bound.

The exact maximum of IC10 over all common3/5 reference positions and all7 separation depths is

    0.016009057187721578... <1601/100000.          (IC11)

It occurs with common ternary prefix2 mod27, common quinary prefix3 mod25, and distinct7 roots. All prefix cells containing a reference have their exact geometric tails; omitted valuations already give L_q>=20. No numerical tail cutoff is used.

All seven allowed q-cases in the worst coarse source therefore have BAD mass below1601/100000. Together with the other seven source types,

    nu(GOOD)>m7-1601/100000
      =31455529/450000000000>1/15000.             (IC12)

## Return to original integers and attach the large-prime tail

The actual process nu avoids every original old-only class. Divide IC12 by its density cap27/2, and integrate the original fibre floor1/77 from IC3. This proves IC1. A positive mass set for the original finite CRT period contains an uncovered integer.

For further primes explicitly switch to Haar restricted to the full original head survivor set. Its density is at most1 and its mass exceeds1/15592500. Resolve all head digits queried by later original classes without inserting their projections as head exclusions. The [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) continuation applies, with

    M2=product_(p in P union {23,29}) p(p+1)/(p-1)^2=14003665/540672,
    B=1000000000, ell=18, c=(2ell^2+1)/(2ell^2-1),
    tau7=(c^7/B)(B/(B-3))^2 sum_(j=0,...,7) 7!/((7-j)!ell^j).

The inherited analytic prime-product bound requires B>=286, ell>=4 and3^ell<=B, all satisfied here. Exact arithmetic gives

    M2 tau7=0.00000004139354973843466...,
    1/15592500-M2 tau7>1/50000000.                (IC13)

Each original tail-touching class keeps its numerical label, fixed residue and complete earlier cofactor, and is assigned once to its last exposed outside prime. This gives the stated positive distorted mass without restricting the tail's center choices or joint support.

## Verification boundary and remaining cases

The [standalone verifier](../../frontier/cover-geometry/independent_center_single_coordinate.py) and [result data](../../frontier/cover-geometry/independent_center_single_coordinate.json) check the scalar positive laws, exact product convolutions, finite anchor distributions, arithmetic of the pure-tail bound, every coarse-source margin, original Haar conversion and tail constants. Source mass and conditional-kernel theorems, continuous-budget interpolation, joint normalization, the actual pure-tail inclusion and the analytic large-prime estimate are ordinary proof inputs. The retained source producers and Lean are not rerun.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/independent_center_single_coordinate.py
```

Optional `--input-dir DIR` relocates the two retained, hash-pinned source inputs; `--output PATH` writes exact rational result data. The program uses only the Python standard library, and all checks remain active under optimization. The finite calculations include all20 separation representatives at7 and11, all19 allowed representatives at3 and5, and exact joint anchor signatures. Every omitted valuation is already in the absorbing BAD event; these checks do not enumerate or certify arbitrary original families by themselves.

The remaining phase restrictions are explicit: the two old references may differ in only one old prime coordinate, and their first digit must agree when that coordinate is3 or5. Neither simultaneous disagreements in several old coordinates nor arbitrary independently chosen old residues have been settled. In particular, the failing six-cylinder estimate before IC10 was an insufficient comparison, not an original covering counterexample.

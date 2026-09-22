[Index](../../marked_head_profile.md) · [Endpoint source](../001-064/59-endpoint-linear-source-deletion-bound.md) · [Original pair caps](../001-064/62-endpoint-square-from-cylinder-intersections.md) · [Common pure3 head](../001-064/64-one-zero-seven-layout-and-complete-pure-three-tails.md)

# Complete positive-five tails strengthen the endpoint square to114/25

For the actual endpoint class of profiles59 and64, every complete
independently labelled original357 test A satisfies

    limsup integral_survivor A^2<=114/25=4.56.             (P1)

The hypotheses are convergence to source404, actual survivor mass
S=D=3/20, and carrier(root0,cell1). Original residues may vary with
the finite family. The signed square barrier45 has margin at least
219/100, improving profile64's margin by13/100.

This is an ordinary endpoint theorem. It does not update global K,
prove a survival denominator, extend the neighborhood of68, or claim
Lean verification. Every exponent tail below is complete.

## 1. Descendant-five cylinders retain their first-slot geometry

Use the five source slots P,A,Beta,Q,H and five ternary cells of59.
Let J_b be an arbitrary five-coordinate cylinder of depth b>=2, with
first slot s. The surviving measure mu obeys

    mu(cell_l times J_b)<=v_l,s*5^-b,                    (P2)

where the rows of V are

| Cell | P | A | Beta | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 2/45 | 2/45 | 2/45 | 1/30 |
| 1 | 0 | 1/15 | 1/15 | 1/15 | 2/45 |
| 2 | 0 | 0 | 0 | 1/9 | 1/15 |
| 3 | 0 | 0 | 1/18 | 1/9 | 1/15 |
| 4 | 0 | 0 | 1/9 | 1/9 | 1/15 |

To prove the table, discard all deeper source deletions in Q and
retain the forced full-slot exclusions P, root1 times A, and cell2
times Beta. The available raw ternary mass on each remaining slot
is at most eta_l. On cell3 times Beta retain additionally the entire
late source family with b=1. As proved in59, every such label lies
there, attains its raw mass3^-a/5, and these additional deletions
are disjoint. Their ternary union therefore has eta mass

    sum_(a>=3)3^-a=1/18.

Each of these source labels removes the whole Beta first slot over
its ternary cylinder. Hence their deletion on every descendant J_b
is exactly(1/18)*5^-b, leaving at most(1/9-1/18)*5^-b.
This uses only the b=1 late family. The total late mass x in59
can also include b>=2 labels and is not asserted uniform inside Beta.

Finally apply the four distinct complete forbidden-cofactor families
3,9,5,15. They multiply each remaining raw entry by

    1-(1_root0+1_(l=1)+1_(s=H)+1_(root1 and s=H))/5.

Their sum is a valid lower measure for deletion because delta=V at
the endpoint. No disjointness of their projected supports is assumed.
This proves(P2) for every independently chosen descendant residue.

## 2. Keep the same six-label load in two complete new tails

At zero seven depth, use profile64's load

    X=B+T,
    B=load of{1,3,9,5,15,45},
    T=sum_(a>=3)1_(I_a), modulus(I_a)=3^a.

The fixed shallow layout B is constant on each cell-slot rectangle.
Define

    q5(B)=max_s sum_l v_l,s*B_l,s,
    q15(B)=max_(r,s) sum_(ROOT(l)=r) v_l,s*B_l,s.

Equation(P2) gives, separately for every test residue,

    integral B*1_(J_5^b) dmu<=q5(B)*5^-b,
    integral B*1_(J_3*5^b) dmu<=q15(B)*5^-b.           (P3)

Now set F=sum_(b>=2)1_(J_5^b) and G=sum_(b>=2)1_(J_3*5^b).
The labels within these sums need not be nested. Nevertheless,

    F^2<=sum_(b>=2)(2b-3)*1_(J_5^b),
    G^2<=sum_(b>=2)(2b-3)*1_(J_3*5^b).               (P4)

At maximum depth b there is one diagonal term and two terms for
each of the b-2 earlier labels; each intersection is bounded by
the deeper indicator. The inherited individual surviving caps are
(4/9)*5^-b for F and(1/3)*5^-b for G. Each intersection with a
pure3 label of depth a>=3 has mass at most3^-a*5^-b. Thus

    integral(2*X*F+F^2) dmu<=q5(B)/10+7/180,
    integral(2*X*G+G^2) dmu<=q15(B)/10+11/360.         (P5)

These are sums over all b>=2, using exactly

    sum 5^-b=1/20,
    sum(2b-3)*5^-b=3/40,
    sum_(a>=3)3^-a=1/18.

For comparison, the old separate-pair budgets for the same two
groups are respectively13/60 and67/360. For F the six shallow
caps sum to16/9 before multiplication by5^-b; for G they sum to14/9.
Consequently those budgets are

    2*(16/9)/20+2*(1/18)/20+(4/9)*(3/40)=13/60,
    2*(14/9)/20+2*(1/18)/20+(1/3)*(3/40)=67/360.       (P6)

The pair groups in(P5) are disjoint. The cross terms2*F*G, all
pairs with other positive-five labels, and all positive-seven
occurrences of F or G retain their old caps. No group is credited
twice and no test residues are identified.

## 3. One layout controls the zero and cross-seven terms

Profile64 supplies, for each of12500 shallow layouts B,

    integral_mu(X^2-1)<=Z(B),
    integral_Lambda X^2<=R(B),
    Rstar=max_B R(B)=212153/87480.

Its complete pure3 tails and raw positive-seven comparisons remain
unchanged. Subtract(P6) from the previously unreplaced pair sum.
The remaining complete bound is E=109/90. For the whole square,
including every seven depth, we therefore obtain

    integral A^2<=E+7/180+11/360+(4/15)*Rstar
       +max_B[Z(B)+(q5(B)+q15(B))/10
                         +(2/5)*sqrt(R(B)*Rstar)].      (P7)

The factors2/5 and4/15 are the complete seven-depth ordered-pair
sums from64. In particular B is the same zero-depth layout in
all three terms inside the maximum. Positive-depth tests retain
their own independently chosen layouts and residues.

Put

    K=114/25-E-7/180-11/360-(4/15)*Rstar
     =138187/52488.

For every layout the exact checker verifies

    g(B)=K-Z(B)-(q5(B)+q15(B))/10>=0,
    [(5/2)*g(B)]^2-R(B)*Rstar>=0.                     (P8)

The minimum second slack is495114037/9685512225>0. Since g(B)
is nonnegative, squaring in(P8) is equivalent to the required
square-root bound. Substitution into(P7) proves(P1), entirely
with rational comparisons.

For comparison, maximizing the zero and raw contributions separately
would give4565473/984150=4.6390011685..., a weaker bound.
The finite zero-depth calculation also gives

    max_B[Z(B)+(q5(B)+q15(B))/10]=6856267/3936600.

Both this maximum and the tightest comparison(P8) use the layout
(root3,cell9,slot5,root15,slot15,cell45,slot45)
=(1,4,Beta,1,Beta,4,Beta). The independent residues at every deeper
label remain arbitrary throughout the bound.

## 4. Complete tails, varying families, and reproduction

The original pair-cap polynomial-geometric tails of62 dominate every
term used here. The pure3 affine tails are those of64; the new pure5
tails are summed in(P5), with no depth cutoff. The same labelwise
compactness and uniform-tail argument of59--65 passes the endpoint
inequality to limsup along arbitrary changing finite source/test
families. Nothing requires stabilization of an entire infinite test
at a finite stage.

The [checker](../../frontier/endpoint-bounds/endpoint_square_positive5.py) reconstructs
all12500 inherited primal/dual equalities and both complete pure3
tails for every layout, checks(P2)--(P6), then verifies(P8). Its
[certificate](../../certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json)
records the exact table, budgets and rational comparison slack.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/endpoint_square_positive5.py --check
```

This calculation enumerates all shallow layouts in an analytically
bounded expression. It does not enumerate covering systems or
substitute a finite experiment for unrestricted quantifiers.

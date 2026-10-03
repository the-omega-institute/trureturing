# Three kernels cover all source vertices but miss a strict interior point

Three fixed retained-kernel tables have a positive inherited h16 continuation gate at every one of the320 categorical product vertices: each vertex admits at least one of the three tables. The same three tables all have a strictly negative gate at one explicit point in the interior of the continuous probability domain.

This gives a finite exact counterexample to using a union of successful vertex tests as a continuous source-domain atlas. No subdivision of the domain can repair this particular three-table collection: the displayed point fails for each table itself. It does not prove that the pointwise optimized LP fails, that a fourth table cannot work, or that a sharper source/query comparison fails.

The third table also supplies a positive algebraic continuation certificate at the previously missing endpoint. These are ordinary mathematical conclusions with exact rational verification, not Lean results or a resolution of unrestricted Erdős#7.

## 1. The common source problem

Use the actual selected phases, ternary leaves(4,7,2,5,8), and nonternary primes

    Q=(5,7,11,13,17,19,23)

from [Report808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md). In particular the selected originals include10 mod15 and11 mod45. The complete literal family is stored once in the accompanying certificate. No original is rephased by table or query.

The categorical partitions are{0},{1},{2,3,4} at5 and{0},nonzero at each otherq. Writea=pi5(0), b=pi5(1). The local5 domain is

    P5={(a,b): 0<=a,b<=4/15, a+b>=1/5}.

The probability of the third colour is1-a-b. The five vertices, in the indexing used by the data, are

    v0=(0,1/5,4/5), v1=(0,4/15,11/15),
    v2=(1/5,0,4/5), v3=(4/15,0,11/15),
    v4=(4/15,4/15,7/15).

Their cyclic polygon order isv0,v1,v4,v3,v2. Each other local probability has

    0<=piq(0)<=Cq/q, Cq=(q-1)/(q-2).

The full domain isP=P5 times these six intervals. It has5 times2^6=320 product vertices. The six-bit endpoint mask usesbit0 forq7 throughbit5 forq23.

Each table consists of one normalized weight vectorw and one retained tableu with0<=u_l(s)<=w_l. All750 pointwise zeros required by the23 selected actual cylinders are imposed on the same192-pattern table. The full numerical residual inventory and every higher ternary power are included in the head lower boundL(pi,u), as in [Report810](810-categorical-retained-kernels-give-a-finite-common-source-interface.md).

This report retains the comparison used in [Report813](813-arbitrary-retained-kernels-give-a-uniform-head-and-an-all-threshold-query-obstruction.md): normalize the full source restricted to the complete old survivor,

    mu=lambda_w restricted to U / lambda_w(U),

and use its full-source hinge and fourth-moment comparisons. For each fixed table define

    r=max(w4+w7,w2+w5+w8), v=max_l w_l,
    G(pi)=12L(pi,u)-H16(r,v)-27Kq(1+15r+216v)T1600.

The complete [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md) tail is

    T1600=4301685063112470380207/10^30.

Kq includes the actual pure29 factor. The verifier reconstructs the complete hinge and the179-prime bridge to the analytic tail above3000. The mass and every common-colour query envelope are evaluated at the samepi.

## 2. Three literal rational tables

The first table is the fractional all-upper-point certificate from [Report812](812-fractional-categorical-kernels-admit-explicit-finite-pure-families.md). Its weights are

    (236809,236809,226024,150179,150179)/10^6.

It has134 nonzero entries:106 equal their full leaf weight and28 are fractional.

The second table uses the quarter law

    (1/4,1/4,1/6,1/6,1/6),

and retains every K8-allowed cell at its full weight. It has210 nonzero entries, all Boolean relative to their leaf weight.

The third table has weights

    (23289806,23289806,17736838,17339709,18343841)/10^8.

It has90 nonzero entries:26 full-weight and64 fractional. All three complete tables are retained as rational data; omitted entries are zero. The verifier independently checks the normalization, bounds and all actual selected-cylinder zeros.

At the point(v3,mask63), wherepi5=(4/15,0,11/15) and all other zero-colour probabilities areCq/q, the third table has

    L=1381659295439858066767/32339882303244140625000
     =0.04272307742138129...,

    G=0.15009670708743675... >3/20,

    G/(27L)=0.1301202449604568... >13/100.

These inequalities are checked as exact rational comparisons. The endpoint belongs to the enclosing cap polytope; this report does not assert that a finite actual pure family realizes its probability vector exactly. The certificate is a positive algebraic point certificate, with the same complete inventory and full tail as the other tables.

## 3. The endpoint union is complete

Exact enumeration gives the following number of positive gates among the64 binary endpoints above each local5 vertex:

| local5 vertex | first table | quarter table | third table |
| --- | ---: | ---: | ---: |
| v0 | 32 | 64 | 0 |
| v1 | 33 | 64 | 0 |
| v2 | 30 | 64 | 62 |
| v3 | 19 | 63 | 64 |
| v4 | 62 | 42 | 0 |
| total | 176 | 297 | 126 |

The first two tables together miss exactly(v3,mask63). The third table repairs it. Thus the union of successful endpoint tests is exactly all320 vertices.

One nontrivial continuous region can already be certified without mixing table choices: the quarter table works on

    conv(v0,v1,v2) times the full six-interval box.

Its minimum gate on that region's product vertices is0.20995128655910117...>1/5. The fixed-table block-concavity argument therefore extends positivity throughout that region. This is a valid partial source-domain certificate; it does not cover the whole polygon.

## 4. A strict interior point defeats all three tables

Take

    pi5=(1/4,1/8,5/8),
    piq(0)=(99/100)Cq/q forq=7,11,13,17,19,23.

Every categorical probability is positive and strictly below its local cap. In particulara,b<4/15 and1/5<a+b<8/15. The point is therefore in the relative interior of every local simplex and in the interior ofP.

At this same point the exact gate values are:

| table | gate, decimal display | verified strict upper bound |
| --- | ---: | ---: |
| first table | -0.08896765431433334... | -2/25 |
| quarter table | -0.14319446143518144... | -7/50 |
| third table | -0.29360237687300006... | -29/100 |

The complete rational values are generated by the verifier. These are evaluations of the three specified certificates, not upper bounds on the best possible certificate at this point. No claim of pointwise LP infeasibility follows.

The point is a valid point of the cap relaxation. Its realizability by a finite actual pure family is not needed to disprove coverage of that relaxation, and is not asserted here.

## 5. The correct continuous atlas rule

Let a source-domain cell have the product form

    D=product_q D_q,

where eachD_q is a convex polytope contained in the corresponding local probability simplex. Select one fixed tableu,w for that entire cell. The gateG is concave in each whole local probability block: its positive source mass is affine, and each common-colour envelope is a maximum of affine functions with a nonnegative loss coefficient.

Consequently, ifG>0 at every product vertex ofD, thenG>0 throughoutD. The same table and weight vector must be used for all vertices in that certificate.

A finite collection of such cells gives a source-adaptive atlas only after proving

    P=union_j D_j.

Different cells may use different fixed tables. Once the actualpi is in a certified cell, its table supplies one coherent source and all queries use that source. A correct geometry proof can, for example, use a split tree that intersects one local polytope with two complementary closed halfspaces. All newly created local vertices must be checked.

The statement established by the endpoint table is weaker:

    for every vertexv ofP, there exists a tablej withG_j(v)>0.

It does not imply the cellwise condition with one table on all cell vertices, nor positivity at nonvertex points. Takingmax_j G_j does not preserve the concavity needed to extend a vertex test.

The strict interior counterexample proves more than failure of a proposed triangulation. Any claimed atlas using only these three tables and this gate would have to assign the displayed point to one cell and hence to one successful table. All three gates there are negative. Therefore no amount of subdivision using only these three tables can coverP under the stated certificate rule.

This says nothing about a new table, a smaller source-specific probability domain, a different observation system, or the retained-source moment comparison that changes the normalization and the gate itself.

## 6. Reproduction

The [standalone verifier](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample.py) uses only the Python standard library. Its [certificate](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample_certificate.json) contains the shared actual source data and all three rational tables. The [result](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample.json) stores the exact positive-point certificate, endpoint counts and minima, and strict interior failures.

```sh
python3 -I -S -B three_kernel_atlas_counterexample.py
```

Normal execution recomputes and checks the saved result without rewriting it. Regeneration requires `--write-result`; alternate inputs use `--certificate` and `--result`. Floating values are displays of previously computed exact fractions. No solver output is needed to verify either the positive point or the interior counterexample.

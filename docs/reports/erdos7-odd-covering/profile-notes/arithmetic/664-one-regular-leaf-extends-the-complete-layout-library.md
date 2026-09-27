# One regular leaf extends the complete layout library

Exactly one of the ten originals9qs, q<s in Q={7,11,13,17,19}, may have its central role in any one of the three regular leaves0,1,2. Its numerical edge is arbitrary. The other nine roles independently lie inleaf4 orleaf5. The same four rational field families from [Report663](663-a-finite-field-library-covers-every-binary-leaf-layout.md) suffice for all

    10×3×2^9=15360

such assignments. The complete declared three-parent ordinary/private networks have full survivor density strictly greater than

    1/(490000 Q_off).

Together with663's1024 binary assignments, this certifies16384 distinct live-leaf assignments using the same library and the common lower density bound1/(490000 Q_off). It does not cover assignments containing two or more regular-leaf edges, nor all5^10 assignments.

The fixed first/square pure phases and nulls, central15 phase0, three square7 central roles, fifty retained root incidences, literal head primes and ordinary/private interfaces remain those of661--663. In particular all225q incidences remain; all twenty square pairs and ten9qs may still have arbitrary globally fixed outside phases. Arbitrary finite higher central pure phases retain the same actual-source scope. No numerical prime or edge weight is permuted.

This is ordinary mathematics and exact rational computation, not new Lean verification or a solution of unrestricted Erdős #7.

## 1. A complete branch, with every numerical edge retained

Use the root-major central leaves

    x3(l)=l//3+3(l mod3) modulo9,
    x5(m)=m//5+5(m mod5) modulo25.

The regular leavesl=0,1,2 are literal residues0,3,6mod9. Leaves4,5 are residues4,7mod9; leaf3 is the fixed null residue1mod9. First pure phases are2mod3 and4mod5, the quinary null leaf is5, and the central15 mask is l<3,m<5.

First fix the exceptional regular role toleaf0. Choose its actual edgee0 from the ten lexicographically ordered edges. ChooseA⊆E\{e0} to record the edges with roleleaf4; putB=E\(A∪{e0}) for those with roleleaf5. These three disjoint sets partition the original edge labels. There are10×512=5120 canonical assignments. A nine-bit mask indexesA in the lexicographic list with e0 removed; a set bit meansleaf4.

The shared unary masses remain

    r_q=1/(q-1), a_q=1/[q(q-2)],
    Z7(c)=5/6-[1_(l//3=1)+1_(m//5=2)+1_(l=5)]/35,
    Zq=(q-2)/(q-1)-2a_q, q>7.

With b_e=a_q r_s+r_q a_s andd_e=r_q r_s for e={q,s}, the actual edge-union bound is

    beta_e(c)=b_e+d_e[1_(e=e0)1_(l=0)
                          +1_(e in A)1_(l=4)
                          +1_(e in B)1_(l=5)].           (R1)

The square7 depth-two role staysleaf5. Edgee0 may carry any one of the ten distinct numerical pairs, with its own prime-dependent b_e,d_e. The calculation treats all ten cases separately rather than transporting one edge's weights to another.

Every beta_e<=b_e+d_e. The same full strict-Shearer bound754111121894423/876550251053789 therefore gives one actual conditional matching source for every admitted layout. Its exact empty response and simultaneous full-height query envelopes are the matching polynomials H_T(c) from663, evaluated withR1. This ensures a common actual source; positive complete charged gates are established separately below.

## 2. Eight exact response profiles

Write H_T(n,S) for663's local-subset polynomial usingZ7=5/6−n/35 and beta_e=b_e+d_e1_(e in S). LetS0={e0}. The eight response profiles now are

    leaf0, column other than2:       H_T(0,S0);
    leaf0, column2:                  H_T(1,S0);
    leaves1,2, column other than2:   H_T(0,empty);
    leaves1,2, column2:              H_T(1,empty);
    leaf4, column other than2:       H_T(1,A);
    leaf4, column2:                  H_T(2,A);
    leaf5, column other than2:       H_T(2,B);
    leaf5, column2:                  H_T(3,B).            (R2)

The pure-null and central15 cells contribute zero. All profiles are computed from actual disjoint setsS0,A,B. No row takes an independently optimized phase assignment.

The same exact degree-two expansion on the ten edge variables computes everyH_T(n,S), with the fifteen disjoint-edge interactions. Its full table has four unary profiles,1024 subsets and32 supports. The complete512 coefficients, guarded9q² additions, height tails and unit/mass contribution are unchanged.

## 3. The comparison symmetry shrinks

For a fixed canonical assignment, only the transposition of regular leaves1 and2 remains a ternary symmetry. Leaf0 is active and must stay fixed; using the oldS3 to treat it as equivalent to an inactive leaf within the same layout would be wrong. The quinary group still independently permutes live leaves inside each column, with the null fixed.

This smaller group preserves eachH_T, both nulls, the common mask and all complete selector menus. It fixes every outside numerical prime, edge and support. There are now FOUR ternary weak-marker orbits, represented by0,1,4,5, and four quinary ones. Hence the complete95 corners have16 representatives

    (i,j) in{0,1,4,5}×{0,6,10,15}.                      (R3)

The supplied four field families already have the stronger invariance used by663, so they are invariant under this subgroup. Their180-entry representations remain valid. No claim is made that180 parameters describe every field invariant only under the smaller group, and no additional symmetry restriction is imposed on an optimized problem here: the task is to verify these four existing fields.

Each whole-weight, root/column, leaf and deep selector is transported with its weak markers. The deep constants1 and4/5 and all512 coefficients are preserved. Thus the16 exact corner gates determine the gates at all95 corners. Actual original root tables and conditional submeasures need not be symmetric; only the common numerical response and selector interface is used in this reduction.

## 4. Select one whole field family per layout

The witness reuses663's four exact rational tables without changing any entry. Family0 has denominator180; families1--3 have denominator2^20. Every item consists of95 fields and satisfies both645 priority inequalities on all live cells. The new total selection function has an entry for every pair(e0,A):

    s(e0,A) in{0,1,2,3}.

For each of the5120 canonical assignments, the same selected item is used for mass, all corner comparisons and every query. The statement checked is

    for every(e0,A), min_(i,j) G_(e0,A,i,j)
                               (theta_(s(e0,A))^ij)>=gamma1. (R4)

No maximization over field indices is performed inside a corner or selector. Field selection may depend on the whole globally fixed original layout; it does not alter any original phase.

The exact certificate aggregates each literal field-weighted selector to the eight response profiles inR2. Every such aggregation is an equality. It removes duplicates and vectors dominated entrywise by another vector in the same menu, explicitly checking that every original vector is represented or dominated. Positivity of all eightH_T profiles makes this reduction valid for each menu's maximum. All remaining selectors are maximized, so selector switching is preserved.

It checks all

    5120×16×512=41943040

complete screen maxima with exact integers and fractions. The exact minimum is

    gamma1=1851931013276210341843005889
              /931162766019912935308800000000
           =0.001988837054977998... >197/100000.           (R5)

It occurs with exceptional edge{17,19}, every other role atleaf5, selected family0 and weak pair(4,6).

## 5. From canonical leaf0 to all three regular leaves

For an actual family whose exceptional edge has regular roleleaf1 orleaf2, choose a rooted ternary-coordinate bijection that sends that leaf toleaf0. Explicitly, on the first root0 write x=3t+9u witht in{0,1,2} and send it to3sigma(t)+9u; leave the other first roots unchanged. This permutes the three mod9 children and carries their deeper subtrees with them. Explicitly, inside root0 write x=3t+9u with t in{0,1,2} and send it to3sigma(t)+9u; leave other roots fixed. It fixes first roots, leaves3,4,5 and the quinary coordinate.

Apply this ONE relabelling simultaneously to every original central component, reference leaf, root table, source and query. It preserves every congruence-cylinder height, Haar measure and numerical modulus. It preserves the fixed first/square pure deletions, central15 root mask and all three specified square7 roles. The other admitted central phases, including arbitrary higher pure phases, remain in their declared class. Since linear-star andqs incidences are transported with their original components and root table, those required relations also remain true.

The resulting family lies in a certified canonical assignment. Build its actual source and field usingR4, then transport that construction back through the same coordinate bijection. All actual original labels and phases belong to the one original family again. This is not a permutation of outside primes or their costs, nor an assumption that the arithmetic operations on residues commute with an arbitrary relabelling. It is a bijective transport of the declared congruence-cylinder avoidance problem.

The three choices of the regular role therefore yield3×5120=15360 assignments. Transporting only the new9qs role while leaving the other original reference data unmoved would not justify this conclusion.

## 6. Actual higher-pure sources and complete continuation

Fix any one admitted original family, its canonicalized layout(e0,A) and the chosen indexs(e0,A). Construct the actual pure3/pure5 survivor laws with the624/661 capacity argument. All actual higher pure originals are removed first. The laws are normalized, supported on that same finite family's pure survivors, and bounded by2H3 and(4/3)H5.

Decompose their numerical leaf weightsw,v into the fixed-null weak-corner vectors usingalpha,beta. Let

    lambda_c=sum_(i,j)alpha_i beta_j w^i_l v^j_m
                                     theta_(s(e0,A))^ij(c),
    theta_eff(c)=lambda_c/(w_l v_m)

on positive cells, zero elsewhere. The same actual conditional outside submeasure defined byR1 is attached at each cell, independently of the numerical weak markers and deeper central digits. Both priority inequalities hold for the selected whole family, so645 transportsR4 without clipping loss:

    G_actual(theta_eff)>=sum_(i,j)alpha_i beta_j G_(e0,A,i,j)
                                             >=gamma1.     (R6)

The density inequalities provide every finite query depth. No numerical corner law is substituted for an actual deep source, and no field or outside source is changed in response to a query.

Domination by the same actual pure product and fixed unary submeasures preserves the inherited joint caps and omitted-coordinate estimates. Rebuild the23/29/31 continuation and all actual normalized rows on this source using the657/658 recipes. Pay all193 finite row bounds, complete owner tail, Type I fee and the selected full arbitrary-parent tail. The two policies still permit at most three earlier declared parents below2^46 or2^68 respectively, and arbitrary fixed finite parent unions above the chosen switch.

Exact subtraction of those full source-unit budgets fromgamma1 and projection by2673/110656 gives reserves0.000002750321858565062... forRS46 and0.0000020819124030602784... for the elementary68 policy. Both are strictly greater than1/490000. Simultaneous private filling and CRT give the stated full density, divided by that family's actualQ_off. Ordinary domains, private interiors, original assignment rules and finite size/depth/height scope remain unchanged.

## Exact evidence and scope

The portable [producer](../../frontier/cover-geometry/one_regular_leaf_pair_library_certificate.py) and [exact result](../../frontier/cover-geometry/one_regular_leaf_pair_library_certificate.json) read only pinned640,658 and663 JSON. In particular the field tables are inherited by exact content hash; they are not reoptimized or rounded. The new5120-entry family selection is explicit certificate data.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/one_regular_leaf_pair_library_certificate.py
```

The producer accepts `--directory` and `--output`. It passes310,372 explicit checks with assertions disabled, including every selected layout/corner gate, all inherited priority conditions, literal-selector preservation or domination, local-response positivity and both complete density comparisons. The independent [verifier](../../frontier/cover-geometry/one_regular_leaf_pair_library_independent.py) and its [result](../../frontier/cover-geometry/one_regular_leaf_pair_library_independent.json) reconstruct the caps and direct matching sums without reading the producer. Its 3,518,687 explicit checks evaluate all 41,943,040 selector maxima and reproduce every one of the 81,920 candidate corner gates exactly. They also verify the 295 actual stabilizer orbits, the unchanged four field families, all 95-corner priorities, the transport to each other regular leaf, and both complete network margins. Family usage is1931,155,179,2855 for indices0,1,2,3. Both programs were rerun locally with assertions disabled; their retained results were reproduced byte for byte.

The result enlarges the certified layout set structurally: every numerical edge may be the single regular-role exception, all three regular leaves are included by full-data transport, and all remaining binary roles vary independently. The boundary is still at most one regular-role edge. More regular edges change both the joint partitions and their stabilizers; neither the local-subset table nor the known four fields by itself certifies those additional layouts.

The independent program accepts `--directory`, `--witness`, `--library` and `--output`:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/one_regular_leaf_pair_library_independent.py
```

# Dense irredundant families separate stage debits from actual unions

There are finite actual two-copy families on Q={5,7,11,13,17,19} for which the best possible sum of ALL four PA stage-completion debits tends to zero, together with the pure and mixed packing deficits. Every original has a private integer point, and every fixed nonunit Q-smooth numerical label is eventually occupied twice. Thus finiteness, irredundancy and access to every missing tail do not force the positive stage credit needed in [report544](544-missing-original-slots-restore-a-common-law-debit.md).

Nevertheless, the SAME actual PA law for these families has complete query norm at most

    59509/13850 =4.296678700361011... <257/51

once the old pure/mixed height is at least two. The repair retains the common current-prime phases of different old cofactors. Counting old-cofactor query occurrences discards this actual-union saving.

The statements below are ordinary proofs and exact finite arithmetic. They neither give an actual-law lower witness nor resolve arbitrary two-copy families or unrestricted Erdős #7. No Lean verification is claimed. The actual/completed kernels and all constants are those of [report348 PA](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md); no new source law is introduced.

## 1. A finite family with every selected numerical slot occupied

Choose positive integers N,A,E. At p=5,7 put the two pure originals

    p^(e-1), 2*p^(e-1) modulo p^e, 1<=e<=N.

For every 1<=a,b<=N put the two mixed originals

    (3*5^(a-1),3*7^(b-1)), (3*5^(a-1),4*7^(b-1))

at modulus 5^a*7^b. Their removed union U57=D5 times D7 is inside the complete pure survivor: D5 has first nonzero digit3 at depths through N, and D7 has first nonzero digit3 or4 at those depths. Hence, with eta=H restricted to U57,

    m=eta(1)=(1-5^-N)(1-7^-N)/12,
    d5=1/(2*5^N), d7=1/(3*7^N),
    delta=1/12-m=(5^-N+7^-N-35^-N)/12.                 (DU1)

A depth-a digit c always means residue c*p^(a-1) modulo p^a, with digits read from least significant to most significant.

For each q=11,13,17,19 let Pq be the smaller primes in Q. For every S subset Pq, every tuple 1<=a_p<=A on S, and every 1<=e<=E, put two originals at

    q^e * product_(p in S) p^a_p.

Their q-digits are 2|S|+1 and 2|S|+2 at depth e. The largest digits at the four rows are respectively6,8,10,12, all smaller than q.

Give old p=5 digit4 and old p=7 digit5. For previous later primes use safe palettes

    Safe11={7,8,9,10}, Safe13={9,10,11,12},
    Safe17={11,12,13,14,15,16}.

Every such palette avoids ALL terminal digits used at that prime's own earlier row. Let Rq=Pq without {5,7}. For each p in Rq choose different safe digits c(q,S,p) for the distinct nonempty supports S subset Rq containing p. There are at most four such supports per p, so the palettes suffice. For supports containing5 or7, take any fixed safe digit on each other coordinate. The old p-phase is c(q,S,p)*p^(a_p-1), identical for both copies. Fix these choices once, independently of exponents, points and comparison queries.

For example an explicit choice orders Rq increasingly, encodes its supports by binary masks, and assigns the containing-support masks to each p's safe palette in increasing mask order. Use the first safe digit for supports containing5 or7. This choice works for all N,A,E simultaneously.

The total number of originals is

    4N+2N^2+2E*sum_(j=2..5)(A+1)^j.                    (DU2)

Numerical multiplicity is exactly two at every listed label; different largest primes cannot duplicate a label. The all-zero point survives. Taking N=A=E=n exhausts all nonunit Q-smooth numerical labels as n increases.

## 2. Every original has a private point

An old pure original takes its specified p-coordinate and zeros elsewhere. An old mixed original takes its two specified5/7 coordinates and zeros at all later primes. Prefix-disjoint depths and digits distinguish the old originals, and every later original requires a nonzero largest-prime coordinate.

For a new largest-prime-q original, take its assigned old coordinates on S, its q terminal coordinate, and zeros outside S union {q}. Old5/7 classes are excluded by the safe digits4 and5. An earlier later-prime row is excluded by its coordinate being either zero or a digit outside its entire terminal palette. A later row is excluded by its zero largest-prime coordinate.

In the same q row, a different exponent e or a different support size/copy has a disjoint q-comb. Equal terminal digit forces equal support size and copy. A different support of the same size uses some coordinate outside S, which is zero at the chosen point. If the support agrees, a different old exponent is excluded by its first nonzero depth. These cases exhaust all competing originals. CRT realizes an integer with these residues at the complete finite prime-power heights, including when A>E. No class is redundant.

## 3. Actual occupied loads stay below all four thresholds on eta

Write eta_q=eta*Ktilde_<q for the removed measure transported through the fixed completed PA kernels. Its5/7 coordinates remain in U57. Any old cofactor using5 or7 is inactive there because its safe digit differs from the defining digits of D5 or D7.

For the remaining supports S subset Rq, one support can activate at most one exponent tuple. Two distinct intersecting supports cannot both activate: on a shared coordinate their assigned safe first nonzero digits differ. Consequently active nonempty supports are pairwise disjoint and number at most |Rq|. Including the unit, each occupied old slot load at every e<=E is at most

    1,2,3,4 <= tq=2,2,4,4.                              (DU3)

Both copies have the same old phase, so this holds for EVERY lawful assignment to slots. It is pointwise on every history over U57, without assuming productness of eta_q.

The actual q-forbidden fraction is at most 2(1+|Rq|)/(q-1). Thus its survivor fraction gq is at least4/5,2/3,5/8,5/9 respectively, each at least1/Cq for Cq=5/3,3/2,2,9/5. Every actual row has mass one on transported eta and equals its completed row there. Hence eta_q=eta*K_<q and retains mass m. Comparison completions affect neither kernel.

## 4. One tail bound for every possible completion

Set

    Dq=product_(11<=p<q) Cp,
    Zq=product_(p in Pq) p/(p-1),
    tau_q(A)=Zq*[1-product_(p in Pq)(1-p^(-A-1))].

Here tau_q(A) is the exact reciprocal sum outside the occupied old exponent rectangle, including its entire tail. The constants are

| q | Dq | Zq |
| --- | --- | --- |
| 11 | 1 | 35/24 |
| 13 | 5/3 | 77/48 |
| 17 | 5/2 | 1001/576 |
| 19 | 5 | 17017/9216 |

Completed conditional densities give eta_q<=Dq*H on the old coordinates. At e<=E, every cofactor inside the rectangle has both phases fixed. Its occupied load B is bounded by tq in DU3. If X is the load added by any missing comparison phases, then (B+X-tq)_+<=X. The integral is at most Dq*tau_q(A).

At e>E the slots are entirely absent. Since tq>=1, their hinge is bounded by the complete NONUNIT old query count, with integral at most Dq*(Zq-1). The two-slot beta weights have head mass1-q^-E and tail massq^-E. Therefore, simultaneously for all four rows and uniformly over ALL lawful comparison completions and slot assignments,

    0<=Jq<=Dq*[(1-q^-E)*tau_q(A)+q^-E*(Zq-1)].           (DU4)

Finite sums and monotone convergence justify every countable completion; the reciprocal majorants are finite. No missing-height tail is dropped, no maximizers from incompatible laws are combined, and no intermediate normalization is made.

Let A5,A7,A57,c0 be exactly report544 PD3's constants, aq=(1/3,1/4,1/4,1/5), and T=257/51. As N=A=E=n tends to infinity, DU1 and DU4 prove

    sup_(all completions) [A5*d5+A7*d7+A57*d5*d7
          +(T-2)*(delta+sum_q aq*Jq)] -->0.             (DU5)

Thus the infimum of that best stage credit over finite irredundant actual families is zero. At N=A=E=4 the formula describes31248 originals, without requiring their enumeration, and its credit upper bound is

    110382359184068166213935387347
      /16051257544045797121429180800000
      =0.006876866742756516... <c0.

The strict gap is

    143978246159999205632374630181
      /32102515088091594242858361600000.                (DU6)

This bounds every possible stage lower-payoff construction too, since it cannot exceed its dominating stage hinges. It does NOT bound the final-query debit JL. In particular DU5-DU6 do not refute the full PD3 inequality or give a lower bound on the actual PA norm.

## 5. Retain the current-prime phases to repair the same law

At an arbitrary old point x, let E_(q,S) be the event that an old exponent tuple of support S is active. Define kq(x) to be the number of DIFFERENT active support cardinalities, including cardinality zero from the unit. All originals with equal support cardinality share precisely the same pair of q-digits. Different cardinalities and different q depths give disjoint q-combs. Hence the actual forbidden union has exact Haar fraction

    bq(x)=2*kq(x)*(1-q^-E)/(q-1).

Using 2Cq/(q-1)=aq and Cq-1=aq*tq, its actual mass loss is

    1-sq(x)=aq*[kq(x)*(1-q^-E)-tq]_+
       <=aq*(kq(x)-tq)_+
       <=aq*sum_(S subset Pq, |S|>=tq)1_(E_(q,S))(x).   (DU7)

The last inequality holds because at most tq different cardinalities are below tq. The current-prime union counts a cardinality once, even when many old cofactors of that size are active. This is the relation missing from the individual old-cofactor slot counts.

The one actual prefix measure obeys lambda_<q<=Dq*H. Disjoint old comb depths give

    H(E_(q,S))=product_(p in S)(1-p^-A)/(p-1)
             <=product_(p in S)1/(p-1).

Integrating DU7 produces the four absolute row-loss bounds

    1/72, 7/192, 1/4608, 49/46080,

whose sum is793/15360. The complete initial actual mass is

    lambda0(1)=w5*w7-m
      =1/4+(5/12)*5^-N+(1/4)*7^-N+(1/12)*35^-N>=1/4.

Telescope without intermediate normalization to obtain

    lambda(1)>=3047/15360.                              (DU8)

For any final cylinder, integrate the actual kernels backwards. An unqueried current coordinate has row mass at most one; a queried q^a cylinder has conditional mass at most Cq/q^a, pointwise in earlier coordinates. After all four rows, use lambda0<=sigma, where sigma is the product of the two pure-survivor restrictions. An unqueried old coordinate contributes wp, and a queried p^a contributes at most p^-a. This proves a phase-uniform bound under the SAME lambda; it makes no independence claim about lambda itself.

Sum these bounds over all numerical labels INCLUDING the unit. Geometric series give

    sum_(d Q-smooth, including 1) max_(b mod d)lambda([b]_d)
       <=W_N=(w5+1/4)*(w7+1/6)
                        *product_q(1+Cq/(q-1)).         (DU9)

For N>=2, w5<=13/25, w7<=33/49 and the last product is2079/1280. Thus W_N<=268983/256000. The unit term on the left is lambda(1), so after one normalization DU8-DU9 give

    R_Q<=W_N/lambda(1)-1<=59509/13850<257/51,            (DU10)
    257/51-59509/13850=524491/706350>0.

This holds for every N>=2 and every finite A,E>=1 in the constructed family. It controls all query phases and heights without selecting or bounding a maximizing JL. It is not a uniform theorem for unrelated actual families.

## 6. What the construction distinguishes

[Report545](545-bounded-completion-payoffs-pass-dense-small-labels.md) shows that bounded lower payoffs can use available numerical slots to certify additional families. DU5 proves that increasing such finite slot lists cannot alone force a positive uniform credit: every fixed list is eventually occupied in this irredundant sequence, and even the best full remaining completion has vanishing stage credit.

DU10 supplies the positive counterpart. The same sequence has a strict upper law once shared current-prime phases are retained in its actual forbidden union. A general extension must control a joint saving from stage debits, actual phase overlap, the final query, or a different common law. Neither separate saturation of local bounds nor failure of a selected certificate establishes an actual lower witness. The arbitrary two-copy problem and the separate unrestricted ternary-gluing problem remain unresolved.

## 7. Independent exact finite controls

The standalone [consumer](../../frontier/cover-geometry/dense_stage_debit_obstruction.py) and [retained result](../../frontier/cover-geometry/dense_stage_debit_obstruction.json) use explicit rational inputs without importing previous producers. The final execution exited0 with1019 named checks passing.

At N=A=E=1 the consumer constructs126 originals on63 labels, with a literal safe-palette assignment. It checks15876 private-point/class pairs by integer congruences and by coordinate membership. The274 representatives of the occupied old-phase predicates over eta give maximum slot loads1,2,3,4 and mass-one actual rows. A further548 predicate representatives, including histories outside eta, verify the actual forbidden union by distinct support cardinalities and its pointwise loss bound. These representatives exhaust the indicated finite predicate classes, not every integer in the original period.

For N=A=E=4, the consumer evaluates DU4 by subtracting the finite reciprocal box from the full Euler product, separately retaining head and absent-height-tail contributions. It verifies DU6 exactly and obtains31248 originals from DU2; it does NOT construct or enumerate that larger family. Exact subset sums independently recover the four loss bounds, final mass bound, complete-query factor and DU10. The arbitrary-parameter and all-completion conclusions rely on the ordinary proofs, not an extrapolation of these finite controls.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/dense_stage_debit_obstruction.py
```

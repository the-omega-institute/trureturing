# A source-adaptive atlas covers both forbidden reference roots at five

Under the selected23 mixed-phase conditions of [Report808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md), every actual finite pure-prime family whose modulus5 original is either0 mod5 or1 mod5 has a positive continuation certificate through29 and the complete finite prime tail above1600. All higher pure exponents may vary independently and have arbitrary phases. The final distorted surviving mass is strictly greater than1/800.

The source is chosen from two already specified rational retained tables. No new optimization or arbitrary mixing of their endpoint successes is needed: each table certifies an entire product region, and those regions cover the stated actual source cases. This is an ordinary proof with exact rational checks. It is not Lean verification, does not include a different modulus5 phase or an absent modulus5 original, and does not resolve unrestricted Erdős#7.

## 1. Actual-family assumptions

The family is finite, all numerical moduli are pairwise distinct odd integers greater than one, and each original has one globally fixed phase. The old nonternary primes are

    Q=(5,7,11,13,17,19,23).

Require the literal25 originals from808:0 mod3,1 mod9 and its23 selected mixed originals, including10 mod15 and11 mod45. The remaining old originals can have arbitrary allowed phases and heights, including arbitrary pure powers. The actual modulus5 original is required to be0 mod5 or1 mod5. No extra old prime outside{3} union Q is allowed. In the continuation, all permitted originals involving29 are arbitrary, as is every finite further prime support strictly above1600. Primes31 through1600 remain excluded. These are the same support and tail conditions as [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md).

Every actual pure-q original is incorporated in the single normalized Haar survivor law lambda_q. The actual higher pure ternary originals remain in the complete residual inventory, as in [Report810](810-categorical-retained-kernels-give-a-finite-common-source-interface.md). Selected originals can be redundant; the bound does not assume irredundancy or change their phases after inspecting a query.

Use the full source lambda_w on ternary leaves(4,7,2,5,8), with independent nonternary laws lambda_q. The categorical observation is{0},{1},{2,3,4} at5 and{0},nonzero at every other q. Write

    a=pi5(0), b=pi5(1),
    0<=piq(0)<=Cq/q, Cq=(q-1)/(q-2).

The selected source table is used to bound the mass of the actual old survivor U. The subsequent normalized source remains the full law lambda_w restricted to U divided by lambda_w(U), exactly as in814. It is not the retained-source normalization studied in815.

## 2. A forbidden reference root leaves one actual probability interval

Suppose the actual modulus5 original deletes root0 or root1. Before deeper pure deletions, each of the other four roots has Haar mass1/5 and their total mass is4/5. The total additional deleted mass satisfies

    0<=D<=sum_(j>=2)5^(-j)=1/20.

This accounts for all actual finite higher pure powers. Overlap can only reduce their union mass. For any surviving root, let its actual additional deletion be d, so0<=d<=D. Its conditional probability is

    p=(1/5-d)/(4/5-D).

The minimum at fixed D has d=D, and its value decreases with D. The maximum has d=0 and increases with D. Consequently

    1/5<=p<=4/15.

Thus the two actual source cases lie on the segments

    root0 deleted: (a,b)=(0,b), b in[1/5,4/15];
    root1 deleted: (a,b)=(a,0), a in[1/5,4/15].

These bounds also follow from the joint actual-source classification in [Report816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md). Their use here needs no assertion that every point of either closed segment is attained by a finite pure family.

## 3. The two fixed tables and their full-domain endpoint bounds

Use the quarter and third tables of [Report814](814-three-kernels-cover-all-source-vertices-but-miss-a-strict-interior-point.md). Their weights are respectively

    w_quarter=(1/4,1/4,1/6,1/6,1/6),
    w_third=(23289806,23289806,17736838,17339709,18343841)/10^8.

Both complete retained tables and their selected-cylinder nullity are unchanged. For a fixed table define

    r=max(w4+w7,w2+w5+w8), v=max_l w_l,
    G(pi)=12L(pi,u)-H16(r,v)-27Kq(1+15r+216v)T1600.

Here L is the complete old-source lower bound, H16 is the full-source hinge, Kq includes the pure29 factor exactly once, and T1600 is804's complete tail constant. The verifier recomputes all these terms. The source mass and the query envelopes use the same pi.

The following entries are exact minima over all64 endpoints of the six other probability intervals. The decimals are displays of the saved rational values.

| deleted root | table | varying probability=1/5 | varying probability=4/15 |
| --- | --- | ---: | ---: |
| 0 | quarter | 0.670690306153582... | 0.5797880881990328... |
| 1 | quarter | 0.20995128655910117... | -0.051733606583071474... |
| 1 | third | -0.05115910405086246... | 0.08590443304865045... |

For one fixed table, G is concave in each whole local probability block. Therefore each displayed bound holds over the full six-interval box at its stated5 endpoint. Interpolation along the5 segment gives the corresponding linear lower bound throughout the segment. This uses one unchanged table across all vertices of each certified region.

## 4. A genuine continuous atlas

If root0 is deleted, use the quarter table throughout. Its gate is greater than0.57 on the entire segment times the full six-interval box.

If root1 is deleted, choose the source by the following exact rule:

    a<=11/45: use the quarter table;
    a>11/45: use the third table.

The split is at relative position2/3 in[1/5,4/15]. Let Q0,Q1 denote the two quarter endpoint lower bounds and R0,R1 the third endpoint bounds in the last two rows of the table. At the common split the two concavity bounds are

    (Q0+2Q1)/3=0.03549469113098607... >7/200,
    (R0+2R1)/3=0.04021658734881281... >1/25.

The outer endpoints in their respective subsegments have larger positive lower bounds. Thus every point in all three product cells has

    G(pi)>7/200.

The cells are the complete root0 segment, the root1 subsegment[1/5,11/45], and the root1 subsegment[11/45,4/15], each times the entire six-interval box. Their union contains every actual source satisfying section1. This establishes an atlas by regionwise certificates and a direct union identity, rather than by assigning unrelated tables to the endpoints of a larger region.

The rule chooses one source for the actual family. It does not select a different source for different queries, optimize phases independently, or average incompatible realizations. Its input a is the probability computed from the same finite actual pure5 family.

## 5. Full continuation and the uniform reserve

Put alpha=lambda_w(U). Since alpha>=L and G>0, both alpha and L are positive. The inherited29-admission and full-tail argument gives final distorted mass at least

    12/27-[H16+27Kq(1+15r+216v)T1600]/(27alpha).

The bracket is nonnegative. Replacing alpha by its lower bound L therefore gives

    final mass >=G/(27L)>=G/27>7/5400>1/800,

where L<=1 because it is retained source mass minus nonnegative complete loss bounds. This is a positive mass certificate for the actual family under the stated source/support conditions, so that family cannot cover all integers.

The conclusion permits arbitrary finite heights, arbitrary other pure-q phases and all the specified mixed phases outside the selected23 constraints. It does not include the root-other and absent-pure5 source cases. Report816 gives a finite actual root-other source at which all three old814 tables fail; that obstruction is outside the atlas just proved.

## 6. Reproduction

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/reference_phase_atlas.py) imports814's local common-source evaluator and reads its literal rational certificate. It recomputes the six endpoint faces, their complete inventory and tail, and the exact splice. The [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/reference_phase_atlas.json) stores rational minima and the uniform reserve.

```sh
python3 -I -S -B reference_phase_atlas.py
```

Normal execution compares the recomputed result with the saved data. `--write-result` is explicit regeneration; `--source-dir` and `--result` select local inputs. Neither a solver nor network access is needed.

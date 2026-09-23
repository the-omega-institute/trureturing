[Index](../../marked_head_profile.md) · [Actual lifting](439-actual-residual-lifting-and-exact-free-coordinate-cost.md) · [Private head law](449-equality-sources-have-a-private-law-below-nine.md) · [Original antichains](../321-384/363-common-source-antichain-capacity.md)

# Weighted original depths give joint deletion credit; outside blocks still need a shared budget

For original mixed labels d=3^e a b with a dividing1225 and fixed numerical outside cofactor b, comparable-class disjointness gives a sharp all-ternary-height weighted count bound34/9. If b=1, so the mixed condition excludes a=1, the sharp bound is11/3. This allows the original3-exponent layers to be combined in ONE Gram/deletion estimate, retaining their weights and full event indicators.

Different b blocks may delete the same physical mass, so their credits cannot simply be added. There is also an explicit702-label actual odd family for which a head marginal with Gamma_1225<=25/3 has a uniform actual-fibre lift whose original completion load exceeds the necessary whole-cover threshold. The same law leaves positive uncovered mass, and a different supported lift makes the completion load zero. Thus the example identifies a limitation of the specified uniform lift, not an obstruction to every lift or a covering counterexample.

These are ordinary mathematical results with exact controls. The Gram projection mechanism is reused from Chapter08; no new Lean certification, mathematical priority, or unrestricted Erdős #7 conclusion is claimed.

## 1. A sharp weighted bound retaining every original ternary depth

Let a finite original family have at most one residue class A_d for each numerical modulus d, and suppose distinct comparable moduli have disjoint classes:

    d divides d', d!=d'  =>  A_d intersect A_d'=empty.

An irredundant family has this property: if comparable classes intersect, the larger-modulus class is contained in the smaller-modulus class and is redundant. It is therefore available after taking an inclusion-minimal subcover of a hypothetical whole cover, as well as in the extremal model of350.

Fix an odd integer b coprime to3*5*7. Consider just the original mixed labels

    d=3^e a b, 1<=e<=H, a|1225, ab>1,
    w_d=3^(1-e), I_d(x)=1_[x in A_d].

Other original labels may exist. Labels with higher5- or7-height are not included in this block, and cannot be hidden inside b under its coprimality condition. Missing labels contribute zero.

At each actual full point x, the active exponent triples(e,v_5(a),v_7(a)) form an antichain: coordinatewise comparison would make the original numerical moduli comparable. Therefore

    W_b(x)=sum_d w_d I_d(x) <= kappa_b(H),

where the exact constants are

| Ternary height | b>1 | b=1, mixed labels only |
| --- | ---: | ---: |
| H=1 | 3 | 3 |
| H=2 | 11/3 | 11/3 |
| H>=3 | 34/9 | 11/3 |

The statement uses the complete original indicators, including the actual ternary and outside residues. It does not claim that the projected head labels alone remain an antichain when different e are merged.

### Proof and sharpness

Each fixed-e head slice is an antichain in the3-by-3 exponent grid and contains at most three points. Its unique three-point antichain is

    a=25,35,49, with head exponents(2,0),(1,1),(0,2).

For H=1 this proves the bound. For H>=2, if the first slice has at most two active points, its entire weighted count is at most

    2 + 3 sum_(e>=2)3^(1-e) = 7/2,

which is less than both11/3 and34/9.

If the first slice has three points, they must be25,35,49. No later active head can be a multiple of any of them. The only remaining head possibilities are1,5,7. Each can occur at most once, since repetitions at different e would give comparable original moduli. Heads5 and7 each contribute at most1/3. If head1 occurs and either of those heads occurs, its ternary exponent must be strictly greater than theirs. In particular, an occurrence of head1 at e=2 excludes both5 and7 from all later slices; this gives only1/3 additional weight. If it occurs at e>=3, its weight is at most1/9. Thus the later contribution is at most2/3+1/9. At H=2 it is at most2/3. When b=1, head1 is excluded by the mixed-label condition, leaving the bound2/3 at every H>=2.

All constants are attained. At H>=3 and b>1 take the six actual original classes of phase1 whose(e,a) pairs are

    (1,25),(1,35),(1,49),(2,5),(2,7),(3,1).

Their numerical moduli are pairwise incomparable, and the integer1 lies in all six. Their weighted sum is3+2/3+1/9=34/9. For H=2 omit the last class; for H=1 keep only the first three. For b=1 always omit the a=1 class. These sharpness examples are actual distinct odd APs; they are not claimed to be whole covers or extremal covering residuals.

## 2. One Gram estimate across all e in the fixed b block

Let rho be any one finite positive measure on the full carrier. Put

    u_d=integral I_d d rho,
    G_dd'=integral I_d I_d' d rho,
    c_d=integral L I_d d rho,

where L is any real test load on that same carrier. If u_d=0, then c_d=0; omit such labels from divisions below.

Weighted Cauchy--Schwarz at each full point gives, for every real vector v,

    (sum_d v_d I_d)^2
       <= (sum_d w_d I_d)(sum_d v_d^2 I_d/w_d)
       <= kappa_b(H) sum_d v_d^2 I_d/w_d.

After integrating,

    G <= kappa_b(H) diag(u_d/w_d)

in positive-semidefinite order. If B contains the union of this block's original classes, Chapter08's least-squares deletion identity gives

    integral_B L^2 d rho >= 2 v^T c - v^T G v.

Choose v_d=w_d c_d/[kappa_b(H)u_d]. Then

    integral_B L^2 d rho
       >= [1/kappa_b(H)] sum_d w_d c_d^2/u_d.          (WD1)

All ternary depths in the block occur in this one sum. No credit is added separately for each e. In particular the universal coefficients are9/34 for b>1 and3/11 for b=1. If s=rho(B^c)>0, the corresponding conditional upper bound is

    integral L^2 d(rho|B^c/s)
       <= [integral L^2 d rho
            - kappa_b(H)^(-1) sum_d w_d c_d^2/u_d]/s. (WD2)

This uses the actual masses u_d and actual test/forbidden correlations c_d. Separate head marginals or independently chosen phase maxima do not supply them.

The constant is also sharp for the Gram and deletion statements under these hypotheses. Use one of the sharp phase1 families above and put rho mass1/2 at each full residue1 and2. Every original indicator equals1 at the first atom and0 at the second. The direction v_d=w_d makes the Gram bound an equality. For the complete test layout having phase1 at every nonunit divisor of its true period, L(1)=tau(period) and L(2)=1; (WD1) gives exactly the deleted second moment and (WD2) gives the surviving value1.

The fixed-b estimates cannot be added without another joint bound. Take the sharp six-label families for b=11 and b=13 together, using the same two-atom rho and L=1. Their twelve numerical moduli remain distinct and pairwise incomparable. Each block's right side in(WD1) is1/2, but their union has deleted mass1/2. Adding the two credits would assert1<=1/2. The obstruction is overlap under the same law, not a change of measure.

## 3. A good actual head marginal does not control its uniform outside lift

Retain the eight original3-free head classes from447:

| Modulus | 5 | 7 | 25 | 35 | 49 | 175 | 245 | 1225 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Residue | 0 | 0 | 21 | 34 | 48 | 173 | 242 | 241 |

Their actual common avoid-set S in Z/1225 has736 points. It contains the following labelled private structure. Write a point as(r,c,g+7h). At each r=2,3,4 take the five points with c=h and g=r, each of mass3/60. At r=1 use private column g=1 and the four children

    c=0: h=0, mass3/60;
    c=1: h=1,2, masses3/60,1/60;
    c=2: h=2,3, masses2/60,2/60;
    c=3: h=3,4, masses1/60,3/60.

All22 points belong to S. This is449's private law, here called mu; the exact nine numerical cylinder caps give Gamma_1225(mu)<=25/3. The construction is on an actual avoid-set, not an abstract projection supplied with unverified fibres. The736-point source also has stronger previously available bounds; no improvement of its best head constant is claimed.

For any H>=1 and finite set P of primes greater than7, add these original classes:

    3^e : a_e=3^(e-1)-1 mod3^e,       1<=e<=H;
    p   : 0 mod p,                    p in P;
    3^e p : (b_e mod3^e, 1 mod p),    b_e=2*3^(e-1)-1.

The last row specifies one literal CRT residue for each full original modulus3^e p. All numerical moduli are distinct, odd and greater than one. The family is divisor-closed above one. When P is an initial prime segment beginning at11, its prime support is the complete odd initial segment through max(P).

The a_e and b_e prefixes are the two noncontinuing children of a ternary comb: in lowest-digit-first notation they are2^(e-1)0 and2^(e-1)1. All these prefixes are pairwise disjoint. This proves comparable-class disjointness for the ternary and mixed labels; the pure p class is disjoint from its mixed classes because its p-residue is0 instead of1. The original head comparable pairs are already disjoint. No remaining cross-kind pair is numerically comparable.

Each original also has an actual private point. Use CRT with default head coordinate1, ternary coordinate3^H-1, and every outside coordinate2. For a head label replace only the head coordinate by its private point relative to the eight head classes. For a pure ternary label replace only the ternary coordinate by a_e. For a pure p label replace only that outside coordinate by0. For a mixed3^e p label replace the ternary coordinate by b_e and the p-coordinate by1. Disjointness of the comb leaves and the unchanged outside values show that exactly the intended original label is hit. The unchanged default point is uncovered. These are local irredundancy facts about this explicit noncover; no globally minimum-cover provenance is asserted.

The actual3-free residual is exactly

    R_3 = S times product_(p in P)(Z/p minus {0}).

Thus every actual outside fibre has the same positive Haar density product_p(1-1/p). Fix the head marginal mu and take the genuinely uniform law on each of these actual fibres:

    nu = mu times product_p Uniform(Z/p minus {0}).

For every original mixed label its full cofactor event is C_(e,p)={x_p=1}; under this same nu it has mass1/(p-1). Put

    T_H=sum_(e=1,...,H)3^(1-e)=(3/2)(1-3^(-H)),
    s_H=3^(1-H),
    B_H=(3+3^(1-H))/2=T_H+s_H,
    S_P=sum_(p in P)1/(p-1).

The original completion load is therefore exactly

    L_comp=sum_(e,p)3^(1-e) nu(C_(e,p))=T_H S_P.       (UL1)

It is independent of the chosen head marginal. Improving only that marginal's Gamma cannot reduce(UL1) for this specified lift.

For H=4, take all138 primes from11 through821. Exact arithmetic gives

    T_4=40/27, B_4=41/27,
    S_P>41/40,
    L_comp-B_4 >= 16847/16875000 > 0.                 (UL2)

A compact integer certificate is

    sum_(p in P) floor(10^8/(p-1))=102567388.

Multiplying its lower bound for S_P by40/27 gives(UL2). The previous prime cutoff811 does not cross the threshold;821 is the first crossing within this consecutive-prime construction. This family has8+4+138+4*138=702 original labels. No globally smallest example is claimed.

The whole-cover condition in378 requires L_comp>=B_H for every supported law. The explicit noncover here satisfies that numerical inequality under its uniform actual-fibre lift. Hence the head bound and the listed structural conditions cannot force this particular lift's load below B_H. This does not make the necessary inequality sufficient for covering, and does not refute an argument using the additional whole-cover premise essentially.

## 4. The same law exposes the overlap and the remaining ternary prefix

No law change is needed to account for the excess in(UL2). Under nu the outside indicators1_[x_p=1] are independent. Set

    Z_P=product_(p in P)(1-1/(p-1)).

Let tau be the sum of the uniform measures on the two nonzero first-3-root copies; each copy has mass one, so tau has total mass two. A depth-e mixed comb leaf has tau-mass3^(1-e). After deleting the pure comb leaves, the remaining ternary domain has tau-mass B_H; it consists of all mixed comb leaves and the last continuation leaf of mass s_H.

Under the ONE product measure tau times nu, the actual mixed union mass, surviving mass in that remaining domain, and excess multiplicity are respectively

    union = T_H(1-Z_P),
    U     = s_H+T_H Z_P > 0,
    W     = T_H(S_P-1+Z_P).

They satisfy the exact account

    L_comp-B_H = W-U.                                (UL3)

This is the actual-family instance of340's existing incidence/escape identity. It is not a new generic overlap identity. At the702-label parameters, exact rational enclosures give

    0.558689 < U < 0.558690,
    0.559689 < W < 0.559690.

These masses use tau, not normalized full ternary Haar. Divide by three for the full ternary Haar normalization, or by two to condition on a nonzero first root. The terminal prefix3^H-1 avoids every ternary comb leaf regardless of the outside coordinates; its contribution s_H cannot be discarded by averaging the original labels.

The full original Gram matrix also retains this geometry. With t_p=1/(p-1), the cofactor matrix on p is

    G_P = t t^T + diag(t_p(1-t_p)).

The cofactor events repeat at every e. When the actual ternary prefixes are included under tau times nu, distinct e blocks have zero intersection, and the block at e is3^(1-e)G_P. The original e labels have not disappeared. Within any fixed(e,p) block there is just head a=1; this example does not test a nontrivial width-three head block. It shows why local antichain or Gram information still needs a joint account across the different numerical outside cofactors.

There is no obstruction to all supported lifts in this example. Preserve the same mu and assign every outside coordinate the actual value2. This is supported on R_3 and gives every original mixed cofactor event mass zero, so its completion load is zero. The uniform lift and this alternative are separately specified laws, not components selected afresh for individual tests.

## 5. Controls, reuse and remaining obligations

The [weighted-depth checker](../../frontier/cover-geometry/weighted_original_depth_gram.py) and [exact data](../../frontier/cover-geometry/weighted_original_depth_gram.controls.json) enumerate all20 antichains of the3-by-3 head grid. A Bellman state retains the available head positions; selecting a slice removes its upward closure from every later slice and discounts the continuation by1/3. It checks230 states for H=1,...,6 in both the full and mixed-only head cases. Six literal original-AP examples attain the stated constants and the same-law Gram/deletion equalities. A two-b example rejects unbudgeted addition of the credits. The proof above covers arbitrary H; these finite controls do not replace it.

The [uniform-lift countercontrol](../../frontier/cover-geometry/original_completion_uniform_lift.py) and [exact data](../../frontier/cover-geometry/original_completion_uniform_lift.controls.json) reconstruct the702 original moduli and residues, check all2785 comparable pairs for actual disjointness, and check divisor closure with1395 factor-pair tests. It checks each of702 CRT private witnesses against every original class, for492804 membership checks. It verifies the head law against1767 numerical cylinders and all81 divisor pairs, checks304704 ordered mixed pairs with their full CRT compatibility and cofactor/ternary Gram distinction, and verifies the exact cutoff, overlap and escape account. The large common period is not enumerated.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/weighted_original_depth_gram.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_completion_uniform_lift.py
```

The pointwise original-antichain mechanism is already in363 and Chapters40/42; Chapter08 supplies the generic Gram projection. Their fixed-layer statements do not give the displayed sharp weighted count across all e. The proof here supplies that count and applies the existing projection inside the resulting joint estimate; no separate Lean wrapper or new generic Gram theorem is introduced. The ternary comb is already used in Chapter03, and420 gives a different all-centre first-moment obstruction. The present countercontrol retains the actual736-point head marginal, actual outside fibres, original3-bearing labels and the specific B_H completion budget in one family.

The remaining quantitative task is to control the actual c_d and their joint deletion support across b, or to construct a suitable phase-aware supported lift for the whole original family. A count bound does not supply those correlations, and the uniform-lift example shows why scalar head quality alone does not pay their full budget. Arbitrary higher5/7 heights, outside composite supports, and the whole-cover quantifiers remain outside the new sharp block constant. The unrestricted goal is not settled.

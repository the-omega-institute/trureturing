[Index](../../../marked_head_profile.md) · [Actual lifting](../400-449/439-actual-residual-lifting-and-exact-free-coordinate-cost.md) · [Private head law](../400-449/449-equality-sources-have-a-private-law-below-nine.md) · [Original antichains](../../321-384/363-common-source-antichain-capacity.md)

# Weighted original depths give joint deletion credit; outside blocks still need a shared budget

For original mixed labels d=3^e a b with a dividing1225 and fixed numerical outside cofactor b, comparable-class disjointness gives a sharp all-ternary-height weighted count bound34/9. If b=1, so the mixed condition excludes a=1, the sharp bound is11/3. This allows the original3-exponent layers to be combined in ONE Gram/deletion estimate, retaining their weights and full event indicators.

Different b blocks may delete the same physical mass, so their credits cannot simply be added. There is also an explicit702-label actual odd family for which a head marginal with Gamma_1225<=25/3 has a uniform actual-fibre lift whose original completion load exceeds the necessary whole-cover threshold. The same law leaves positive uncovered mass, and a different supported lift makes the completion load zero. Thus the example identifies a limitation of the specified uniform lift, not an obstruction to every lift or a covering counterexample.

For this same family, section6 proves that every head marginal with a uniform actual-fibre lift has original cofactor second moment above893/81>9. Even exact deletion credit leaves a positive certificate gap; full owners and actual private-owner densities are evaluated under the same law.

Section7 identifies a whole-cover condition that this countercontrol fails: every prime3-private point has a hole on its complete3-coordinate line. More generally, an original pure prime power at minimum positive height has an exact private-product region, and every hole resets into it. This extracts the pointwise mechanism of Reports354 and357 without importing their later whole-cover matching conclusions.

Section8 computes the exact defect in the original owner-pair capacity. Prime privacy forces a positive pure-owner defect under distinct original pure moduli, but enlarging the actual private centers to a whole cofactor cylinder still leaves an insufficient bound. Two actual noncover families separate positive scalar defect and distinct numerical matching from the required joint contradiction.

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

The [weighted-depth checker](../../../frontier/cover-geometry/weighted-original-depth-gram/weighted_original_depth_gram.py) and [exact data](../../../frontier/cover-geometry/weighted-original-depth-gram/weighted_original_depth_gram.controls.json) enumerate all20 antichains of the3-by-3 head grid. A Bellman state retains the available head positions; selecting a slice removes its upward closure from every later slice and discounts the continuation by1/3. It checks230 states for H=1,...,6 in both the full and mixed-only head cases. Six literal original-AP examples attain the stated constants and the same-law Gram/deletion equalities. A two-b example rejects unbudgeted addition of the credits. The proof above covers arbitrary H; these finite controls do not replace it.

The [uniform-lift countercontrol](../../../frontier/cover-geometry/original-prime-private-reset/original_completion_uniform_lift.py) and [exact data](../../../frontier/cover-geometry/original-prime-private-reset/original_completion_uniform_lift.controls.json) reconstruct the702 original moduli and residues, check all2785 comparable pairs for actual disjointness, and check divisor closure with1395 factor-pair tests. It checks each of702 CRT private witnesses against every original class, for492804 membership checks. It verifies the head law against1767 numerical cylinders and all81 divisor pairs, checks304704 ordered mixed pairs with their full CRT compatibility and cofactor/ternary Gram distinction, and verifies the exact cutoff, overlap and escape account. The large common period is not enumerated.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/weighted-original-depth-gram/weighted_original_depth_gram.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-prime-private-reset/original_completion_uniform_lift.py
```

The pointwise original-antichain mechanism is already in363 and Chapters40/42; Chapter08 supplies the generic Gram projection. Their fixed-layer statements do not give the displayed sharp weighted count across all e. The proof here supplies that count and applies the existing projection inside the resulting joint estimate; no separate Lean wrapper or new generic Gram theorem is introduced. The ternary comb is already used in Chapter03, and420 gives a different all-centre first-moment obstruction. The present countercontrol retains the actual736-point head marginal, actual outside fibres, original3-bearing labels and the specific B_H completion budget in one family.

The remaining quantitative task is to control the actual c_d and their joint deletion support across b, or to construct a suitable phase-aware supported lift for the whole original family. A count bound does not supply those correlations, and the uniform-lift example shows why scalar head quality alone does not pay their full budget. Arbitrary higher5/7 heights, outside composite supports, and the whole-cover quantifiers remain outside the new sharp block constant. The unrestricted goal is not settled.

## 6. Exact cofactor second moments also obstruct the uniform actual-fibre lift

The same702-label family in section3 provides a stronger test of the specified uniform lift. It requires no new original classes or head source. Keep H=4 and all138 outside primes P from11 through821. Let lambda be ANY probability supported on the actual736-point head avoid-set S. In particular lambda can be the displayed law with Gamma_1225<=25/3, or any improvement of that head marginal.

On the cofactor carrier B=1225 product_(p in P)p, use ONE reference probability

    rho=lambda times product_(p in P)Uniform(Z/p),
    R=R_3=S times product_(p in P)(Z/p minus{0}),
    Z=rho(R)=product_(p in P)(1-1/p),
    nu=rho conditioned on R.

All original cofactor phases are those in section3. For every original3-bearing class3^e d, use weight3^(1-e) and its actual d-cylinder. The sum over the pure3 originals contributes T_H, while every mixed3^e p contributes3^(1-e)1_[x_p=1]. Hence the full ORIGINAL cofactor load is

    W_3=T_H(1+N),
    T_H=40/27,
    N=sum_(p in P)1_[x_p=1].                         (UG1)

For an actual whole cover, union bounding the original classes on each surviving3^H-fibre gives W_3>=3 on R_3. That pointwise implication remains a whole-cover requirement; it is not asserted for this noncover.

Under nu the outside indicators in N are independent with probabilities t_p=1/(p-1). Under rho their probabilities are u_p=1/p. Define

    S_0=sum_p u_p, V_0=sum_p u_p(1-u_p),
    S_1=sum_p t_p, V_1=sum_p t_p(1-t_p).

The exact moments, unchanged by the choice of lambda, are

    J_0=E_rho W_3^2=T_H^2[(1+S_0)^2+V_0],
    J_R=E_nu W_3^2=T_H^2[(1+S_1)^2+V_1],
    D_W=integral_(R^c)W_3^2 d rho=J_0-Z J_R.        (UG2)

Section3 already proves S_1>41/40. Since every p>=11, t_p<=1/10 and

    V_1>= (9/10)S_1>369/400.

Consequently

    E_nu W_3=T_H(1+S_1)>3,
    J_R>9+(40/27)^2*(369/400)=893/81>9.             (UG3)

This is a uniform obstruction over EVERY supported head law lambda for this specified uniform conditional lift. It does not rely on whether lambda's complete head moment bound is sharp.

The exact rational calculation gives the following certified intervals; each omitted interval width is10^-12:

|quantity|lower endpoint|upper endpoint|
|---|---|---|
|Z|0.364555701040|0.364555701041|
|E_nu W_3|3.000999249680|3.000999249681|
|J_0|10.831807983986|10.831807983987|
|J_R|11.181132511931|11.181132511932|
|D_W|6.755662382669|6.755662382670|
|J_0-D_W-9Z|0.795144291949|0.795144291950|

The program retains exact rational values for Z,J_0,J_R,D_W and the last positive gap. The decimal table is only a readable enclosure.

### Exact deletion bounds every owner credit

Let Phi be the vector of the actual cofactor indicators and w the original weights. Set

    G^0=E_rho[Phi Phi^T],
    G^D=E_rho[1_(R^c) Phi Phi^T].

Then w^T G^0 w=J_0 and w^T G^D w=D_W. For ANY valid deletion-owner matrix H satisfying0<=H<=G^D in Loewner order,

    w^T(G^0-H)w-9Z
      >=w^T(G^0-G^D)w-9Z
      =Z(J_R-9)>0.                                  (UG4)

Thus even the exact deleted Gram matrix cannot make the certificate w^T(G^0-H)w<9Z succeed on this family under this lift. This is stronger than saying a particular fractional-private lower estimate was too small. It applies to every such owner choice while rho and the actual original indicators stay fixed.

The conclusion has precise limits. This original family is an irredundant noncover, not a hypothetical minimum whole cover. The result excludes deriving that certificate from the displayed head bound, odd distinct labels, divisor closure, comparable-class disjointness, private witnesses and uniform positive actual fibres ALONE. It does not refute a proof that uses additional whole-cover consequences, and it does not obstruct all supported laws. Keeping the same lambda and fixing every outside coordinate to2 gives W_3=T_H<3 and W_3^2=1600/729<9, as the zero mixed-completion law in section4 already implies.

### Full owners and projected actual private owners are different objects

A fixed actual owner partition can assign every deleted point to the first outside prime whose coordinate is zero. Put all3-free classes first; the original head classes have zero mass on lambda's support. Order the outside prime classes increasingly. The owner event for p has mass

    d_p=(1/p) product_(r<p)(1-1/r).

Conditional on it, earlier outside indicators have probabilities1/(r-1), the current indicator is zero, and later ones have probabilities1/r. Let m_p and v_p be the resulting conditional mean and variance of W_3. The same owner partition gives

    D_W=sum_p d_p(m_p^2+v_p),
    H_full[w]=sum_p d_p m_p^2,
    D_W-H_full[w]=sum_p d_p v_p.                    (UG5)

The exact controls give

    5.439810371312 < H_full[w] < 5.439810371313,
    1.315852011357 < D_W-H_full[w] <1.315852011358.

These owners include overlap points. They must not be identified with the actual private regions U_t in the Lettl–Sun rows.

For an outside prime class0 modp, project its ACTUAL private region vertically along the3^H-coordinate. Since all head originals are avoided, that region is nonempty only when p is the unique zero outside coordinate. The pure ternary comb has normalized Haar mass a=T_H/3=40/81. If N>0, all mixed ternary comb leaves are also present, leaving only the terminal prefix of mass1/81; if N=0, the available vertical mass is41/81. Thus the exact fractional-private density is

    eta_p(b)=1_[p is the unique outside zero]
                *[1/81+(40/81)1_[N=0]].             (UG6)

This formula retains the correlation between private mass and the original cofactor load. In particular the larger vertical private density occurs where that load is small.

Let q_p=E_rho eta_p and v_p^*=E_rho[eta_p W_3]. The projected-private Loewner credit is

    H_private[w]=sum_p (v_p^*)^2/q_p.

For an exact finite expression, put

    b_p=Z/(p-1), s_p=S_1-1/(p-1),
    z_p=product_(r!=p)(1-1/(r-1)), epsilon=1/81.

Then

    q_p=b_p(epsilon+a z_p),
    v_p^*=b_p T_H[epsilon(1+s_p)+a z_p].             (UG7)

The exact controls give

    0.178735778663 < H_private[w] <0.178735778664,
    0.197794573739 < sum_p E_rho[eta_p W_3^2] <0.197794573740.

The remaining private-credit gap separates exactly into unrepresented deleted weight and conditional variance within each private owner:

    D_W-H_private[w]
      =E_rho[(1_(R^c)-sum_p eta_p)W_3^2]
         +sum_p [E_rho(eta_p W_3^2)-(v_p^*)^2/q_p].  (UG8)

Both terms are nonnegative. Here the first lies between6.557867808929 and6.557867808930; the second lies between0.019058795076 and0.019058795077. Retaining partial-private intersections is valid, but it does not make the resulting debit large enough, even before accounting for the stronger exact obstruction(UG4).

All quantities above use rho and its full-source lift Uniform(Z/3^H) times rho. That full-source law is generally NOT uniform on the original period when lambda is nonuniform. Pointwise original-owner or shell identities can be integrated against it, but their previously computed Haar CRT capacities cannot be inserted unchanged. The values in(UG2),(UG5),(UG7) are recomputed under this ONE specified law.

The [standard-library program](../../../frontier/cover-geometry/original-cofactor-gram-uniform-lift/original_cofactor_gram_uniform_lift.py) and its [exact JSON data](../../../frontier/cover-geometry/original-cofactor-gram-uniform-lift/original_cofactor_gram_uniform_lift.json) evaluate these finite rational formulas, verify the disjoint first-zero owner decomposition against exact deletion, and verify every private-owner Cauchy–Schwarz contribution. It runs under python3 -I -S -B -O. It reuses section3's original-family construction and its existing702-private-witness verification; it does not claim another whole-period enumeration, new Lean verification, or an unrestricted odd-covering theorem.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-cofactor-gram-uniform-lift/original_cofactor_gram_uniform_lift.py
```

## 7. Original prime-private regions meet every hole line

The distinction between a countercontrol for a uniform lift and a whole cover has a pointwise witness. Let PS1 mean that every ENTIRE prime-power CRT coordinate line through every actual private point is covered. This is the private-to-hole nonadjacency condition of the [original-label interface](../../../../../../Library/Arith/lettlsun2008cosets.md); it concerns actual private points, not points assigned by an owner partition.

### A pure original at minimum positive height

Fix a nonempty finite irredundant family of literal original classes C_s=a_s mod m_s, of period L. Suppose a distinguished original C_t has modulus p^a for a prime p and a>=1, and

    p divides m_s => p^a divides m_s.                 (PR1)

Thus p^a is at the minimum positive p-height of the original inventory. This holds automatically if the original prime modulus p is present. Write L=p^H B with gcd(p,B)=1, let K be the p-prefix of C_t in Z/p^H, and let R_p be the cofactor residues modulo B avoiding every original p-free class. Then its ACTUAL private region is exactly

    U_t = K times R_p.                               (PR2)

Indeed a cofactor outside R_p is covered by a p-free original everywhere on its p-line. Above a cofactor in R_p, every other p-bearing original is disjoint from C_t: by(PR1) an intersecting class would be contained in C_t and would have no private point, contradicting irredundancy. This argument permits repeated numerical moduli when the original classes are irredundant; the odd-distinct application keeps the stronger numerical restriction.

Let Hole denote the actual hole set. Every h in Hole has its cofactor in R_p. Replacing its full p-coordinate by ANY member of K therefore produces a genuine private point of t while keeping every non-p coordinate fixed. Each hole has exactly p^(H-a) such private neighbors. Consequently

    Hole nonempty => an actual private-to-hole edge,
    irredundancy + PR1 => (PS1 iff whole coverage).   (PR3)

Only PS1 at U_t in direction p is needed for the forward implication. Whole coverage gives the reverse implication directly. This does not prove that a covering family cannot exist.

In particular, an irredundant PS1 noncover cannot contain an original prime modulus. If it contains a pure p^a, it must contain a p-bearing original at a strictly smaller positive p-height. A nonempty divisor-closed original set above one contains prime labels, so overlap cannot separate all private points from holes in an irredundant divisor-closed family.

The [extremal normalization](../../321-384/350-extremal-paired-branch-and-source-support.md) obtains divisor closure AFTER assuming a whole cover exists and minimizing first its cardinality and then its modulus sum. It does not normalize an arbitrary noncover while preserving noncoverage and PS1. No such transformation is supplied by(PR3).

### The height premise is sufficient, not necessary

A weaker sufficient condition for(PR2) is that every other p-bearing original be disjoint from C_t. The odd-distinct irredundant family 0 mod9,1 mod15 violates(PR1) at p=3, but its two first3-digits differ. Every point of0 mod9 is private, and every hole still resets to that class.

With the SAME numerical moduli and the changed residue6 mod15, the hole1 modulo45 instead resets to36, which belongs to both0 mod9 and6 mod15. This refutes an unconditional higher-pure reset; it does not make(PR1) necessary or rule out other private neighbors on that line. The difference is the actual phase relation, not the modulus inventory.

### One-law quantitative consequences

Under uniform probability mu on the original period, the product identity and containment of holes in K-complement times R_p give

    mu(U_t)=|R_p|/(p^a B),
    mu(Hole)<=(p^a-1)mu(U_t),
    number of Hole-to-U_t p-edges=|Hole|p^(H-a).      (PR4)

For ONE arbitrary cofactor law beta and an independent uniform p-coordinate, the same mass statements hold with beta(R_p) in place of |R_p|/B. They are not Haar constants for an arbitrary nonuniform p-coordinate. The pointwise reset is stronger than the mass inequality: PS1 requires the actual edge count to vanish, hence rules out every hole immediately under the stated hypotheses.

### The actual702-label family violates PS1 under every supported cofactor law

Keep all original classes of section3 and let nu be ANY probability supported on its actual3-free residual

    R_3 = S times product_(p in P)(Z/p minus{0}).

Use the SAME full-source law mu=Uniform(Z/81) times nu. The cofactor law need not be uniform or a product within its coordinates. The original0 mod3 class is present. Above every cofactor in R_3, all first3-digit0 points are private to this original: the3-free classes are absent, and the other3-bearing comb prefixes are disjoint from its first digit. This private slice has mu-mass exactly1/3.

At that same cofactor, the full3-coordinate80 avoids every pure and mixed ternary comb prefix. It is an actual hole, so the terminal-hole slice has mass1/81. Every point in the displayed prime3-private slice therefore violates PS1. Independently resampling the full3-coordinate while keeping the SAME cofactor gives

    P(old point private to0 mod3, new3-coordinate80)
      =(1/3)(1/81)=1/243.                            (PR5)

These constants apply to every nu supported on the stated R_3. They witness a missing whole-cover condition and do not invalidate the section6 Gram obstruction, which concerns this same noncover under its specified lift.

### Exact controls and reuse boundary

The [standard-library program](../../../frontier/cover-geometry/original-prime-private-reset/original_prime_private_reset.py) and [exact data](../../../frontier/cover-geometry/original-prime-private-reset/original_prime_private_reset.json) retain the original702-class input. They construct a literal integer hole with full3-coordinate80, head coordinates1 and all138 outside coordinates2. Resetting to every value in each original prime's0-root gives177 genuine private neighbors in141 prime directions. The124956 original-AP membership checks equal702 times(1+177); no whole-period enumeration is used.

The small controls include0 mod3,1 mod5,4 mod15, whose prime3 and prime5 private regions have4 and2 points among15, with7 holes; and0 mod9,1 mod45,2 mod175, whose pure9 region has174 private points among1575, with1357 holes. The last family has no prime label but satisfies(PR1) for pure9. The two same-modulus phase examples above verify the boundary of the sufficient condition.

[Report354](../../321-384/354-synchronized-prime-private-cofactor-matching.md)'s(SM3) already gives the prime-private Cartesian identity using only the original prime label, comparable-class disjointness and the p-free residual. Its subsequent coverage of every other root and tail, and synchronized matching, do use whole coverage. [Report357](../../321-384/357-original-private-swaps-and-prime-reset-transport.md)'s(PT6) starts at another original's private region, so a hole cannot be substituted into that statement literally. Its pointwise reset mechanism and(PT9)'s private-product identity supply the same reuse after the weaker premises are extracted; the hole argument above checks the changed source domain directly.

The higher pure-power case repeats that containment argument under(PR1). This is ordinary reuse and a same-law consequence, not a new Lean declaration or a claim of mathematical priority. For the conditional extremal divisor-closed #7 family, the remaining task is to turn the full coverage of these actual private fibres into a contradictory common arithmetic budget or a legal global transformation. Recovering whole coverage from PS1 does not itself provide that contradiction.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-prime-private-reset/original_prime_private_reset.py
```

## 8. Exact original owner defects and the prime-private capacity boundary

The actual owner partition in the [coset library](../../../../../../Library/Arith/lettlsun2008cosets.md), clauses(OB1)–(OB4) and(OS1)–(OS3), admits an exact linewise defect formula. Combined with the prime-private product identity from section7, it forces positive first-digit defect under distinct original moduli at every prime height. The resulting coarse whole-fibre capacity still does not contradict the private demand. Two explicit original families identify separate boundaries: positive local defects can exactly fit the remaining demand, and distinct numerical-cofactor matching need not distribute suppliers among different prime supports.

All results in this section use ordinary finite proofs and exact original-AP controls. No Lean verification or resolution of unrestricted Erdős #7 is asserted.

### 8.1 One original law and an exact owner-line identity

Let C_s be the ORIGINAL class a_s modulo m_s, with complete period

    L=product_p p^H_p.

Use the uniform probability mu on Z/L. Its global-top CRT decomposition is X=B times Q, where Q=product_p F_p, R=|Q|, and B retains all digits below each global top digit. Write beta for the uniform law on B, so mu=beta times Uniform(Q). These are two factors of one original law.

Fix one total order of original labels and define

    O_s=C_s minus union_(r<s)C_r,
    T_s={p:v_p(m_s)=H_p},
    Z_s=projection_B(O_s).

The owner sets O_s are disjoint and partition the actual covered union, even when the family is a noncover. At a fixed lower source z, an active original class is a hyperplane with support T_s and fixed phase theta_s. Two labels with the same support and phase define the same hyperplane there; the later one has no owned point in that fibre. In particular owner-positive labels of a fixed support have distinct phases.

For a support A put

    Y_A(z)=disjoint union_(s:T_s=A) O_s(z),
    n_A(z)=|Y_A(z)|,
    K_A(z)=#{s:T_s=A, z in Z_s},
    Omega_A(W)=(1/R) integral_W n_A(z) d beta(z).

Here W is any subset of B. For p in A, a p-line fixes every top coordinate other than p. Let h_(A,p)(z,ell)=|Y_A(z) intersect ell|. Each original with support A owns at most one endpoint of this line.

Let tau_(s,p) replace only the top p-digit by theta_(s,p), and define the actual replacement preimage

    F_(s,p)={x:x_p!=theta_(s,p), tau_(s,p)x in O_s}.

Let B_(A,p)(W) sum mu(W^up intersect F_(s,p) intersect F_(t,p)) over unordered original pairs s,t of support A whose phases differ only at p. Pairs with any other phase discrepancy have empty intersection. Two distinct owned endpoints on a p-line yield exactly p-2 common replacement bases, one at each of the other p-phases. Conversely every such pair of replacements recovers those endpoints. Therefore

    B_(A,p)(W)
      = (p-2)/R integral_W sum_(ell parallel p) binom(h_(A,p),2) d beta.
                                                               (OD1)

Define the nonnegative exact defect

    Delta_(A,p)(W)
      = (p-2)/(2R) integral_W sum_(ell parallel p)
                              h_(A,p)(p-h_(A,p)) d beta.

Since 2 binom(h,2)+h(p-h)=(p-1)h and sum_ell h=n_A,

    B_(A,p)(W)+Delta_(A,p)(W)
      = binom(p-1,2) Omega_A(W).                     (OD2)

For odd p, zero defect is equivalent to every relevant line having h=0 or h=p. At p=2 both the coefficient and the defect vanish, so this equivalence is not asserted.

Sum over A containing p and write B_p, Delta_p and Omega_p for the resulting quantities. Formula(OD2) gives the exact slack in(OS3). At a base point x, let

    k_(A,p)(x)=#{s:T_s=A, x in F_(s,p)},
    k_p(x)=sum_(A containing p)k_(A,p)(x)<=p-1.

There is at most one owner per replacement endpoint. Also integral k_p dmu=(p-1)Omega_p on W^up, and the pair service is integral sum_A binom(k_(A,p),2) dmu. Thus the same defect has the decomposition

    Delta_p(W)
      = (1/2) integral_(W^up) k_p(p-1-k_p) dmu
        + integral_(W^up) sum_(A<A') k_(A,p)k_(A',p) dmu.       (OD3)

The first term counts missing replacement supply; the second counts its division among different supports. Both refer to this same owner partition and source law.

### 8.2 Arithmetic inventory improves the cap but depends on the observed digit

Let lambda_A be the total number of original labels with global top support A. For any occupied support A,

    h_(A,p)<=min(p,lambda_A),
    B_(A,p)(W)
      <= (p-2)/2 [min(p,lambda_A)-1] Omega_A(W).       (OD4)

Retaining the actual lower source gives the source-dependent bound

    B_(A,p)(W)
      <= (p-2)/(2R) integral_W n_A(z)(K_A(z)-1)_+ d beta(z).
                                                               (OD5)

Under pairwise distinct original numerical moduli, their exponents at primes in A are fixed at H_p; at every q outside A there are H_q choices, namely 0 through H_q-1. Hence

    lambda_A<=product_(q outside A)H_q.              (OD6)

One useful source-local defect lower bound follows without replacing the owner sets. For a demanded prime set J, set

    g_J(z)=max_(A:K_A(z)>=2)
             K_A(z) sum_(p in A intersect J)(p-2)(p-K_A(z))_+,

with maximum zero when there is no eligible A. The inequalities h<=K_A and n_A>=K_A give

    sum_(p in J)Delta_p(W)
      >= (1/(2R)) integral_W g_J(z) d beta(z).        (OD7)

Indeed sum_ell h(p-h)>=(p-K_A)_+ n_A for each p in A, and any one support's contribution is bounded by the sum of all nonnegative support defects. A positive right side strictly reduces the old capacity; it need not place that capacity below the actual demand.

The choice of digit matters for applying these formulas to a prime-private region. An original prime modulus p has global top support {p} when H_p=1 and empty top support when H_p>1. At a lower source containing its private point, that prime class fills the entire global-top fibre in the latter case. The proper-hyperplane private-source argument cannot then be applied as though this were a top-touching prime target.

Alternatively expose the FIRST digit of every prime and keep every higher digit in the base. An original class is then inactive or a hyperplane whose support is the ordinary prime support supp(m_s). Formulas(OD1)–(OD5) remain valid with this carrier. But the distinct-modulus inventory becomes

    #{s:supp(m_s)=A}<=product_(p in A)H_p.            (OD8)

Each included prime now has H_p positive exponent choices and every excluded prime has exponent zero. The complement-height product(OD6) cannot be retained after this change. In particular the numerical cofactors distinguished by [Report354](../../321-384/354-synchronized-prime-private-cofactor-matching.md) can all have the same ordinary prime support.

### 8.3 An actual odd-distinct local equality control

Consider the following original classes:

| Modulus | Residue |
| ---: | ---: |
| 5 | 1 |
| 35 | 7 |
| 245 | 98 |
| 1715 | 1029 |
| 15 | 0 |
| 105 | 70 |
| 735 | 245 |
| 2401 | 1 |

Their complete period is L=36015=3*5*7^4, the lower modulus is343, and the top cardinality is R=105. The first four originals fix the four nonzero5-roots and have global top support {5}. The next three fix5-root zero and respectively the three3-roots, with support {3,5}. The last original makes the true7-height four and is inactive above z=0 modulo343.

At that specified lower source, the first seven classes tile the entire105-point top fibre disjointly. Every point in it is genuinely private. The full family is irredundant: in the displayed label order, private witnesses are

    6, 7, 98, 1029, 0, 70, 245, 2402.

Let V be just this fibre, of original mu-mass1/343. For a private point whose p-alternatives are covered, phi_p denotes the minimum of sum_A binom(n_A,2) over legal choices of one actual original supplier for each alternative, where n_A counts suppliers with support A. An actual owner choice is one such assignment.

Here every alternative has a unique supplier. At a {5}-owned point, three alternatives have support {5} and one has support {3,5}, giving phi_5=3. At a {3,5}-owned point, all four alternatives have support {5}, giving phi_5=6. Conditional on this V alone, the exact values are

| Quantity | Value |
| --- | ---: |
| Omega_5 | 1 |
| Mean phi_5 | 18/5 |
| Exact pair capacity B_5 | 18/5 |
| Exact defect Delta_5 | 12/5 |
| Original cap binom(4,2)Omega_5 | 6 |
| Inventory cap from(OD4) | 21/5 |

Thus demand plus the positive exact defect equals the old cap. The unnormalized original integrals are these values multiplied by1/343.

The only owner-positive collision supports are {5}, with K=4, and {3,5}, with K=3. Both meet the demanded prime, both have 2<=K<5, and every pair in either support differs in at most two top coordinates. The inventory inequalities hold:

    lambda_{5}=4<=H_3 H_7=4,
    lambda_{3,5}=3<=H_7=4.

Formula(OD7) has g_{5}=18 and conditional contribution18/(2*105)=3/35. Neither this positive contribution nor the stronger exact defect creates a strict demand/capacity contradiction.

The full original family has24811 holes and is not divisor-closed. Complete coverage here is only coverage of the specified top fibre. This refutes a deduction from the stated local conditions; it does not supply a whole odd-distinct cover or address an argument that additionally uses the full extremal hypothesis. V is not identified with the entire private union or all prime-private cofactors.

### 8.4 Prime privacy forces positive first-digit defect at every height

Assume a finite irredundant original family contains a designated prime class A_p, where p is odd. Use its complete period L=p^H B with gcd(p,B)=1 and the same fixed original owner order. Let R_p be the set of cofactors in Z/B avoiding all original p-free classes. The product identity from section7, [Report354](../../321-384/354-synchronized-prime-private-cofactor-matching.md) and [Report357](../../321-384/357-original-private-swaps-and-prime-reset-transport.md) gives

    Priv(A_p)={its first p-root} times {all p-tails} times R_p,
    V_p=(Z/p^H) times R_p,
    pi_p=mu(Priv(A_p)),
    mu(V_p)=p pi_p.                                  (PD0)

No whole-cover premise is needed here. Any other p-bearing original intersecting A_p would be contained in it and would have no private point. The p-free originals are absent exactly on R_p. Irredundancy gives pi_p>0.

Partition V_p into FIRST-p-digit lines, keeping every p-tail digit and all non-p coordinates fixed. Let h_ell be the number of endpoints owned by an original pure p-power label. Each line contains its genuine prime-private endpoint, so 1<=h_ell<=p. The pure-support case of(OD2) is

    Delta_p^pure(V_p)
      = (p-2)/(2L) sum_(ell subset V_p) h_ell(p-h_ell).

Since h_ell(p-h_ell)>=p-h_ell, writing Y_p for the actual pure-owner union yields

    Delta_p^pure(V_p)
      >= (p-2)/2 [mu(V_p)-mu(Y_p intersect V_p)].

Define the inventory sum over ORIGINAL LABELS, counting repeated moduli with multiplicity:

    T_p=sum_(s:m_s=p^e for some e>=1)1/m_s.

Each pure class depends only on the full p-coordinate. Therefore the one uniform product law and the union bound give

    mu(Y_p intersect V_p)<=T_p mu(V_p),
    Delta_p^pure(V_p)>=p(p-2)/2 (1-T_p)pi_p.          (PD)

The basic inequality permits repeated original moduli. Its right side is strictly positive when T_p<1. If each pure modulus p^e occurs at most once, then

    T_p<=(1-p^(-H))/(p-1),
    Delta_p^pure(V_p)
      >=p(p-2)/(2(p-1)) (p-2+p^(-H))pi_p>0.         (PD1)

Pairwise distinct ORIGINAL numerical moduli suffice for this premise. Divisor closure is unnecessary for the upper bound on T_p; when all pure powers up to H are present exactly once, that upper bound is attained. The result retains every tail digit and makes no assumption K_A<p.

The multiplicity condition cannot be silently discarded. The three classes0 mod3,1 mod3,2 mod3 form an irredundant complete partition. For the designated0 mod3 class, pi_3=1/3, V_3 is the full period, h=3 and Delta_3^pure=0. The actual label sum is T_3=1, so(PD) correctly gives zero. Collapsing the repeated modulus into one exponent would give the incorrect T_3=1/3 and false positive lower bound1/3.

This positive defect still does not close the coarse budget. Assume now whole coverage. On V_p all owners are p-bearing because its cofactors avoid every p-free original. Its coarse first-digit cap is therefore binom(p-1,2)mu(V_p). The actual owner assignment on Priv(A_p), followed by enlargement to V_p, and subtraction of the pure defect give only

    integral_(Priv(A_p)) phi_p^first dmu
      <=binom(p-1,2)mu(V_p)-Delta_p^pure(V_p)
      <=p(p-2)/2 (p-2+T_p)pi_p.                     (PD2)

The last upper bound is greater than the automatic pointwise ceiling binom(p-1,2)pi_p. Their difference is

    (p-2)/2 [p^2-3p+1+p T_p]pi_p>0,  p>=3.          (PD3)

Consequently(PD) combined only with this enlarged capacity cannot force a contradiction. A useful further estimate must preserve the actual prime-private centers or pay for the enlarged source through a compatible joint budget.

### 8.5 Divisor-closed numerical matching can coexist with maximal support collision

For any two distinct odd primes p,q, take the original inventory

    {p} union {q^j,p q^j:1<=j<=p-1}.

It is odd, numerically distinct and divisor-closed above one. Let

    A_p=0 modulo p,
    A_(q^j)=q^(j-1) modulo q^j,
    A_(p q^j)={x:x=0 modulo q^j, x=j modulo p}.      (MC1)

The last row specifies one literal CRT class for each original numerical modulus. The complete period is p q^(p-1).

The pure q-prefixes are pairwise disjoint. Comparable children have different p-roots, and a child's comparable pure q-parent is disjoint from it because that parent requires a nonzero q-prefix. The original prime p is disjoint from all children. These observations check every comparable pair.

Every original has a private point. Use the full CRT coordinates modulo p and q^(p-1): A_p uses(0,0); child j uses(j,0); and pure q^j uses(j,q^(j-1)). For the last witness, all other pure q-prefixes fail. Children of lower depth may meet its q-prefix, but have different p-roots; child j and all deeper children fail the q-prefix. Thus no competing original contains any of the stated witnesses.

At the actual full cofactor x_q=0, the complete p-fibre is privately covered by A_p and its p-1 children. The p-height is one, so this includes the entire original p-tail. The alternative roots give a synchronized matching of rank p-1 with distinct numerical cofactors

    q,q^2,...,q^(p-1).

All these suppliers nevertheless have ordinary prime support {p,q}. At the actual prime-private root every alternative has its unique child supplier, hence

    phi_p^first=binom(p-1,2),                        (MC2)

the maximal support-assignment cost. Distinct cofactor colors do not imply different support bins, even with original parents, divisor closure and genuine private witnesses.

The family is an explicit noncover: the full coordinates(1,2) miss the prime p, every pure q-prefix and every child. Complete p-fibre coverage is asserted only at cofactor zero, not throughout R_p. The latter condition would imply whole coverage by section7 and is not satisfied here.

### 8.6 Exact finite controls and the remaining joint inequality

The [owner-line program](../../../frontier/cover-geometry/original-owner-line-defect/original_owner_line_defect.py) and [exact owner-line data](../../../frontier/cover-geometry/original-owner-line-defect/original_owner_line_defect.json) reconstruct original residue membership, one owner partition, all lower sources and complete top lines. They check the line and inventory formulas on the eight-class period36015 noncover, the distinct even period60 whole cover, and the complete repeated-modulus15 partition. The last two are controls of the stated incidence formulas, not odd-distinct covering candidates. The repeated15 partition attains the old cap with zero exact defect for both3 and5; the p=2 calculation in the even control makes no zero-defect characterization claim.

The [matching and prime-defect program](../../../frontier/cover-geometry/original-matching-support-boundary/original_matching_support_boundary.py) and [exact matching data](../../../frontier/cover-geometry/original-matching-support-boundary/original_matching_support_boundary.json) enumerate these instances of(MC1):

| p,q | Period | Holes | Matching rank | Support cost | pi_p | mu(V_p) | Pure defect |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3,5 | 75 | 33 | 2 | 1 | 19/75 | 19/25 | 19/75 |
| 5,3 | 405 | 142 | 4 | 6 | 41/405 | 41/81 | 82/135 |
| 7,3 | 5103 | 2005 | 6 | 15 | 365/5103 | 365/729 | 1825/1701 |

The defects are unnormalized integrals under the original probability mu; they need not be bounded by one because their integrands include combinatorial factors. Each displayed pure defect attains(PD). An additional higher-pure control0 mod3,1 mod9,2 mod27 has one first-digit line with h=3, two with h=2 and six with h=1. Its exact defect is8/27, above the(PD) lower bound7/27. The repeated pure-modulus3 partition records the necessary multiplicity boundary explicitly.

Both programs use exact integer and rational arithmetic and complete successfully with Python optimization enabled:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-owner-line-defect/original_owner_line_defect.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-matching-support-boundary/original_matching_support_boundary.py
```

The line identity refines the existing owner cap; prime privacy supplies a uniform positive pure-owner defect under distinct moduli. The two countercontrols explain why neither that positivity alone nor numerical matching alone forces the required strict inequality. The unresolved obligation is a joint estimate on the same original private centers and owner partition, using whole-cover supply to make demand exceed a compatible arithmetic capacity. No sum of independently optimized laws or replacement of numerical cofactors by their supports discharges it.

## 9. Whole coverage needs weighted excess of distinct projected phases

This ordinary finite argument retains every original numerical modulus and every finite prime-power height. It gives a necessary whole-cover demand and a sufficient noncoverage criterion. It does not supply the common outside law meeting that criterion for an arbitrary original family, and is not Lean verification.

Let the original distinct odd moduli greater than one be m_i=b_i d_i, where d_i has all its prime factors in B={3,5,7}, and b_i is coprime to3*5*7. Split the full CRT carrier as X_A times X_B, at the maximum original heights in each coordinate. Write the original cylinder as C_i^A times C_i^B. An absent coordinate has a singleton carrier. Let

    V_A = X_A minus union_(i:d_i=1) C_i^A.

For d>1 and r modulo d, merge the original outside events carrying the SAME projected phase:

    E_(d,r) = union_(i:d_i=d, a_i^B=r mod d) C_i^A,
    E_d = union_r E_(d,r),
    R_d(y) = #{r mod d : y in E_(d,r)}.

All sums over d below are over the finitely many retained numerical moduli that occur. R_d counts distinct active residues; several original labels with the same(d,r) contribute once. This merging does not declare their other weighted-label obligations interchangeable.

The set V_A is nonempty by the published [Hough--Nielsen Theorem1](https://arxiv.org/html/1703.02133v2), already used in [Report526](../500-549/526-supported-unit-mixtures-control-the-sum-of-all-original-responses.md). The A-only originals have d_i=1, so b_i=m_i>1; their numerical moduli remain pairwise distinct and are all coprime to6. If they covered X_A, periodicity and CRT would give a distinct integer cover with no modulus divisible by2 or3, contradicting that theorem. An empty A-only inventory leaves all of X_A. This is direct reuse of a published theorem, not a new proof or Lean result. It guarantees an outside-supported probability exists, but supplies no bound on its merged phase excess.

### 9.1 A distinct retained core has a uniform positive reserve

Take any finite B-family with at most one residue for each numerical modulus greater than one, at arbitrary heights. For each p in B, remove all its pure p-power classes. Distinct numerical moduli allow at most one class for each exponent. The surviving fraction s_p of the complete p-coordinate satisfies

    s_p >=1-sum_(e>=1)p^(-e)=(p-2)/(p-1).

The product of these actual pure-coordinate survivors has Haar mass at least5/16. Give it the product uniform law rho. For a fixed exact mixed support T contained in B, the full exponent vectors of the numerical moduli are distinct. Its total class mass is bounded by

    sum_(support(d)=T) rho(C_d)
      <=product_(p in T)[(1/s_p)sum_(e>=1)p^(-e)]
      <=product_(p in T)1/(p-2).

The four possible mixed supports together cost at most

    1/3+1/5+1/15+1/15=2/3.

Thus the core complement U has

    rho(U)>=1/3,     H_B(U)>=5/48.                 (PE1)

This uses the same actual pure-survivor and exponent-vector mechanism as the [support-incidence theorem](../../../problem-details/50-prime-support-incidence-at-most-five.md). Neither constant is asserted sharp. Missing classes, empty pure inventories and arbitrary finite heights are included.

### 9.2 Extra phases must cover that reserve

Suppose the original family is a whole cover, and fix y in V_A. No A-only original covers this y, so all active retained classes have d>1 and jointly cover X_B. Choose one active residue r_d for each active numerical d. These choices form a distinct-modulus core to which PE1 applies. Its holes must be covered by the remaining active phases. Their number at modulus d is exactly(R_d(y)-1)_+.

Each excess phase has Haar mass1/d. Under the chosen core's pure-survivor law it has mass at most

    omega_B(d)=product_(p^e || d) (p-1)/((p-2)p^e).

Consequently every y in V_A obeys

    F_H(y):=sum_d (R_d(y)-1)_+/d >=5/48,           (PE2)
    F_S(y):=sum_d omega_B(d)(R_d(y)-1)_+ >=1/3.   (PE3)

The core and its pure-survivor law may depend on y. The uniform cylinder upper bound omega_B removes that dependence from PE3; no single retained source valid for all y is claimed. Since omega_B(d)<=(16/5)/d, PE3 also implies PE2. These demands cannot be added as independent budgets.

In particular a whole cover requires at least two distinct active phases for some retained d at every y in V_A. If D_A is the union of C_i^A intersect C_j^A over pairs with d_i=d_j>1 and different retained residues, then V_A is contained in D_A. This is a phase condition: duplicate original occurrences of one retained phase do not suffice.

### 9.3 One outside law keeps the subtraction and all original correlations

For any one finite positive measure eta on X_A, pointwise indicator arithmetic gives the exact identity

    integral_(V_A) (R_d-1)_+ d eta
      =sum_r eta(V_A intersect E_(d,r))
         -eta(V_A intersect E_d).                  (PE4)

Therefore whole coverage implies, under that SAME eta for every d and phase,

    sum_d [sum_r eta(V_A intersect E_(d,r))
             -eta(V_A intersect E_d)]/d
       >=(5/48)eta(V_A),                           (PE5)

    sum_d omega_B(d)[sum_r eta(V_A intersect E_(d,r))
             -eta(V_A intersect E_d)]
       >=(1/3)eta(V_A).                            (PE6)

If eta(V_A)>0 and either inequality is violated, the original family is not a whole cover. Equivalently, one normalized eta supported on V_A with integral F_H<5/48 or integral F_S<1/3 is sufficient. Nonemptiness of V_A follows from Hough--Nielsen as above; constructing one law attaining either strict bound remains an additional obligation. If eta(V_A)=0, the displayed necessary demands are vacuous.

The subtraction in PE4 allows one active phase per numerical modulus for free. Replacing it by original-pair intersections is only a majorant:

    (R_d-1)_+ <= choose(R_d,2)
      <=sum_(i<j:d_i=d_j=d, a_i^B!=a_j^B)
           1_(C_i^A intersect C_j^A).

For such a pair, choose delta_ij congruent to a_j^B-a_i^B modulo d, and translate only the retained coordinate by it. Full retained Haar gives the exact transported overlap

    (eta times H_B)(C_i intersect tau_delta_ij^(-1)(C_j))
      =eta(C_i^A intersect C_j^A)/d.                (PE7)

The shifts can be chosen coherently: for each d fix a reference phase, choose one lift of each original label's phase difference from that reference, and use differences of those label shifts for delta_ij. This represents incompatible retained phases by aligned overlap, but supplies no upper bound on the sum. Distinct original numerical moduli imply that a useful pair with the same d must have DIFFERENT b. A fixed-b Gram estimate therefore does not directly pay for these useful cross-b pairs. Any use of a non-Haar retained law needs its own transport identity and cannot substitute PE7 unchanged.

### 9.4 Complete outside collision can coexist with insufficient phase mass

Set p=11,q=13 and index the143 outside points t=(u,v). Give each its own retained modulus

    d_t=3^(1+t)5^(143-t),     t=0,...,142.

Include two original classes per point: modulus p*d_t with outside phase u and retained phase0, and modulus q*d_t with outside phase v and retained phase1. The286 numerical moduli are odd, distinct and pairwise incomparable: the3-exponent increases while the5-exponent decreases, and the p/q cofactors differ.

At y=(u,v), exactly its own d_t has both retained phases active. Every other active d has one phase. Thus

    D_A=X_A,     V_A=X_A,
    F_H(y)=1/d_t<5/48,
    F_S(y)=(8/3)/d_t<1/3.

No collision-free outside point exists, yet PE2 or PE3 excludes whole coverage. The literal integer2 is also a direct hole because all retained phases are0 or1 at moduli greater than2. This family already belongs to the support-incidence theorem's range; its purpose is to refute the stronger requirement that a successful outside law must avoid every collision. The quantitative criterion needs only insufficient excess phase mass.

### 9.5 Merging phases can succeed when the same-law original-pair bound fails

Let Q={11,13,17,19,23}. Include pure3,9,27 with residue0 and, for q in Q and e,h in{1,2,3}, the original modulus3^e*q^h with retained phase1 modulo3^e and outside phase0 modulo q^h. Pure5 and7 at residue0 may also be included. There are no A-only originals, so V_A=X_A; use one outside Haar law eta.

The useful original pairs are each pure3^e label paired with its same-e mixed labels. Their source-weight energy is

    (sum_(e=1..3)2/3^e)(sum_(q in Q,h=1..3)1/q^h)
      =277120755748135798/830038705801515639 >1/3.

At fixed e, the phase1 events with q-heights1,2,3 are nested. Merging the events leaves precisely the event that at least one outside coordinate is0 modulo its prime. Hence under the SAME eta,

    integral F_S d eta
      =(26/27)(1-product_(q in Q)(1-1/q))
      =54914/200583 <1/3,                          (PE8)

with margin11947/200583. The merged functional certifies noncoverage where its raw-pair majorant cannot do so under this law.

This is also a scope control: the only mixed exact supports are the five sets{3,q}, so the global support-incidence-at-most-five theorem already applies. An additional sufficient criterion demanding small pair energy does not automatically contain that entire established class. Some larger-incidence families may satisfy such a criterion; that is a complementary range, not a containment claim.

### 9.6 The phase-balanced transport obstruction has zero merged excess

The raw-transport obstruction of [Report525](../500-549/525-phase-balanced-originals-defeat-all-outside-laws-and-groupings.md) does not obstruct this merged functional. Take its three-prime family alone: H>=0, K>=1 are integers, q ranges over{23,29,31}, and for1<=i<=Kq use the original modulus and fixed CRT phase

    m_(q,i)=3^(H+i)q,
    a_(q,i)=1 mod3^(H+i),   a_(q,i)=i modq.

These83K odd numerical moduli are pairwise distinct. For the present retained set B={3,5,7}, their retained modulus is d_i=3^(H+i) and their outside cofactor is q. There are no A-only originals, so V_A=X_A. At every fixed d_i, every original has the SAME retained phase1. Consequently E_(d_i,1) is a union of its actual outside cylinders, all other phase events are empty, and

    R_(d_i)(y)<=1,
    F_H(y)=F_S(y)=0  for every y in X_A.            (PE9)

This is compatible with Report525's failure of every outside-law raw transport when13K>H+1: that expense counts original labels whose retained phases have already been merged in PE9. The family was already known to be noncovering, since its whole union lies in1mod3^(H+1). PE9 identifies why that method counterexample does not defeat the present phase-excess account; it is not a new unrestricted covering result.

There is also a direct phase-free estimate for this same finite numerical inventory. Replace each retained phase1 by an arbitrary fixed alpha_(q,i) modulo3^(H+i), keeping its outside phase i modq. At each d_i there are at most three original labels, and hence at most three distinct active retained phases, regardless of outside correlations. Since d_i is a pure power of3,

    omega_B(d_i)=2/d_i.

More precisely there are three labels for i<=23K, two for23K<i<=29K and one thereafter. Thus, pointwise for EVERY outside y,

    F_S(y)
      <=4 sum_(i=1..23K)3^(-H-i)
          +2 sum_(i=23K+1..29K)3^(-H-i)
       =3^(-H)[2-3^(-23K)-3^(-29K)]
       <2*3^(-H).                                 (PE10)

The finite sum is bounded above by the corresponding infinite geometric sum; no tail is inserted as an actual original. For H>=2, PE10 is strictly below2/9<1/3. Every outside probability law therefore meets the PE3 sufficient bound for these83K originals, with their retained phases chosen once and arbitrarily. The raw transport obstruction, when13K>H+1, is unchanged because its calculation uses the original numerical cofactors and outside phase cycles, not these retained residues.

This calculation includes no additional unit originals, retained core, or other nonunit labels. Their support restrictions and phase-excess contributions require their own common-law accounting. The bridge concerns the already explicit Report525 inventory: merging actual equal phases and weighting the remaining excess by its retained depth avoids the raw-label obstruction without asserting that an arbitrary original family has a small-excess law.

### 9.7 Remaining upper-bound obligation

PE1--PE6 apply to arbitrary retained heights and all original outside labels. Their advance is a precise target: obtain one compatible outside law for which the MERGED distinct-phase excess cannot cover the retained reserve. Whole coverage supplied the lower demand, not the contradictory upper bound. The latter must still be derived from actual arithmetic, common-source or minimality relations. Qualitative outside survival is supplied by Hough--Nielsen, but a small phase-excess law does not follow from that existence result alone.

The [phase-excess controls](../../../frontier/cover-geometry/merged-phase-excess/merged_phase_excess_controls.py) and [exact output](../../../frontier/cover-geometry/merged-phase-excess/merged_phase_excess_controls.json) check the constants,130 finite distinct cores on period315, the286-label deep-collision family on all143 outside points, its literal integer2 hole, the merged identity under one nonuniform eta, and the strict same-law comparison PE8. The finite checks are not a proof of the arbitrary-height reserve, which is supplied by section9.1, and no unrestricted odd noncoverage result follows here.

## 10. Anchor phases give a same-law arithmetic supplier

This ordinary finite argument continues section9 with the SAME original family m_i=b_i d_i and complete original-height carriers X_A times X_B, where B={3,5,7}. It supplies a sufficient condition for one outside law with zero merged phase excess. The ingredients are product conditioning, numerical exponent-vector distinctness and the union bound; no new general probability method or Lean verification is claimed. Original heights, numerical moduli, residues and owners are retained throughout.

### 10.1. One anchor per retained numerical modulus

For every appearing numerical d>1 choose one residue alpha_d modulo d. If a pure-B original has b_i=1 and d_i=d, REQUIRE alpha_d=a_i^B. There is at most one such original at any d because the original numerical moduli are distinct. Call an original bad when

    i in J_alpha iff d_i=1
       or (d_i>1 and a_i^B!=alpha_(d_i) mod d_i).

Thus all A-only originals are bad. All originals with the chosen retained phase are free, including arbitrarily many labels with different numerical outside cofactors. The forced choice at pure-B originals ensures that no bad label has b_i=1. Without it an empty-support outside bad event would equal the whole X_A and escape the sums below.

Define the actual outside avoidance set

    Omega_alpha = X_A minus union_(i in J_alpha) C_i^A.

At y in Omega_alpha there is no active A-only original, and for each numerical d>1 all active originals have phase alpha_d. After merging identical retained classes, this is a distinct-modulus B-core. By PE1 its complement is nonempty. Therefore

    Omega_alpha nonempty implies original noncoverage;
    F_H(y)=F_S(y)=0 for every y in Omega_alpha.      (AP1)

The assertion uses one actual y with all original constraints together. It is not a selection of separate favorable y values for different d.

### 10.2. A fixed retained d pays every outside height in one row

For p in A let P_p^alpha be the union in X_p of all bad projected cylinders with outside support exactly{p}. Put

    S_p^alpha = X_p minus P_p^alpha,
    s_p^alpha = H_p(S_p^alpha),

where H_p is uniform on the full ORIGINAL p-power carrier. Suppose every s_p^alpha>0 and use ONE product source

    rho_alpha = product_(p in A) H_p(. | S_p^alpha).

It avoids every pure-support bad event pointwise. For each mixed outside support E, |E|>=2, put

    D_E^alpha = {d_i : i in J_alpha, support(b_i)=E},
    N_E^alpha = |D_E^alpha|,
    z_p^alpha = 1/((p-1)s_p^alpha),
    Phi_alpha = sum_(E:|E|>=2) N_E^alpha product_(p in E) z_p^alpha.

The value d=1 is included in D_E^alpha when A-only originals occur on E. The coefficient N_E counts different retained NUMERICAL moduli, not original labels or distinct phases.

Fix one E and one d in D_E^alpha. Write b_i=product_(p in E)p^(e_(i,p)). At this fixed d, distinct original numerical m_i=b_i d imply distinct outside exponent vectors. For each actual original cylinder,

    rho_alpha(C_i^A)
       <=product_(p in E) p^(-e_(i,p))/s_p^alpha.

Summing its finite actual row and enlarging to all positive exponent vectors gives

    sum_(i in J_alpha:d_i=d,support(b_i)=E) rho_alpha(C_i^A)
       <=product_(p in E) [(1/s_p^alpha) sum_(e>=1) p^(-e)]
       =product_(p in E) z_p^alpha.                (AP2)

This is an upper bound on actual finite data. It inserts neither a new original class nor a new residue at an unoccupied height. Different retained d values are counted separately by N_E; numerical distinctness does not remove that remaining multiplicity.

The union bound over those rows, all under the SAME rho_alpha, now gives

    rho_alpha(Omega_alpha)>=1-Phi_alpha.

Consequently

    all s_p^alpha>0 and Phi_alpha<1
       imply eta_alpha=rho_alpha(. | Omega_alpha) exists,
       eta_alpha(V_A)=1,
       integral F_H d eta_alpha=integral F_S d eta_alpha=0,
       and the original family is not a whole cover. (AP3)

Conditioning is performed once on the common global event Omega_alpha. The zero-excess conclusion is pointwise on its support. This is an outside-law supplier for section9; it need not preserve a separately prescribed 1225 head marginal and is not a proof of the arbitrary-cofactor Gram lift from sections1--6.

If A is empty, there are no bad originals after the forced pure-B choices. Interpret the product source on its singleton carrier and Phi_alpha=0; AP1 reduces directly to the retained-core theorem.

### 10.3. A degree48 sufficient condition with a positive reserve

An explicit uniform specialization of AP3 uses the additional pure-event hypothesis

    H_p(P_p^alpha)<=1/(p-1),  for every p in A.     (AP4)

It gives s_p^alpha>=(p-2)/(p-1) and z_p^alpha<=1/(p-2). One sufficient way to check AP4 is that, after merging identical pure-support bad projected classes, each outside modulus p^e has at most one bad residue. This extra property does NOT follow from distinct original numerical moduli: distinct retained d values can project to different bad residues at the same p^e. The exact pure union mass in AP4 is weaker than that convenient one-residue condition.

Define the bad retained-depth incidence

    D_alpha=max_(p in A) sum_(E contains p, |E|>=2) N_E^alpha,

with D_alpha=0 if A is empty. This is a weighted incidence: a support with N_E retained numerical rows contributes N_E at each of its primes.

Every p in A is at least11. With beta_p=1/(p-2)<1 and |E|>=2,

    product_(p in E) beta_p <= (1/2)sum_(p in E) beta_p^2.

For a pair this is 2ab<=a^2+b^2. For larger E, discard all but two factors first and then enlarge the sum. Therefore

    Phi_alpha <=(D_alpha/2) sum_(p>=11 prime) 1/(p-2)^2. (AP5)

An elementary exact bound for the entire infinite prime sum is

    Q = sum_(p in P97) 1/(p-2)^2
        +1/2520+1/2580+1/2700+1/2760
        +1/2880+1/3060+1/3120+1/3300
      =25333216947944940335217017219727643
         /619258216451156108309703080921860800
      <1/24,

where

    P97={11,13,17,19,23,29,31,37,41,43,47,
         53,59,61,67,71,73,79,83,89,97}.

To justify the infinite tail, every prime above97 lies in one of the eight reduced residue classes modulo30. Bound each entire progression 30k+r beyond97, allowing its composite members:

| r | first k | first integer | tail upper bound |
|---|---:|---:|---:|
| 1 | 4 | 121 | 1/3120 |
| 7 | 4 | 127 | 1/3300 |
| 11 | 3 | 101 | 1/2520 |
| 13 | 3 | 103 | 1/2580 |
| 17 | 3 | 107 | 1/2700 |
| 19 | 3 | 109 | 1/2760 |
| 23 | 3 | 113 | 1/2880 |
| 29 | 3 | 119 | 1/3060 |

For a=30k+r-2, the centered-cell integral of (30x+r-2)^(-2) on[k-1/2,k+1/2] equals 1/(a^2-225)>1/a^2. Summing those cells from the stated first k to infinity yields the table. In particular composites such as119 are harmless enlargements. This proves the infinite estimate; a finite list of tested primes would not do so.

Under AP4 and D_alpha<=48, AP5 gives Phi_alpha<=24Q<1. AP3 supplies one zero-excess law, with the explicit common product-source reserve

    rho_alpha(Omega_alpha)>=1-24Q
       =469208737519897511020611152016557
          /25802425685464837846237628371744200
       >0.01818467547.                              (AP6)

The constant48 is a sufficient threshold, not an optimality claim. The exact criterion AP3 can succeed when AP4 fails.

### 10.4. Collisions may remain: a dominant-phase upper test

Complete anchor avoidance is stronger than section9 needs. For any ONE probability eta supported on V_A and nonnegative weights w_d, let F_w=sum_d w_d(R_d-1)_+. The merged indicator identity gives

    integral F_w d eta
       =sum_d w_d[sum_r eta(E_(d,r))-eta(E_d)]
       <=sum_d w_d[sum_r eta(E_(d,r))-max_r eta(E_(d,r))]. (AP7)

The maximum chooses one deterministic free phase at each d after fixing eta. It does not change the law from one d or query to another. The subtraction remains a whole SAME-PHASE UNION, not a sum of independently optimized original labels.

For a source sigma not yet supported on V_A, retain s=sigma(V_A)>0 and put Q_(d,r)=sigma(V_A intersect E_(d,r)). Applying AP7 to eta=sigma(.|V_A), noncoverage follows from either

    (1/s)sum_d [sum_r Q_(d,r)-max_r Q_(d,r)]/d <5/48,

or

    (1/s)sum_d omega_B(d)[sum_r Q_(d,r)-max_r Q_(d,r)] <1/3. (AP8)

These are alternative sufficient inequalities, not additive credits. They permit phase collisions at every outside point. AP3 is the special supplier making every nonanchor phase term zero. No unrestricted upper bound in AP8 is established here.

### 10.5. Two actual families show the criteria have different scopes

For a high-incidence family take ten outside primes Q={11,13,17,19,23,29,31,37,41,43}. For each three-element subset E of Q include the original modulus3*product_(q in E)q with retained phase0 modulo3 and outside residues0. Add the original3*product_(q in Q)q with retained phase1 and all outside residues0. All121 moduli are odd and distinct.

With alpha_3=0, only the last original is bad. There are no bad pure supports, N_Q=1 and D_alpha=1, so AP4 and the degree48 criterion hold. The retained prime3 belongs to121 distinct exact original supports; each q belongs to C(9,2)+1=37. Thus the old global support-incidence-at-most-five hypothesis does not hold. Each triple-support anchor has a private witness by setting exactly its three outside coordinates to0 and the others to1, with retained coordinate0. The large class has a private witness at retained coordinate1. Retained coordinate2 misses the whole family. This is a noncover diagnostic establishing scope separation, not evidence of an odd cover or an unrestricted theorem.

Conversely, for e=1,...,120 include two originals with retained modulus d=3^e, outside cofactors11*13 and11^2*13, retained phases0 and1 respectively, and all outside residues0. All240 numerical moduli are distinct, while there is only one exact original mixed support{3,11,13}; its global support incidence is1.

Every possible anchor at each d leaves at least one bad original. There are no pure outside bad events, so s_11=s_13=1, while N_{11,13}=120. Consequently every anchor has

    Phi_alpha=120/((11-1)(13-1))=1.

AP3's strict condition fails for every anchor, even though y_11=1 avoids every original outside cylinder. This demonstrates both reverse noncontainment and nonnecessity: the existence of a collision-free outside point does not imply Phi_alpha<1. The degree48 and old global-degree-five sufficient classes are incomparable. Their failures concern these estimates, not noncoverage itself.

The exact criterion also recovers section3's known successful law on the702-label uniform-lift diagnostic: choose the pure ternary phases as anchors. At each outside p the bad pure projections forbid0 and1, so s_p=(p-2)/p>0, while there are no mixed outside bad supports and Phi_alpha=0. The one outside product law conditioned on y_p notin{0,1} has zero phase excess. Here 2/p>1/(p-1), so AP4 fails although AP3 succeeds. This is reuse of that diagnostic's successful phase-aware lift, not a new analysis of its second moment.

### 10.6. Literature interfaces and the remaining arithmetic condition

Hough--Nielsen Theorem1 already supplies V_A nonempty, as explained in section9. Prime-support minimality is not needed for that fact. It provides no bound on Phi_alpha or AP8.

Theorem4 of [Hough--Nielsen](https://arxiv.org/abs/1703.02133) allows finite residue SETS at each numerical modulus. The bad outside family can be grouped in that form even when different original labels project to the same b. A nonnegative supersolution to its displayed inequalities is still a premise to prove. Its equation(6) states queries in the supplied modulus inventory; extending to additional queries needs the corresponding extension argument. AP2--AP6 bypass such a supersolution only for their stated sufficient class.

[Scott--Sokal Theorem4.1](https://arxiv.org/abs/cond-mat/0309352) can improve a union-bound supplier when its conditional nonneighbor bounds and strict Shearer-region membership hold. Under rho_alpha, disjoint-support events are independent, so the support-intersection graph is available. The required positivity is for the relevant induced-subset polynomials; positivity of just one full endpoint polynomial does not suffice. No such universal positivity is supplied here.

The staged distorted-measure method of [BBMST](https://arxiv.org/abs/1811.03547) is another candidate interface, but its quoted simplified numerical-modulus moment bounds do not automatically apply to a projected family with repeated b and several residues. Required label/tuple multiplicities and moment estimates under the STAGED distorted laws must be checked. In particular AP2 is proved under the particular PRODUCT rho_alpha and cannot be carried unchanged to those distorted laws. These are missing interface obligations, not a claimed application already completed.

The [squarefree parallel-hyperplane theorem](https://arxiv.org/abs/1901.11465) has its own odd-prime product-box and proper-support hypotheses. It supplies no arbitrary-height extension of AP3. The present construction permits arbitrary finite original heights because it retains them and explicitly sums their distinct exponent vectors.

The unresolved arithmetic issue is now explicit: original distinctness pays all outside cofactors within a fixed retained d, but does not by itself control the repetition N_E across different d, the actual pure survivor masses s_p, or the weaker weighted dominant-phase deficits. Section11 below retains the weights before summing retained depths and supplies further sufficient classes, but no implication from unrestricted whole-cover minimality or private witnesses to a successful anchor or an AP8 bound has been proved. The240-label example also prevents treating AP3 as a necessary description of successful outside laws. The unrestricted odd-covering goal remains open in this route.

### 10.7. Exact finite controls

The exact rational controls verify the prime-tail constants and reserve, the two scope-separation families, each fixed-d row bound in one actual CRT source, and the merged subtraction identity under one common product law. The actual12-label CRT source has full outside heights11^2 and13, pure survivor masses98/121 and12/13,1176 product-source points and1142 points after all bad events are removed. Its values are

    rho_alpha(Omega_alpha)=571/588,
    Phi_alpha=1573/47040.

Every retained outside point avoids A-only originals and has zero distinct-phase excess. Its pure-event mass at11 violates AP4, while AP3 succeeds, checking the distinction between exact and simplified suppliers. These finite tests are controls of the stated formulas; the proofs of arbitrary finite heights and the infinite tail are the arguments above, and no Lean or unrestricted whole-cover result is inferred from the controls.

The [anchor-phase controls](../../../frontier/cover-geometry/merged-phase-excess/anchor_phase_controls.py) and [exact output](../../../frontier/cover-geometry/merged-phase-excess/anchor_phase_controls.json) retain these finite checks. Run the program with an explicit `--output` path.

## 11. Retained weights pay arbitrary depth multiplicity under one outside law

This continues sections9--10 with the original finite distinct odd moduli, full original heights, numerical retained moduli and phase unions unchanged. The result is a sufficient ordinary mathematical criterion. It allows phase collisions and arbitrarily many retained numerical depths on one outside support, but requires the stated common-source and incidence bounds. It is not an unrestricted noncoverage theorem or a Lean result.

### 11.1. Weighted rows under an actual cylinder-cap source

For each occurring d>1 fix an anchor phase alpha_d, forced to be the original retained phase if a pure-B original with b_i=1 occurs. There is at most one such original at each d. Define the NONANCHOR depth set of a nonempty outside support E by

    D_(E,+)^alpha = {d>1: some original i has d_i=d,
                     support(b_i)=E, a_i^B!=alpha_d},
    W_E(w) = sum_(d in D_(E,+)^alpha) w_d,

where all w_d are nonnegative. The plus sign distinguishes this set from AP2's D_E^alpha, which can also contain the A-only row d=1.

Let sigma be ONE probability on the full actual outside carrier, and suppose

    s=sigma(V_A)>0,   eta=sigma(. | V_A).

Suppose nonnegative c_(p,e) bound every actual original outside cylinder by

    sigma(C_i^A)<=product_(p in support(b_i)) c_(p,e_(i,p)),
    Lambda_p=sum_(e>=1)c_(p,e)<infinity.

Only actual finite-height cylinders need such bounds; values above the carrier's maximum original height may be zero or any larger summable majorant. Sigma need not be a product measure. Then

    integral F_w d eta
      <= (1/s) sum_(nonempty E) W_E(w) product_(p in E) Lambda_p,
    F_w(y)=sum_(d>1)w_d (R_d(y)-1)_+.             (WR1)

Indeed, pointwise,

    (R_d-1)_+ <= sum_(r!=alpha_d) 1_(E_(d,r)).

The inequality holds even when the chosen anchor is inactive: in that case its right side is R_d. Integrate under eta, union-bound the actual originals in each nonanchor phase, and use eta(C)<=sigma(C)/s. At a FIXED numerical d and outside support E, distinct original m_i=d b_i imply distinct full positive exponent vectors of b_i. Thus

    sum_(i:d_i=d,support(b_i)=E,a_i^B!=alpha_d) sigma(C_i^A)
       <=sum_((e_p) in positive integers^E) product_(p in E)c_(p,e_p)
       =product_(p in E)Lambda_p.

Multiplying by w_d and summing gives WR1. The forced pure-B anchor ensures no nonanchor cylinder has empty outside support. No distinctness is asserted after varying d or projecting away its numerical value.

### 11.2. One shared envelope can replace many same-phase supports

For each nonanchor(d,r), let A_(d,r) be a finite family of actual outside events with controlled sigma masses. Assign nonnegative gamma_(d,r,A) such that EVERY original i at that phase obeys

    sum_(A: V_A intersect C_i^A subset A) gamma_(d,r,A)>=1.

For y in V_A intersect E_(d,r), choose one original cylinder containing it. Every envelope in the displayed sum contains y, so

    1_(E_(d,r))(y)<=sum_A gamma_(d,r,A)1_A(y).

The same pointwise excess bound therefore gives

    integral F_w d eta
       <=(1/s)sum_(d>1)w_d sum_(r!=alpha_d)
                 sum_A gamma_(d,r,A) sigma(V_A intersect A). (WR2)

All envelope masses and the denominator belong to ONE sigma. Different phases may share an envelope, but each phase cost is still charged as displayed; no unjustified cross-phase discount is taken. Actual-cylinder envelopes recover the pre-row version of WR1. A common coordinate cylinder can instead pay once for a whole phase union across many different supports. This is a sufficient fractional cover, not an assertion that its optimal cost has an unrestricted arithmetic bound.

### 11.3. Pure-deleted product specialization with one conditioning

Use section10.2's actual product source rho_alpha, with all s_p^alpha>0 and z_p^alpha=1/((p-1)s_p^alpha). All bad singleton-support events, including A-only ones, are already excluded pointwise. Put

    E_0={E:|E|>=2 and some A-only original has support E},
    U_0=sum_(E in E_0)product_(p in E)z_p^alpha,
    Psi_w=sum_(E:|E|>=2)W_E(w)product_(p in E)z_p^alpha.

The fixed d=1 exponent-vector bound gives

    s=rho_alpha(V_A)>=1-U_0.

If U_0<1, the SAME law eta=rho_alpha(. | V_A) satisfies

    integral F_w d eta<=Psi_w/s<=Psi_w/(1-U_0).    (WR3)

Consequently either of the following suffices for original noncoverage:

    Psi_H < (5/48)(1-U_0),   w_d=1/d;
    Psi_S < (1/3)(1-U_0),    w_d=omega_B(d).       (WR4)

These alternative tests consume PE2 and PE3; they are not additive credits. One can replace 1-U_0 by the actual positive s when it is known. Unlike AP3, eta conditions only on avoiding A-only originals, and may give positive probability to several retained phases at the same d.

### 11.4. Support incidence replaces the number of retained numerical rows

Assume the additional pure-event hypothesis AP4. Put beta_p=1/(p-2), so z_p^alpha<=beta_p. Let Q be the EXPLICIT RATIONAL UPPER BOUND on the infinite prime-square sum proved in section10.3; Q<1/24. Define

    Delta_0=max_p #{E in E_0:p in E},
    Delta_w=max_p sum_(E contains p,|E|>=2)W_E(w),

with empty maxima zero. The product inequality from AP5 gives

    U_0<=Delta_0 Q/2,   Psi_w<=Delta_w Q/2.

It follows that each of these inequalities suffices:

    48 Delta_H+5 Delta_0<=240;                    (WR5H)
    3 Delta_S+Delta_0<=48.                        (WR5S)

For WR5H, Delta_0<=48 and hence 1-Delta_0 Q/2>0. The desired strict inequality is equivalent to

    Q(48 Delta_H+5 Delta_0)<10,

which follows from Q<1/24 and WR5H. The zero-coefficient case also satisfies it. The WR5S rearrangement is Q(3 Delta_S+Delta_0)<2. This verifies the denominator and strictness, including equality in the incidence hypotheses.

The complete retained-weight sums over ALL B-smooth numerical d>1 are

    sum_d 1/d = (3/2)(5/4)(7/6)-1=19/16,
    sum_d omega_B(d)
       =product_(p in B)(1+1/(p-2))-1=11/5.

Let k be the largest number of DISTINCT mixed outside support sets E incident at one outside prime with D_(E,+)^alpha nonempty, and put k_0=Delta_0. A support is counted once regardless of how many retained d or original labels occur on it. Then

    Delta_H<=(19/16)k,   Delta_S<=(11/5)k.

Thus two simpler sufficient conditions are

    57k+5k_0<=240;                               (WR6H)
    33k+5k_0<=240.                               (WR6S)

In particular, when there are no mixed-support A-only originals, k<=4 suffices for WR6H, and k<=7 for WR6S. Arbitrarily many distinct retained d and arbitrary finite original heights are allowed on each support. These statements retain AP4; original distinctness does not imply it. They extend the available weighted supplier beyond the earlier degree48 test, which counted retained rows. They do not assert that every earlier degree48 instance satisfies these coarser conditions.

### 11.5. The existing240-label family has positive collisions and small excess

Take section10.5's original family with d=3^e, 1<=e<=120, one original at outside cofactor11*13 and retained phase0, and another at11^2*13 and retained phase1. Outside residues are zero. All240 original numerical moduli are distinct. There are no A-only or singleton-outside originals, so rho_alpha is the complete uniform outside law and s=1. Choose alpha_(3^e)=0.

The unweighted AP3 row envelope is Phi_alpha=120/(10*12)=1 and does not certify avoidance. Its incidence exceeds48. In contrast

    W_{11,13}(H)=(1-3^(-120))/2,
    W_{11,13}(S)=1-3^(-120),
    Psi_H=(1-3^(-120))/240 <5/48,
    Psi_S=(1-3^(-120))/120 <1/3.                  (WR7)

Both weighted tests succeed under one uniform law. The phase1 outside cylinder is contained in the phase0 cylinder and has mass1/1573. At each d the excess equals the indicator of that smaller cylinder. Hence the EXACT common-law expectations are

    integral F_H d eta=(1-3^(-120))/3146,
    integral F_S d eta=(1-3^(-120))/1573.          (WR8)

These are positive. The result permits actual collisions rather than implicitly finding a collision-free law.

The conditioning denominator is independently necessary. Use original moduli11,3,33, with outside-only residue0 modulo11, pure retained phase0 modulo3, and the33 class having retained phase1 and outside residue1 modulo11. The one outside uniform law has s=10/11. The sole nonanchor event has unconditioned mass1/11 but conditioned mass1/10, giving integral F_H=1/30 rather than1/33. Omitting s in the pre-row or envelope inequality would fail even in this complete three-label family.

### 11.6. Support-row costs can diverge while a phase envelope stays small

For any finite set P of primes greater than11, take the distinct odd original moduli

    3*11*p at retained phase0,
    3*11^2*p at retained phase1,  for p in P,

with all outside residues zero. There are no A-only originals. For anchor0, WR1's H row envelope under uniform outside Haar is

    (1/30)sum_(p in P)1/(p-1).                    (WR9)

This grows without bound along increasing finite prime sets, by divergence of the sum of reciprocal primes. Anchor1 has the same exponent-vector row envelope; another anchor cannot decrease it. Even the unsummed original-cylinder majorant for anchor0 is (1/363)sum_(p in P)1/p, also unbounded.

However, with U_P=union_(p in P){x_p=0}, the actual merged phase events are

    E_(3,0)={x_11=0 mod11} intersect U_P,
    E_(3,1)={x_11=0 mod121} intersect U_P,

and the latter is contained in the former. The EXACT expectation is

    integral F_H d eta
       =(1/363)(1-product_(p in P)(1-1/p))<1/363<5/48,
    integral F_S d eta=2 integral F_H d eta<2/363<1/3. (WR10)

One envelope {x_11=0 mod121}, with coefficient1, covers every phase1 original and gives the bounded WR2 cost1/363. These actual families show that weighted numerical-depth rows do not by themselves control arbitrarily many outside supports. The obstruction concerns that estimate, not original noncoverage or the general phase-excess criterion.

The outstanding unrestricted obligation is a simultaneous arithmetic upper bound on same-phase envelope costs under ONE suitable outside law, or another whole-cover consequence supplying PE2/PE3's strict reverse. WR1--WR10 do not establish it.

### 11.7. Actual original-label controls

The [weighted-phase control program](../../../frontier/cover-geometry/merged-phase-excess/weighted_phase_rows_controls.py) and [data](../../../frontier/cover-geometry/merged-phase-excess/weighted_phase_rows_controls.json) reconstruct every original numerical residue by CRT and check all247 original labels in the three families of sections11.5--11.6. Across their complete outside carriers,28325 points are examined. The shared-envelope fixture takes P={13,17} and gives exact H expectation29/80223. The program also checks all333 criterion-labelled nonnegative integer(k,k_0) cases satisfying their displayed degree condition, using section10.3's rational Q bound. These finite controls do not replace the all-height, arbitrary-support-count proofs or the infinite-tail estimate.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/merged-phase-excess/weighted_phase_rows_controls.py --output docs/reports/erdos7-odd-covering/frontier/cover-geometry/merged-phase-excess/weighted_phase_rows_controls.json
```

## 12. A literal noncover forbids every unconditional low-excess law

The unrestricted supplier suggested in sections9 and11 cannot hold for
every original odd-distinct family. There is a452-class family with an
explicit integer hole for which EVERY outside survivor satisfies

    F_S(y)>=256/735=1/3+11/735,
    F_H(y)>=(5/16)F_S(y)>=16/147=5/48+11/2352.       (UC1)

Consequently no probability supported on its actual outside-only avoiding
set gives either strict reverse of PE2 or PE3. This is an obstruction to
an unconditional sufficient criterion, not an odd covering system. The
necessary whole-cover implications PE2/PE3 and the conditional suppliers
AP1--AP8 and WR1--WR10 remain valid. A supplier restricted by consequences
of a hypothetical whole cover or justified minimality is still a separate
open question.

### 12.1. Complete numerical original classes

Let B={3,5,7}, A={11,13,17,19}, and Q=46189. The retained numerical moduli
are

    D={3,5,7,9,15,21,25,27,35,45,49,63,75,81,
       105,125,135,147,175,189,225,243,245,315,
       343,375,405,441}.

The [original-class input](../../../frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_originals.json)
specifies every class solely by its full integer modulus and residue. It
has four outside-only classes0 modp, p in A; one pure retained class1 modd
for every d in D; and one mixed class at each modulus db, for every d in D
and every nonempty squarefree divisor b of Q. Thus the class count is

    4+28+28(2^4-1)=452.

For clarity, those outside cofactors in increasing support size and then
numerical order are

    b_j=(11,13,17,19,143,187,209,221,247,323,
         2431,2717,3553,4199,46189),  j=0,...,14.

Each mixed class has retained phase2+(j mod(d-2)), hence a nonzero phase
different from1. Its complete residue, including the actual outside
phase, is fixed by the numerical input. No choice of a residue is made
separately for different outside points or probability laws.

Unique prime factorization separates all pairs(d,b), as well as the
outside-only and pure retained classes. All452 original numerical moduli
are therefore distinct, odd, and greater than one. Their common period
and the retained period are

    L_B=lcm(D)=10418625,
    L=L_B Q=481225870125.

The literal integer

    h=64366265250,   h=0 modL_B,   h=1 modQ          (UC2)

avoids every original class: its outside coordinate avoids all0 modp
classes, and its retained coordinate0 avoids every pure or mixed retained
phase. The numerical verifier also checks h against each full original
pair(m,a). No irredundancy or inclusion-minimality property is asserted.

### 12.2. Exact pointwise merged-phase certificate

The actual outside-only avoiding set is exactly

    V_A={0<=y<Q: y modp!=0 for each p in A},
    |V_A|=10*12*16*18=34560.

At each retained numerical d and actual y, form the SET

    P_d(y)={a modd: (m,a) an original class,
                    B-part(m)=d, y mod(m/d)=a mod(m/d)}.

It always contains1, by the pure retained original. Set R_d(y)=|P_d(y)|.
Repeated equal phases from different original cofactors are merged before
counting. With the same retained weights as PE3, put

    omega_B(d)=product_(p^e||d) (p-1)/((p-2)p^e),
    W_d=L_B omega_B(d),
    N(y)=sum_(d in D) W_d (|P_d(y)|-1).             (UC3)

Every W_d is an integer. Evaluation of UC3 at ALL34560 actual outside
survivors gives

    min N(y)=3628800,
    {y in V_A:N(y)=3628800}={19802},
    min F_S=3628800/10418625=256/735.              (UC4)

The [checker](../../../frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_obstruction.py)
starts from the numerical(m,a) pairs, factors out their B-parts, and
reconstructs every retained phase and outside congruence. It enumerates
the entire nonzero CRT carrier, constructs a bitset for each outside
coordinate event, and unions the original events at the same(d,phase)
before adding their integer weights. Thus it computes UC3 without using
projected labels or heuristic search scores as premises. Its
[exact result](../../../frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_obstruction.json)
includes the minimum, unique minimizer, literal hole, input hash, and
hash of all numerical-survivor/score pairs. A separate direct-set
computation agreed at every one of those34560 pairs. All substantive
checks use explicit exceptions and remain active with Python optimization.

Finally

    d omega_B(d)
       =product_(p|d) (p-1)/(p-2)<=2*(4/3)*(6/5)=16/5.

The excesses are nonnegative, so F_S<=(16/5)F_H. Combining this with UC4
proves UC1 pointwise. Integrating UC1 against ANY supported probability
gives the same lower bounds. The obstruction survives all changes of the
outside law, including nonproduct laws and point masses; it is not merely
a failure of the uniform law or an upper estimate.

### 12.3. The remaining whole-cover obligation

This example has a retained zero hole above every outside survivor, while
its number of other active phases exceeds both scalar reserve thresholds.
It shows exactly what the phase-count scalar omits: the actual position
of the uncovered retained set relative to the additional phases. A
sufficient upper-bound test need not recognize every noncover.

Therefore the unrestricted task cannot be reduced to proving a strict
PE2/PE3 reverse for all original families. A continuation must either use
additional structure of a hypothetical whole cover to supply that
reverse, or preserve more of the joint retained-phase geometry in a
different contradiction. Sections9--11 supply conditional tools for that
task, not the missing universal statement. Erdős #7 remains open here.

This is an ordinary finite certificate, not new Lean verification.
Reproduce it from the repository root with explicit input and output:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_obstruction.py --input docs/reports/erdos7-odd-covering/frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_originals.json --output docs/reports/erdos7-odd-covering/frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_obstruction.json
```

### 12.4. Containment reduction removes this particular obstruction

The452-class example does not obstruct the same supplier after a
union-preserving reduction. For classes A=(a modulo m) and C=(c modulo n),
with m>n, the conditions n divides m and a=c modulo n imply A is contained
in C. Delete every original class properly contained in another original
class. Finite descent in the numerical modulus ensures that every deleted
class is contained in one of the retained classes. Thus the covered subset
of the integers is EXACTLY unchanged. Numerical distinctness and oddness
also persist; no new class or residue is introduced.

For the complete numerical input of UC1, this leaves263 original classes
and deletes189. Each deletion has a retained containing class, explicitly
recorded in the [exact reduction data](../../../frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_containment_reduction.json).
The four outside-only classes are still precisely0 modulo11,13,17,19.
Take the SINGLE outside coordinate

    y=24950 modulo46189,
    (y modulo11,13,17,19)=(2,3,11,3).

It belongs to the unchanged outside survivor set. Reconstructing the
active retained phases from all263 FULL numerical originals gives exactly

    (d,r)=(3,1),(5,1),(7,1),(49,3),(63,5),
          (75,2),(105,3),(125,2),(147,2),(243,2).

All other retained numerical rows have no active phase at this y. Every
row therefore has at most one phase, and the reduced family has

    F_S(y)=F_H(y)=0.                              (UC5)

Since each excess summand is nonnegative, zero is also the exact global
minimum of each reduced excess on V_A; an exhaustive search is unnecessary
to certify that minimum. The point mass at this common y is one supported
law for every retained numerical row. By contrast, the ORIGINAL452 classes
at this SAME y have

    F_S(y)=118982/297675>1/3,
    F_H(y)=291596/1488375>5/48.

Thus the scalar excess is not invariant under an exact preservation of the
covered set. This leaves UC1--UC4 intact for their stated original family,
but prevents using that example to rule out a supplier restricted to
containment-free families or to a genuinely minimal whole cover. The263
retained classes have no pairwise class containment; this does NOT assert
that none is covered by a UNION of the others. No inclusion-minimality or
universal low-excess theorem is inferred.

The [numerical verifier](../../../frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_containment_reduction.py)
checks all189 retained-containment witnesses, the unchanged outside-only
family, all active original congruences at y, and both exact excesses. A
separate complete outside-carrier probe also found minimum zero; UC5 and
nonnegativity already provide the exact certificate. Reproduce with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_containment_reduction.py --input docs/reports/erdos7-odd-covering/frontier/cover-geometry/merged-phase-excess/universal_phase_supplier_originals.json --output /tmp/e7_phase_containment_reduction.json
```

The unrestricted obligation remains to prove an appropriate supplier for
every relevant reduced original family, or to use further whole-cover
structure. This diagnostic neither supplies that quantifier nor settles
Erdős #7, and it is not new Lean verification.

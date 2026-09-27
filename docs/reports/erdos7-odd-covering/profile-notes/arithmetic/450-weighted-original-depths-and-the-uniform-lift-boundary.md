[Index](../../marked_head_profile.md) · [Actual lifting](439-actual-residual-lifting-and-exact-free-coordinate-cost.md) · [Private head law](449-equality-sources-have-a-private-law-below-nine.md) · [Original antichains](../321-384/363-common-source-antichain-capacity.md)

# Weighted original depths give joint deletion credit; outside blocks still need a shared budget

For original mixed labels d=3^e a b with a dividing1225 and fixed numerical outside cofactor b, comparable-class disjointness gives a sharp all-ternary-height weighted count bound34/9. If b=1, so the mixed condition excludes a=1, the sharp bound is11/3. This allows the original3-exponent layers to be combined in ONE Gram/deletion estimate, retaining their weights and full event indicators.

Different b blocks may delete the same physical mass, so their credits cannot simply be added. There is also an explicit702-label actual odd family for which a head marginal with Gamma_1225<=25/3 has a uniform actual-fibre lift whose original completion load exceeds the necessary whole-cover threshold. The same law leaves positive uncovered mass, and a different supported lift makes the completion load zero. Thus the example identifies a limitation of the specified uniform lift, not an obstruction to every lift or a covering counterexample.

For this same family, section6 proves that every head marginal with a uniform actual-fibre lift has original cofactor second moment above893/81>9. Even exact deletion credit leaves a positive certificate gap; full owners and actual private-owner densities are evaluated under the same law.

Section7 identifies a whole-cover condition that this countercontrol fails: every prime3-private point has a hole on its complete3-coordinate line. More generally, an original pure prime power at minimum positive height has an exact private-product region, and every hole resets into it. This extracts the pointwise mechanism of Reports354 and357 without importing their later whole-cover matching conclusions.

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

The [standard-library program](../../frontier/cover-geometry/original_cofactor_gram_uniform_lift.py) and its [exact JSON data](../../frontier/cover-geometry/original_cofactor_gram_uniform_lift.json) evaluate these finite rational formulas, verify the disjoint first-zero owner decomposition against exact deletion, and verify every private-owner Cauchy–Schwarz contribution. It runs under python3 -I -S -B -O. It reuses section3's original-family construction and its existing702-private-witness verification; it does not claim another whole-period enumeration, new Lean verification, or an unrestricted odd-covering theorem.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_cofactor_gram_uniform_lift.py
```

## 7. Original prime-private regions meet every hole line

The distinction between a countercontrol for a uniform lift and a whole cover has a pointwise witness. Let PS1 mean that every ENTIRE prime-power CRT coordinate line through every actual private point is covered. This is the private-to-hole nonadjacency condition of the [original-label interface](../../../../../Library/Arith/lettlsun2008cosets.md); it concerns actual private points, not points assigned by an owner partition.

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

The [extremal normalization](../321-384/350-extremal-paired-branch-and-source-support.md) obtains divisor closure AFTER assuming a whole cover exists and minimizing first its cardinality and then its modulus sum. It does not normalize an arbitrary noncover while preserving noncoverage and PS1. No such transformation is supplied by(PR3).

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

The [standard-library program](../../frontier/cover-geometry/original_prime_private_reset.py) and [exact data](../../frontier/cover-geometry/original_prime_private_reset.json) retain the original702-class input. They construct a literal integer hole with full3-coordinate80, head coordinates1 and all138 outside coordinates2. Resetting to every value in each original prime's0-root gives177 genuine private neighbors in141 prime directions. The124956 original-AP membership checks equal702 times(1+177); no whole-period enumeration is used.

The small controls include0 mod3,1 mod5,4 mod15, whose prime3 and prime5 private regions have4 and2 points among15, with7 holes; and0 mod9,1 mod45,2 mod175, whose pure9 region has174 private points among1575, with1357 holes. The last family has no prime label but satisfies(PR1) for pure9. The two same-modulus phase examples above verify the boundary of the sufficient condition.

[Report354](../321-384/354-synchronized-prime-private-cofactor-matching.md)'s(SM3) already gives the prime-private Cartesian identity using only the original prime label, comparable-class disjointness and the p-free residual. Its subsequent coverage of every other root and tail, and synchronized matching, do use whole coverage. [Report357](../321-384/357-original-private-swaps-and-prime-reset-transport.md)'s(PT6) starts at another original's private region, so a hole cannot be substituted into that statement literally. Its pointwise reset mechanism and(PT9)'s private-product identity supply the same reuse after the weaker premises are extracted; the hole argument above checks the changed source domain directly.

The higher pure-power case repeats that containment argument under(PR1). This is ordinary reuse and a same-law consequence, not a new Lean declaration or a claim of mathematical priority. For the conditional extremal divisor-closed #7 family, the remaining task is to turn the full coverage of these actual private fibres into a contradictory common arithmetic budget or a legal global transformation. Recovering whole coverage from PS1 does not itself provide that contradiction.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_prime_private_reset.py
```

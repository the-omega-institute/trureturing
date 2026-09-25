# Actual selected overlap improves joint query and loss budgets

The unchanged two-copy six-prime PA law from
[Report569](569-complete-suffix-debits-close-the-six-prime-query-target.md)
admits simultaneous improvements of its complete query bound and its
positive-part bounds. The extra quantity is the overlap of the actual
selected forbidden cylinders at each row. All credits use the same
actual prefixes and the same final probability; none changes the
selected phases or substitutes a different law for a different query.

Write Q={5,7,11,13,17,19}, and retain Report569's constants B, caps C_q,
row envelopes a_q F_q, cap-slack coefficients eta_q and prefix credits
J_q. Let K3,K7 be the complete-suffix constants of
[Report574](574-four-level-query-hinge-removes-pointwise-overlap.md)
and [Report580](580-actual-branch-loads-extend-the-height-four-query-certificate.md).
All selected numerical labels and phases are fixed globally, with at
most two phases per nonunit Q-label and arbitrary finite heights.

For each later row q in{11,13,17,19}, at its actual earlier history,
let C_i be the indexed selected q-cylinders and set

    U_q=sum_i H_q(C_i), f_q=H_q(union_i C_i), D_q=U_q-f_q,
    tau_q=1-1/C_q,
    gamma_q=C_q min(D_q,(U_q-tau_q)_+),
    O_q=integral gamma_q d lambda_<q,
    omega_q=O_q/s, s=lambda_final(1)>0.                  (SO1)

The index retains original numerical labels: identical cylinders
coming from different labels remain different entries in U_q.
For the unchanged normalized law nu=lambda_final/s,

    R_Q(nu)<=B-delta_R,
    delta_R=sum_q [B-2-zeta_q(3)] omega_q,
    E_nu(L-t)_+<=K_t-delta_t, t=3,7,
    delta_t=sum_q [K_t-zeta_q(t+1)] omega_q.             (SO2)

Here zeta_q(r) is the auxiliary suffix hinge at threshold r AFTER row q.
The second bound holds for every finite partial one-phase nonunit query
layout L and its convex mixtures, simultaneously under nu. Query heights
are unrestricted. All displayed credit coefficients are nonnegative.

These are ordinary proofs with exact arithmetic, not new Lean results.
They do not imply a uniformly positive overlap credit for arbitrary
original families and do not settle unrestricted Erdos #7.

## 1. Retain overlap before the signed-penalty comparison

Suppress q. The actual row loss is ell=C(f-tau)_+, and exactly

    ell=C(U-tau)_+-gamma.                              (SO3)

For eta>=0 and w>=eta C define

    p_w(v)=-eta[C-(1-v)^(-1)]  if 0<=v<tau,
           w C(v-tau)          if v>=tau.

Its second branch applies also to U>1. The function is increasing and
convex, and

    p_w(U)-p_w(f)>=w gamma.                            (SO4)

If U<tau, gamma=0 and monotonicity proves SO4. If f>=tau,
both sides are w C(U-f). In the remaining case f<tau<=U,
the difference is w gamma+eta[C-(1-f)^(-1)]>=w gamma.
This proves SO3--SO4 for all admissible real f,U, without relying on
finite numerical samples.

Under u=(q-1)v/2, p_w is Report569 SD8's joint convex penalty. Split
actual original labels into their two fixed slots at every positive
q exponent. Complete each slot to an earlier-coordinate query L_i,
including its unit once. The weights beta_(e,j)=(q-1)/(2q^e) sum to one,
and (q-1)U/2<=sum_i beta_i L_i. Apply SO4 BEFORE the existing Jensen
and shifted nonnegative comparison of Report569 SD9. Restoring the
actual prefix mass gives

    w Delta_q-eta_q K_q^cap
       <=w a_q F_q-J_q-w O_q.                        (SO5)

Here K_q^cap is the actual integrated cap slack, not K3 or K7.
The old J_q remains: it arose from the subsequent shifted-prefix
comparison, while SO4 retains slack before that comparison. The old
prefix lower bound is unchanged, so this does not count the overlap
twice through an improved prefix estimate.

Take w=B-2-zeta_q(3). The suffix identity
zeta_previous(3)=zeta_q(3)+C_q eta_q and B-2>=zeta_0(3) imply
w>=eta_q C_q. Substitution into Report569 SD5--SD10 retains its four
nonnegative corner expressions and adds sum_q w O_q. Dividing by s
and maximizing all finite query layouts proves SO2's query bound.

## 2. The positive-part credit includes the existing suffix correction

The same nominal two-slot comparison, now with SO3, gives

    Delta_q<=a_q F_q-O_q.                            (SO6)

For t=3,7, write H_t=integral(L-t)_+ d lambda_final and Phi_(t+1)
for the full auxiliary hinge including the unit. Report574's complete
suffix comparison gives

    K_t s-H_t >= K_t xy-Phi_(t+1)
       -(K_t-zeta_0(t+1))m
       -sum_q (K_t-zeta_q(t+1))Delta_q.              (SO7)

Every coefficient is nonnegative. Apply m<=1/12, SO6 and the retained
four-corner certificate for K_t. The result is
K_t s-H_t>=sum_q(K_t-zeta_q(t+1))O_q, proving SO2. Extension to
complete finite query boxes and then exhaustion includes every height;
convexity supplies mixtures of partial layouts.

K_t already includes the old suffix debits. The new coefficient is
K_t-zeta_q(t+1), not K_t. Subtracting the suffix loss from K_t a second
time would be invalid.

## 3. A compatible residual group forces selected overlap

At one earlier history, restrict to residual numerical labels d=b q^a
ACTIVE there: the history satisfies the residual phase on b. Call such
a label aligned when both its selected phases agree with its residual
phase on b. Both selected q-cylinders then occur in the actual current
row. Suppose a group of these active aligned labels has residual
q-cylinders with a common intersection, of maximum depth A. Each
selected cylinder avoids that intersection, whose Haar mass is q^(-A).
For disjoint indexed groups j put

    T_j=(2 sum_(d in j)q^(-v_q(d))-1+q^(-A_j))_+.

The selected union in group j has mass at most1-q^(-A_j). Consequently
D_q>=sum_j T_j. If any T_j>0, the nominal mass of that group includes
both T_j and1-q^(-A_j)>=1-1/q>tau_q, since C_q<q. Summing positive
groups therefore also gives U_q-tau_q>=sum_j T_j. Thus the truncation
in SO1 preserves this lower bound:

    gamma_q>=C_q sum_j T_j.                          (SO8)

All later kernels are substochastic. Their final raw marginal on the
earlier coordinates is dominated by lambda_<q, so

    omega_q>=C_q E_nu sum_j T_j.                    (SO9)

Groups must be disjoint as indexed numerical labels. The same selected
pair cannot be counted again at another original ternary height.
Arbitrary finite q-adic depths remain allowed.

For six aligned exponent-one labels at q=11 with a common residual
11-root, let H be their common earlier-history activation event.
All six residual b-phases must hold on H. Then SO9 reads

    omega_11>=(10/33)nu(H).                          (SO10)

Alignment and a common residual root are hypotheses; occupation of
two selected slots and a large residual mean alone do not imply them.

## 4. A stronger conditional height-four continuation

Keep Report580's original geometry EXACTLY: distinct P-smooth original
moduli for P=Q union{3}, pure originals1 mod3 and3 mod9, at most two
projected Q phases through ternary exponent3, and those phases included
in the selected source. Let L_A4 count residual exponent4 originals in
A=[0]_9 union[6]_9 and rho_A=E_nu L_A4. The other root and all later
original loads retain Report580's unrestricted scope.

Replace B,K3,K7 in its SAME construction by SO2. Its sufficient gate is

    rho_A<rho_star+(3087/566)delta_R+delta_3/2+3delta_7/2,
    rho_star=15232049749731473125568032040735530696696089170781
             /17675397446262147818643258984205266694377556670000.
                                                               (SO11)

Indeed put N'=B-delta_R+(10/11)(1+B-delta_R) and
s0'=1-rho_A/33-(K3-delta_3)/66-(K7-delta_7)/22. Then SO11 is exactly
566 s0'>49 N'. The actual lifted law has R_P<=N'/s0'<566/49, and the
unchanged23/29 continuation leaves Haar survivor mass at least

    alpha_min(566 s0'-49 N')/13608>0.                (SO12)

All additional originals touching23 or29 may have arbitrary fixed
phases and finite heights. This continuation does not include primes
outside P union{23,29}.

For an event H satisfying SO10, define

    c3=(10/33)[K3-zeta_11(4)]
      =8244066111879375261150234274193
       /13028880122830538422109839318848,
    cR=(10/33)[B-2-zeta_11(3)]
      =3787386056391202331868949579
       /4231163303870143894252908480.

Then delta_3>=c3 nu(H), delta_R>=cR nu(H), and a sufficient condition is

    E_nu(L_A4-6 1_H)_+<epsilon0,
    epsilon0=rho_star+c3/2+(3087/566)cR-6
       =12761728260541168481019359351214624369307852770247
        /212104769355145773823719107810463200332530680040000
       =0.06016709713478002...>0.                    (SO13)

To check this, write h=nu(H) and bound rho_A by6h plus the displayed
positive part. Since c3/2+(3087/566)cR<6, the worst required margin
over0<=h<=1 is attained at h=1. The unused nonnegative delta_7 only
improves SO11.

## 5. Large residual mean alone does not force this overlap

Keep the pure originals1 mod3 and3 mod9. For the seven cofactors
d=(5,7,11,13,17,19,25), in that order, take four originals each:

| Ternary exponent | Q phase modulo d | Ternary phase |
|---:|---:|---|
|0|0|vacuous|
|1|1|2 mod3|
|4|2|0,6,9,15,18,24,27 mod81, respectively|
|5|2|33,36,42,45,51,54,60 mod243, respectively|

CRT fixes one actual residue for each of the30 distinct odd numerical
moduli. Select phases{0,1} at every cofactor. The selected25 classes
are already removed at5. The actual PA law is the product of Haar
conditioned on x_q modq not in{0,1}. Each later row has just two
disjoint selected root cylinders: U_q=f_q=2/q, so gamma_q=0.
Its normalization density q/(q-2) is below C_q; no alternative source
has been substituted.

Every residual exponent4 original lies in A, and

    rho_A=sum_(q in Q)1/(q-2)+1/15
         =1561/1683=0.9275103980986333...>rho_star,
    R_Q(nu)=product_(q in Q)[1+q/((q-1)(q-2))]-1
           =214267985/147806208=1.4496548412905634... .

Thus high rho_A and two occupied selected slots do not force positive
SO1 overlap. But the small ACTUAL R_Q already makes Report580's old
numerator succeed: retaining K3,K7 gives R_P<=4.068895102263064... .
This control does not refute good-law existence or all earlier
certificates. The two shallow25 originals are redundant; no
irredundancy claim is made.

The same retained control checks all96 feasible cofactor-incidence
patterns. If n cofactors are active, c_A=1-2n/27 and c_B=1. Seven are
simultaneously active with probability1/1893375, giving c_A=13/27<1/2.
It therefore does not meet the separate reserve-at-least-one-half or
at-most-six-per-layer hypotheses of the weighted-branch construction.

## 6. Reuse, verification and remaining arithmetic obligation

Report559 already retains pure-union saving and joint loss/cap slack;
Report569 supplies its signed penalty and J_q; Report574 supplies the
complete-suffix K_t. The additional retained quantity here is the
indexed selected-cylinder overlap and its simultaneous use in all
three bounds under one law. O_q avoids reusing Report559's Gamma name
for a different aggregate. No external novelty claim is made.

The missing uniform step is to show that adverse residual load and
adverse complete-query cost force enough actual overlap, another
comparison saving, or a successful different source. Earlier-coordinate
disagreement, distribution across rows or depths below the packing
threshold, and concentration in the5/7 anchors are not covered by
SO8. No theorem here forces SO11 or SO13 for every original family.

The [exact producer](../../frontier/cover-geometry/actual_selected_overlap.py)
and [data](../../frontier/cover-geometry/actual_selected_overlap.json)
reconstruct the auxiliary moments, the four-corner comparisons including
J_q, suffix identities, nonnegative credit coefficients and SO13, and
retain the complete30-original control with its actual source quantities.
Rational samples including U>1 supplement the general three-case proof;
they do not replace it. Run with Python3 standard library only:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_selected_overlap.py

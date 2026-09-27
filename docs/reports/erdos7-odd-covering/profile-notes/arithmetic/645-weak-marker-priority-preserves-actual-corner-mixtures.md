# Weak-marker priority transports corner-dependent thinnings without loss

A selected thinning may vary across the numerical weak-leaf corners without losing its complete gate, provided it retains a cell at least as strongly when that cell carries the weak marker. This is a direct actual-source mixing rule, with no clipping debit. It applies to one fixed admissible cell-dependent outside response table and preserves every finite-depth query.

This is ordinary mathematics with exact rational examples, not new Lean verification. [Report624](624-arbitrary-central-pure-phases-admit-two-complete-boundary-gates.md) supplies the actual pure sources; [Report637](637-the-remaining33-require-a-rebuilt-common-source-interface.md) §5 identifies the obstruction to uncoupled corner choices; [Report643](643-central-cell-root-choices-preserve-complete-continuation.md) supplies the conditional response geometry; [Report644](644-actual-capacity-clipping-realizes-corner-dependent-thinnings.md) gives the general capacity-clipping repair. The present priority condition removes that repair loss and can use the original normalized query fields directly. Its positive example reuses an admitted643 class; it does not add a new phase class or settle unrestricted Erdős #7.

## 1. Fixed-null source and the lossless condition

Fix null leaves and let I and J denote the 5 nonnull ternary and 19 nonnull quinary leaves. At each actual central cell c=(l,m), write

    w^i_l = u − d 1_(i=l),   u=2/9, d=1/9,
    v^j_m = U − D 1_(j=m),   U=4/75, D=1/75.

Let alpha and beta be probability vectors, gamma_ij=alpha_i beta_j, w_l=sum_i alpha_i w^i_l, and v_m=sum_j beta_j v^j_m. These are leaf masses of ONE actual Report624 source with w_l<=C3_l and v_m<=C5_m, spread at constant Haar density on each actual surviving leaf. Numerical corner sources need not be realizable individually.

The actual capacities and the mixing weights are related. Write

    c_l=(2/9−C3_l)/(1/9),   d_m=(4/75−C5_m)/(1/75).

The higher-pure tail bounds give nonnegative c,d with sum c<=1 and sum d<=1. The actual feasibility conditions are exactly

    alpha_l>=c_l, sum alpha=1;
    beta_m>=d_m, sum beta=1.                               (A)

For example, a concrete choice requiring no unsupported corner law is

    alpha_l=c_l+(1−sum c)/5,
    beta_m=d_m+(1−sum d)/19.

These determine w,v and constant thinnings within each actual surviving leaf. All nonnull weights are positive. The capacities are computed from the ONE finite original family; no phase is changed or optimized separately in different branches. The theorem below holds for every choice satisfying A, so the unused capacity need not be distributed in this particular way.

For every cell and corner pair choose 0<=theta^ij_c<=1, zero on the common central mask, and use the same entire fields for all query labels. Impose weak-marker priority, separately at every c=(l,m):

    theta^lj_c >= theta^ij_c for every i,j,
    theta^im_c >= theta^ij_c for every i,j.                 (P)

Thus retention is at least as large when the weak marker coincides with the cell's queried leaf. P permits nonconstant corner fields.

At c define the same four arrays as644:

    lambda = sum_ij gamma_ij w^i_l v^j_m theta^ij_c,
    a3     = sum_ij gamma_ij       v^j_m theta^ij_c,
    a5     = sum_ij gamma_ij w^i_l       theta^ij_c,
    a35    = sum_ij gamma_ij             theta^ij_c.

Then

    0<=lambda<=w_l v_m,
    lambda<=w_l a3, lambda<=v_m a5,
    lambda<=w_l v_m a35.                                  (L)

Proof. For fixed j let A_j=sum_i alpha_i theta^ij_c. Since theta^lj_c>=A_j,

    sum_i alpha_i w^i_l theta^ij_c
      =u A_j−d alpha_l theta^lj_c <=w_l A_j.

Multiply by beta_j v^j_m and sum to obtain lambda<=w_l a3. Exchanging coordinates proves lambda<=v_m a5. Moreover, column priority gives

    a3=U a35−D beta_m sum_i alpha_i theta^im_c
       <=(U−D beta_m)a35=v_m a35.

Combining this with lambda<=w_l a3 proves the last inequality. Product mixing and theta<=1 give the first bound. Zero alpha_i or beta_j cause no problem.

Since w_l<=C3_l and v_m<=C5_m, all644 capacity inequalities follow from L. In particular lambda*=lambda and capacity-clipping loss is zero. L is stronger: it directly supports the UNMODIFIED old640 effective-thinning query envelope, rather than requiring the capacity-aware refinement in644.

## 2. Weaker conditions for fixed mixing; exactness over all mixing

For fixed alpha,beta, the three inequalities in L are linear in the theta entries. On positive cells they are exactly the conditions needed for

    lambda/w_l<=a3, lambda/v_m<=a5,
    lambda/(w_l v_m)<=a35.                                (W)

Thus a source-adapted optimization may impose these three inequalities instead of P. They are sufficient, and necessary for these particular averaged old-menu fields; no claim is made that they are necessary for every conceivable actual-source query argument.

An intermediate, weaker-than-P sufficient condition is

    theta^lj_c >= sum_i alpha_i theta^ij_c for every j,
    theta^im_c >= sum_j beta_j theta^ij_c for every i.      (CP)

The proof of L above works verbatim under CP. CP need only be imposed on j with beta_j>0 and i with alpha_i>0.

For an explicit averaged form put p=alpha_l, q=beta_m,

    A=sum_ij alpha_i beta_j theta^ij_c,
    B=sum_j beta_j theta^lj_c,
    C=sum_i alpha_i theta^im_c,
    t=theta^lm_c.

Then

    lambda−w_l a3 = d p [U(A−B)−D q(C−t)],
    lambda−v_m a5 = D q [u(A−C)−d p(B−t)],
    lambda−w_l v_m A
      =d U p(A−B)+u D q(A−C)+d D p q(t−A).

Requiring all three displayed differences to be nonpositive is the fixed-mixing version of W. The factors p,q should not be cancelled when zero.

There is also an exact robust characterization: for a fixed theta matrix at c, P holds if and only if lambda<=w_l a3 and lambda<=v_m a5 hold for EVERY pair of probability vectors alpha,beta. Sufficiency was proved above. For necessity, fix i!=l and j, set beta=delta_j and alpha=(delta_i+delta_l)/2. Then

    lambda−w_l a3=(d/4)v^j_m(theta^ij_c−theta^lj_c).

The positive v^j_m forces the first priority inequality. Exchange the coordinates for the second. The third bound then follows. This exactness statement quantifies over full simplices, not merely the actual-capacity-constrained feasible subsets; P is only asserted sufficient on those subsets.

## 3. One actual source, all depths, all32 cell-dependent responses

Define theta_eff(c)=lambda/(w_l v_m) on a positive cell, zero on a null cell. Thin the SAME actual rho3*rho5 by this scalar within the actual surviving cell. Attach the SAME outside submeasure zeta_c, independent of corner index and higher central digits. Require zeta_c<=rho_Q for one common actual normalized outside pure product. Let H_empty(c)=zeta_c(1) exactly, and let all H_T(c) be the simultaneous full-height response envelopes from644. This defines one submeasure eta<=rho3*rho5*rho_Q, preserving inherited Haar domination.

For a deep ternary cylinder A of depth e and a whole quinary survivor leaf,

    eta_c,central(A×S_m)
      <=2·3^(−e) lambda/w_l <=2·3^(−e)a3.

The first inequality uses the actual rho3 density cap2, not a fictitious corner law. The quinary case is bounded by (4/3)5^(−f)a5. For two deep cylinders the bound is (8/3)3^(−e)5^(−f)a35. Shallow modes use the retained masses lambda exactly. Consequently the old640 normalized fields

    lambda, lambda/w_l, (4/5)lambda/v_m,
    (4/5)lambda/(w_l v_m)

are bounded by the gamma-averaged corresponding corner fields. Multiply each cell by its SAME H_T(c), sum, and then maximize over the same labelled selector menu. A maximum of the average is at most the average of maxima. This proves every one of the16 central modes and32 outside responses at every finite query depth. The argument is a density proof, not extrapolation from finite-prefix checks. Null/masked cells have zero mass and need no division.

With the unchanged complete nonnegative512 coefficients and unit-inclusive mass coefficient g,

    G_actual(theta_eff) >= sum_ij gamma_ij G_ij(theta^ij).  (G)

The source mass is EXACTLY sum_c H_empty(c)lambda_c, which is the average corner source mass; there is no clipping debit. Every charged original, conditional root set, pure-source restriction, continuation law and Haar conversion must still satisfy its previously declared same-source hypotheses. Corner-dependent outside sources cannot be silently combined by this theorem.

## 4. Canonical repair of an arbitrary field

At each c define

    theta#^ij_c=min(theta^ij_c,theta^lj_c,theta^im_c,theta^lm_c).

Then theta# satisfies P and theta#<=theta. It is the greatest entrywise minorant satisfying P: any feasible phi<=theta obeys

    phi^ij<=theta^ij, phi^ij<=phi^lj<=theta^lj,
    phi^ij<=phi^im<=theta^im,
    phi^ij<=phi^lm<=theta^lm.

The displayed minimum therefore bounds phi^ij, and theta# attains that bound. It preserves every required zero mask.

Let lambda# be its averaged retained cell mass. All corner query screens decrease when theta is replaced by theta#. Their positive coefficient debits cannot increase. Hence

    G_actual(theta#_eff)
      >=sum_ij gamma_ij G_ij(theta^ij)
           −g sum_c H_empty(c)(lambda_c−lambda#_c).        (R)

This gives a computable repair loss, not a claim that the loss is uniformly small or payable. The old complete coefficients remain unchanged.

## 5. A finite LP sufficient for arbitrary actual higher pure phases

For fixed nulls, central mask, original inventory and actual outside response table H_T(c), there are exactly95 corner pairs. Choose one entire theta field for each pair. The constraints0<=theta<=1, zero-mask conditions, and P are finite linear constraints. Introduce one screen variable for each corner and each of the512 complete modes; require it to dominate every finite labelled central selector expression, and require every corner gate to be at least a common delta.

If this finite LP admits an EXACT certified delta>0, then every actual source weight pair in624's fixed-null polytopes, whatever the finite higher pure exponent heights, admits the one actual thinning constructed above with gate at least delta. A phase-class conclusion additionally requires the outside response table and its source-null incidence conditions to hold uniformly over that class; the finite LP does not itself prove those conditions for arbitrary original phases. The density proof supplies all query depths. Individual uncoupled corner optima are not enough; a jointly feasible priority-constrained family is required. A uniformly positive LP result would be a sufficient arithmetic certificate under the given original inventory and response geometry, not the unrestricted Erdős #7 theorem.

## 6. Nonconstant positive witness on the already positive643 profiles

Take any of643's23 already positive second7-root masks, with its SAME cell-dependent outside response table. Let M(c) be the common central allowed mask and choose

    theta^ij_c=M(c)[1−epsilon 1_(i!=l)1_(j!=m)],
    epsilon=1/1000.

This is nonconstant on live cells, satisfies P, and lies between(1−epsilon)M and M. All query screens are no larger than their theta=M values. For every corner, source mass loss is at most epsilon max_c H_empty(c), since the corner central product has total mass1. Report643 gives max H_empty<=935/1536 and the common lower corner gate

    gamma643min=41908790232778304321/59732853887443968000000,
    g=200163067/201247200.

Therefore every corner gate, and then the one actual mixed-source gate, is at least

    delta=gamma643min−g(1/1000)(935/1536)
         =11487698589965543917/119465707774887936000000
         ≈0.00009615896313620044 >0.

Independent exact rational arithmetic verifies this equality. Using only H_empty<=1 would give a negative bound; the actual643 envelope matters. This is a nonempty positive witness for the lossless NONCOMMON-field bridge. It does not add a24th mask, new phase freedoms, optional releases, head-prime transports or network continuation bounds.

## 7. Exact finite witness and the remaining obligation

The [standard-library producer](../../frontier/cover-geometry/weak_priority_actual_mixing_certificate.py) and [result data](../../frontier/cover-geometry/weak_priority_actual_mixing_certificate.json) verify the displayed rational margin using643's retained complete512 certificate and nonnegative costs. They do not claim to rerun its11400-corner calculation. Their input digests identify both640's coefficients and643's conditional certificate.

The actual-source example uses644's literal pure originals

    2mod3,0mod9,3mod27;
    4mod5,0mod25,1mod125.

It retains the same within-leaf constant densities. The ternary numerical mixture has alpha_1=2/3,alpha_2=1/3; the quinary one has beta_5=4/5,beta_10=1/5, in643's root-first leaf indices. Take the conditional second7-root set S={1,3}. All other mixing weights vanish. The epsilon family is nonconstant even on these positive-weight corner pairs.

An actual outside realization takes every pure root0, uniform mass on the remaining roots, removes root1 everywhere, and additionally removes root2 at7 on the leaves in S. Its higher digits are Haar within the retained roots. The source is fixed across every comparison and query; its32 envelopes are exactly CS1. The producer reconstructs the actual central submeasure, verifies domination and zero clipping, and checks all32 times6240 central prefix-pair inequalities through resolving heights3. It passes209187 explicit rational checks. The unbounded finite-depth conclusion comes from §3's density proof, not the finite scan.

An independent exact reconstruction passes10999 checks:1316 actual joint atoms,6240 central prefix pairs,3840 outside cell/support responses, all512 complete-mode comparisons, and all95 priority corner pairs. The effective actual gate is

    212100882515955506889143177/5150076309959454720000000000,

and the average of its four positive-weight corner gates is

    331258503675355266863201/8046994234311648000000000.

The former is at least the latter, which is at least delta. Separate two-point mixtures produce positive field defects1/900 and1/2700 when the corresponding priority condition is dropped; the2×2 Boolean check also confirms the greatest-minorant direction. These are ordinary exact finite computations, not new Lean verification.

The constructive success criterion for a new geometry is now precise: supply one actual outside source table with all32 valid responses and the full original inventory; solve the coupled95-field problem with priority or otherwise certify the fixed-mixing inequalities; then provide an exact strictly positive complete gate. The theorem supplies the transport from those numerical fields to an actual source. It does not supply positivity for every such table, nor prove that an arbitrary original layout admits the required outside source.

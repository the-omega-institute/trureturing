# Actual-capacity clipping realizes corner-dependent thinnings

A corner-dependent central thinning can be transported to ONE actual source by clipping its retained cell masses against the actual surviving capacities. This preserves every finite-depth query bound and makes the lost mass explicit. The outside source may depend on the central leaf cell, so the construction applies to [Report643](643-central-cell-root-choices-preserve-complete-continuation.md) conditional root exclusions as well as global exclusions.

This is an ordinary construction with exact finite examples, not new Lean verification. It does not supply a uniformly positive gate: corner margins still have to pay the capacity-clipping loss. The final example also gives an exact limitation of one specified fixed-source query envelope.

## 1. Actual capacities, numerical corners and outside responses

Fix the actual pure-survivor sources of [Report624](624-arbitrary-central-pure-phases-admit-two-complete-boundary-gates.md) §2. Within the ternary mod9 survivor leaf S_l and quinary mod25 survivor leaf S_m, put

    h3_l=H3(S_l), C3_l=2h3_l,
    h5_m=H5(S_m), C5_m=(4/3)h5_m.

The actual sources have constant Haar densities w_l/h3_l and v_m/h5_m on those surviving sets, with w_l<=C3_l, v_m<=C5_m. They avoid the actual pure originals at every finite height. Null cells will receive zero; every division below concerns positive weights and capacities.

Use624's fixed-null numerical decompositions

    w=sum_i alpha_i w^i, v=sum_j beta_j v^j,
    gamma_ij=alpha_i beta_j.

Their comparison corners need not themselves be realizable on this actual higher-digit survivor. Choose one entire thinning field theta^ij_lm in[0,1] for each corner pair. Every field vanishes on the central15 mask. Its entries are fixed across all query labels.

For each cell c=(l,m), also fix ONE actual outside submeasure zeta_c. It is the same for every comparison corner and depends on the central cell, not on deeper central digits. For the Report640/643 application, require zeta_c<=rho_Q for one same normalized actual pure-source product rho_Q=product_q rho_q; the conditional root restrictions satisfy this requirement. It preserves the inherited product-density and Haar bounds as well as the query estimates below. For every outside support T, suppose its complete-height queries satisfy

    zeta_c(query on T)
      <=H_T(c) product_(q in T) cap_q(query_q).

Take H_empty(c)=zeta_c(1), because this field also bounds empty-support queries. If only a lower mass b_c is certified, first thin zeta_c uniformly to mass b_c, then use that actual submeasure and its query upper bounds throughout; at b_c=0 set the source and all response fields to zero. A lower bound on an unthinned source is not an upper bound for an empty-support query. All query grids refer to this same zeta_c. This includes Report643's cell-dependent outside source whenever its response fields are supplied; no constant-in-c assumption is needed.

## 2. The actual-source construction

At each cell define

    lambda=sum_ij gamma_ij w^i_l v^j_m theta^ij_lm,
    a3    =sum_ij gamma_ij       v^j_m theta^ij_lm,
    a5    =sum_ij gamma_ij w^i_l       theta^ij_lm,
    a35   =sum_ij gamma_ij             theta^ij_lm.

The product decomposition and theta<=1 give lambda<=w_l v_m. Set

    lambda*=min(lambda, C3_l a3, C5_m a5, C3_l C5_m a35).    (C1)

On S_l times S_m, use the actual central submeasure

    mu_c=[lambda*/(w_l v_m)] (rho3 times rho5)|_c,

and attach the already fixed zeta_c. Sum these cell measures to obtain one actual source eta. Because 0<=lambda*<=lambda<=wv, its central component is dominated by the actual product source. No unsupported corner law or query-dependent outside law is introduced. Under zeta_c<=rho_Q, the resulting eta is dominated by the same rho3 times rho5 times rho_Q; the inherited Haar domination is therefore preserved.

The joint central Haar density on cell c is lambda*/(h3_l h5_m). Thus, for arbitrary-depth cylinders D3,D5 within these leaves,

    mu_c(D3 times S_m)<=2a3 H3(D3),
    mu_c(S_l times D5)<=(4/3)a5 H5(D5),
    mu_c(D3 times D5)<=(8/3)a35 H3(D3)H5(D5).               (C2)

Full-leaf masses are lambda*<=lambda. Root and unqueried-coordinate bounds follow by summing cells. These are density arguments valid at every finite query depth; no depth cutoff is inferred from a finite experiment.

In624's normalized central menus, a retained actual cell mass x=lambda* therefore uses the fields

    shallow: x,
    deep3: x/C3_l,
    deep5: (4/5)x/C5_m,
    doubly deep: (4/5)x/(C3_l C5_m).                       (C3)

They are bounded respectively by lambda,a3,(4/5)a5,(4/5)a35. Multiply each queried cell by the corresponding H_T(c) and then sum. This supplies all16 central modes and32 outside-support responses simultaneously.

The complete512 fee vector can remain unchanged, but the old query evaluation cannot merely substitute theta_eff=lambda*/(wv). For example its old deep3 field would be x/w_l, which need not be at most a3. C3 is the capacity-sensitive evaluation required by this construction.

## 3. The exact gate price

Let C_j>=0 be the complete coefficients for the declared original inventory and future queries, and g=1-c as before. Form each numerical corner gate G_ij using the chosen whole field theta^ij, the common response grids H_T(c) and the same512 coefficients.

For a fixed query, C1–C3 bound the repaired actual response by the gamma-weighted corner responses. Maximizing over phases gives at most the weighted sum of the corner maxima. Consequently

    G_actual >=sum_ij gamma_ij G_ij
                 -g sum_c H_empty(c)(lambda_c-lambda*_c). (C4)

The sign follows from upper-bounding each loss screen and lower-bounding retained mass. This is the unit-inclusive mass-debit coefficient g, not1. Constant outside responses reduce C4 to the earlier product case g h_empty sum(lambda-lambda*).

Thus corner-dependent choices are usable without pretending that numerical corners are actual laws. A positive conclusion requires the averaged corner gate to exceed the weighted ACTUAL capacity deficit in C4. This report proves the construction and that conditional criterion; it proves no uniform positive bound for the deficit.

## 4. A literal finite example shows why clipping is necessary

Use actual ternary pure originals2mod3,0mod9,3mod27. The target leaf3mod9 retains children12,21mod27, each with mass2/27. Give leaf6mod9 mass5/27 uniformly over its three children, and the other three live leaves mass2/9 each, also uniformly. This is a probability obtained by constant thinning of2H3 on every actual survivor leaf.

Its leaf vector is the1/3,2/3 mixture of numerical corners whose target-leaf masses are2/9,1/9, with the weak marker exchanged between leaves3 and6. Retain the target only at the first corner. The averaged target mass is lambda=2/27. Thinning the actual source to this mass gives each surviving child1/27, exceeding the averaged corner deep bound2/81.

The actual target capacity is4/27, below the strong corner's requested2/9. C1 instead retains lambda*=4/81, making each child exactly2/81 and paying mass deficit2/81.

The [exact example program](../../frontier/cover-geometry/corner_theta_actual_capacity_examples.py) and [data](../../frontier/cover-geometry/corner_theta_actual_capacity_examples.json) add the actual quinary originals4mod5,0mod25,1mod125. In their joint target cell,

    lambda=8/10125, lambda*=64/151875,
    lambda-lambda*=56/151875.

All eight repaired actual atoms meet the averaged doubly-deep cap8/151875; the naive atom1/10125 exceeds it. The program passes6257 exact checks, including every6240 prefix pair through resolving heights3. The all-height justification is C2. An independent review reran these checks and verified the actual constant-density source requirement.

## 5. One fixed actual-capacity envelope still has zero optimum

Actual-capacity information is useful but does not by itself guarantee that the global21111 outside exclusion budget passes the complete gate. Fix the literal ternary originals

    2mod3, 1mod9, 13mod27, 31mod81,

and either quinary family

    4mod5,1mod25,31mod125,131mod625; or
    4mod5,1mod25,25mod125,125mod625.

At3 take weak mass1/9 on leaf4mod9 and mass2/9 on each other nonnull leaf. At5 take weak mass3/75 on leaf6mod25 in the first family, or0mod25 in the second, and mass4/75 on each other nonnull leaf. In every case distribute that mass constantly on the actual survivor within its leaf. The actual weak capacities are

    C3_weak=10/81, C5_weak=76/1875.

Keep the central15 mask, the fixed outside budget(2,1,1,1,1), its32 product responses, Report640's complete512 coefficients and exactly the C3 query fields. For these TWO specified actual sources, respectively, every cellwise thinning theta in[0,1]^120 satisfies

    G_rho(theta)<=-(1/200) sum_lm w_l v_m theta_lm,
    G_rho(theta)<=-(1/1000)sum_lm w_l v_m theta_lm,          (C5)

where theta is zero on the mask and null cells. The zero field attains0, so this fixed-source gate has exact maximum0.

The [exact checker](../../frontier/cover-geometry/two_root_actual_capacity_exact_zero_gate.py) and [certificate](../../frontier/cover-geometry/two_root_actual_capacity_exact_zero_gate.json) reconstruct the finite actual pure supports, capacities and all16 normalized query menus. For each specified source,45 nonzero rational selector weights distributed over the16 modes give a convex lower bound on every screen. The resulting debit-minus-mass coefficient at every live cell exceeds the stated positive multiple of w_l v_m. The274 checks use rational arithmetic; no numerical optimizer is executed or trusted. An independent reconstruction passes445 checks, including all120 cells in each case, the16 convex selector mixtures and the exact coefficient inequalities; null and masked cells are explicitly included.

C5 is restricted to those fixed actual rho, the stated outside source and the specified query envelope. It does not exclude a different source construction, conditional outside geometry, sharper query information or an actual surviving configuration. In particular it does not negate the conditional-source positive cases: their H_T(c) are different, and C4 is designed to preserve that distinction.

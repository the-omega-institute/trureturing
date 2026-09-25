# Two exact raw-envelope obstructions on the632 difficult layout

The fixed [Report632](632-a-common-thinning-repairs-a-negative-free-endpoint-gate.md) STAR and actual central source admit no positive certificate in either of the two declared raw-product envelopes below. Both statements have exact selector-mixture duals. They are limitations of these coefficient/menu envelopes, not arithmetic covering counterexamples and not a claim about every possible certificate.

## Fixed data and full scope

Q=(7,11,13,17,19). STAR rows(R,C,I,J,L,M):

    (0,3,0,3,0,15)
    (1,2,0,2,5,11)
    (1,2,0,2,5,11)
    (1,1,0,1,5,6)
    (1,1,0,1,5,6)

Source w=(2,2,2,0,1,2)/9 and v=(4,4,4,4,4,0,4,4,4,4,3,4,4,4,4,4,4,4,4,4)/75. This is source corner(3,4,5,10), with an explicit actual realization using pure2mod3,1mod9,4mod5,1mod25, uniform higher digits, no additional live central pure deletion. Central15 is phase0. The80 cells have positive w_l*v_m and are outside central root pair(0,0). No good-cell mask, matching polynomial, or pair-avoidance conditioning is applied.

Set r_q=1/(q-1), a_q=1/[q(q-2)]. At cell(l,m), the raw responses are R_T=product(q notin T)Z_q, where

    Z_q=1-(r_q+a_q)(1_row=R_q+1_col=C_q)
          -r_q(1_point=(I_q,J_q)+1_l=L_q+1_m=M_q).

The coefficient source is actual_pair_activation_certificate.json, SHA2562e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f. Let c=1084133/201247200,g=1-c. All512 L/W costs and all32 responses are retained. Full inherited selectors are used: actual source, root restriction, weighted live leaf, and deep delta_l on3 / (4/5)delta_m on5; deep selectors are not multiplied by another leaf mass.

## First envelope: one thinning before arbitrary pair central phases

For each of10 edges, charge all12 labels 3^a5^b q^u s^v, a,b in{0,1},(u,v)in{(1,1),(2,1),(1,2)}. The120 moduli are distinct. At each relevant cost index j=32(4a+b)+T, P_j=r_q*r_s+a_q*r_s+r_q*a_s. Define

    S_j(theta)=max(selector s in full menu_j) sum_c s_c*theta_c*R_T(c),
    G_free(theta)=g*sum_c w_l*v_m*theta_c*R_empty(c)
                  -sum_j[g(L_j+P_j)+cW_j]*S_j(theta).

A rational dual with511 exact cost budgets and579 supported selector entries proves, for every theta_c>=0,

    G_free(theta) <= -(1/54)*sum_c w_l*v_m*theta_c.

The exact smallest normalized dual slack is

    36641736777333917410230645393410551 /
    1970714848719392455680000000000000000

which is greater than1/54. Thus every nonzero thinning has strictly negative envelope gate; theta=0 attains0. This excludes a single theta uniform over all pair central phase choices for this fixed STAR/source. It does not, by itself, exclude choosing theta after a full pair-central layout is fixed.

The all-ones baseline equals

    -141614965675533908203951945099 /
     2483100709386434494156800000000.

## Second envelope: fix632's pair central layout before choosing theta

Fix codes(27,27,27,27,50,50,50,50,50,41), in lexicographic edge order, where code=32R+8C+4I+J. All outside endpoints/lifts remain charged by the same caps. At each cell and edge define

    beta_qs(c)=(r_q*r_s+a_q*r_s+r_q*a_s)
                *(1+1_row=R+1_col=C+1_point=(I,J)).

The verifier enumerates all12 labels independently at all80 cells for each edge and checks this beta. Set

    A_c=w_l*v_m*(R_empty(c)-sum_edges beta_qs(c)*R_{q,s}(c)),
    G_fixed(theta)=g*sum_c A_c*theta_c
                   -sum_j[gL_j+cW_j]*S_j(theta).

A second rational dual with511 exact cost budgets and565 supported selector entries proves

    G_fixed(theta) <= -(1/78)*sum_c w_l*v_m*theta_c

for every theta_c>=0. The exact smallest normalized slack is

    14313130449308111871935702801406239 /
    1103600315282859775180800000000000000

which exceeds1/78. Again the bounded LP optimum is exactly0. This is one fixed pair-central layout for which every raw-envelope thinning fails; it is stronger than the first minimax-ordered obstruction, while remaining only an envelope obstruction.

The all-ones baseline equals

    -138602168147328176324180268139 /
     2483100709386434494156800000000.

## Why each dual proves its statement

For each charged row j, the certificate gives nonnegative rational probabilities p_jk summing exactly to1. Therefore S_j(theta) is at least the probability-weighted average of its selector linear forms. The verifier computes the resulting exact coefficient charge at each cell. It exceeds the corresponding source coefficient by more than(1/54)w_l*v_m in the free case, and(1/78)w_l*v_m in the fixed case. Multiplication by any nonnegative theta and summation proves the displayed inequalities. The theta<=1 constraints are unnecessary for this stronger homogeneous domination; no omitted upper-bound dual term is required.

## Implication and limits

Report632 already has a positive certificate on this same actual source, STAR and fixed pair-central codes using its matching/conditional responses. The new second dual establishes that retaining raw responses and optimizing a single thinning cannot recover that result with the stated complete union-bound/selector envelope. The obstruction is not explained solely by asking theta to work uniformly before pair phase choices: it persists when those phases are fixed. This points to conditional pair structure or another sharper joint bound as a necessary change to this raw route, without claiming uniqueness of the conditional method or failure of actual survival.

## Verification and replay

The [portable exact verifier](../../frontier/cover-geometry/difficult_star_raw_envelope_dual.py)
includes both rational selector mixtures; its [result data](../../frontier/cover-geometry/difficult_star_raw_envelope_dual.json)
include every response, fee and coordinate slack. It uses standard-library
Fraction arithmetic and the pinned coefficient input;4132 exact checks pass.
An independent checker imports no producer, reconstructs all32 responses,
all16 menus, every pair label and both full fee arrays, and verifies the
511 normalized budgets and80 strict coordinate inequalities in each case.
Its6002 exact checks pass. A fresh isolated producer execution reproduces
the result JSON byte for byte. These are ordinary exact certificates, not
new Lean verification. The supplied verifier needs no floating solver.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/difficult_star_raw_envelope_dual.py

## A matched convex blend cannot improve the conditional envelope

### 1. Precisely matched inputs

Fix ONE actual family, ONE actual central law with nonnegative cell weights μ_c, its actual star submeasures ξ_q(c), and their strictly positive masses Z_q(c), for Q={7,11,13,17,19}. Set

    σ_c = tensor_q ξ_q(c),  P_c = product_q Z_q(c),
    R_T(c) = product_(q outside T) Z_q(c).

For the ten edge union events E_e(c), use one and the same nonnegative cap field β_e(c) from Report629. Thus σ_c(E_e)≤β_e R_e. Define

    u_e = β_e/(Z_q Z_s),  e={q,s},
    Δ_c = sum_e β_e R_e = P_c sum_e u_e,
    A_c = P_c−Δ_c.

All label roles remain globally fixed. No phase is chosen again at another cell or query. The strict-good set Γ consists of all cells on which every induced independence polynomial is positive:

    S_D(u) = 1−sum_(e in D) u_e
                +sum_(e<f in D, disjoint endpoints) u_e u_f >0.

There are no degree-three terms because a matching in K5 has size at most two. On Γ, Report629 supplies one pair-avoiding submeasure ζ_c with exact certified mass

    H_empty(c) = P_c S_all(u),

and simultaneous query grids

    H_T(c) = R_T(c) S_{edges disjoint T}(u).

Outside Γ set all H_T=0 and ζ_c=0. Write F_c for avoidance of every actual edge union.

### 2. The pointwise comparison

On a good cell,

    H_empty−A = P sum_(e<f, disjoint) u_e u_f ≥0.        (D1)

For every edge subset D and e∈D, the independence-polynomial recurrence is

    S_D = S_(D\{e})−u_e S_(D\N[e]),                     (D2)

where N[e] contains e and edges meeting e. Every induced polynomial on the right is positive in Γ. Successively delete edges to obtain

    0<S_D≤S_empty=1.

Consequently, on Γ every query response satisfies

    0<H_T≤R_T.                                         (D3)

If sum_e u_e<1, then for every D the displayed degree-two formula gives

    S_D≥1−sum_(e in D)u_e≥1−sum_all u_e>0.

Hence any cell outside Γ has sum_e u_e≥1 and therefore A≤0. Together with (D1), this proves, on all cells,

    H_empty≥max(0,A),       0≤H_T≤R_T.                 (D4)

This argument specifically uses the K5 degree-two matching formula for the implication from a positive first-order residual to strict goodness. It makes no assertion for a differently specified conditional criterion or cap polynomial.

### 3. One actual hybrid source and all queries

Let t_R(c),t_C(c)≥0 with t_R+t_C≤1. The conditional term vanishes off Γ. A legitimate pair-avoiding hybrid is

    χ_c = t_R σ_c|F_c + t_C ζ_c.

It is dominated by σ_c, so it preserves all inherited pure-source/Haar caps. Its mass and every cylinder query admit the simultaneous envelopes

    M_hyb(c) = t_R A_c + t_C H_empty(c),
    J_hyb,T(c) = t_R R_T(c) + t_C H_T(c).             (D5)

The possibly negative M_hyb is only a lower estimate. It is not claimed to be a measure or the actual cell mass. These envelopes remain usable after imposing all remaining actual originals with the full original-loss inventory.

Now use the pure conditional source

    χ*_c = (t_R+t_C) ζ_c,

with the SAME scalar thinning on mass and all32 responses. Its envelopes are

    M*(c) = (t_R+t_C) H_empty(c),
    J*_T(c) = (t_R+t_C) H_T(c).

Equations (D1)--(D4) imply pointwise

    M*≥M_hyb,                 J*_T≤J_hyb,T.            (D6)

Off Γ, the first inequality is 0≥t_R A, and the second is 0≤t_R R_T.

Let S_j(J_T) denote the maximum of the COMPLETE inherited central selector menu for coefficient j, applied to the indicated grid. Every selector coefficient is nonnegative, including the correctly normalized deep selectors; no extra factor μ_c is inserted into deep selectors. Thus S_j is monotone for pointwise grid order. With

    g=1−1084133/201247200>0,
    d_j=g L_j+(1−g)W_j≥0,

and all512 j retained, the complete hybrid gate

    G_hyb = g sum_c μ_c M_hyb(c) −sum_j d_j S_j(J_hyb,Tj)

satisfies

    G_hyb≤g sum_c μ_c M*(c)−sum_j d_j S_j(J*_Tj)
          =G_cond(t_R+t_C).                             (D7)

The pure conditional choice is itself a hybrid with t_R=0. Therefore their optimized gates are equal when both optimize over these same cell thinnings and envelopes. Mixture coefficients may depend on the actual family, provided each resulting source uses the one coherent family and one common field across all its queries. If the coefficients were fixed across a class of families, their sum is still fixed; the good-cell mask is already part of each family's conditional response. This comparison does not need or assert concavity under that adaptive mask.

### 4. Report631's global pair maxima are also dominated

Report631 pays raw pair events by sum_j P_j S_j(t_R R), which allows a separate global selector maximum for each numerical label. For each actual fixed cap field β, each such maximum bounds that label's integrated actual central-role cap. Therefore

    sum_c μ_c t_R(c) Δ_c ≤ sum_j P_j S_j(t_R R).

Replacing this conservative global pair charge by the left side can only increase the gate. Equation (D7) then dominates this increased gate. Thus the same conclusion holds for a hybrid which uses Report631's max-per-label raw pair budget.

In particular, Report631's uniform positive raw certificate immediately implies at least the same gate lower bound for the fully masked conditional responses of each actual family within Report631's existing STAR and pure-source scope, using its same fixed thinning. The mask may vary by family; the pointwise comparison supplies the uniform lower bound without a Jensen step through that mask. This transfers an already established positive bound; it does not enlarge the class of admitted stars or numerical originals.

### 5. Why this is envelope dominance, not source dominance

On Γ let m_c=σ_c(F_c)>0. The Report629 construction has

    ζ_c=α_c σ_c|F_c,   α_c=H_empty(c)/m_c∈(0,1].

Thus the actual hybrid equals (t_R+t_C α_c)σ_c|F_c. It supplies no new local shape compared with the restricted raw source. Moreover χ*_c≤χ_c as actual measures on good cells. A smaller actual source can have a better certified lower gate because its jointly improved conditional query bounds and mass lower bound remove slack in the raw first-order envelopes. No claim is made that the pure conditional source dominates the hybrid's actual mass or its actual nonlinear moment gate.

### 6. Exact limits and research consequence

The no-improvement conclusion applies only to the convex coefficient budget t_R+t_C≤1, with the same ξ,Z,β, full strict-good mask, first-order raw union loss, inherited conditional H_T, and nonnegative complete costs. If actual m_c=σ_c(F_c) is certified, the sharp local domination budget is t_R+t_C α_c≤1 with α_c=H_empty/m_c; this can permit t_C>1. Such rescaling by actual m_c/H_empty is outside the theorem and is not ruled out. It need not hold if the raw side gains actual event-overlap savings or smaller event caps not also made available to the conditional side; uses different star submeasures; produces sharper post-deletion query bounds; or introduces a source with a genuinely different conditional law. An arbitrarily restricted fixed mask Γ0⊊Γ also cannot claim this comparison on its discarded good cells.

Accordingly, merely adding a raw/conditional mixture LP to the present same-cap gate cannot improve its optimum. A productive next source route must strengthen one of these inputs or discharge the separate arbitrary-STAR/missing-inventory obligations. This result does not say that the current conditional optimum is positive for every layout, or that an actual covering exists when a gate fails.


The finite comparison above connects the actual source interfaces of Reports629
and631. It does not require averaging through a changing good-cell mask.
Thus the positive raw gates in Reports631 and633 transfer to the corresponding
conditional envelope for each admitted actual family, with the same lower
bound and no enlarged arithmetic scope. Conversely, the fixed-family dual
above shows why this comparison can be strict: the conditional response on
Report632 succeeds where every thinned raw envelope fails.

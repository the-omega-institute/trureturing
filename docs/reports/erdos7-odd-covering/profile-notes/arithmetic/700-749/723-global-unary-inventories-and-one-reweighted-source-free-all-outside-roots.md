# Global unary inventories admit a common-source head minimax

The once-only eleven-label inventory at each of 11,13,17,19 can be passed directly to a finite minimax on the actual head. One normalized head probability controls all 192 shallow queries, all 132 multi-support shallow deletions, every higher nonternary original, and the later 23/29 continuation. The outside roots of the 44 singleton labels need not be fixed: their head projections and a strict certificate suffice.

Two explicit projection templates on the actual 75/85-cell heads pass this criterion for EVERY assignment of those 44 outside roots, every 132 multi-support phase assignment, and every permitted higher-height extension. For one actual root assignment in each template the original fixed head weights give a negative gate, while the new common head law gives a positive gate. This proves a useful conditional bridge and a failure of the fixed-weight specialization. It does not prove the criterion positive for arbitrary 44 head projections.

All families are finite, have distinct odd numerical moduli greater than one, are supported on{3,5,7,11,13,17,19,23,29}, and satisfy whole-familyv 3<=2. The results are ordinary proofs and exact rational certificates, not new Lean verification.

## 1. One actual inventory, followed by normalized conditional kernels

Fix either actual eleven-class 3,5,7 head from Reports 715–720. Its surviving residues u modulo 315 formU, of size 75 or 85. The four outside pure roots are 0. Write

    B={11,13,17,19},
    C={3,5,7,9,15,21,35,45,63,105,315}.

For each q in B and c in C, fix the HEAD component alpha_(c,q) mod c of the original with complete numerical modulus c*q. Its outside component beta_(c,q) mod q may be arbitrary. Because gcd(c,q)=1, each pair gives exactly one actual full CRT residue; different rows do not receive independent phase choices.

The common head inventory is

    n_q(u)=sum_(c in C)1_(u=alpha_(c,q) mod c).

For one entire actual outside-root assignmentbeta, let R_q^beta(u) be the union of its forbidden nonzero q roots at that row. Put

    r_q^beta(u)=|R_q^beta(u)|<=n_q(u),
    t_q^beta(u)=q-1-r_q^beta(u),
    tbar_q(u)=q-1-n_q(u).

Choose a head support G contained in U on which every tbar_q>0. The inventory theorem implies that only q=11 can fail this condition, on at most one head row. This ensures nonempty G for the 75/85-cell heads, but does not alone establish a positive continuation gate.

Fix ONE probability p on G. For each actual beta, define a normalized conditional source eta_beta by:

- sample u with law p;
- conditional on that same u, independently sample each q first root uniformly from its actual pure-live roots outside R_q^beta(u);
- extend all deeper nonternary digits by independent Haar, conditional on these joint first digits.

This source avoids the head, four pure outside roots and all 44 actual singleton originals. Every quantity below refers to this ONE eta_beta. Different beta assignments give different actual supports; their measures are not combined.

The monotonicity is specifically a statement about NORMALIZED conditional kernels. Their individual live-root masses obey

    1/t_q^beta(u)<=1/tbar_q(u).                         (GI1)

It is not a claim that the mass or H_T of an unnormalized restricted xi decreases when fewer roots are removed. The source eta_beta always has total mass 1, and the head law p stays fixed as beta varies.

## 2. One 192-screen table, independent of all 44 outside colors

Forj=0,1,2, E subset{5,7}, T subset B, let

    c=3^j product_(q inE)q,
    L_(E,T)=product_(q inE unionT)q/(q-1),
    C_(c,T)(p)=max_(a mod c)
        sum_(u=a mod c)p(u) product_(q inT)1/tbar_q(u).   (GI2)

There are 12 head modes and 16 outside supports, hence 192 values; C_(1,empty)=1. For any single complete shallow query, the source mass is

    sum_(u=a mod c)p(u)
        product_(q inT)[1_(queried root is live at u)/t_q^beta(u)].

Discarding its indicators and applying GI 1 proves it is at mostGI 2. Thus ALL query cylinders are bounded simultaneously by the same p and the same actual source. Maximizing a head phase in each cap supplies an upper bound; it does not construct different actual source laws.

This is the conditional-product special case of the sixteen-response interface. Before normalization the row response is H_T=product_(q notinT)m_q; after normalization, the queried coordinates contribute their reciprocal live-root counts. No multivariate Shearer claim is required for the present simpler source.

## 3. Pay the complete remaining inventory on that same source

There are exactly 132 shallow labels with at least two outside coordinates:12 head cofactors times 11 outside supports of size at least two. All their phases are arbitrary. The complete common debit is

    B(p)=sum_(c,T:|T|>=2) C_(c,T)(p).                  (GI3)

Because every deeper nonternary coordinate is Haar conditional on the joint first digits, the prefix-tail lemma applies with exact cylinder ratioq^(1-e). Define

    A(p)=sum_(c,T)(L_(E,T)-1) C_(c,T)(p),
    K(p)=sum_((c,T)!=(1,empty))L_(E,T) C_(c,T)(p).     (GI4)

A pays all numerical core labels with some nonternary exponent at least two, including pure powers. B pays only the disjoint shallow multi-support inventory. Restrict the SAMEeta_beta by all these actual forbidden events. The resulting nu has mass at least 1-A-B and complete nonunit query sum at mostK.

Therefore the existing actual pure-conditioned 23/29 continuation is positive if

    Delta(p)=(566/49)(1-A(p)-B(p))-K(p)>0.              (GI5)

All actual 23/29-bearing originals have arbitrary fixed phases and permitted nonternary heights. No new prime support or ternary height is introduced. Deleting actual events only decreases query masses; deeper Haar ratios are used oneta_beta before deletion.

Equivalently, set R=566/49. Then

    Phi_alpha(p)=sum_((c,T)!=(1,empty))
      [1+(615/49)(L_(E,T)-1)+R*1_(|T|>=2)] C_(c,T)(p),

    Delta(p)=R-Phi_alpha(p).                            (GI6)

For fixed 44 head projections, minimizingPhi over one head probability p is a finite rational LP. Every selector epigraph uses the same p. The root-color assignment does not enter this conservative LP.

## 4. Haar conversion and the f<=U representation

For each actual beta the exact first-digit density ofeta_beta on a live cell overu is

    315 p(u) product_(q in B)q/t_q^beta(u).

Thus the same projection certificate gives the simultaneous Haar bound

    D0=315 max_(u inG)p(u) product_(q in B)q/tbar_q(u).   (GI7)

The surviving Haar density is at least

    49 Delta(p)/(616 D0)>0.                            (GI8)

This follows from the same unnormalized mass coefficient 49/567 and outside pure-law density cap 616/567 used in Report 717. Neither factor changes when beta varies.

If the original sixteen-response interface requires a submeasure dominated by the fixed head weights a(u)=w_l/24, one may rescale. Let

    Z_beta(u)=product_q t_q^beta(u)/(q-1),
    epsilon=min_(p(u)>0)[a(u)product_q tbar_q(u)/(q-1)]/p(u)>0,
    f_beta(u)=epsilon p(u)/(a(u)Z_beta(u)).

Then 0<=f_beta<=1 for every actual beta, and applying f_beta to the unnormalized row product yields precisely epsilon eta_beta. This is one common function across all rows and queries. The positive gate and density conversion are homogeneous, so the normalized construction is within that source class after one scaling. In particular, permitting a nonuniform p has not silently granted a different source for different query screens.

## 5. Two exact projection templates

Use the same actual head originals as before. The seven mixed head phases at numerical labels 15,45,21,63,35,105,315 are respectively

    opposite:11,2,1,58,3,74,187;
    same:     1,22,1,16,3,74,47.

The common pure head originals are 0 mod3,1 mod9,0 mod5,0 mod7. The following entries fix ONLY alpha_(c,q), not the outside q root of the original c*q.

Opposite-root template:

|c|q=11|q=13|q=17|q=19|
|---|---:|---:|---:|---:|
|3|2|1|2|2|
|5|3|2|3|2|
|7|2|4|5|5|
|9|5|7|8|4|
|15|8|1|8|2|
|21|8|4|2|19|
|35|23|32|33|27|
|45|32|16|17|31|
|63|8|40|61|13|
|105|23|46|61|52|
|315|256|286|313|157|

Same-root template:

|c|q=11|q=13|q=17|q=19|
|---|---:|---:|---:|---:|
|3|2|2|2|2|
|5|2|3|3|3|
|7|4|6|6|4|
|9|5|2|8|4|
|15|2|11|13|13|
|21|4|2|13|5|
|35|17|23|18|18|
|45|17|2|17|43|
|63|8|53|13|61|
|105|17|17|88|101|
|315|277|58|218|263|

The exact witness provides65 positive head atoms in the first case and59 in the second. Each law is an integer table of total20004, hence p(u)=k_u/20004. Those tables and full actual191-class representatives are in[rational witnesses](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_inventory_source_witnesses.json). No optimality assertion is needed: their exact feasibility and strict primal gates are sufficient.

The independently reconstructed exact values are:

|Head|Delta|D0|Haar survivor lower|
|---|---|---|---|
|opposite|638398042571354575733/774763098377748480000|133399/6668|638398042571354575733/194854545919174901760000|
|same|326689328847837768548357/474662133871574777856000|103694305/3840768|326689328847837768548357/161103898535152780247040000|

The gates are respectively 0.8239912870... and 0.6882565630..., and the Haar lower bounds 0.00327627995... and 0.00202781765....

The quantifiers are:

    for each of the two fixed head/projection templates,
    there exists the displayed ONE rational head law p,
    such that for EVERY simultaneous choice of the44 outside roots,
    EVERY132 shallow multi-support phase assignment,
    and EVERY finite allowed higher-height/23/29 extension,
    the actual normalized conditional construction eta_beta supplies
    one common positive continuation certificate.

The head law is fixed before the free root choices. Its actual conditional outside support is rebuilt from that one chosen family. This does not claim a single literal measure is supported on the survivors of all different root assignments simultaneously.

## 6. Why deleting only extreme-load rows does not settle this bridge

The exact witnesses also provide actual global outside-root choices realizing r_q(u)=n_q(u) on EVERY live head row simultaneously. The maximum active counts across the four axes are(7,7,6,4) and(6,5,5,5). No row has count 9 or 10 on any axis, so the previous extreme-row deletion rule removes nothing.

For these actual configurations, keep the old head weights w_l/24 and use the same unary-product source, the same uniform 132 multi-support debit and the same complete-height query fees. The exact unnormalized gates are

    opposite: -2718857266981/8989483991040;
    same:     -6388565015627/26968451973120.

Both are negative. A common rescaling cannot change their sign. The displayed nonconstant head laws restore a strict positive gate for exactly that sufficient mechanism. Thus a bound ruling out only extreme rows does not prove the fixed-weight specialization sufficient; moderate loads and the distribution of shared query fibers still matter.

These negative values are not covering examples, not failures of all common sources, and not failures of the full multivariate avoidance construction. They only reject the specified fixed-weight unary-product specialization; the positive certificates directly exhibit its permitted repair by one common reweighting.

## 7. The remaining uniform theorem is a finite game on global inventories

Let alpha range over the globally fixed 44 head projections, with one phase per numerical label. Let G_alpha be the head rows where all tbar_q>0. A sufficient target for arbitrary singleton phases on either fixed head is

    max_alpha min_(p probability on G_alpha)Phi_alpha(p)<566/49. (GI9)

This is a finite max-min problem, with the inner problem an exact LP and the outer configurations constrained by the once-only cofactor inventory. All phase choices must precede the row counts. The capacity and binomial-moment inequalities from the inventory theorem constrain these configurations and any common test weight; they do not permit arbitrary independent row loads.

The present two exact certificates establish GI 9 only at their two declared projection points, while quantifying over all their outside colors and continuations. Numerical searches suggest candidate head laws but do not bound the outer maximum. No universal positivity or counterexample toGI 9 is claimed.

## Exact verification boundary

[exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_inventory_source.py) uses only the standard library under `python3 -I -S -B -O`. It reads the actual191 full numerical originals and integer head laws; checks complete shallow labels, literal head supports, global eleven-label inventories, all actual row root unions, the simultaneous count-profile realization, normalized primal support, all192 rational screen caps, all132 shallow debit terms, complete geometric-height fees, Haar density caps and common admissible scalings. The retained exact result is[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_inventory_source.json).

The free-color theorem is proved by GI 1–GI8; the checker does not claim to enumerate every free color assignment. Numeric search, fixed-weight search and LP solver outputs are proposals only and are not needed to consume the exact witnesses.


The global row-capacity bounds are in
[Report 721](721-common-original-label-inventory-limits-simultaneous-bad-head-rows.md).
The full-height and 23/29 continuation is the common-source construction of
[Report 717](717-four-fixed-shallow-families-survive-arbitrary-nonternary-heights.md).

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_inventory_source.py
```

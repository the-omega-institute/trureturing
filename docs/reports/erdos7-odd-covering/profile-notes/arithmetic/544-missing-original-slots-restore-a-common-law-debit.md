# Missing numerical slots restore a common-law mixed debit

For any finite actual two-copy family on Q={5,7,11,13,17,19}, if at least two of the three full numerical labels 55,77,385 occur at most once, the unchanged PA law has complete query norm strictly below 257/51. Consequently, any strict all-laws lower witness above that target must contain two original classes at at least two of those three labels. All other original phases and finite heights are arbitrary. Such a strict all-laws lower witness must additionally satisfy: for each actual modulus-35 class, at least two of those full labels must have both old phases disjoint from that class; otherwise the same upper law closes the target.

The result comes from choosing legal comparison completions in empty original slots and debiting the same actual mixed 5/7 deletion. A weighted missing-label condition is stronger than this simple numerical corollary. A nested family also demonstrates why the choice matters: a fixed zero-debit completion fails even with the best labelwise maximizing final query, whereas another globally fixed completion certifies the same family and same PA law. No original class or actual kernel is changed.

Throughout, Q={5,7,11,13,17,19}, original numerical multiplicity is at most two, the original family is finite with all phases fixed, and every query height is retained. These are ordinary mathematical deductions from [report348 CP/PA](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md) and the nested constructions of [report537](537-two-copy-lower-witnesses-require-nested-pure-five-prefixes.md) and [report538](538-near-maximal-mixed-packing-preserves-the-anchor-query-hinge.md). They are not Lean results and do not resolve the remaining arbitrary two-copy case or unrestricted Erdős #7.

## 1. The same-law phase-debit inequality

Let H be product Haar, u and v the complete pure-5 and pure-7 forbidden masses, w5=1-u, w7=1-v, d5=1/2-u, and d7=1/3-v. Let sigma be Haar restricted to the complete pure survivors S5 times S7. Let U be the actual mixed 5/7 forbidden union inside that survivor, eta=H restricted to U, and m=eta(1). Later coordinates initially carry Haar.

The actual initial measure is lambda0=sigma-eta. Use precisely report 348's actual kernels Kq, without intermediate normalization, and its completed probability kernels Ktilde_q. In particular, at gq=0 the actual density is zero. Write

    (q,tq,Cq,aq)=(11,2,5/3,1/3),(13,2,3/2,1/4),
                 (17,4,2,1/4),(19,4,9/5,1/5).

For each q-exponent e and slot j=1,2, extend that slot's actual old-cofactor phases to a comparison query Lq,e,j. The unit may always be added. An entirely absent slot may instead be left zero. Every completion is fixed before taking the integrals and changes no original class or kernel. Put beta_q,e,j=(q-1)/(2q^e), whose sum over all e,j is one, and define

    Jq=sum_(e,j) beta_q,e,j * integral (Lq,e,j-tq)_+
                                      d(eta Ktilde_<q).
    JL=integral (L-3)_+ d(eta Ktilde_all)

for a finite complete final query L including the unit.

Let Fq(u,v), alpha_PA(u,v), and Phi_PA(u,v) be the unchanged PA comparison quantities. Then the one actual final subprobability lambda satisfies

    lambda(1)>=alpha_PA+(1/12-m)+sum_q aq Jq,                 (PD1)
    lambda(L-1)<=2 lambda(1)+Phi_PA-JL.                     (PD2)

Indeed the union bound and convexity give, pointwise,

    1-sq <= aq sum_(e,j) beta_q,e,j (Lq,e,j-tq)_+.

Positivity gives lambda0 K_<q <= lambda0 Ktilde_<q. The completed process is linear in its initial measure, so integrating the nonnegative hinge splits exactly into its sigma contribution minus its eta contribution. The former is bounded by the unchanged Fq. Thus the actual q-row loss is at most aq(Fq-Jq); summing proves PD1. The same subtraction with the completed final process proves the hinge bound in PD2, using L-1<=2+(L-3)_+. This uses one actual source and one normalization throughout.

Set T=257/51 and retain report 348 NC4's exact constants

    c0=6168733163201163811/542935350932041267200,
    A5=44887686823492905683/27146767546602063360,
    A7=20281636668601030051/20313907687933516800,
    A57=585035299774741193/203139076879335168.

The identity (T-2)alpha_PA-Phi_PA=-c0+A5 d5+A7 d7+A57 d5 d7 implies that

    A5 d5+A7 d7+A57 d5 d7
      +(T-2)[1/12-m+sum_q aq Jq]+JL >= c0                 (PD3)

is sufficient for this query's normalized expectation to be at most T. A uniform bound for all finite queries passes to the complete labelwise query sum by choosing each label's maximizing cylinder under the same lambda, then exhausting the labels. PA already gives alpha_PA>0, so the single normalization is legitimate.

## 2. A nested actual family with separated mixed and loss regions

Fix N,K>=4. For p=5,7 use pure originals p^(e-1) and 2p^(e-1) modulo p^e, 1<=e<=N. For every 1<=a,b<=N use the two mixed originals

    (3*5^(a-1),3*7^(b-1)), (3*5^(a-1),4*7^(b-1))

at modulus 5^a 7^b. Their mixed union is U=D5 times D7, with

    H5(D5)=(1-5^-N)/4,
    H7(D7)=(1-7^-N)/3,
    m=(1-5^-N)(1-7^-N)/12.

All prefixes are written least-significant-digit first. This is the transposed packing of report 538: U has 5-root 0 or 3 and avoids root 4. The pure-5 layout has P=[0]_5 and C=[0]_25 inside P. Also

    d5=1/(2*5^N), d7=1/(3*7^N), w7=2/3+1/(3*7^N).

For the four later primes choose paths

    w11=(4,0), w13=(4,1), w17=(4,2,0,0), w19=(4,3,0,0).

Let E_q,1 be the whole 5-coordinate and E_q,i its path prefix of length i-1 for 2<=i<=tq+1. At each 1<=e<=K and 1<=i<=tq+1 add the two originals of modulus 5^(i-1)q^e with 5-condition E_q,i and q-terminal digits 2i-1 and 2i at depth e. These q-cylinders are pairwise disjoint: their first nonzero digits are distinct, and 2(tq+1)<q. Each numerical label has exactly two classes. The all-zero point survives the full family.

Write kq(x5)=sum_i 1_(E_q,i)(x5). Then

    gq(x5)=1-2 kq(x5)(1-q^-K)/(q-1),
    hq(x5)=min(Cq,1/gq(x5)), sq(x5)=hq(x5)gq(x5).

The only loss region is the deepest cell Aq=E_q,tq+1, where

    1-sq=ell_q=aq[1-(tq+1)q^-K].

The four Aq are disjoint and have mass 5^-tq. Every previous row has mass one on the next deepest cell. Hence the exact actual row loss and the local Jensen charge on the actual pre-row measure are

    Delta_q=w7*5^-tq*aq[1-(tq+1)q^-K],
    Charge_q=w7*5^-tq*aq(1-q^-K).

Their ratios tend to one simultaneously. On U, every kq equals one, so each actual row has mass one and agrees with its completed row. The transported removed measure has independent later coordinates, each Haar restricted to its globally active two pure-q combs and normalized. These statements do not assert sharpness of the subsequent PA convex comparison.

## 3. Fixed zero-debit completions remain insufficient even with the best maximizing final query

Choose each missing old-cofactor phase inside a pure forbidden cylinder of a prime dividing that cofactor; use the globally active pure comb if the cofactor uses only previous later primes. On U, completed previous rows equal actual rows, so these missing phases vanish there. The actual nonunit slot cofactors all lie in 5-root 4. Thus each active slot load is one on U, and absent slots may be zero: all four Jq are zero.

We now characterize the largest JL achievable by a final query which maximizes every numerical label under the actual final lambda. This is stronger than merely checking one arbitrary query.

For a label with positive later-prime support A, let

    c_A=product_(q in A) q^-nq,
    H_A=product_(q in A) hq(1),
    f_A(x5)=product_(q in A) hq(kq(x5))
             *product_(q notin A) sq(kq(x5)).

At every positive q-exponent n, either the cylinder with first nonzero digit q-1 at depth n, or the nested cylinder q-1 modulo q^n, avoids every original q-cylinder for every x5. Such phases attain the pointwise upper bound hq(x5)q^-n. Therefore they simultaneously maximize the later-coordinate contribution conditional on any fixed old cylinder. Integrating all later coordinates leaves the weight c_A f_A(x5). Outside 5-root 4, f_A=H_A.

**Every maximizing label involving 5 or 7 has zero mass under the transported eta.** Three cases prove this, including arbitrary choices of later phases.

1. If the label involves 7, replace its 7-phase by 5 modulo 7^b. This cylinder is wholly pure-surviving and disjoint from D7. All later kernels depend only on x5. The replacement weakly increases the actual cylinder mass; if its previous transported eta mass was positive, the increase is strictly positive. A maximizer therefore has zero eta mass.
2. Suppose it involves 5 but not 7, with 5-exponent a>=2. A cylinder meeting U lies outside 5-root 4, where the later-coordinate factor is constant and bounded by c_A H_A. Positive transported eta mass makes its actual mass strictly less than c_A H_A w7 5^-a. A 5-cylinder with prefix (4,4) has no pure or mixed deletion. Here kq=2 for ALL four rows, not one; since tq>=2, all sq=1, while hq(2)>=hq(1). With the safe later phases its mass is at least c_A H_A w7 5^-a. Thus the first cylinder cannot maximize.
3. For 5-exponent a=1 and no 7, only roots 0,3,4 survive. The root-4 mass with safe later phases is at least

       c_A H_A w7 [1/5-sum_q aq 5^-tq]
         =c_A H_A w7*(3299/18750).

   This follows from hq>=hq(1), disjoint loss cells, and ell_q<=aq. Root 0 has mass at most c_A H_A w7*(63/625), because H5(S5 intersect root0)=1/10+1/(2*5^N). Root 3 has mass at most c_A H_A w7*(801/8005), because the whole root belongs to D5 and (w7-H7(D7))/(5w7)<=801/8005. Both bounds are strictly smaller than 3299/18750 for N>=4. Hence all maximizing root choices are in root 4.

In the second case, arbitrary later phases only decrease the outside-root constant. In the first case, the gain from removing mixed deletion is exactly the relevant transported eta mass, in addition to any recovered pure mass. Thus these are statements about every maximizer, not merely the existence of one convenient maximizer. Labels involving both 5 and 7 belong to the first case: they need not maximize at 5-root 4.

Consequently a complete maximizing query, restricted to U, contains only the unit and later-only labels. Put hq=hq(1). Under eta/m, the four later coordinates are independent, with cylinder bounds hq/q^n. The same conditional convex comparison used in report 348 bounds the final hinge by the product of independent Nq with

    Pr(Nq=1)=1-hq/q,
    Pr(Nq=n)=hq(q-1)/q^n, n>=2.

The nested safe phases q-1 modulo q^n attain these laws and maximize every later-only label. They can be combined with maximizing phases for every label involving 5/7. Thus the upper bound is attained by one globally fixed complete maximizing layout:

    sup_(labelwise maximizing layouts) JL
      =m E(product_q Nq-3)_+.                             (PD4)

The infinite statement follows by monotone convergence; its first moment is finite. For finite query inventories the same value is an upper bound.

At N=K=4, exact rational arithmetic gives

    m=4992/60025,
    E(product_q Nq-3)_+
      =4841508204833317525789/81565003794396764378880,
    max JL=4841508204833317525789/980757081882745549247250.

Indeed, if p1_q=1-hq/q and p2_q=hq(q-1)/q^2, the hinge equals

    product_q[1+hq/(q-1)]-3
       +2 product_q p1_q+sum_q p2_q product_(r!=q) p1_r.

With the zero-debit stage completions, even this maximal JL leaves

    c0-A5 d5-A7 d7-A57 d5 d7-(T-2)(1/12-m)-max JL
      =1033608573342003864932556253000744351
        /232113625594504985939851425896313600000 >0.         (PD5)

This refutes both universal and existential repair by final maximizing phases alone WHILE THESE STAGE COMPLETIONS ARE FIXED. It does not rule out another completion, another comparison bound, or another law, and is not a lower bound on the actual PA query norm.

## 4. A weighted missing-label debit for arbitrary actual families

Return to any finite actual two-copy family on Q. Fix two distinct nonunit old 5/7-smooth numerical cofactors d1,d2. For each e>=1 let n1,e and n2,e be the numbers of original classes at the full numerical labels d1*11^e and d2*11^e. Each is 0,1,or2. Define

    Gamma=sum_(e>=1) [5/11^e]*(2-max(n1,e,n2,e))
          =1-sum_(e>=1) [5/11^e]*max(n1,e,n2,e).             (PD6)

Only the latter occupancy sum is finite; the leading one retains the entire free exponent tail. In particular 0<Gamma<=1 for a finite family.

For every cylinder R modulo lcm(d1,d2), there is one fixed assignment of the actual first-11 slots and their comparison completions such that

    J11>=Gamma*eta(R).                                    (PD7)

To prove this, at exponent e put the n1,e occupied cofactor-d1 phases in the first n1,e slots, and independently put the n2,e occupied cofactor-d2 phases in the first n2,e slots. All original phases remain unchanged. There are exactly 2-max(n1,e,n2,e) slots where both labels are absent. In every such slot include the unit and put the two missing phases at R's respective d1 and d2 projections. Their compatible intersection is R. The query load is at least three on R, so its threshold-two hinge is at least 1_R. Other terms are nonnegative. Integrating against the one eta and summing the exact beta weights proves PD7. Completing entirely absent exponent slots is allowed: these are comparison queries, not new original classes or changed kernels.

Therefore the following is a sufficient region for the unchanged PA law, with every original and query height retained:

    A5 d5+A7 d7+A57 d5 d7
      +(T-2)(1/12-m)
      +(T-2)*Gamma*max_(R mod lcm(d1,d2)) eta(R)/3 >= c0.   (PD8)

Choose one maximizing R from this finite cylinder partition and fix the pair, slot assignment and all completions as above. Then PD3 holds for every final query because the other Jq and JL are nonnegative. The same final normalized law has R_Q<=257/51. The slot assignment is lawful separately at each full numerical label and exponent; no previously fixed residue is reoptimized, and the choice of R does not depend on the point being observed or the eventual query.

The mass of a particular removed cylinder need not be supplied as an extra hypothesis. Write delta=1/12-m and let Sraw be the sum of the raw masses of all mixed 5/7 original classes, including multiplicity. Then Sraw<=1/12. For every one of these actual classes C,

    delta=(1/12-Sraw)+(Sraw-m)>=H(C)-eta(C).                (PD8a)

Indeed Sraw-m is the sum of the loss outside the pure survivor and the overlap remaining inside it. It dominates each individual pure-overlap loss H(C)-eta(C). This is a statement about the same actual union U, not a separately packed source.

Now take any two distinct cofactors from {5,7,35}; their least common multiple is 35. If delta<1/35, there must be an actual mixed modulus-35 class C: an absent numerical slot at modulus 35 alone costs 1/35 of the raw cap. Choose R=C. Then eta(R)>=1/35-delta, and

    delta+(Gamma/3)eta(R)
      >=Gamma/105+delta(1-Gamma/3)>=Gamma/105.              (PD8b)

If delta>=1/35, the packing credit alone is already more than sufficient. Therefore, for any one of these three pairs, the entirely numerical condition

    Gamma>=Gamma_crit
      =105*c0/(T-2)
      =6168733163201163811/15715215573196339200
      =0.3925325194852861...                               (PD8c)

guarantees R_Q<=257/51 under the unchanged PA law. When Gamma is strictly greater than this threshold, the query bound is strict. There is no condition on the distribution of eta among mod-35 cells: either missing mixed mass pays directly, or an actual modulus-35 original supplies the needed cell.

In particular, if both full labels 11*d1 and 11*d2 occur at most once, their exponent-one common empty slot gives Gamma>=5/11>Gamma_crit regardless of all deeper occupancy. The resulting minimum credit exceeds c0 by

    155/11781-c0
      =974546642797172189/542935350932041267200>0.           (PD8d)

Writing the positive quantity in PD8d as Delta, PD1–PD2 give R_Q<=T-Delta/lambda(1). Since the actual subprobability has lambda(1)<=1, the same sufficient condition gives the explicit uniform bound

    R_Q<=2734993790406900978211/542935350932041267200
         <5.037421<257/51.

Applying this separately to the three pairs (5,7),(5,35),(7,35) proves the stated two-of-three condition. If fewer than two of 55,77,385 carry two original classes, choose the pair corresponding to two labels with multiplicity at most one; that single chosen pair and one fixed completion supply the strict upper law. Hence an actual strict all-laws lower witness must have two classes at at least two of these three labels. The proof chooses one successful pair and one actual law; it never combines separately optimized source laws.

There is a uniform numerical margin under this same condition. Let Delta be the positive difference in PD8d. Equations PD1–PD2 give R_Q<=T-Delta/lambda(1); since the actual subprobability has lambda(1)<=1,

    R_Q<=T-Delta
       =2734993790406900978211/542935350932041267200
       =5.03742072737... <257/51.                         (PD8e)

This bound holds for every finite actual two-copy family satisfying the stated numerical-label condition, with arbitrary other original phases and heights. It does not apply without that condition.

## 5. Matching original phases give the same debit as empty slots

The first-11 criterion can also use actual matching phases. Fix one actual modulus-35 class C and, for d in {5,7,35}, let

    n_d = number of actual originals at full numerical label 11*d,
    r_d(C) = number whose old d-phase contains C,
    s_d(C) = 2-n_d+r_d(C).

Because d divides 35, each old d-cylinder either contains C or is disjoint from it. Both copies count separately, and their 11-phases remain arbitrary and fixed.

For each d there are r_d matching actual entries, 2-n_d empty entries, and n_d-r_d nonmatching actual entries. Put the matching and empty entries into the first s_d slots, completing each empty phase to C's d-projection, and put the nonmatching actual entries last. This is possible for every 0<=r_d<=n_d<=2. For example n_d=1,r_d=0 puts the empty entry first and the actual entry second; occupied slots need not come first. The three full labels may be assigned independently, without changing any original phase or actual kernel.

Complete each unit. Then on C the two slot loads are at least 1+k1 and 1+k2, where

    k1=#{d:s_d(C)>=1}, k2=#{d:s_d(C)=2}.

The exponent-one beta weights are both 5/11. All other debit terms are nonnegative, so one fixed completion gives

    J11 >= (5/11)*[(k1-1)_+ +(k2-1)_+]*eta(C).             (PS1)

The bracket is at least one exactly when k1>=2. If this occurs for one actual C, the same raw mixed-cap bound PD8a gives, when delta<1/35,

    delta+J11/3 >= delta+(5/33)(1/35-delta)>=1/231.

When delta>=1/35 its direct packing credit is already sufficient. Thus PS1 gives the same strict margin Delta and the same complete-query bound below 5.037421 as PD8d, using one law and a completion fixed independently of the final query.

A strict all-laws lower witness above T must therefore contain two DISTINCT actual modulus-35 classes: a missing copy or a duplicate phase wastes at least 1/35 of raw mixed capacity, which the direct packing credit excludes. For EACH of these classes C it must satisfy

    #{d in {5,7,35}: s_d(C)>0}<=1,

or equivalently at least two of its full labels 55,77,385 must obey

    n_d=2 and r_d(C)=0.                                   (PS2)

Both copies at those two full labels must miss C in their old phases. The pair may depend on C; no common pair avoiding both modulus-35 classes is asserted. This refines the numerical two-of-three obstruction but is still only a necessary condition for a lower witness, not such a witness or a uniform solution of the two-copy problem.

## 6. The same nested family is repaired without changing its law

In the family of section 2, choose the pair (d1,d2)=(7,35). No original has numerical label 7*11^e or 35*11^e, at any height. Hence Gamma=1. Take

    R=[3]_5 times [3]_7.

This entire cylinder belongs to U already at a=b=1, so eta(R)=1/35 for every N>=4. Complete every first-11 slot, including all absent e>K slots, with the unit, the missing old cofactor-7 query [3]_7, and the missing cofactor-35 query R. Put every other missing old phase inside a pure forbidden cylinder. On U, the actual nonunit first-11 cofactors are inactive, so its load is precisely

    1+1_[3]_7+1_R.

Its threshold-two hinge is exactly 1_R. Thus J11=1/35. Other stage completions may remain the zero-debit ones. The stage credit alone obeys

    (T-2)*J11/3=31/1071,
    31/1071-c0
      =9546482409995175389/542935350932041267200 >0.         (PD9)

All remaining terms in PD3 are nonnegative. Therefore the one actual PA law meets the target for ALL N,K>=4, irrespective of final query phases. In particular it does so for one fixed complete labelwise maximizing layout, including the nested later-only phases that attain PD4. The originals, all four actual and completed row kernels, removed measure eta, and final normalization are exactly the same as in section 3. Only permissible comparison completions changed.

## 7. What remains

The zero-completion example identifies a genuine failure of a proposed deduction from packing mass and local row sharpness. It does not defeat the completion-aware debit method. Conversely PD8–PD8d are explicit arbitrary-family sufficient regions, not a uniform proof for all families: all three useful missing-slot weights can be small. The new numerical necessary condition complements report 537's nested pure-5 geometry; neither condition is a lower witness.

A useful next target is a common-source inequality coupling small missing-slot weight with the actual occupied-slot phase geometry or forbidden-fibre overlap. Dense occupancy restricts the completion freedom, but that fact alone does not prove useful overlap. Any such alternative saving must use the same actual kernels, phases, complete tail and final law. Even a uniform two-copy result at 257/51 would still need the separate transport conditions to connect to the unrestricted original problem.

[Report545](545-bounded-completion-payoffs-pass-dense-small-labels.md) supplies a bounded lower witness for this same debit when the eight full labels 11*d, d in {25,125,49,343,175,875,245,1715}, are absent. It gives R_Q<5.038141<257/51 while allowing both copies at all three of55,77,385 and arbitrary other original heights. An actual57-class family satisfies the new condition while every single-pair PD8 test and PS1 is insufficient. The argument bounds the loss of a clipped LOWER payoff on the uncertain removed-source defect; it does not apply a convex upper comparison to that clipped function. Populating the eight additional labels remains outside this sufficient region.

[Report546](546-dense-irredundant-families-separate-stage-debits-from-actual-unions.md) rules out a uniform positive pure/packing/stage credit even for finite irredundant families with dense occupied rectangles: its supremum over ALL comparison completions tends to zero. This does not bound JL or refute PD3. The same constructed family's actual PA law has R_Q<=59509/13850<257/51 because different old cofactors share current-prime phases, reducing the actual forbidden union. A general extension therefore needs the joint relation between completion debits, actual phase overlap and final-query response.

[Report548](548-rainbow-transport-forces-a-next-row-saving.md) gives a quantitative saving directly in the actual 13-row after a fixed finite rainbow 11-prefix. Every continuation admitting factorized nested5/7 completions with full first roots has saving at least 0.0055068697, exceeding the entire NC4 mass requirement. Arbitrarily delayed branch changes and arbitrary fixed old11 phases are included. The same PA law closes without using JL; support-dependent phases, partial first roots and arbitrary prefixes remain outside this result.

[Report559](559-pure-union-savings-control-all-four-later-rows.md) bounds
the actual saving in each row using its pure-prime forbidden union.
Its sufficient region includes at most one original at11, at most one
at13, or at most one at each of17 and19, with all other labels arbitrary.
These are alternative lower bounds for each same-stage saving; the new
bound and a_q*Jq cannot simply be added for that stage.

## 8. Exact finite verification

The self-contained [exact consumer](../../frontier/cover-geometry/phase_debit_completion.py) and its [retained result](../../frontier/cover-geometry/phase_debit_completion.json) use N=K=4. The recorded execution with `python3 -I -S -B -O` exited0, with176 named checks passing. It imports no previous producer and has no external data input.

The consumer explicitly constructs176 original classes on88 numerical labels, with exactly two classes per label, and checks an individual private point for each class. Congruence checks verify the mixed rectangles and q-prefix disjointness. Integration over625 old5 cells reconstructs all four sequential row losses and the actual final subprobability mass

    lambda(1)=48097731105673596116097079/204902695364146715704518750.

It checks the four local Jensen ratios, the zero stage debits under the first completion, both the prefix-free and nested later-query hinges, the positive gap PD5, and the repaired debit J11=1/35. The latter includes BOTH the finite head beta weight and the exact absent-exponent tail. The general Gamma threshold, strict margin,27 numerical occupancy patterns and216 matching/empty-slot alignment patterns are also checked. These finite controls do not replace PD1–PS2's ordinary proofs for arbitrary actual families.

The actual complete query norm is computed independently of the PA upper envelope. For each of16 selected later-prime supports and each of the two possibilities for a positive7 exponent, the conditional factors from section3 give a625-cell density on the old5 coordinate. Bottom-up prefix aggregation gives the maxima at depths0 through4. Beyond depth4 this density is constant on every cell, so the exact sum of all remaining5-depth maxima is one quarter of the depth-four maximum. Positive7 and later-prime exponents contribute the geometric factors1/6 and1/(q-1). Divide the total raw query mass by the same actual lambda(1), then subtract one.

These32 profiles,160 finite maxima and32 exact tails agree with a separate direct-sum reconstruction. The exact rational norm is retained in the JSON and is approximately2.2551350554091405, strictly below257/51. Thus the zero-completion failure in PD5 is not an actual-query lower witness. Universal maximality of the removed-source hinge is the analytic argument PD4; the finite calculation checks its specified control values. No Lean verification is claimed.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_debit_completion.py
```

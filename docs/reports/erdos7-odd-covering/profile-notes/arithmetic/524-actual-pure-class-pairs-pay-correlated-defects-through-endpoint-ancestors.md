# Actual pure-class pairs pay the correlated defect through endpoint ancestors

The correlated bridge523 required a constant bounding every pure-union rectangle defect of the full-common comparison, and charged that constant to the mixed unit row. Here the actual pure R/S classes generate the defect expenses themselves. Each expense follows a pair of complete original numerical labels and may be paid by an ancestor of EITHER endpoint. Pair expenses and actual mixed originals share one column budget.

This removes the need for a supplied global or generated-query defect constant and for enumerating old activation states to obtain one. The finite outside joint kernel and the payment matrices remain explicit inputs. The criterion is sufficient; it neither makes arbitrary matrices feasible nor removes the old-template/source premises.

The construction reuses [report523](523-correlated-unit-conditioning-pays-generated-rectangle-defects.md)'s centred joint kernel and nonnegative proxy, [report520](520-actual-modulus-inventories-and-divisor-transport.md)'s old ancestor accounting, and [reports518](518-finite-prefix-templates-allow-arbitrary-old-residue-tails.md)--[522](522-fixed-product-subcarriers-absorb-shared-mixed-unit-projections.md)'s source and row transfer. Finite signed-measure decomposition and union bounds are standard. Report452 assigns actual outside projections to endpoints for a different tail-exclusion problem; the endpoint here is an old cofactor of a pure-class pair and the expense is negative joint-kernel mass. No Lean wrapper, source rerun or claim of literature priority is made.

## Fixed original input and signed kernel

Take a finite family of pairwise distinct odd numerical moduli greater than1, supported on P union R union S, with P={3,5,7,11,13,17,19} and finite disjoint outside groups R,S. Retain the finite old templates of518: a role p in{7,11,13,17,19}, first-root-distinct A/B prefixes of depths11,7,6 at3,5,p, common depth4 prefixes at the other four old primes, and one fixed selector per complete later label. Every later modulus has its unique actual decomposition m=d*n_R*n_S. Old-only classes and the permitted deeper old tails remain actual.

At finite outside periods resolving the original family, define V to be EXACTLY the complement of the union of all original d=1 cylinders. Assume lambda=H_outside(V)>0, and set rho=H_outside(. intersect V)/lambda. Its marginals are rho_R,rho_S. This is one law for the whole family. Old-prefix repair changes neither V nor any outside phase.

Let X_R,X_S be the finite group carriers. On their FULL product define the matrix of probability masses

    C(r,s)=rho(r,s)-rho_R(r)rho_S(s),
    Cminus(r,s)=max(0,-C(r,s)).                         (P1)

Both sums of C along a row or a column are zero. These are probability masses, so the sums below carry no second Haar-density factor. The full product includes cells outside V: there rho(r,s)=0 but Cminus can be positive. Restricting the negative kernel to live joint cells would be incorrect.

Index the actual pure-R nonunit original classes by i, and the actual pure-S nonunit classes by j. Their old cofactors are d_i,d_j, their fixed comparison activations are I_i(x),J_j(x), and their actual outside cylinders are R_i,S_j. Define one fixed nonnegative pair price

    kappa_ij=sum_(r in R_i,s in S_j) Cminus(r,s).         (P2)

Keep each pair's two original numerical labels. Equal or overlapping cylinders can give conservatively repeated prices; they are not silently merged into new original moduli.

## The pair sum controls every comparison activation

At any comparison old point x, let

    A_x=union_(i:I_i(x)=1) R_i,
    B_x=union_(j:J_j(x)=1) S_j

be the pure DELETED sets. Since C has zero row and column sums,

    sum_(A_x^c times B_x^c) C=sum_(A_x times B_x) C.

Thus the pure-survivor rectangle deficit is bounded by

    Delta_x=[-sum_(A_x times B_x) C]_+
        <=sum_(A_x times B_x) Cminus
        <=sum_(i,j) I_i(x)J_j(x) kappa_ij.              (P3)

The last step is a union bound for a nonnegative measure. It assumes neither independence nor laminarity and is valid for every activation pattern. It therefore also covers patterns created by the full-common old-prefix repair, without enumerating them. All kappa values are unchanged by that repair because they depend only on the one joint law and the original outside phases.

## Why either endpoint ancestor is allowed

For finitely many comparison old points x_l and weights w_l>=0 use the common two-reference inventory

    h_d(w)=max(sum_l w_l 1[x_l=A mod d],
               sum_l w_l 1[x_l=B mod d]),
    N(w)=sum_(full old matching inventory) h_d(w).

Each endpoint has one fixed selector for its complete numerical label. If e divides d_i, joint activation implies I_i=1 and hence the corresponding e-reference activation. Therefore

    sum_l w_l I_i(x_l)J_j(x_l)<=h_e(w)                 (P4)

whenever e divides d_i OR e divides d_j. The two endpoint selectors may differ. The disjunction is intentional: a payment need not be restricted to common divisors, and joint activation does not generally follow one of the two full references modulo lcm(d_i,d_j).

Let E be finite, divisor closed and contain1 and every original old cofactor. Define the pure marginal accounts b_d^R,b_d^S and the actual JOINT mixed account b_d^M as in523, without any added uniform defect. Supply the ordinary pure transports T^R,T^S paying their rows, supported on e|d, with each column at most1. Require

    sum_d T^R_(d,1)<=1-eta, 0<eta<=1.                 (P5)

For the mixed account supply T^M_(d,e)>=0, supported on e|d, with row sums at least b_d^M. For the pair prices supply Q_((i,j),e)>=0 satisfying

    Q_((i,j),e)=0 unless(e|d_i or e|d_j),
    sum_e Q_((i,j),e)>=616 kappa_ij,
    sum_d T^M_(d,e)+sum_(i,j) Q_((i,j),e)<=1
                                        for every e.  (P6)

The final line is ONE shared mixed-column capacity, including e=1. It is not a separate capacity for each endpoint, pair, original mixed label or defect source.

Multiplying each pair's row payment by its nonnegative weighted joint activation and using(P4), then adding all original mixed expenses, gives

    sum_l w_l c_l<=N(w),
    c_l=616[sum_(active mixed originals m) rho(C_m)
               +sum_(i,j) I_i(x_l)J_j(x_l) kappa_ij].  (P7)

This is simultaneous in all w for the same actual family, law and matrices. No lcm pseudo-label or independently optimized selector is introduced.

## Retained source consequence

Put t_l=22rho_R(A_l), u_l=28rho_S(B_l), and R_l=(22-t_l)(28-u_l). The actual joint survival s_l satisfies616s_l>=R_l-c_l by(P3) and the raw mixed union bound. As in523 set

    y_l=min(R_l,c_l), sstar_l=(R_l-y_l)/616.

Then0<=sstar_l<=s_l, w*y<=N(w), and R_l-y_l=616sstar_l. The pure transports give the other two unchanged axis budgets. The reserve(P5) supplies t_x<=Q_x-eta and the522 strict pair gap17eta. Consequently the retained rows apply to actual strict badness at

    theta=min(1/3696,17eta/1232).

The source remains the same old-only survivor law; actual order rows follow survivor-set inclusion under this fixed rho. The finite-prefix repair and its same-source error bound are unchanged. Their retained margin and domination nu<=(27/2)H_old give

    H_full(original survivors)>lambda*theta/270000.    (P8)

This is the conditional ordinary consequence of the explicit pair certificate. The role of pair accounting is to discharge523's defect obligation by original-label data, rather than by a constant charged to the unit row. The source construction and its arbitrary-height verification boundary retain their attribution through518--523 to Michael Schroeder's Nine Prime Divisors in Odd Distinct Covering Systems, edition1.0.1; see the [library entry](../../../../../Library/Arith/schroeder2026nine.md).

## An actual family rejected by scalar unit-defect accounting

Use R={23}, S={29,31}, E={1,3,9} and these nine original classes:

| Modulus | Residue |
|---|---:|
|23|0|
|29|0|
|31|0|
|69|25|
|87|31|
|93|64|
|667|2|
|713|2|
|6003|1|

The three changed pure residues are all1 mod3. Their outside phases are respectively2 mod23,2 mod29,2 mod31. The mixed6003 phase is1 mod9. Thus every nonunit original uses the same actual A=1 old reference; B=2 supplies the required distinct split reference. The fixed finite templates and their full-common comparison have these same activations.

After the three pure unit roots are removed, the two group carriers have22 and840 points. The two mixed unit originals delete one R row I, root2, against the S union D={s29=2 or s31=2}, of size57. The full all-unit survivor count is Z=18423 and lambda=18423/20677=801/899.

At old x=1 mod3, the actual pure deleted sets are exactly I and D. The523 rectangular-hole identity therefore gives

    616Delta_x=616*21*57*783/18423^2
              =7127736/4190209>1.                    (P9)

Every constant valid for all comparison activations must be at least this value after scaling. Hence the523 criterion that pays the constant through the unit row necessarily fails on this same law, even before paying remaining mixed originals. This is an actual generated-query obstruction, not merely an expensive global maximum on an unused rectangle.

On the hole I times D, Cminus=21*783/18423^2 per cell. The two actual pure pairs therefore have scaled prices

    k1=616 kappa_(69,87)=3751440/4190209,
    k2=616 kappa_(69,93)=3501344/4190209.

The pair sum counts30+28=58 S cells, including the one overlap twice. Thus it conservatively exceeds the true57-cell defect, but

    k1+k2=7252784/4190209<2.

Both pair rows can pay ancestors3 or1. Use

    Q_((69,87),3)=3751440/4190209,
    Q_((69,93),3)=438769/4190209,
    Q_((69,93),1)=3062575/4190209.

The nonunit mixed original6003 has b_9^M=6160/6141. Pay T^M_(9,9)=1 and T^M_(9,1)=19/6141. The mixed column3 is exactly full; the shared mixed unit column uses

    3062575/4190209+19/6141=9226618/12570627<1,

leaving3344009/12570627. All other mixed entries are zero.

The pure accounts are b_3^R=1914/2047<1 and b_3^S=11368/6141. Pay the R expense entirely to3, so eta=1. Pay the S expense by T^S_(3,3)=1 and T^S_(3,1)=5227/6141. Every separate pure column stays within capacity. Thus(P5)--(P6) hold and theta=1/3696; coefficient(P8) is89/99681120000.

This separates the endpoint-pair criterion from523's constant-to-unit criterion for one fixed actual law. It does not assert failure of every522 product-subcarrier certificate or of any stronger future correlated accounting method.

## Why lcm is not a free destination

Take global old references A=1,B=2, an actual pure-R class1 mod69=3*23 and a pure-S class117 mod145=5*29. Their old selectors are A at3 and B at5; both outside phases are1. The old point7 matches both originals' old conditions, but it is neither1 nor2 mod15. For a singleton weight at7,

    joint activation=1, h_3=h_5=1, h_15=0.

Hence replacing(P4) by a blanket lcm destination would be false. These are actual CRT-compatible original phases:1 mod3 and2 mod5 combine to7 mod15, a third phase rather than either declared reference. If unit originals0 mod23,0 mod29 and2 mod667 are supplied, their one-cell conditioned law gives this pair positive price1/615^2. Thus the invalid lcm destination can affect a genuine nonzero defect expense.

The endpoint destinations3 and5 remain valid, including3 even though3 does not divide the other endpoint5. This explains both the soundness of the OR rule and why a rule restricted to gcd ancestors would discard valid capacity. No positive old-source mass at the specific witness7 is claimed or needed for this transport-implication counterexample.

## Scope and computational boundary

The criterion computes fixed pair prices on the actual outside kernel and checks a finite shared-capacity matrix. It does not enumerate the old period or presuppose a list of all generated pure unions. The proof covers all repaired comparison activations through endpoint implications. Outside kernels and pair inventories can themselves be large, and no polynomial-time or minimal-boundary claim is made.

Pointwise negative parts and the pair union bound may overcharge cancellations or repeated intersections. Failure of this certificate is therefore not a covering result. Its verified gain is a new usable relationship between the signed outside response and the existing old ancestor budget: a defect created only when two original pure classes are active need not consume a global unit-column allowance.


## Exact portable control

From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/paired_original_defect.py
```

The [standard-library consumer](../../frontier/cover-geometry/paired_original_defect.py), [pinned input](../../frontier/cover-geometry/paired_original_defect_input.json) and [retained exact result](../../frontier/cover-geometry/paired_original_defect.json) are portable together. `--input-dir` selects the input directory; `--output` writes the recomputed result. Default execution compares it with the retained result.

The consumer reconstructs the full outside period from the original moduli, deletes exactly the original unit classes, and computes the centred kernel on every product cell. It checks actual phase prices, every actual pure pair, the shared pair-plus-mixed column budgets and the pure-R reserve. One old residue is used to witness the failure of every constant-to-unit defect charge; the consumer does not enumerate all old activations. The general pair-implication proof supplies their simultaneous bound.

The controls retain the positive pair expenses lost by an incorrect live-support-only kernel and the actual CRT witness against arbitrary lcm routing. They check the displayed conditional density coefficient without regenerating the source factor270000. These are finite computations and ordinary proofs; no source producer, geometric optimizer or Lean build is run.

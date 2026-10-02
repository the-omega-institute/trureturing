# Queried colour capacities sharpen complete head and moment bounds

The same categorical source that supplies a retained table also bounds the mass of every queried colour. Retaining this relation improves the complete head and fourth-moment envelopes without changing the source, selected phases, or continuation normalization. A colour of probability zero cannot support a nonzero cylinder, even if its unused retained-table entries are positive.

The all-height calculation is finite for any fixed rational categorical law. On the actual pure-Haar source cells of Report816 it has only three depth types per nonternary coordinate: unqueried, depth one, and depth at least two. On each fixed structural cell it preserves block-concavity and therefore admits a product-vertex certificate with one common table.

One exact evaluation of the already fixed Report815 rational table makes its second diagnostic gate positive, while its first and third gates remain negative. This is a sharper sufficient interface, not a positive uniform certificate or a Lean result.

## 1. Reuse and the missing relation

[Report810](810-categorical-retained-kernels-give-a-finite-common-source-interface.md) K4–K7 already gives the exact common-colour factorization of a numerical cylinder under one genuine submeasure `nu_u <= lambda_w`. Its present upper estimate bounds each queried coordinate by `C_q/q^e` and explicitly permits source-null colour choices in the maximum. [Reports815](815-retained-source-moments-have-a-three-point-common-kernel-obstruction.md) and [816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md) supply, respectively, the retained-source fourth-moment normalization and the actual pure-Haar source domains.

These results supply the source construction, ordinary cylinder domination, common-colour menus, numerical inventories and ternary summation. The additional step here is to keep the queried colour's probability inside the same maximum before summing the depth inventory. Conditional-root clipping and actual-capacity thinning construct different source laws; neither is needed for this refinement.

Fix the first-digit colour partitions, one actual product source, one normalized leaf vector `w`, and one table `0 <= u_l(s) <= w_l`. Write

    pi_q(c) = lambda_q(first digit belongs to colour c),
    A_(l,D,kappa) = sum_(s outside D) product_(q outside D) pi_q(s_q)
                                           u_l(kappa,s).

All quantities use the same actual laws and the same retained table. A literal cylinder `a mod q^e`, `e >= 1`, belongs to exactly one first-digit colour `c`. Thus

    lambda_q(a mod q^e) <= b_(q,e,c),
    b_(q,e,c) = min(C_q/q^e, pi_q(c)).                         (CC1)

At depth one, equality with `pi_q(c)` holds when `c` is a singleton. For a nonsingleton category, CC1 remains an upper bound for one literal digit, not the probability of the whole category being selected as a cylinder.

For an exponent vector `e_q >= 1` on `D`, the correct common-colour bounds are

    G_(e,0) = max_kappa [product_(q in D) b_(q,e_q,kappa_q)]
                              sum_l A_(l,D,kappa),
    G_(e,1) = max_(root R,kappa) [product_(q in D) b_(q,e_q,kappa_q)]
                              sum_(l in R) A_(l,D,kappa),
    G_(e,2) = max_(leaf l,kappa) [product_(q in D) b_(q,e_q,kappa_q)]
                              A_(l,D,kappa).                  (CC2)

The queried colour tuple is common to all leaves in a sum. No separately optimized colour probabilities or source normalizations enter. A colour with zero probability contributes zero at every height. Independence is used only for the underlying product `lambda_w`; no independence of the retained measure is asserted.

An actual cylinder with ternary depth `j=0,1,2` has retained mass at most `G_(e,j)`. At `j >= 3` its mass is at most `3^(2-j) G_(e,2)`. These statements follow from Report810's exact factorization, CC1, and the unchanged ternary Haar suffix.

## 2. Complete heights remain finitely computable

For a fixed finite rational vector `pi_q`, omit its zero-probability colours. Choose an integer `E_q >= 1` such that

    C_q/q^E_q <= min_(c: pi_q(c)>0) pi_q(c).

For all `e >= E_q`, CC1 equals `C_q/q^e` on every live colour. Split the depth inventory into the finite singleton depths `1,...,E_q-1` and the one tail class `e >= E_q`. Within a tail class the maximizing colour menu is unchanged and the factor `q^-e` is common to every menu branch. It can therefore be summed exactly outside the maximum.

For head inventories the tail coefficient is

    C_q sum_(e>=E_q) q^-e = C_q/[q^(E_q-1)(q-1)].

For fourth moments it is

    C_q sum_(e>=E_q) [(e+1)^4-e^4]/q^e.

The latter is the full rational `C_q A4(q)` minus a finite rational prefix, where

    A4(q) = 15t + 50t^2 + 60t^3 + 24t^4,  t=1/(q-1).

Taking the product of the finite depth-type menus accounts for every exponent vector, including vectors with some coordinates in their finite prefix and others in their infinite tail. It does not truncate the head or the ordered four-query expansion. The empty nonternary support is also retained.

For selected-null numerical labels, determine their exact exponent type and subtract their own complete coefficient from that type's head inventory. Since each selected label occurs once in the full inventory, every residual coefficient remains nonnegative. A selected label's nullity must be certified for the same table and its actual phase; colour capacities are not permission to rephase it.

This gives a finite exact calculation at any fixed rational law. Its number of depth types need not be uniformly small on the old cap relaxation as a positive colour probability tends to zero. Fixed-probability finite computability does not by itself give a global vertex theorem.

## 3. Actual pure-Haar sources require only three depth types

Use [Report816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md)'s actual pure-survivor laws at `q >= 5`, with the inherited constants

    C_q=(q-1)/(q-2).

Every live singleton colour has probability at least

    ell_q = (q-2)/(q^2-q-1) > C_q/q^2.                        (CC3)

The strict comparison follows by clearing positive denominators: its numerator is

    q^2(q-2)(q-3)-1 > 0.

At 5, the other category `{2,3,4}` has probability at least `7/15 > 4/15=C_5/5`. At every other observed prime, the nonzero category has probability at least `1-C_q/q > C_q/q`. These lower bounds already hold in the enclosing cap simplex. Consequently every positive category has probability greater than the second-depth cap.

Within one fixed structural source cell, the zero/live pattern is fixed. At depth one a singleton capacity is its affine probability `pi_q(c)`; a nonsingleton other-category capacity is the constant `C_q/q`. At every depth at least two, a live category has capacity `C_q/q^e` and a dead category has capacity zero.

For a nonternary support `D` and a subset `S` of its coordinates having depth exactly one, define

    rho_q(c) = min(C_q/q, pi_q(c))/(C_q/q),
    F_(D,S,0) = max_(live kappa) product_(q in S) rho_q(kappa_q)
                                      sum_l A_(l,D,kappa),
    F_(D,S,1) = max_(root R,live kappa) product_(q in S) rho_q(kappa_q)
                                      sum_(l in R) A_(l,D,kappa),
    F_(D,S,2) = max_(leaf l,live kappa) product_(q in S) rho_q(kappa_q)
                                      A_(l,D,kappa).           (CC4)

The coordinates in `D` outside `S` have arbitrary depths at least two. Coordinates outside `D` are unqueried. The empty-support formulas are the ordinary retained mass, root masses and leaf masses. Each coordinate has three types, so the seven-prime calculation has `3^7=2187` nonternary depth types, not an infinite height scan.

The complete head and fourth-moment coefficients for a type are

    B_(D,S) = product_(q in S) C_q/q
              product_(q in D outside S) C_q/[q(q-1)],
    W_(D,S) = product_(q in S) 15 C_q/q
              product_(q in D outside S) C_q [A4(q)-15/q].    (CC5)

For an individual selected cofactor `n`, its factor is still `C_D/n`, where `C_D=product_(q in D) C_q`. The ratio between its exact-depth coefficient and the summed coefficient of its depth type is scalar and independent of the colour choice. Thus the selected-label subtraction belongs to its one type and uses precisely `C_D/n`, including selected prime squares.

Let `R_(D,S,h)` equal `B_(D,S)` on the allowed shallow types (`h=0, |D|>=2`, or `h=1,2, D nonempty`), and zero on the other types, minus the coefficients of the selected labels with that `(D,S,h)`. With `M` the exact retained mass, the complete lower bound is

    L_cap = M - sum_(D,S,h=0,1,2) R_(D,S,h) F_(D,S,h)
              - (1/2) sum_(D,S) B_(D,S) F_(D,S,2).            (CC6)

The final sum includes the empty support and all ternary depths at least three. Numerical pure-q originals are absorbed into their actual `lambda_q` and are not charged again. The known pure-3 and pure-9 anchors are null; every higher pure ternary original is charged by the same final sum.

For four arbitrary finite query layouts, the full retained-source mixed moment is bounded by

    K_cap = sum_(D,S) W_(D,S)
                   [F_(D,S,0)+15F_(D,S,1)+216F_(D,S,2)].     (CC7)

To prove CC7, expand their ordered fourfold numerical-label sum. An incompatible tuple contributes zero. A compatible tuple is a cylinder at the coordinatewise maximum depth. The number of ordered exponent quadruples with maximum `e` is `(e+1)^4-e^4`. CC2 bounds that one cylinder; summing its three depth types gives CC5, and the full ternary sums give `1,15,216`. Different query layouts need not share phases. The common colour requirement is within each compatible tuple, not a new cross-layout phase hypothesis.

Every normalized source still uses the same survivor `U` and retained table:

    alpha_u = nu_u(U) >= L_cap,
    mu_u = nu_u restricted to U / alpha_u.

For `0 <= h < 28`, the unchanged full-source hinge and complete [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md) tail give the sufficient numerator

    (28-h)L_cap - H_h(w) - 27 T29 T1600 K_cap.                (CC8)

The actual pure-29 factor appears exactly once. Positivity implies `L_cap>0`, hence supplies the required positive denominator. The formula uses Report815's retained-survivor normalization, not a retained numerator inserted into the full-source denominator.

## 4. Pointwise improvement and the precise convexity boundary

Each CC4 envelope is at most the corresponding old Report810 envelope. Also

    sum_(S subset D) B_(D,S) = product_(q in D) C_q/(q-1),
    sum_(S subset D) W_(D,S) = product_(q in D) C_q A4(q).

Selected coefficients partition into exactly one depth type each, and all residual coefficients are nonnegative. Therefore, at every source law satisfying this three-type condition,

    L_cap >= L_old,       K_cap <= K_old.                    (CC9)

This is a simultaneous improvement at one fixed source, not a combination of independently attained extrema.

On a fixed actual-source structural cell, every branch of CC4 is affine in each whole local probability block. If `q` is queried at depth one, its block appears only through the affine singleton probability or the constant other-colour cap; it does not occur in the complementary-coordinate average. If `q` is queried deeply, its coefficient is constant with the fixed live/dead status. If it is unqueried, its block occurs only in the complementary-coordinate average. A coordinate never supplies both factors in one branch.

Thus CC4 is block-convex; CC6 and, for `0 <= h < 28`, CC8 are block-concave. Product vertices suffice on each such product cell, with one shared `u,w`. At a fixed vertex all branch expressions are linear in `u`, so finite epigraph constraints give a shared-table LP. This statement authorizes no change of table between vertices of one cell and no uncovered gap between structural cells.

The same argument does not extend across zero/live changes or an arbitrary old cap domain. A concrete counterexample uses one prime `q=5`, `C=4/3`, one occupied ternary leaf, and a retained table equal to one only in singleton colour zero. Let `t=pi_5(0)`, distributing the remaining mass evenly over the four other digits. These are valid all-height capped product laws, but the small positive values below are not actual pure-Haar laws from Report816.

With no selected mixed labels, put

    S(t)=sum_(e>=1) min(C/5^e,t).

The complete head lower bound is `L(t)=t/2-(5/2)S(t)`. At `t=2/75,4/75,6/75`, the values of `S` are respectively `5/75,9/75,11/75`. Hence

    L(4/75) - [L(2/75)+L(6/75)]/2 = -1/30 < 0.

The corresponding complete fourth-moment envelope is

    K(t)=232 [t+sum_(e>=1)((e+1)^4-e^4)min(C/5^e,t)].

Its midpoint value exceeds the average of these endpoints by `3016/15>0`, so it is not convex. The obstruction is the depth-two capacity breakpoint. Report816's positive lower bound excludes this breakpoint from each actual live cell. Consequently the old 320-vertex argument cannot simply be reused on the entire old cap domain for CC8.

## 5. One fixed-table three-point diagnostic

Keep exactly the already rationalized Report815 table and its one weight vector. The source points, actual selected phases, h16 hinge, once-only pure-29 factor and complete tail are unchanged. No table is reoptimized or replaced. Exact arithmetic gives:

| Source point | Old gate | Capacity-aware gate |
| --- | ---: | ---: |
| `(4,63)` | `-0.03256609375861133...` | `-0.03256609375861133...` |
| `(0,32)` | `-0.03256621566554399...` | `+0.035337916830079995...` |
| `(3,63)` | `-0.03256608298779183...` | `-0.03256608298779183...` |

At the second point, the mass floor increases from `0.0278179196110892...` to `0.03344871564338886...`; its fourth-moment bound decreases from `314312.75585654477...` to `312539.5472715049...`. Both changes concern the same retained submeasure. They give a strict head improvement and a strict all-height moment improvement simultaneously.

At the all-upper first point, every observed singleton is already at its old cap, and every other-category probability exceeds that cap. There are no dead observed categories. CC1 is therefore identical to the old cylinder bound at every depth, so neither the head nor the moment changes for any table at that point. At the third point this particular table also has no gain after the colour maxima are taken; no claim of such equality for every table is made.

The evaluation covers exactly these three source-closure points and one shared table. Its 38,217 explicit checks reconstruct the full depth-type inventories, selected-label subtractions, shared-colour envelopes and complete moment coefficients, and match every old value to the prior rational-table diagnostic. It runs no solver and no full source-domain sweep. The first and third points remain negative, so this diagnostic does not establish a successful common certificate, a source atlas, or unrestricted noncoverage.


## 6. Exact reproduction

The [standalone consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/queried_colour_capacity.py), [rational certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/queried_colour_capacity_certificate.json), and [generated result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/queried_colour_capacity.json) reproduce the fixed-table diagnostic and the complete-height convexity counterexample.

```sh
python3 -I -S -B queried_colour_capacity.py
```

Normal execution checks the saved result without rewriting it. Regeneration requires `--write-result`; alternate inputs use `--certificate` and `--result`. The certificate contains the exact 174 nonzero rational retained coefficients, five weights, literal selected phases, three probability points, and complete tail data. No floating proposal, optimizer, external Python package or repository import is needed.

The 38,217 explicit checks also reconstruct the complete hinge, the 179-prime bridge to the analytic tail above 3000, the once-only pure-29 factor, both complete-height midpoint gaps, and the exclusion of zero-probability colours from deep queries. Floating numbers are display values only. Checks remain active under optimized Python execution. The ordinary proofs establish the general all-height and fixed-cell conclusions; the finite replay does not substitute for their hypotheses or quantify over further source points.

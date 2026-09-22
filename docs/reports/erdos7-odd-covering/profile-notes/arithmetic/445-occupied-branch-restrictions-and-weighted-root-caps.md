[Index](../../marked_head_profile.md) · [Row/tree coupling](443-one-supported-law-couples-rows-and-tree-prefixes.md) · [Uniform restrictions](444-uniform-subtree-restrictions-couple-two-prefix-trees.md)

# Occupied-child restrictions and weighted four-root coupling

These are ordinary finite-flow and averaging deductions, with exact rational constructors as controls. They do not assert new Lean certification, a literature-priority claim, or a resolution of Erdős #7.

The source throughout is an actual subset R of Z/5^H x Z/7^K, H,K>=1, meeting every product of a complete ternary five-tree and a complete five-ary seven-tree at the full indicated heights. Assume exactly four first-five roots are occupied. Do not assume three individually robust roots or any fixed fine-fibre selector. All probabilities below are on actual source points and are chosen before any independent phases of the original divisor labels.

## A restriction rule that uses the occupied children

At any occupied internal five-prefix at or below a first-five root, let n be its number of occupied children in the original source projection. The source and these occupancies are fixed before constructing a law; an occupied internal prefix has n>=1.

- If n>=3, select n-2 occupied children uniformly and include all 5-n empty children.
- If n<=2, select three empty children, so this prefix has no surviving actual descendants.

In either case exactly three children are selected. Make the choices independently at all occupied internal prefixes, including those that an earlier choice will later exclude. Complete all empty branches arbitrarily. Keeping the selected descendants produces a legal ternary subtree under each of the four first-five roots.

For an occupied prefix u of depth A>=1, let

    tau(u) = product over its deeper path of delta(n),
    delta(n) = (n-2)/n for n>=3, and 0 for n<=2.

There are A-1 factors; tau=1 at the first-five roots. This is the exact probability that the original prefix survives the random restriction. It depends on actual occupancies, not just the modulus or the number of abstract possible children.

Fix the entire restriction profile. Any pair of occupied first-five roots, together with the one empty first-five root, is a legal first-level ternary choice. Full product-tree blocking therefore says that the restricted column projection at every pair of roots meets every five-ary seven-tree. The complement duality yields a column law with all depth-B prefix caps 3^(-B).

Apply report443 with m=4,q=2 to the four projected root/column supports. Lift its law to actual selected source points and average over all restriction profiles. The resulting single law satisfies

    nu(five-prefix u)                  <= tau(u)/3,
    nu(seven-prefix v of depth B)      <= 3^(-B),
    nu(five-prefix u, seven-prefix v)  <= tau(u)3^(-B)/2,       B>=1.

The conditional coupling may depend on the entire restriction profile. Independence between that law and the event that u survives is not assumed: outside the event its mass is zero, and inside it the relevant pointwise root cap applies. The proof consequently preserves actual support and cross-prime incidences.

This strengthens uniform 3-of-5 restriction averaging when fewer than five children are occupied. Empty branches consume legal test-tree choices without consuming probability in the actual law.

## Full original-label moment certificate

Set tau_A=max tau(u) over all depth-A occupied five-prefixes, and

    S_K = sum_(B=0)^K (2B+1)3^(-B) = 3-(K+2)3^(-K).

Identify the actual product source with its CRT residues modulo Q=5^H7^K. For one law nu define

    Gamma_Q(nu) = max_(a_d mod d, d|Q) E_nu (sum_(d|Q) 1_(x=a_d mod d))^2.

This includes divisor one. Keep every original divisor label 5^A7^B, A=0,...,H and B=0,...,K. For arbitrary independent phases, an ordered pair of classes is either disjoint or intersects in a cylinder at its original-label LCM. Thus the SAME law satisfies

    Gamma_(5^H7^K)
      <= S_K + sum_(A=1)^H (2A+1)tau_A [1/3+(S_K-1)/2].

No phase is changed into a common centre; no divisor is replaced by its radical. The factors (2A+1)(2B+1) count the original ordered label pairs.

If every occupied internal five-prefix at or below the four roots has at most d children, with d in {3,4,5}, then

    tau_A <= theta^(A-1),        theta=(d-2)/d,
    W_H(theta)=sum_(A=1)^H (2A+1)theta^(A-1),
    Gamma <= S_K + W_H(theta)[1/3+(S_K-1)/2].

Nodes with one or two occupied children are permitted; their contribution is killed by the legal empty-child restriction.

For d=3, W_H=3(S_H-1), so the bound is

    S_H S_K + (S_H-1)(S_K-1)/2.

This is below nine whenever H=1 or K=1, and also at (H,K)=(2,2),(2,3),(3,2),(2,4),(4,2). The relevant exact values include

    (2,2):209/27,       (3,2):697/81,        (4,2):727/81.

Monotonicity and the first excluded values (2,5):6653/729 and (3,3):4651/486 show that this is the exact strict domain of this formula. At K=1 its limit as H grows is seven. This result includes the exact ternary descendant skeleton but does not require every actual node to have exactly three occupied children.

For d=4,

    W_H=10-(2H+5)/2^(H-1).

The bound is below nine precisely for H=1 at every finite K, for H=2 with K<=2, and for H=3 or4 with K=1. In particular,

    (H,K)=(2,2): 26/3,
    (H,K)=(3,1): 193/24,
    (H,K)=(4,1): 431/48.

The next boundaries are (2,3):347/36, (3,2):191/18 and (5,1):917/96, all above nine. Thus arbitrary four-root height-(2,2) sources with at most four occupied children per root admit a strict common-law certificate, without any robust-root assumption.

For d=5 the formula reduces to uniform restriction averaging:

    W_H=15-5(H+3)(3/5)^H.

It gives every finite K at H=1 and K=1 at H=2, but at (2,2) it is 83/9. This number only marks a limitation of that uniform-cap certificate; it is not a lower bound on the source's minimax value.

## A weighted version of the row/tree coupling theorem

The next finite-flow theorem permits different row budgets, which is useful when their occupied-child counts differ.

Let Y be the leaf set of a finite rooted tree with nonnegative rational proper-prefix capacities kappa(v). Let F be an actual subset of {1,...,m} x Y, m>=2, and suppose every pair of distinct rows has a column projection supporting these caps. Choose nonnegative rational row caps alpha_r and joint coefficients beta_r. For every subset A of rows require:

    |A|<=1:  sum_(r outside A) alpha_r >=1;

    |A|>=2:  sum_(r outside A) alpha_r + (1/2)sum_(r in A) beta_r >=1,
              sum_(r outside A) alpha_r + sum_(r in A) beta_r-beta_j >=1
              for every j in A.

Then one actual law has simultaneously

    nu(row r)<=alpha_r,
    nu(Y_v)<=kappa(v),
    nu(row r,Y_v)<=beta_r kappa(v).

Use report443's private/public column-tree network, replacing the source-to-row capacity by alpha_r and each private prefix capacity by beta_r kappa(v). An actual bridge has capacity one. A unit flow gives exactly the claimed common law.

For a cut not crossing an actual bridge, let A be the private roots on the source side. If |A|<=1, the source edges alone cost at least one. Otherwise write R for the public-prefix cut cost and L_r for the private-prefix cost before scaling by beta_r. Each pair in A supplies

    R+L_r+L_s>=1.

If R>=1 the cut already suffices. Otherwise put t=1-R, b=sum_A beta_r and

    c_A=min(b/2, b-max_(r in A) beta_r).

The pair constraints imply sum_A beta_r L_r>=c_A t. To see this, if every L_r>=t/2, use b t/2. Otherwise choose a smallest L_j=z<t/2; all other L_r>=t-z. Hence the weighted sum is at least

    (b-beta_j)t+(2beta_j-b)z
      >= min(b-beta_j,b/2)t >= c_A t.

Consequently R+sum beta_r L_r>=min(1,c_A). Adding the top-edge cost and applying the displayed hypotheses makes every cut at least one. Finite max-flow/min-cut proves the theorem. This proof only uses pairwise projected-law feasibility, not compatible choices of the separate witnesses.

The exact interface extends report443's existing `couple_tree_caps` with optional `row_caps` and `joint_coefficients`, accepted together when q=2. It checks every sufficient cut inequality, every actual pair-projection premise, and all final same-law caps. The previous default interface and result metadata are preserved.

The occupied-child averaging construction now gives the more general prefix bounds

    nu(u)<=alpha_(root u) tau(u),
    nu(u,Y_v)<=beta_(root u) tau(u) kappa(v).

Thus, defining a_A=max alpha_(root u)tau(u) and b_A=max beta_(root u)tau(u) at depth A, the original-label certificate is

    Gamma <= S_K + sum_(A=1)^H (2A+1)[a_A+(S_K-1)b_A].

## One fully populated root is also allowed at height (2,2)

Assume H=K=2. Designate one of the four occupied first-five roots before choosing a law or any layout phases. It may have all five occupied second-five children; the other three roots each have at most four. Their restriction survival factors are bounded by

    (3/5,1/2,1/2,1/2).

Choose

    alpha=(5,6,6,6)/17,
    beta =(10,12,12,12)/23.

All sixteen row-subset cases, comprising forty-four displayed inequalities, satisfy the weighted cut requirements. After actual-point lifting and occupied-child averaging the common law has

    max first-five-root mass             <=6/17,
    max second-five-prefix mass          <=3/17,
    max first-five/seven-prefix mass     <=(12/23)3^(-B),
    max second-five/seven-prefix mass    <=(6/23)3^(-B).

The pure seven-prefix caps remain 3^(-B). Keeping all nine original labels and all eighty-one ordered pairs,

    Gamma_1225
      <= 23/9 + 3(6/17)+5(3/17)
                +(14/9)[3(12/23)+5(6/23)]
       = 31532/3519
       = 9-139/3519 <9.

This includes every source in the stated height-(2,2) class with at most one fully populated first-five fibre. It does not require each sparse root to supply an individually good fine fibre. When all four roots have at most four children, the earlier 26/3 bound is stronger; the weighted theorem's purpose is to admit the additional five-child root.

## Exact barrier for the (5,5,4,4) occupancy bound

At height (2,2), fix survival bounds delta=(3/5,3/5,1/2,1/2) and optimize over all nonnegative alpha,beta satisfying the weighted pair-cut conditions above. Write A=max alpha_i, P=max delta_i alpha_i, B=max beta_i and Q=max delta_i beta_i. The present original-label LCM objective is

    J=23/9+3A+5P+(14/9)(3B+5Q).

Its exact minimum is 83/9. Indeed, label the two full roots 1,2. The singleton cut with active root3 requires alpha_1+alpha_2+alpha_4>=1, implying both 3A>=1 and A+10P/3>=1. Taking one half of the former and three halves of the latter gives 3A+5P>=2. The balanced full-root cut gives sum beta_i>=2; since that sum is at most 2B+10Q/3, it follows that 3B+5Q>=3. Thus J>=83/9. Equality holds for alpha_i=1/3, beta_i=1/2, which satisfy every cut condition and give A=1/3,P=1/5,B=1/2,Q=3/10.

This exactly limits the specified universal cut-budget and maximum-cylinder certificate at these fixed survival bounds; it is not a lower bound on any actual source's Gamma. Retuning these budgets alone cannot remove the remaining 2/9. Source-specific conditions, smaller actual occupancy factors, stronger actual-point coupling, and estimates retaining more simultaneous phase information remain outside this obstruction.

## Scope

These are bounds for explicitly specified actual product-tree blocker classes, with original label phases independent. They do not establish an arithmetic realization of every abstract source, transport a full cofactor moment floor, or settle the arbitrary four-root source with two or more fully populated second-five fibres at height (2,2). A bound exceeding nine is only failure of that sufficient certificate. The work makes no claim about a common projectively compatible law as heights or sources vary.

There is also a precise obstruction to uniformly improving the joint coefficient 1/2 while keeping the pure column caps. Use the existing recursive source in [report401, RC1--RC3](401-a-recursive-minimum-source-has-one-law-at-every-height.md): column digit zero continues the source, and a first nonzero digit r in {1,2,3,4} assigns the point to row r. The all-zero leaf occurs in three rows. Its full column projection contains a complete five-ary tree and every row pair contains a complete ternary tree.

For any law with pure depth-j cap 3^(-j) and joint depth-i cap beta_i 3^(-i), partition the source by the first nonzero column digit among its first j digits. The remaining all-zero prefix gives

    1 <= 3^(-j) + 4 sum_(i=1)^j beta_i 3^(-i),      1<=j<=K.

Thus beta_1>=1/2; if all earlier beta_i<=1/2, then beta_j>=1/2. Report443 attains the constant coefficient 1/2 on this source. No depth-dependent coefficient vector can weakly improve that constant vector and strictly improve a coordinate while these pure caps are retained. This is a boundary of the common-cap template, not a lower bound on Gamma or a claim that the source lacks a good moment law. The weighted theorem permits different row coefficients, and the occupancy theorem improves the deeper five-prefix survival factors.

## Exact construction controls

The companion [occupied-branch constructor](../../frontier/cover-geometry/occupied_branch_coupling.py) uses the original source's literal occupied child digits, finite restriction families with their exact probabilities, grouped projected-neighborhood signatures, and uniform lifts to available actual children. Its height-two interface also accepts the weighted coefficients. Higher-height results above are the ordinary sampling proof and formula, not an implemented general-height constructor.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/occupied_branch_coupling.py
```

The report432 irregular 21-point source, lifted to all seven tails at K=2, supplies 147 actual points. Its occupied-child restriction families have 324 original profiles and 96 grouped projected supports. The exact constructor checks 576 pair projections and returns a law on 51 actual points with full original-label LCM upper 223/27<=26/3.

Adding two actual child points in the designated root before the same lift gives 161 actual points. Its 540 original restriction profiles compress to 48 groups; the weighted constructor checks 288 pair projections and returns a law on 60 actual points with full original-label LCM upper 90074/10557<=31532/3519.

Both controls retain all nine original labels and eighty-one ordered pairs. They verify the general constructions on actual irregular sources; neither is an optimized minimax claim. The previous 450- and 540-point restriction-constructor controls retain their previous exact bounds. The weighted pair interface checks its forty-four sufficient inequalities and rejects insufficient row budgets, insufficient joint budgets, inexact coefficients, and a missing coefficient array. Finite formula controls cover 675 height/occupancy cases; the unbounded strict ranges follow from the displayed formulas and monotonicity, not from those finite checks.

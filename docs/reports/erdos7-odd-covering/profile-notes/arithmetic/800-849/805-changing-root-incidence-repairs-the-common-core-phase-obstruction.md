# 805: Changing the root incidence repairs the common-core phase obstruction

Assigning all seven reference star exclusions to the short ternary root repairs the actual25-class example from [Report803](803-common-reference-phases-and-five-leaf-weights-do-not-remove-the-phase-obstruction.md). The complete23-slot residual inventory remains in use. One fixed law now admits arbitrary actual pure-q inventories and every finite prime tail strictly above3000. A second fixed law, under empty old pure-q inventories, admits every finite prime tail strictly above1600.

| Actual old pure-q inventory, q in Q | One fixed five-leaf law | Source mass lower bound | Complete allowed tail | Final distorted mass |
|---|---|---:|---|---:|
|arbitrary finite phases and heights|(7/26,7/26,2/13,2/13,2/13)|0.029809272344642618|all primes strictly above3000|0.015075518713312398>3/200|
|empty|(1/4,1/4,1/6,1/6,1/6)|0.05660114112027814|all primes strictly above1600|0.18064743228781174>9/50|

Each row uses its own law consistently for the source, every cylinder charge, the complete29 query, and the full tail. The first row does not acquire the second row's1600 cutoff. The second row does not admit arbitrary old pure-q inventories. These are ordinary conditional sufficient theorems, not new Lean verification or unrestricted Erdős#7.

The selected23 numerical labels retain a common-source null condition. Every other shallow old label, every higher old ternary height, every29 phase and every permitted large-prime phase is arbitrary. Original moduli must remain odd, greater than1, and pairwise numerically distinct. The support is contained in

\[
\{3,5,7,11,13,17,19,23,29\}\cup\{p:p>B\},
\]

whereB is3000 or1600 in the respective row. Intermediate primes31 throughB remain excluded.

## 1. A root partition changes which actual stars the core avoids

Put \(Q=\{5,7,11,13,17,19,23\}\). Use the same common normalization of actual3/9 originals as [Report801](801-retained-core-intersections-reduce-shallow-phase-contracts-to23-labels.md): the live mod9 leaves are \((4,7,2,5,8)\), with Haar suffixes above depth2. Missing or redundant3/9 originals permit the same auxiliary restrictions; these are not extra actual numerical labels. Every actual phase is transported in the one common frame.

Choose reference first digits \(\xi_q\), once for the entire source, and write \(E_q=\{x_q=\xi_q\bmod q\}\). For a subset \(R\subseteq Q\), define a core \(G_R\) by excluding all pairs of reference hits and assigning the star exclusions as follows:

- on short root1, exclude every hit inR, while allowing at most one hit in \(Q\setminus R\);
- on long root2, exclude every hit in \(Q\setminus R\), while allowing at most one hit inR.

The old one-distinguished core is \(R=\{d\}\). Here take

\[
\boxed{R=Q.}
\]

The short-root event is now no reference hit at all; the long-root event is at most one reference hit. The core remains decreasing in every hit indicator.

The actual803 family has pure classes \(0\bmod3\), \(1\bmod9\), all seven3q classes on root1 with q-coordinate0, and the remaining selected phases recorded in the certificate. Choose all \(\xi_q=0\). Every actual3q class is then excluded by this new core. A selected cylinder with two nonternary prime factors and their first digits0 lies in a pair exclusion. Every other selected singleton cylinder has short ternary root and its nonternary first digit0, so it too is excluded. All23 selected actual classes are therefore structurally null on \(G_Q\), independently of which actual pure-q survivors are later chosen.

This changes the root allocation of the seven stars. It does not merely rename reference digits or redistribute weights inside803's one-distinguished template.

## 2. Complete intersection charges for any declared root partition

For arbitrary actual pure-q inventories, let \(\lambda_q\) be their normalized actual survivor law. Distinct numerical powers imply

\[
\lambda_q([a]_{q^j})\le C_q/q^j,
\qquad C_q=\frac{q-1}{q-2}.
\]

The source is one product \(\lambda=\lambda_3\otimes\prod_{q\in Q}\lambda_q\). Its actual first-digit probabilities \(t_q=\lambda_q(E_q)\) lie in \([0,C_q/q]\). If the actual old pure-q inventories are empty, then \(\lambda_q\) is Haar and \(t_q=1/q\).

For a queried supportD, force all its reference hits to zero. Let \(A_D(t)\) and \(B_D(t)\) be the resulting short- and long-root core probabilities. Equivalently,

\[
A_D=\prod_{q\in R\setminus D}(1-t_q)
\Pr\left(\sum_{q\in(Q\setminus R)\setminus D}\mathbf1_{E_q}\le1\right),
\]

withB obtained by exchangingR and its complement. The indicators here are independent under the original product source. For \(R=Q\),

\[
A_D=\prod_{q\notin D}(1-t_q),\qquad
B_D=\Pr\left(\sum_{q\notin D}\mathbf1_{E_q}\le1\right).
\tag{RI1}
\]

The probability formula remains valid at all box endpoints; the consumer evaluates it by a zero/one-hit recurrence without division.

For fixed five-leaf weightsw, write \(s_A=w_4+w_7\), \(s_B=w_2+w_5+w_8\), \(v_A=\max(w_4,w_7)\), and \(v_B=\max(w_2,w_5,w_8)\). Define

\[
F_{D,0}=s_AA_D+s_BB_D,\quad
F_{D,1}=\max(s_AA_D,s_BB_D),\quad
F_{D,2}=\max(v_AA_D,v_BB_D).
\tag{RI2}
\]

Use admissible nonternary cylinder caps \(c_q\): the two theorem rows retain \(c_q=C_q\). For a Q-smooth nonunitn with supportD, put \(c(n)=\prod_{q\mid n}c_q/n\). The same monotone-hit removal argument as801 gives

\[
\lambda(G_R\cap A_{3^hn})\le
\begin{cases}
c(n)F_{D,h},&h=0,1,2,\\
c(n)3^{2-h}F_{D,2},&h\ge3.
\end{cases}
\tag{RI3}
\]

These upper bounds concern each one actual cylinder and one source. They do not assert simultaneous attainment of phase maxima. Pure-q cylinders have already been removed by their actual survivor laws; pure3 and9 are absent from the live ternary support.

The complete numerical support budget is

\[
\beta_D=\sum_{\operatorname{supp}(n)=D}c(n)
=\prod_{q\in D}\frac{c_q}{q-1},\qquad \beta_\varnothing=1.
\tag{RI4}
\]

LetS be the same23 numerical labels as801 and803. Require that every present actual class at a label inS be null on the same \(G_R\). Absent labels contribute no deletion. Subtract the selected contributions from their corresponding shallow height/support inventories:

\[
R_{D,h}=\beta_D-\sum_{3^hn\in S,\,\operatorname{supp}(n)=D}c(n),
\]

forh=1,2 and nonemptyD, and forh=0 with at least two primes inD; set the remaining coefficients to zero. All these residual coefficients are nonnegative because the selected labels are distinct members of the complete positive inventoryRI4.

Summing every height at least3 gives \(\sum_{h\ge3}3^{2-h}=1/2\), including pure3 powers through \(D=\varnothing\). Therefore the actual old survivorU obeys

\[
\lambda(U)\ge L_R(t):=
F_{\varnothing,0}
-\frac12\sum_D\beta_DF_{D,2}
-\sum_{D,h=0,1,2}R_{D,h}F_{D,h}.
\tag{RI5}
\]

No finite exponent cutoff replaces either complete inventory. Intersections among deleted classes are allowed; the bound is a conservative union charge on their actual intersections with the one core.

## 3. Two source estimates, with different premises

Both \(A_D\) and \(B_D\) are affine in each individual \(t_q\) while the other coordinates are fixed. InRI5, affine terms are reduced by maxima of affine functions with nonnegative coefficients. Thus \(L_R\) is separately concave. Successively lowering to an endpoint in each coordinate yields

\[
L_R(t)\ge\min_{\varepsilon\in\{0,1\}^7}
 L_R(\varepsilon_qC_q/q).
\tag{RI6}
\]

For \(R=Q\), \(c_q=C_q\), and fixed law

\[
w=(7/26,7/26,2/13,2/13,2/13),
\]

all128 exact endpoints give the minimum at the all-upper vertex:

\[
\boxed{\alpha_{\rm box}
=\frac{572908282021678}{19219130054499375}
=0.029809272344642618\ldots.}
\tag{RI7}
\]

This is the arbitrary-pure-inventory theorem's source bound. The same weights are used at every endpoint and in every subsequent query. The minimum does not assume that a finite actual family attains all cap endpoints.

Under the separate empty-pure-q premise, use \(t_q=1/q\) and

\[
w=(1/4,1/4,1/6,1/6,1/6).
\]

Keeping the original, looser caps \(c_q=C_q\) throughout the deletion and query estimates gives

\[
\boxed{\alpha_{\rm Haar}
=\frac{44628705330203}{788477130441000}
=0.05660114112027814\ldots.}
\tag{RI8}
\]

For this quarter-law, the full128 box instead yields

\[
\frac{3158635751951}{140242967865000}
=0.022522596320063266\ldots,
\]

below its complete3000 gate \(0.0268769267002831\ldots\). That box failure is retained as a control. The strongerHaar source valueRI8 cannot be used for arbitrary actual pure-q inventories.

## 4. One complete29 and prime-tail continuation per row

For each fixed law set \(r=\max(s_A,s_B)\), \(v=\max_iw_i\). Use the complete comparison variable \(Z=\prod_{p\in\{3\}\cup Q}(1+J_p)\), with independent nested-run tails

\[
\Pr(J_3\ge1)=r,\quad
\Pr(J_3\ge e)=v3^{2-e}\ (e\ge2),\quad
\Pr(J_q\ge e)=c_q/q^e.
\]

The complete mean and hinges are

\[
\mathbb EZ=(1+r+3v/2)\prod_q\left(1+\frac{c_q}{q-1}\right),
\qquad H_h=\mathbb E(Z-h)_+.
\tag{RI9}
\]

The consumer computes each hinge from the full mean and exact atoms belowh, without truncating any upper-height probability. The arbitrary-phase complete-query rearrangement of [Report790](../750-799/790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md) gives, for the one normalized actual old survivor source \(\mu=\lambda|U/\lambda(U)\) with \(\lambda(U)\ge\alpha\),

\[
B(\mu)\le\min_{0\le h\le27}\left(h+H_h/\alpha\right).
\tag{RI10}
\]

Every numerical query may have its own fixed original phase. No query receives a separately optimized source. Avoid actual pure29 originals by their actual normalized survivor law, with cap28/27, and restrict this same product source by all remaining29-ending originals. The resulting unnormalized supported measure has mass at least \((28-B(\mu))/27\).

Put

\[
A_4(p)=\frac{15}{p-1}+\frac{50}{(p-1)^2}+\frac{60}{(p-1)^3}+\frac{24}{(p-1)^4},
\]

\[
K=(1+15r+216v)\prod_q(1+c_qA_4(q))
\left(1+\frac{28}{27}A_4(29)\right).
\]

For cutoffB, choose \(\ell=7\) at3000 and \(\ell=6\) at1600. The complete quartic prime-tail factor of [Report734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md) is

\[
\tau_B=\frac{21609}{10240}
\left(\frac{2\ell^2+1}{2\ell^2-1}\right)^{21}
\frac{B}{(B-1)^4}
\sum_{j=0}^{21}\frac{21!}{(21-j)!(3\ell)^j}.
\tag{RI11}
\]

Both parameter sets satisfy the inherited analytic range and quartic coefficient conditions. Every outside original is assigned once to its largest outside prime, retaining its complete earlier cofactor, exponent and fixed phase. The final same-source mass is bounded below by

\[
\frac{28-B(\mu)}{27}-\frac{K\tau_B}{\alpha}.
\tag{RI12}
\]

ForRI7, the16 hinge gives a complete query bound approximately27.186009269357918. EquationRI12 at3000 is approximately0.015075518713312398, strictly greater than3/200. ForRI8, the12 hinge gives approximately20.334233974529816; RI12 at1600 is approximately0.18064743228781174, strictly greater than9/50. The latter row also gives approximately0.27653792471981564 at3000.

The7/26 law's uniform source does not pass its1600 continuation gate. There is no inference combining its arbitrary-pure premise with the quarter-law's stronger source mass. Positive distorted mass in either valid row supplies a common finite CRT survivor of every admitted finite family; the numerical mass floors are not asserted to be Haar-density floors.

## 5. The same actual family and the optional tighterHaar cap

The certificate retains exactly803's25 actual modulus/phase pairs, including the pure3/9 classes. Its23 selected labels are

```
15,21,45,33,35,39,63,51,57,55,105,75,
69,65,99,77,85,117,95,165,91,147,225.
```

Their nullity on the new core is checked by compatibility with all five live leaves and all128 first-digit hit patterns. The common CRT point7808250451 is4 mod9 and1 on each of the nonternary axes25,49,11,13,17,19,23. On the period11712375675, it belongs to the new short-root core and avoids every one of the25 actual classes. This witness concerns the displayed finite family, not every further extension; the complete source estimates certify some survivor after each admitted extension.

The arbitrary-pure row remains applicable after adding arbitrary old pure-q originals because the displayed selected classes are structurally excluded by the core. The empty-pure row permits arbitrary unlisted mixed originals and higher pure3 powers, but adding an old pure-q original would change its source premise. Both rows retain their respective allowed29 and large-prime extensions.

A separate empty-pure control tightens \(c_q\) from \(C_q\) to1, which is valid for the sameHaar nonternary source. With the quarter-law and the same core it gives

\[
\alpha_{\rm tight}
=\frac{2451321248291693}{12665107161907200}
=0.19354919125078734\ldots.
\]

This control is not needed for either theorem row. Its correct nonternary complete mean is

\[
\prod_q\left(1+\frac1{q-1}\right)=\frac{676039}{331776},
\]

not \(\prod_q1=1\). The simplification \(\prod_qc_q\) holds for the original \(c_q=C_q\) only because \(1+C_q/(q-1)=C_q\). The consumer uses the general formulaRI9 in every regime.

## 6. Exact evidence and scope

The [generic root-incidence consumer](../../../frontier/cover-geometry/refined-capped-source/root_incidence_repair.py) reads the [declarative certificate](../../../frontier/cover-geometry/refined-capped-source/root_incidence_repair_certificate.json) and checks the [retained result](../../../frontier/cover-geometry/refined-capped-source/root_incidence_repair.json). Root allocation, reference digits, the actual family, selected labels, fixed laws, source regimes, tail parameters and the CRT witness are certificate data. The code computes general root probabilities, actual structural nullity, complete residual inventories, all128 parameter endpoints, full comparator atoms/means, fourth moments and prime tails.

From the asset directory, run

```sh
python3 -I -S -B root_incidence_repair.py
```

Default certificate/result paths are adjacent to the script. `--certificate` and `--result` accept explicit paths; `--write-result <path>` regenerates the result. The script uses only the Python standard library and declared inputs.

Normal and optimized runs each pass134155 explicit checks. An independent directory with spaces in its path reproduces the exact result and its regeneration. Twelve altered-input kinds are rejected in both modes, including a non-null actual phase, changed root incidence, tight caps falsely assigned to arbitrary pure inventories, an unexpected pure-q original in theHaar case, forged source mass, unnormalized weights, an invalid tail cutoff, duplicate/even originals, a false CRT witness, an unearned mass floor, and a forged retained result. A positive control permits an absent selected slot.

Independent arithmetic agrees on all256 endpoint values and their core/high/shallow components for the two main laws, together with the7/26 complete hinges, fourth moment and the continuation fractions;269 exact comparisons passed. The independent direct source and tail implementation also matches both theorem rows. These calculations supportRI1–RI12 and do not replace their ordinary conditional argument or the inherited analytic prime-product premise. No global optimization over laws or root allocations is claimed.

The improvement is specific: changing the root incidence supplies a core that avoids the actual selected cylinders which defeated every one-distinguished core in803. The23-slot null interface remains substantive. This does not certify arbitrary shallow phases, remove the excluded intermediate primes, change the common-source rule, or settle unrestricted Erdős#7.

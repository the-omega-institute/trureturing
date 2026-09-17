[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md) · [Next](15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md)

<a id="a-shared-parameter-improvement-for-arbitrary-three-prime-heights"></a>
### A shared-parameter improvement for arbitrary three-prime heights

For every finite family with distinct nonunit moduli supported on
`{3,5,7}`, the uniform law on its complete actual survivor set satisfies

\[
 \boxed{\Gamma_{357}\le\frac{937}{24}<\frac{1889}{48}.} \tag{JG1}
\]

The improvement is `5/16`. It keeps the old square bound and cylinder
sum in the same actual five-cell domain, rather than independently
maximizing the two inputs of (N9). It is an upper bound; sharpness for
actual families and a new tail cutoff are not asserted.

When the pure modulus-3 and modulus-9 exclusions are effective, use the
five cells and budgets of (CM2). Put `r(j)=(0,0,1,1,1)`, and retain

\[
 n_j=\frac{w_j(z-\alpha_{r(j)}-\beta_j)}9-t_j,
 \quad s=\sum_jn_j,\quad x=\frac{\sum_jw_j}9,
 \quad n_r=\sum_{r(j)=r}n_j,\quad
 v_r=\frac{\sum_{r(j)=r}w_j}3,\quad d_r=z-\alpha_r.
\]

Thus `v_r/3` is the actual pure-ternary mass in root `r`, and `n_r`
is its complete two-prime survivor mass. The deeper mixed deletion in
that root is exactly `sum_{r(j)=r}(w_j beta_j/9+t_j)`. Its total over
the two roots is at most `1/36+1/72=1/24`, so these quantities satisfy
the hypotheses of the unshifted (ZG3). In particular, the same law has

\[
 \Gamma_{35}\le U/s,\qquad R_{35}\le T/s,
\]
\[
 \begin{aligned}
 U&=s+\max_{r=0,1}\left\{3n_r+
       \max(d_r,2d_{1-r}/3)+\frac{x+v_r+1}4+
       \frac58(x+\max(v_0,v_1)+1)\right\},\\
 T&=\max(n_0,n_1)+\max_jn_j+z/18+x/4+1/8.
 \end{aligned}
\]

Here (ZG3) is used before moving any deletion between roots. Its actual
zero-exponent layout and the cylinder masses therefore use identical
cell parameters. Form the product with the actual pure-7 survivor law
and condition away the original mixed-7 classes. This produces the
uniform complete three-prime survivor law. Applying (N9) with these
same-parameter bounds gives

\[
 \Gamma_{357}\le
       \frac{(5/3)U-T/5}{s-T/5}.                     \tag{JG2}
\]

For fixed `s,U`, the displayed quotient increases in `T`, since
`U>=s>0`; it also increases in `U`. The maxima may consequently be
expanded into `2*2*2*2*5=80` branches: selected test root, its tail
choice, the pure square-norm root, the cylinder root, and the cylinder
cell. For each branch, both numerator and denominator of (JG2) are
affine separately in each of the five groups `1-w,alpha,beta,t,z`.
Their domain is precisely the product of the four budget simplexes
and the interval used in (CM2).

The denominator-weighted vertex identity therefore reduces each
branch to the same `6*3*6*6*2=1296` vertices. Exact arithmetic checks
all **103680** branch-vertex pairs: every denominator is at least
`53/360`, and every margin

\[
 (937/24)(s-T/5)-((5/3)U-T/5)
\]

is nonnegative. Separate affinity also transports denominator positivity
throughout the continuous domain. The relaxed maximum is `937/24`.
At one maximizing vertex the cell masses are
`(1/72,1/36,1/12,1/12,1/12)`, with

\[
 s=7/24,\quad U=191/48,\quad T=5/8,\quad
 U/s=191/14<55/4,\quad T/s=15/7.
\]

This explains why the independent input maxima lose information.
The maximizer is a parameter-relaxation certificate, not a claim of
attainment by actual residue classes.

If modulus 3 is absent, the established same-law bounds
`Gamma35<=215/24` and `R35<=17/12` give `Gamma357<=5273/258` by (N9).
If modulus 3 is present but modulus 9 is absent or ineffective, use
`Gamma35<=55/4` and `R35<=47/24`, giving `Gamma357<=2703/73`.
Both are strictly below `937/24`; these cases include smaller actual
ternary heights. Arbitrary finite heights at 5 and 7 are already
covered by the geometric sums and missing-class allowances.

The existing [cofactor verifier](../verify_uniform_gamma_cofactor_coupling.py)
checks the continuous-domain certificate and both missing-class branches
under `shared_three_prime_parameters`. It preserves the earlier
72-branch square certificate. The transfer and vertex argument above
are ordinary mathematical proofs; this is not an end-to-end Lean
statement or a new unrestricted-tail exclusion.

<a id="signed-deletion-with-both-initial-ternary-test-prefixes"></a>
### Signed deletion with both initial ternary test prefixes

For the same uniform law on complete actual survivors, at arbitrary finite
heights of 3, 5 and 7, the shared-cell argument strengthens to

\[
 \boxed{\Gamma_{357}\le\frac{3849}{106}<\frac{937}{24}.} \tag{SD1}
\]

The improvement over (JG1) is `3473/1272`. This bound retains the actual
zero-seven test layout in both its product cross terms and the energy
removed by the mixed-seven classes. It makes no optimal-law, actual-family
sharpness or new tail-cutoff claim.

First suppose the original pure modulus-3 and modulus-9 exclusions are
effective. Use exactly the five-cell parameters of (CM2), without moving
any deletion between cells, and write

\[
 d_l=z-\alpha_{r(l)}-\beta_l,\qquad
 n_l=w_ld_l/9-t_l,\quad s=\sum_ln_l,\quad
 x=\sum_lw_l/9,\quad
 n_r=\sum_{r(l)=r}n_l,\quad v_r=\sum_{r(l)=r}w_l/3.
\]

Let `A0` be the zero-seven block of a complete test layout; it is itself
a complete `{3,5}` test load. Retain the root `r` and cell `j` chosen by
the modulus-3 and modulus-9 tests in its zero-five block. If either test
is inactive on pure survivors, changing it to any surviving root or cell
increases the whole load pointwise. Thus it suffices to consider these
`2*5` choices. The two choices are independent: the test cell need not
lie in the test root.

Define `c_l=3+2*1[r(l)=r]+2*1[l=j]` and

\[
 \begin{aligned}
 P_{rj}&=s+3n_r+(3+2\mathbf1_{r(j)=r})n_j
       +\frac{\max_l(c_ld_l)+\max_ld_l}{18},\\
 V_{rj}&=x+v_r+(3+2\mathbf1_{r(j)=r})w_j/9
       +\frac{\max_lc_l+1}{18},\\
 U_{rj}&=P_{rj}+V_{rj}/4+
                \frac58(x+\max(v_0,v_1)+1),\qquad
 U=\max_{r,j}U_{rj}.
 \end{aligned} \tag{SD2}
\]

Here `s E_mu35 A0²<=U_rj`, while `s Gamma35<=U`. To verify these
statements, write the zero-five ternary load as
`1+I_root+I_cell+sum_{a>=3} I_a`. The first three terms have exact raw
square `s+3n_r+(3+2*1[r(j)=r])*n_j`. A depth-`a>=3` test cylinder in
cell `l` has raw complete-survivor mass at most `d_l*3^(-a)`: it already
avoids the pure-five exclusions and all first- and second-level mixed
exclusions represented by `alpha,beta`. Its diagonal and cross terms
with the first three tests have coefficient `c_l`. These terms sum to
at most `max_l(c_l*d_l)/18`. The ordered pairs of distinct deeper tests
are bounded by `max_l(d_l)/18`, since

\[
 \sum_{a\ge3}3^{-a}=\frac1{18},\qquad
 2\sum_{b\ge4}(b-3)3^{-b}=\frac1{18}.
\]

This proves `P_rj`. The same expansion under the raw pure-ternary law
has root mass `v_r/3`, cell mass `w_j/9` and depth caps `3^(-a)`, giving
`V_rj`. The already proved (ZG2), with its global pure-ternary norm bound
`x+max(v_0,v_1)+1`, gives `U_rj`. No consistency between distinct test
prefixes has been assumed. Finite sums are bounded by the displayed
nonnegative infinite sums.

The existing Lean theorem
`ArbitraryRootEventMoment.arbitrary_root_event_moment_le` supplies this
tail estimate directly, and even bounds it by the smaller quantity
`max_l((c_l+1)*d_l)/18`. Use the five surviving cells as root labels,
discount `1/3`, initial caps `d_l/27`, and initial counts
`1[r(l)=r]+1[l=j]`. The actual depth-`a` tests restricted to complete
survivors satisfy its geometric caps by the preceding product-count
bound; empty tests remain at their original depths. For the pure-ternary
law, use initial caps `1/27`. This is direct library reuse inside the
ordinary arithmetic argument, not an additional Lean declaration or a
claim that the actual-family extraction has been formalized end to end.

Take a target `C>=9` and let

\[
 k_l=C-(1+\mathbf1_{r(l)=r}+\mathbf1_{l=j})^2\ge0.
\]

The actual complete old load satisfies `(C-A0²)_+<=k_l` in cell `l`.
The raw weighted sum of maximum cylinder masses over all nonunit old
cofactors is at most

\[
 \begin{aligned}
 W_{rj}(C)={}&
 \max_{a=0,1}\sum_{r(l)=a}k_ln_l+\max_lk_ln_l
       +\frac{\max_lk_ld_l}{18}\\
 &+\frac{\sum_lk_lw_l}{36}
       +\frac{\max_{a=0,1}\sum_{r(l)=a}k_lw_l}{36}
       +\frac{\max_lk_lw_l}{36}
       +\frac{C-1}{72}.
 \end{aligned} \tag{SD3}
\]

The seven terms respectively cover cofactors `3`, `9`, `3^a (a>=3)`,
`5^b`, `3*5^b`, `9*5^b`, and `3^a*5^b (a>=3,b>=1)`. The first two
use the actual cell masses. The third uses the residual availability
`d_l` just proved. For the next three, drop all five-coordinate
exclusions and use the weighted pure-ternary masses. The last drops
both sets of exclusions and uses `max_l k_l=C-1`, together with
`sum_{a>=3,b>=1}3^(-a)*5^(-b)=1/72`. This accounts for every old
cofactor without identifying distinct original labels.

Let `nu7` be the uniform actual pure-seven survivor law, and put
`M=mu35 times nu7`. Its positive-depth cylinder caps `a_e` satisfy
`sum a_e<=1/5` and `sum(2e-1)*a_e<=4/15`. For the full test load `L`,
retain `A0` in each zero/positive-seven cross block. The same square
inequality as in (ZG2) gives

\[
 \mathbb E_M L^2\le
       \frac65\mathbb E_{\mu_{35}}A_0^2+
       \frac7{15}\Gamma_{35}
 \le\frac{(6/5)U_{rj}+(7/15)U}{s}. \tag{SD4}
\]

Let `B` be the actual mixed-seven forbidden union. Conditioning `M`
on its complement gives precisely the uniform complete three-prime
survivor law. Since `L>=A0` pointwise, weighted union bounding and (SD3)
give

\[
 \begin{aligned}
 \mathbb E_M[(L^2-C)\mathbf1_{B^c}]
 &\le\mathbb E_M L^2-C+
           \mathbb E_M[(C-A_0^2)_+\mathbf1_B]\\
 &\le\frac{(6/5)U_{rj}+(7/15)U+W_{rj}(C)/5-Cs}{s}.
 \end{aligned} \tag{SD5}
\]

For each fixed positive seven exponent the original mixed moduli have
distinct old cofactors, so (SD3) applies before summing its cap `a_e`.
The complete survivor set is nonempty by (CM2). Therefore a nonpositive
right side proves `Gamma357<=C` on this same law.

For `C=3849/106`, exact rational arithmetic verifies

\[
 Cs-\frac65U_{rj}-\frac7{15}U-\frac15W_{rj}(C)\ge0 \tag{SD6}
\]

at all `1296*2*5=12960` parameter-vertex/test-choice pairs. This is a
continuous-domain certificate, not finite-height sampling. For a fixed
test choice, expand each maximum in `U_rj,U,W` into its finitely many
branches. Each resulting margin is affine separately in every group
`1-w,alpha,beta,t,z`; the full margin is their pointwise minimum and
hence concave in each group separately. Its value throughout each
simplex or interval is at least the convex combination of its vertex
values. Applying this successively to the five groups proves (SD6)
everywhere. Checking the maxima at each vertex already checks the
worst branch there, so a separate enumeration of all branch products
is unnecessary.

The least vertex margin is zero. One equality point in this relaxation
has

\[
 \begin{gathered}
 1-w=(1/2,0,0,0,0),\quad\alpha=(0,1/4),\quad
 \beta=(0,0,1/4,0,0),\\
 t=(1/72,0,0,0,0),\quad z=3/4,\quad(r,j)=(0,1),\\
 (n_l)=(1/36,1/12,1/36,1/18,1/18),\quad
 s=1/4,\quad U_{rj}=U=163/48.
 \end{gathered}
\]

This is not an assertion that an actual residue family attains (SD1).

If modulus 3 is absent, reuse the same-law bounds
`Gamma35<=215/24,R35<=17/12`; (N9) gives `Gamma357<=5273/258`.
If modulus 3 is present but modulus 9 is absent or ineffective, the
already proved (P11)--(P12) give the stronger input
`Gamma35<=K35<=593/48,R35<=47/24`. Substitution in (N9) gives

\[
 \Gamma_{357}\le\frac{14543}{438}<\frac{3849}{106}.
\]

These include ternary heights below two and preserve the complete actual
uniform law. Missing five- or seven-coordinate classes and smaller
heights are already covered by the cap inequalities. Thus (SD1) holds
for every finite original family with these prime supports.

The existing [cofactor verifier](../verify_uniform_gamma_cofactor_coupling.py)
recomputes all signed margins and both fallback bounds under
`signed_two_level_three_prime_parameters` in its
[certificate](../certificates/uniform_gamma_cofactor_certificate.json).
The earlier certificate fields are retained unchanged. Equations
(SD1)--(SD6) are ordinary mathematical proofs with exact arithmetic;
they have not been checked end to end in Lean.

<a id="a-uniform-survivor-obstruction-and-sharpness-at-two-primes"></a>
### A uniform-survivor obstruction and sharpness at two primes

Let P be the twenty odd primes from 3 through 73 and H>=1. Set
Q_H=product_{p in P} p^H. Give every nonunit divisor exactly one forbidden
class, according to its support:

* p^e: residue p^(e-1)-1 modulo p^e;
* 3^i 5^j: CRT residues 2*3^(i-1)-1 and 2*5^(j-1)-1;
* all other mixed divisors: residue 0.

These support cases are disjoint and exhaustive, with no duplicate modulus.
The third class lies in 0 mod p for any prime p dividing that modulus;
0 mod p is already the e=1 pure forbidden class. Thus all higher-support
moduli are present but redundant. No antichain or nonredundancy hypothesis
is required by the uniform-head statement being tested.

<a id="geometry-for-every-finite-height"></a>
#### Geometry for every finite height

Write F_{p,e} and C_{p,e} for the cylinders with residues p^(e-1)-1 and
2*p^(e-1)-1. If e<f, either depth-f residue reduces to -1 modulo p^e.
Neither depth-e residue equals -1 modulo p^e for odd p: their differences
from -1 are p^(e-1) and 2*p^(e-1). At equal depth F and C are distinct.
Hence all 2H cylinders are mutually disjoint. Put

    s_p=sum_{e=1}^H p^(-e), lambda_p=1-s_p,
    S_p=(union_e F_{p,e})^c, C_p=union_e C_{p,e}.

Then C_p is contained in S_p, U_p(C_p)=s_p and U_p(S_p)=lambda_p.
The union of all support-{3,5} mixed classes is exactly C_3 x C_5.
Consequently the complete survivor set is exactly

    R_H=[(S_3 x S_5) minus (C_3 x C_5)] x product_{p>=7} S_p.

Let u=3^(-H), v=5^(-H). Its {3,5} block has ambient mass

    D=lambda_3 lambda_5-s_3 s_5=1-s_3-s_5=(1+2u+v)/4>1/4.

The entire survivor density is D product_{p>=7}lambda_p, strictly above
(1/4) product_{p>=7}(p-2)/(p-1)>0. No exceptional thin set or Dirac law is used.

<a id="one-whole-test-layout-and-its-exact-integral"></a>
#### One whole test layout and its exact integral

Take beta=2 at the 5-adic coordinate and beta=1 at every other prime,
modulo the full p^H. CRT chooses a single beta_H modulo Q_H. At every
divisor d, including 1, use its reduction beta_H mod d as the test class.
Define ell_p=1+sum_{e=1}^H 1_{x_p=beta mod p^e}. Exact divisor expansion gives

    L=product_p ell_p.

The cylinders in each ell_p are nested. Therefore ell_p^2 equals
1+sum_e(2e+1)1_{x_p=beta mod p^e}. Define W_p=sum_e(2e+1)p^(-e).
Every such test cylinder lies in S_p: its first digit is different from
0 and from -1. All positive-depth 3-adic test cylinders lie in C_{3,1};
the 5-adic test cylinders avoid C_5 entirely. Thus

    integral_{S_p} ell_p^2=lambda_p+W_p,
    integral_{C_3} ell_3^2=s_3+W_3,
    integral_{C_5} ell_5^2=s_5.

Using the actual set difference, rather than independent {3,5} marginals,
the exact block score is

    g_H=[(lambda_3+W_3)(lambda_5+W_5)-(s_3+W_3)s_5]/D.

The full coherent-layout score under the uniform COMPLETE survivor law is

    G_H=g_H product_{p>=7}(1+W_p/lambda_p).

Therefore Gamma(Unif R_H)>=G_H. No maximality of this particular test
layout is assumed or needed.

<a id="strict-monotonicity-exact-positive-numerators"></a>
#### Strict monotonicity: exact positive numerators

Put D'=1+2u+v. Algebra gives

    g_H=1+2 A_H W_3+2 B_H W_5+4 C_H W_3 W_5,
    A_H=(1+v)/D', B_H=(1+u)/D', C_H=1/D'.

At H+1, u becomes u/3 and v becomes v/5. All denominators are positive.
After putting each difference over D'_H D'_{H+1}, the exact numerators are

    A_{H+1}-A_H: 4u(5-v)/15 >0,
    B_{H+1}-B_H: 2u/3+4v/5+2uv/15 >0,
    C_{H+1}-C_H: 4u/3+4v/5 >0.

Here 0<v<=1/5 because H>=1. Also W_p strictly increases and lambda_p
strictly decreases while staying positive. Hence both g_H and G_H strictly
increase for every H>=1. In particular any exact H=5 lower bound persists
for every H>=5; finite tests are not the basis of this assertion.

<a id="limit-and-sharpness-of-the-uniform-two-prime-constant"></a>
#### Limit and sharpness of the uniform two-prime constant

As H tends to infinity, W_3->2, W_5->7/8, and A_H,B_H,C_H->1. Therefore

    g_H -> 1+4+7/4+7 =55/4.

Together with the independently proved universal uniform Gamma35<=55/4,
this proves that 55/4 is the sharp constant over finite families: every
smaller proposed uniform constant is exceeded at a sufficiently large
finite height. This does not claim that a finite family attains equality.

The full limiting witness is

    (55/4) product_{7<=p<=73}(1+(3p-1)/((p-1)(p-2))).

Before the mixed rectangle is deleted the limiting {3,5} witness is
5*(13/6)=65/6. The exact amplification ratio is (55/4)/(65/6)=33/26.

For p=3 there is the sharper geometric explanation:
S_3 is the disjoint union of C_3 and the final singleton -1 mod 3^H,
because 2s_3+3^(-H)=1. Thus the mixed cofactors remove C_5 above nearly
all of the pure-3 survivor set; on C_5 the selected 5-load is exactly 1.

<a id="scope-of-the-conclusion"></a>
#### Scope of the conclusion

At height 5 the exact arithmetic gives

\[
 g_5=\frac{2581475}{191467},\qquad
 142.3789923<G_5<142.3789924.
\]

The uniform survivor density at this height is approximately
`0.11216643572445546`. At every height it exceeds
`36779876601/330712481792>11/100`. The limiting score is approximately
`145.21869889477725`. The [exact verifier](../verify_uniform_survivor_obstruction.py)
and its [fixed certificate](../certificates/uniform_survivor_obstruction_certificate.json)
recompute the finite sums, pairwise CRT disjointness and individual
`3^5` and `5^5` coordinates by direct enumeration.

Thus the universal strengthening requiring the uniform complete-survivor
law to satisfy `Γ≤138877/1000` is false, already at height 5. Strict
monotonicity makes the same family an obstruction at every `H≥5`.
The construction does not refute the existence of a nonuniform survivor
law with small Gamma, and it does not construct an odd covering system.
The separate star family refutes the nonuniform existential Γ73 target.
The present rectangular-family argument and exact arithmetic are not a Lean proof.


<a id="a-nonuniform-law-for-the-rectangular-obstruction-family"></a>
### A nonuniform law for the rectangular obstruction family

For the specified rectangular forbidden family on all odd primes through
73, every common height `H≥5` admits a complete-survivor probability law
with

\[
 \boxed{\Gamma\le
 \frac{64245900555623296761826781321804225}
      {479017695593451697408733725605888}
 <134.121<138.877.} \tag{NR1}
\]

This is an existence statement for this family. It does not restore the
uniform-law bound or establish the same existence statement for all
forbidden-residue assignments.

Let `P` be the odd primes at most 73 and `Q_H=∏_{p∈P}p^H`. On the
`p`-power coordinate, with ambient uniform measure `U_p`, define

\[
 F_{p,e}=\{x:x\equiv p^{e-1}-1\pmod{p^e}\},\qquad
 C_{p,e}=\{x:x\equiv2p^{e-1}-1\pmod{p^e}\},
\]
\[
 S_p=(\mathbb Z/p^H)\setminus\bigcup_{e=1}^H F_{p,e},\qquad
 C_p=\bigcup_{e=1}^H C_{p,e},\qquad
 s_p=\sum_{e=1}^H p^{-e}=\frac{1-p^{-H}}{p-1}.
\]

The actual forbidden assignment uses `F_{p,e}` for pure powers, the CRT
rectangle `C_{3,i}×C_{5,j}` for modulus `3^i5^j`, and residue zero for
every other mixed divisor. At different depths the first nonterminal digit
occurs in different positions; at equal depth the `F` and `C` digits are
distinct. Hence these cylinders are pairwise disjoint and `C_p⊆S_p`, with
`U_p(C_p)=s_p` and `U_p(S_p)=1−s_p`. The other mixed classes are redundant,
since each is contained in an already forbidden pure residue `0 mod p`.
Thus the complete survivor set is exactly

\[
 R_H=\bigl((S_3\times S_5)\setminus(C_3\times C_5)\bigr)
             \times\prod_{7\le p\le73} S_p. \tag{NR2}
\]

We use the rectangular subset
`C_3×(S_5\C_5)×∏_{p≥7}S_p` of this actual survivor set.

**The ternary law.** The first cylinder `C_{3,1}` is the entire root
`1 mod 3`, of ambient mass `1/3`. All remaining `C_{3,e}`, `e≥2`, lie
in root `2 mod 3`; their total relative root width is

\[
 w_H=3\sum_{e=2}^H3^{-e}=\frac{1-3^{1-H}}2,
 \qquad \frac{40}{81}\le w_H<\frac12\quad(H\ge5).
\]

Give the raw restricted measure `U_3|C_3` multiplier `h=1` on root 1
and `k=4/3` on root 2. Its mass is

\[
 x_H=\frac{1+(4/3)w_H}{3}\ge\frac{403}{729}>0.
\]

The general weighted two-root event inequality applies to this finite
positive measure: it needs only the two root masses and the depth-wise
cylinder caps `h·3^{-e}`, `k·3^{-e}`. In particular it does not require
`w_H≥1/2`, a condition used in the separate pure-survivor budget problem.
The root masses here are `1/3` and `(4/3)w_H/3`. The root-labelled
finite-itinerary estimate gives

\[
 \Gamma(\text{raw law})\le x_H+
 \max\{2,\ 17/9,\ (4/3)(w_H+1),\ (4/3)w_H+2/3\}
 \le x_H+2.
\]

A modulus-3 test in the zero-mass root contributes no event; its remaining
weighted tail is at most `(2/3)max(h,k)=8/9`, also below 2. All later
root choices, including nonnested choices, are covered by the event bound.
After normalization, the resulting probability `μ_3` satisfies

\[
 \Gamma(\mu_3)\le1+\frac2{x_H}\le\frac{1861}{403}.
 \tag{NR3}
\]

The finite-event inequality is supplied by the existing general weighted
root theorem; the residue identification and normalization here are the
ordinary mathematical application of that component.

**The quinary law.** Let `μ_5` be uniform on `S_5\C_5`. Its ambient
density is

\[
 1-2s_5=\frac{1+5^{-H}}2>\frac12.
\]

Consequently every cylinder modulo `5^e` has `μ_5`-mass at most
`2·5^{-e}`. For completeness, if a probability `ν` on a new `p`-power
coordinate has every depth-`e` cylinder bounded by `C p^{-e}`, then for
any old law `μ`, complete-layout grouping gives

\[
 \Gamma(\mu\times\nu)
 \le\Gamma(\mu)\left(1+C\sum_{e\ge1}(2e+1)p^{-e}\right).
 \tag{NR4}
\]

To see this, group ordered outside exponents by their maximum. Outside
residues may depend on the old divisor, but every old divisor pair has
outside intersection mass at most `C p^{-e}`. Sum the old indicators and
use Cauchy–Schwarz for their two complete old layouts. The count is `2e+1`;
the zero-exponent block has exactly the old bound. Finite-height sums are
bounded by these nonnegative infinite sums. This is the cylinder-cap
transfer; it assumes no general multiplicativity of actual Gamma.

Since `∑_{e≥1}(2e+1)5^{-e}=7/8`, (NR3)–(NR4) give

\[
 \Gamma(\mu_3\times\mu_5)
 \le\frac{1861}{403}\left(1+2\frac78\right)
 =\frac{20471}{1612}. \tag{NR5}
\]

**The remaining primes and support.** For every `p≥7`, take `μ_p` uniform
on `S_p`. Its ambient density is at least `(p−2)/(p−1)`, so its depth-`e`
cylinder cap is `[(p−1)/(p−2)]p^{-e}`. Iterating (NR4), all normalizers
remain positive and the transfer factor at `p` is

\[
 1+\frac{3p-1}{(p-1)(p-2)}
   =\frac{p^2+1}{(p-1)(p-2)}.
\]

The final law `μ_3×μ_5×∏_{p≥7}μ_p` is supported on (NR2): its ternary
coordinate lies in `C_3`, its quinary coordinate avoids `C_5`, and every
coordinate avoids all original pure forbidden classes. Therefore it also
avoids the redundant mixed zero classes. No conditioning or uniform-law
estimate from a different distribution is used.

The exact remaining-prime product is

\[
 \prod_{\substack{7\le p\le73\\p\text{ prime}}}
 \frac{p^2+1}{(p-1)(p-2)}
 =\frac{34522246402806715078896712155725}
        {3268731173404447066684907556864}.
\]

Multiplying by (NR5) proves (NR1). The exact margin below `138877/1000` is

\[
 \frac{284829994413561827400741536145585347}
      {59877211949181462176091715700736000}>0.
\]

The standalone standard-library verifier
[verify_rectangular_family_nonuniform_law.py](../elementary-checks/verify_rectangular_family_nonuniform_law.py) recomputes the root-width
endpoints, affine weighted-root bounds, every prime and transfer factor,
and the exact final inequality against
[rectangular_family_nonuniform_certificate.json](../certificates/rectangular_family_nonuniform_certificate.json). The bounds hold uniformly
for all common heights `H≥5`; the program does not enumerate the full
period. No complete Lean formalization of this family result is claimed.

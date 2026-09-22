[Index](../../marked_head_profile.md) · [The saturated-chain source](388-saturated-chain-blockers-do-not-supply-conditional-caps.md) · [Arbitrary-head transfer](../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md)

# The saturated-chain source has a small complete-layout second moment

The source `R` of report 388 blocks every proposed full-history law
with its specified caps and blocks the corresponding finite-depth
convex comparison. Nevertheless its uniform law satisfies

\[
 \Gamma_{385}(\nu)=\frac{21}{4}<\frac{32}{5}.
 \tag{GM1}
\]

Here the maximum defining `Gamma` ranges over **all** complete divisor
layouts with a freely chosen fixed residue for each numerical divisor.
No common-centre assumption restricts this maximum. A centred layout
is used only to attain the upper bound.

After lifting the same source by independent uniform higher digits,
the complete-layout second moment has an exact formula at every finite
height. Its supremum is `256543/32400<8`, and at every height it remains
strictly below the second moment of the independent finite-depth
comparison using bases `(3,3,5)`. Thus the source counterexample to
full convex comparison does not obstruct this direct second-moment
estimate, which is the type of datum consumed by Chapter 08.

This result concerns one explicitly specified abstract source and
one specified law. It does not prove that the source is an actual
odd-cover residual, optimize over all supported laws, or establish a
general second-moment theorem for all sources satisfying the product
tree conditions. No Lean theorem or solution of Erdős #7 is claimed.

## 1. Source and independent complete test layouts

Let `P={5,7,11}`, `s=(0,1,3)`, and retain exactly the source from
report 388:

\[
 R=\{(u+1,i+1,i+s_u+d+1):
       0\le u\le2,\ 0\le i\le5,\ d\in\{0,1\}\}.
 \tag{GM2}
\]

It has 36 points. For positive finite heights `H_p`, put
`Q_H=product_p p^H_p`. Let `R_H` consist of every complete CRT point
whose first roots lie in `R`; all higher digits are arbitrary.
The probability `nu_H` is uniform on `R_H`, equivalently uniform `R`
with mutually independent uniform higher digits, independent of the
root tuple. In particular `|R_H|=36 product_p p^(H_p-1)`.

For every complete layout `b=(b_d)_(d|Q_H)`, with each `b_d` a fixed
residue modulo `d`, define

\[
 L_b(x)=\sum_{d\mid Q_H}\mathbf1_{x=b_d\bmod d},\qquad
 \Gamma_{Q_H}(\nu_H)=\max_b\mathbb E_{\nu_H}L_b^2.
 \tag{GM3}
\]

Divisor one contributes the constant one. Residues at different
divisors are independent choices and may be incompatible. The layout
is fixed before sampling `x`. All statements below refer to this
one unchanged source law.

## 2. Complete cylinder maxima and simultaneous attainment

For a squarefree divisor `s` of `385`, write `M(s)` for the largest
mass of a cylinder modulo `s` under uniform `R`. Counting projection
fibres gives

| `s` | `1` | `5` | `7` | `11` | `35` | `55` | `77` | `385` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `M(s)` | `1` | `1/3` | `1/6` | `1/6` | `1/18` | `1/18` | `1/18` | `1/36` |

For example, first-5 fibres have 12 points, first-7 fibres have six,
and the largest first-11 fibres have six. Every two-coordinate fibre
has at most two points, with that maximum attained in each direction.
Every triple fibre is a single point.

The root centre

\[
 c=(1,4,5)
 \tag{GM4}
\]

simultaneously attains **every entry** in this table. Specifically
its pair fibres at `(5,7)`, `(5,11)` and `(7,11)` all have two points,
and its first-11 fibre has six. Its CRT representative modulo `385`
is `291`. Any higher-digit extension of this root centre has the
same simultaneous property at every full divisor of `Q_H`.

Indeed, for `d|Q_H`, let `S={p:p|d}` and `a_p=v_p(d)`. Uniform
independent higher digits imply the exact maximum

\[
 M_H(d):=\max_a\nu_H(x=a\bmod d)
 =M\!\left(\prod_{p\in S}p\right)
       \prod_{p\in S}p^{-(a_p-1)}.
 \tag{GM5}
\]

The chosen full centre attains GM5 simultaneously for all `d`. This
simultaneous attainment is verified for this source, not assumed for
general measures or inferred from separately attained maxima.

## 3. Exact maximum over all freely chosen residues

For any fixed layout `b` and any `d,e|Q_H`, the two congruences
intersect either in the empty set or in one cylinder modulo
`lcm(d,e)`. Thus

\[
 \mathbb E_{\nu_H}L_b^2
 \le\sum_{d,e\mid Q_H}M_H(\operatorname{lcm}(d,e)).
 \tag{GM6}
\]

This upper bound retains all independent choices of `b_d,b_e`.
For the one centred layout `b_d=c mod d`, every intersection is
the centred lcm cylinder and attains its GM5 maximum. Consequently

\[
 \boxed{\Gamma_{Q_H}(\nu_H)
       =\sum_{d,e\mid Q_H}M_H(\operatorname{lcm}(d,e)).}
 \tag{GM7}
\]

At height one, the numbers of ordered divisor pairs with each lcm
are `1,3,3,3,9,9,9,27` in the table's order. Therefore GM7 is

\[
 1+3\left(\frac13+\frac16+\frac16\right)
   +9\left(\frac1{18}+\frac1{18}+\frac1{18}\right)
   +\frac{27}{36}
 =\frac{21}{4}.
 \tag{GM8}
\]

The upper and lower bounds agree over the **full** layout space;
no layout enumeration or reduction to common centres was needed.

## 4. Exact all-height formula and its supremum

The number of exponent pairs `(i,j)` with `0<=i,j<=H_p` and
`max(i,j)=a` is `2a+1`. Put

\[
 A_p(H)=\sum_{a=1}^H(2a+1)p^{-(a-1)}.
 \tag{GM9}
\]

Inserting GM5 in GM7 and grouping the positive lcm coordinates gives

\[
 \begin{aligned}
 \Gamma_{Q_H}(\nu_H)
 ={}&1+\frac{A_5}{3}+\frac{A_7+A_{11}}6\\
 &+\frac{A_5A_7+A_5A_{11}+A_7A_{11}}{18}
   +\frac{A_5A_7A_{11}}{36},
 \end{aligned}
 \tag{GM10}
\]

where each `A_p` uses that coordinate's own original height. There
is no common-height assumption. All coefficients are positive.
The geometric sums give

\[
 A_p(\infty)=\frac{p(3p-1)}{(p-1)^2},\qquad
 (A_5(\infty),A_7(\infty),A_{11}(\infty))
 =\left(\frac{35}{8},\frac{35}{9},\frac{88}{25}\right).
 \tag{GM11}
\]

For an explicit finite-height remainder,

\[
 A_p(\infty)-A_p(H)
 =p^{1-H}\left(\frac{2H+3}{p-1}
                         +\frac{2}{(p-1)^2}\right)>0.
 \tag{GM12}
\]

Hence GM10 increases coordinatewise with the heights, and

\[
 \boxed{\sup_{H_5,H_7,H_{11}\ge1}\Gamma_{Q_H}(\nu_H)
       =\frac{256543}{32400}<8.}
 \tag{GM13}
\]

The supremum follows by letting all three heights tend to infinity;
it is not attained at finite heights. GM10--GM12 prove the all-height
result, rather than a finite-height extrapolation.

## 5. Direct second-moment comparison survives at every height

Let `(r_5,r_7,r_11)=(3,3,5)`. The uniform lift retains the
complete-chain marginal bounds `Pr(x_p=a mod p^j)<=r_p^(-j)` from
report 388. Consider independent auxiliary variables `K_p` with
values `0,...,H_p` and tails

\[
 \Pr(K_p\ge j)=r_p^{-j},\qquad 1\le j\le H_p.
 \tag{GM14}
\]

These are finite-height variables, including their terminal atoms.
The second moment of `D=product_p(1+K_p)` is

\[
 T_H:=\mathbb ED^2
 =\prod_p\left(1+\sum_{j=1}^{H_p}(2j+1)r_p^{-j}\right).
 \tag{GM15}
\]

For **every** positive finite height triple,

\[
 \Gamma_{Q_H}(\nu_H)<T_H.
 \tag{GM16}
\]

A uniform rational separation proves this without searching heights.
If `H_5>=2` or `H_7>=2`, the corresponding base-three factor in
GM15 is at least `1+3/3+5/9=23/9`; the other base-three factor
is at least two, and the base-five factor is at least `8/5`.
Thus

\[
 T_H\ge\frac{368}{45},\qquad
 T_H-\Gamma_{Q_H}(\nu_H)
 >\frac{368}{45}-\frac{256543}{32400}
 =\frac{8417}{32400}>0.
 \tag{GM17}
\]

Otherwise `H_5=H_7=1`, so `A_5=A_7=3` and GM10 reduces to
`3+(3/4)A_11`. Consequently

\[
 \Gamma_{Q_H}(\nu_H)<\frac{141}{25},\qquad
 T_H\ge\frac{32}{5},\qquad
 T_H-\Gamma_{Q_H}(\nu_H)>\frac{19}{25}.
 \tag{GM18}
\]

In particular GM17's smaller positive margin works for all height
triples. At height one the exact comparison is GM1. For reference,
the auxiliary infinite-height limit is `135/8`, strictly above GM13.

GM16 is only a second-moment inequality for this one law. It neither
constructs the conditional rows ruled out in report 388 nor asserts
all increasing convex comparisons. At height one, the same uniform
law still has the report-388 centred stop-loss cost `5/12>1/3`
at threshold 49. The two statements concern different functionals
of the same actual load and are compatible.

## 6. Exact checker and scope

The [standalone standard-library checker](../../frontier/cover-geometry/saturated_chain_second_moment.py)
reconstructs the source, computes all complete root-cylinder maxima,
and verifies simultaneous attainment at GM4. It independently expands
the 64 ordered squarefree divisor pairs. For a declared small collection
of height triples, it reconstructs each entire lifted carrier, counts
all divisor-cylinder fibres, checks the chosen centre attains every
maximum, and directly integrates the centred complete load. These
controls agree with GM7 and GM10; the proof supplies their unbounded
height scope. The checker also verifies the exact infinite rational
constant, GM12, and the two strict comparisons GM17--GM18.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/saturated_chain_second_moment.py
```

The square-expansion and lcm-cylinder estimate are the existing
joint-layout technique used in `finite_head_geometry.md` and Chapter
08. Their evaluation here is specific to the source of report 388.
The result rules out treating failure of its conditional/convex bridge
as failure of every second-moment route. The missing general theorem
is still a same-law quantitative bound for actual arithmetic sources
over the full original covering quantifiers, including the construction
of a head law on the required actual survivors. This example alone
does not supply that theorem.

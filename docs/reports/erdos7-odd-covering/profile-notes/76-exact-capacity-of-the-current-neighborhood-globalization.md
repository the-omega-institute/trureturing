[Index](../marked_head_profile.md) · [Neighborhood](73-an-explicit-neighborhood-of-both-controlling-beta-faces.md) · [Global gain](74-a-strict-global-k-gain-from-the-controlling-faces.md)

# Exact capacity of the current neighborhood globalization

The profile74 mechanism can be optimized exactly, but tuning its local
constants cannot produce a substantial decrease of K. With the tighter
pointwise constants already available in profile73 and the complete
geometric tails, the maximum decrement certified by this particular
template is

\[
0.0000119694060222643\ldots<0.000012.
\]

Keeping half the signed reserve, as profile74 does, gives
0.00000598470301113216... instead. These are capacities of the specified
certificate construction, not upper bounds on what other mathematics
could prove. The canonical global K target is not changed here.

The exact [program](../frontier/k_neighborhood_route_limit.py), with
[certificate](../certificates/source_norms/k_neighborhood_route_limit.json),
can be run with:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/k_neighborhood_route_limit.py --check
```

The optimization proof below is analytic; the program verifies rational
crossings and complete geometric tails, not a numerical grid.

## Tighter local errors already justified by the source proof

Profile73(FN11)--(FN12) gives each first-five test cap the error

\[
3\tau+261\epsilon+\frac25\kappa.
\]

Use this for the independent tests5 and15 in place of the coarser
14tau+300epsilon+kappa in its displayed inventory. Keeping every other
category and both complete tails unchanged gives

\[
\int A\le S+\frac{233}{450}
+\frac{2017}{180}\tau+530\epsilon+\frac{739}{450}\kappa
+R_3(\epsilon)+R_5(\epsilon),
\tag{L1}
\]

where

\[
R_3(e)=\sum_{j\ge3}\min(4e,\tfrac1{20}3^{-j}),\qquad
R_5(e)=\sum_{j\ge2}\min(e,\tfrac4{45}5^{-j}).
\tag{L2}
\]

The source mass estimate S>=53/360-8tau/5+epsilon and the true old
margin bound9257/48600+12tau+kappa/2 imply the gain

\[
G(\tau,e,\kappa)=\frac{677}{24300}
-\frac{5617}{180}\tau-530e-\frac{482}{225}\kappa
-R_3(e)-R_5(e).
\tag{L3}
\]

The positive 5epsilon from the actual mass lower bound has been
discarded, as in profile73. A slightly weaker, simpler version is

\[
G_{\rm rounded}=\frac{677}{24300}-32\tau-530e-\frac52\kappa
-R_3(e)-R_5(e).
\tag{L4}
\]

No stronger geometric guard has been introduced: tau<=1/1000 and
e<=1/10000 remain required. All tests retain independent original
residues, and (L2) includes the entire exponent tails.

## Precisely which certificate template is being optimized

Keep the notation from profiles71 and74:

\[
\gamma=\gamma_K>0,\quad
a=q(K_0-b)-L>0,\quad
\beta=\beta_{40}>0,\quad c=\frac4{45}.
\]

Use a single isotropic barycentric radius delta, the face-distance bound
tau<=37delta/8, carrier error kappa<=delta, mass bridge S_0-D<=c delta,
and the outside reserve gamma delta. For an epsilon cutoff e the
certified reserve is

\[
\mathcal R(\delta,e)=\min\left\{
\gamma\delta,\ a(e-c\delta),\
\beta\bigl(g_0-A\delta-530e-R_3(e)-R_5(e)\bigr)
\right\},\tag{L5}
\]

where g_0=677/24300. The coefficient A equals

\[
A_{\rm rounded}=32\frac{37}8+\frac52,
\qquad
A_{\rm exact}=\frac{5617}{180}\frac{37}8+\frac{482}{225}.
\]

The template's guards are

\[
0\le\delta\le\delta_{\max}=\frac1{4625},\qquad
0\le e\le\frac1{10000}.
\tag{L6}
\]

The first guard ensures37delta/8<=1/1000 and also delta<=1/18.
These restrictions describe this sufficient proof template. They do
not assert that a larger neighborhood cannot satisfy a better theorem.

The conversion from reserve to target decrement still uses the uniform
comparison-denominator upper bound5/9. Thus a reserve R permits
decrement9R/5 with a nonnegative final signed margin, or any strictly
smaller decrement with a strictly positive final signed margin. The
half-reserve convention uses9R/10.

## Exact reduction of the optimization to one scalar crossing

Suppose a positive reserve R is feasible in (L5). Its first two entries
force

\[
\delta\ge R/\gamma,\qquad
e\ge R/a+c\delta\ge
\left(c+\frac\gamma a\right)\frac R\gamma.
\]

Write k=c+gamma/a. The local gain in the third entry decreases as either
delta or e increases. Therefore every feasible R must satisfy

\[
R\le\beta\left[g_0-(A+530k)\frac R\gamma
-R_3(kR/\gamma)-R_5(kR/\gamma)\right].
\tag{L7}
\]

Equivalently, with x=R/gamma, define

\[
f(x)=\beta[g_0-(A+530k)x-R_3(kx)-R_5(kx)]-\gamma x.
\]

The tail functions are continuous and nondecreasing, and A,530k,gamma
are positive. Hence f is continuous and strictly decreasing. It has
at most one zero. If a positive zero x_* obeys both guards in (L6),
then delta=x_* and e=kx_* give

\[
\gamma\delta=a(e-c\delta)
=\beta[g_0-A\delta-530e-R_3(e)-R_5(e)].
\]

Thus all three reserves agree there, and gamma x_* is the exact global
maximum of (L5). This proves both the upper bound and its attainability
within the scalar certificate template.

For both A choices, the crossing lies in the geometric piece whose
entrances are7 for R3 and6 for R5. On that entire piece,

\[
R_3(e)=16e+\frac1{29160},\qquad
R_5(e)=4e+\frac1{140625}.
\]

Consequently, with t=1/29160+1/140625,

\[
x_*=
\frac{\beta(g_0-t)}{\gamma+\beta(A+550k)}.
\tag{L8}
\]

The checker evaluates (L8) as an exact fraction and verifies its tail
entrance inequalities, both guards, and equality of all three reserves.
No approximate root finder is part of the certificate.

| Error coefficients | Optimal delta | Optimal epsilon | Maximum reserve | Maximum decrement |
| --- | ---: | ---: | ---: | ---: |
| Rounded32 and5/2 | 0.000138781274739 | 0.0000124561669813 | 0.00000651591071347 | 0.0000117286392842 |
| Exact5617/180 and482/225 | 0.000141630191310 | 0.0000127118684843 | 0.00000664967001237 | 0.0000119694060223 |

All table decimals abbreviate exact rational certificate fields. The
maximum-decrement column uses the full reserve; halve it to retain
half the signed margin. The inherited fallback and sign margins are
much larger than these changes and do not limit this scalar optimum.

## A ceiling independent of local constant improvements

Even an unlimited local identity gain cannot exceed the first entry of
(L5). Under the same radius guard and denominator upper bound,

\[
\text{decrement}\le
\frac95\gamma\delta_{\max}
=0.0000182727966159477\ldots<0.00002.
\tag{L9}
\]

This explains the diminishing gain from constant tuning: the outside
certificate reserve and the guaranteed neighborhood size impose their
own ceiling. Increasing only the face gain cannot remove it.

Profile75 gives the stronger exact-face cap1151/1800 and identity gain
649/12150. That endpoint result is not an input to the first optimum
above, which belongs specifically to the stated profile73 neighborhood
estimates. A quantitative neighborhood theorem for the stronger cap
would be a separate input. Even if its local gain were arbitrarily
large, retaining the same radius guard and outside estimate would still
impose the independent ceiling (L9).

The next useful target must change one of those premises. Candidates
include a uniform actual-source inequality on a substantially larger
region, additional joint observations that strengthen the old source
comparison throughout its domain, or an exact outside estimate that
retains more of the signed table than its single minimum gamma. A
larger isolated endpoint improvement does not by itself provide any of
these ingredients. In particular, a scalar denominator gain must hold
for the same actual family and throughout the relevant region before
being used in a global quotient.

This result rules out spending further effort on small variations of
(L5) as a route to closing the current terminal gap above106. It does
not rule out anisotropic neighborhoods, stronger global tables, new
actual-source feasibility constraints, other live costs, or a different
comparison. No percentage of the unrestricted proof is inferred from
this numerical ceiling, and no Lean claim is made.

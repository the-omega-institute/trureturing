[Index](../../../marked_head_profile.md) · [Fixed lower selector](864-complete-color-covers-and-phase-product-obstruction.md#a-fixed-two-owner-cofactor-selector-on-the-entire-actual-source) · [Parent deletion liability](865-whole-component-digit-stripping-and-shared-parent-repairs.md)

# Fractional fresh-prefix transport on the complete residual

Keep the conditional branch of Report864 PC65--PC68: a globally
count-minimal, then modulus-sum-minimal distinct odd whole cover,
ternary height two, q=113 of height one, and period Q=9qW with
(W,3q)=1. There are at most 27 cofactor primes, with the exponent
envelope stated there. All classes retain their literal original
phases. This does not establish that every hypothetical odd cover
has these additional properties.

Let D consist of all q-bearing originals, F0 of all q-free originals,
and E0 be the exact complement of F0 on the full 9W carrier. Let U
be the at least 110 colors excluding the colors of q,3q,9q. Take S
to be all U-colored lower owners, with original labels

$$
d_i=q3^{a_i}m_i,\qquad a_i\in\{0,1\},\quad m_i>1.
\tag{FP1}
$$

PC65 supplies at least 32 distinct serving colors, hence at least
32 incident owners of S, at every point of E0. For each m there are
at most two owners; a pair consists of the labels qm and 3qm.
PC21 gives at least 105 top originals on each of the five safe
words modulo nine, so at least 525 distinct originals of D lie
outside S. These are statements about this one common source.

The constructions below retain every member of F0 and therefore
have no deleted-parent liability. The lower selector gives load
at least 16/9. Using all three original rows strengthens this to
1430/243 on the complete lifted residual. Neither fractional
assignment yet supplies an integral covering family.

## Candidate outputs and their capacities

Normalize the retained pure guards to 0 modulo three and 1 modulo
nine by the common integer affine bijection used in Report865.
Let Omega={2,4,5,7,8} be the safe old words. Owner i has a literal
ternary phase u_i modulo 3^{a_i} and a literal cofactor phase b_i
modulo m_i. Its allowed old-word set is

$$
T_i=\{z\in\Omega:z\equiv u_i\pmod{3^{a_i}}\},
\qquad t_i=|T_i|.
\tag{FP2}
$$

A row-zero owner has t_i=5. A row-one owner cannot share the pure
three guard's phase, by comparable-original disjointness; its
t_i is two or three. For k=3,4 and r modulo 3^k with r mod9 in T_i,
allow the single CRT class

$$
B_{i,k,r}:\quad x\equiv r\pmod{3^k},\qquad
x\equiv b_i\pmod{m_i}.
\tag{FP3}
$$

There are 3t_i candidates at depth three and 9t_i at depth four.
Work on the entire lifted residual

$$
\widehat E_0=\{(\tau,w)\in\mathbb Z/81\mathbb Z
 \times\mathbb Z/W\mathbb Z:(\tau\bmod9,w)\in E_0\}.
\tag{FP4}
$$

Let A be its candidate incidence matrix. Resource constraints B
allow at most one chosen output per source i and at most one per
numerical label 3^k m. These restrictions are on fixed APs, not
choices made separately at each target point.

Within the one-output-per-owner, same-cofactor interface, depths
three and four suffice whenever any finite heights suffice. At a
singleton cofactor, shorten its one prefix to depth three. For two
outputs with that cofactor, their depths differ; shorten the
shallower one to three and the deeper one to four. If only one is
used, shorten it to three. Prefix truncation enlarges every class,
preserves the old word and cofactor phase, and keeps numerical
labels distinct and fresh. It increases neither count nor cost.
This reduction does not apply to an interface allowing arbitrarily
many outputs with one cofactor.

## An explicit feasible fractional assignment

For a singleton cofactor, use depth three and choose uniformly
among its 3t_i phases. For a paired cofactor, couple the depths:

| Probability | Row-zero owner | Row-one owner |
| --- | --- | --- |
| 3/4 | depth three | depth four |
| 1/4 | depth four | depth three |

Conditional on a depth, each owner's phase is uniform on its own
allowed candidates. Every configuration has one output per source
and exactly one use of each numerical label 27m,81m in a pair.
Thus its expected incidence vector x satisfies x>=0 and Bx<=1.

At a point whose old projection is incident with the owner, the
expected contribution is

$$
\begin{array}{ll}
\text{paired row zero:}&(3/4)/15+(1/4)/45=1/18,\\
\text{paired row one:}&(1/4)/(3t_i)+(3/4)/(9t_i)
 =1/(6t_i)\ge1/18,\\
\text{singleton:}&1/(3t_i)\ge1/15.
\end{array}
\tag{FP5}
$$

Nonincident owners contribute zero. Consequently the actual
32-owner multiplicity gives

$$
\boxed{x\ge0,\quad Bx\le\mathbf1,\quad
 Ax\ge\frac{16}{9}\mathbf1.}
\tag{FP6}
$$

Restricting instead to the C-star selector of PC68 gives the weaker
load 27/18=3/2. No independence of original cofactor phases was
assumed: these are fixed phases, and the auxiliary random choices
are only the permitted new ternary prefixes.

The pair can be balanced more accurately when its row-one width
is two. If theta is the probability that its row-zero owner uses
depth three, the two per-owner loads are

$$
\frac{1+2\theta}{45},\qquad
\frac{3-2\theta}{9t}.
\tag{FP7}
$$

Their minimum is largest at

$$
\theta=\frac{15-t}{2(5+t)},\qquad
c_t=\frac4{9(5+t)}.
\tag{FP8}
$$

For t=2 this is theta=13/14 and c_t=4/63; for t=3 it is
theta=3/4 and c_t=1/18. This is also the best uniform lower
guarantee on all allowed, source-indexed ternary positions for
this two-output interface. At period 81 the two sources have
45+9t such positions. One depth-three output covers three of
its source's positions, and the depth-four output covers one.
Thus their total is four in every configuration, and the minimum
marginal cannot exceed 4/(45+9t). The argument does not bound
strategies tailored to a smaller actual mask or to cofactor changes.

## A genuine integral plan has a complete paid consumer

Suppose the same actual incidence problem has

$$
y\in\{0,1\}^J,\qquad By\le\mathbf1,\qquad Ay\ge\mathbf1.
\tag{FP9}
$$

Delete D, keep F0 and insert the selected outputs. An integer
already covered by F0 is retained. Every other integer projects
into E0 and hence, modulo 81W, into FP4; FP9 covers it. The q
coordinate is free, so this argument covers every integer lift.

The new moduli are distinct odd nonunits. Their ternary heights
are three or four, so none collides with a retained original.
There are at most |S| outputs, whereas

$$
|D|\ge |S|+525.
\tag{FP10}
$$

Thus this would strictly decrease the original count. Independently,
the new modulus sum is at most 81 sum_i m_i, which is strictly
less than 113 sum_i 3^{a_i}m_i and hence less than the deleted sum.
E0 is nonempty, so the selector S is nonempty for this strict
comparison. The count decrease already suffices.

FP6 proves fractional feasibility, not FP9. A common point can
have high expected covering multiplicity while every single
configuration misses some other point. PC69--PC75 gives a concrete
prescribed-mask obstruction to this restricted integral interface;
it is not an instance satisfying all the actual whole-cover premises.

## Coupling without overlap and a precise probabilistic obligation

The pair's old-word choices can have uniform marginals while always
being different. Write T for the row-one allowed set, |T|=t. For
z0 in Omega and z1 in T, give their pair mass

$$
\begin{cases}
0,&z0=z1,\\
1/[5(t-1)],&z0\in T,\ z0\ne z1,\\
1/(5t),&z0\notin T.
\end{cases}
\tag{FP11}
$$

The row-zero marginal is 1/5 and the row-one marginal is 1/t.
Choose the depth permutation as above, then choose each prefix's
remaining digits uniformly within its selected old word. This
preserves FP5 or FP8 and makes the pair's output cylinders disjoint.

Choose different cofactor groups independently. At a fixed actual
point v, let c_i be the marginal of each incident owner, and let
I_v be its incident cofactor groups. Its exact miss probability is

$$
p_v=\prod_{g\in I_v}
 \left(1-\sum_{i\in g\text{ incident at }v}c_i\right)
 \le(17/18)^{\delta(v)},\qquad\delta(v)\ge32.
\tag{FP12}
$$

Disjoint paired cylinders justify the sum within a group; independence
is used only between the constructed auxiliary group choices. The
inequality uses c_i>=1/18 and 1-a-b<=(1-a)(1-b) for nonnegative
a,b. It does not replace the original source by independent phases.

One may identify target points having the same full candidate
incidence row. If there are n remaining rows and
n(17/18)^32<1, the union bound supplies FP9. For example n<=6
suffices; there is no bound of six on the actual rows here.
Alternatively join two target events when their I_v intersect.
If this dependency graph has maximum degree d and

$$
\mathrm e(d+1)(17/18)^{32}\le1,
\tag{FP13}
$$

the symmetric Lovasz local lemma supplies FP9. This directly
reuses Lemma8 of Bollobas--Pritchard--Rothvoss--Scott,
[arXiv:1009.6144v3](https://arxiv.org/abs/1009.6144v3).
No bound satisfying FP13 has been derived for the actual source.

Their Proposition9 concerns minimum incidence degree delta and
maximum hyperedge cardinality R, giving
floor(delta/log(e R delta^2)) disjoint covers. In the old-owner
hypergraph, R counts residual points in an owner, not the number
of owners with one cofactor. The capacity two in FP1 therefore
does not instantiate rank two, and fractional load 16/9 is not
that theorem's integer minimum degree. Source and numerical-label
capacities must also survive a proposed application. Their
Theorem7 shows that bounded primal and dual VC dimension alone
does not supply a general cover decomposition.

## All three rows give load 1430/243

Let S-plus contain all originals of colors in U, including tops.
Every color covers the same E0, so at least 110 owners of S-plus
are incident at every residual point. A numerical cofactor m has
at most three such owners, from its actual labels qm,3qm,9qm.
The three old-word widths are 5,t,1 with t=2 or 3. All phases
remain the literal phases of these original owners.

For a group of g owners permit distinct depths from 3,...,g+2.
At g=1 use depth three. At g=2, a row-zero/row-one pair uses FP5
or FP8. A row-zero/top pair uses depths three/four respectively,
giving rates 1/15 and 1/9. A row-one/top pair uses depths
three/four respectively, giving rates at least 1/9 each.

For g=3 and t=3, use this probability distribution on depth
permutations:

| Probability | Row zero | Row one | Top |
| --- | --- | --- | --- |
| 13/27 | 3 | 4 | 5 |
| 8/27 | 4 | 3 | 5 |
| 6/27 | 3 | 5 | 4 |

Conditional on its depth, each owner's phase is uniform on its
allowed prefixes. The rates at an incident point are

$$
\begin{aligned}
c_0&=(19/27)/15+(8/27)/45=13/243,\\
c_1&=(8/27)/9+(13/27)/27+(6/27)/81=13/243,\\
c_2&=(6/27)/9+(21/27)/27=13/243.
\end{aligned}
\tag{FP14}
$$

The same distribution gives at least these rates when t=2.
Optimally balancing that case instead uses the same three
permutations with probabilities 13/24,7/48,5/16. Each owner's
rate is then 13/216. These balances attain the uniform marginal
upper bound for this interface: at period 243 the three sources
have 135,27t,27 allowed positions, and the three outputs cover
a total of 9+3+1=13 source-indexed positions. Therefore the
smallest marginal cannot exceed

$$
\frac{13}{27(6+t)}.
\tag{FP15}
$$

Every group size and row pattern now gives at least 13/243 per
incident owner. On the whole residual lifted to 243W this yields
the explicit feasible system

$$
\boxed{x^+\ge0,\quad B^+x^+\le\mathbf1,\quad
 A^+x^+\ge\frac{1430}{243}\mathbf1.}
\tag{FP16}
$$

Here the matrices use the group-dependent palette 3,...,g+2,
with the same source and numerical-label constraints as before.
The claim includes all common cofactor coordinates and all
integer lifts. No different phase is chosen at different targets.

An integral solution of these inequalities with coverage right
side one would again retain F0 and cover every integer. Its
output count is at most |S-plus|. Divisor closure supplies the
actual originals q,3q,9q, and their colors were excluded from U;
therefore

$$
|S\text{-plus}|\le |D|-3.
\tag{FP17}
$$

Thus even this larger selector still has a strict count saving.
There is also a direct cost bound by cofactor groups. Their
maximum total output labels are 27m,108m,351m for sizes one,
two,three. Their original label sums are at least
113m,113(1+3)m,113(1+3+9)m respectively, all strictly larger.
Restricting the candidate palette by group size matters for this
cost statement; a singleton is not granted an arbitrary depth-five
output in that comparison.

The finite depth restriction loses nothing within the same
one-output-per-owner interface. For any fixed cofactor, sort its
used depths and truncate them to 3,4,5 in that order, stopping
after its actual number of outputs. Each class expands and all
output labels remain distinct. This is independent of how the
original row labels are assigned to those depths.

## One fresh digit couples all group outputs without overlap

The three-row assignment also admits disjoint outputs within each
cofactor group. Choose the owners' allowed old words uniformly,
choose the depth permutation by the relevant table, and independently
choose a uniform injection of the g owners into {0,1,2}. Write
c_i for the assigned fresh digit. At depth k_i use the prefix

$$
r_i=z_i+9c_i+27h_i,\qquad
0\le h_i<3^{k_i-3},
\tag{FP18}
$$

with h_i uniform. Each c_i has uniform marginal, so every allowed
prefix of its owner still has the required uniform marginal.
Two different owners have different c_i; since 0<=z_i<9, their
prefixes differ modulo 27 even if the old words coincide. Their
entire output cylinders are disjoint. This also gives an
alternative to FP11 for a two-owner group.

Choose the groups independently. The same product argument as
FP12, now using at least 110 incident owners, gives

$$
p_v\le(1-13/243)^{110}=(230/243)^{110}.
\tag{FP19}
$$

This auxiliary miss bound is approximately 0.0023625003. Exact
rational inequalities give

$$
423(230/243)^{110}<1\le424(230/243)^{110}.
\tag{FP20}
$$

Consequently at most 423 distinct full candidate-incidence rows
would suffice by the union bound. More generally a dependency
degree d satisfying

$$
\mathrm e(d+1)(230/243)^{110}\le1
\tag{FP21}
$$

would suffice by the same local lemma. Neither a 423-row bound nor
FP21 is established for the actual residual. Shared primes across
different cofactors do not invalidate the auxiliary independence:
the source is fixed while their new prefix choices are independent.
They also do not prove a small dependency degree between different
target events.

## Remaining arithmetic work and verification boundary

One sufficient next bridge is integral feasibility for FP16 with
coverage right side one, using the actual residual identity,
complete original colors and private points. The lower-only
alternative FP9 leaves at least 525 deleted top labels available
for extra outputs or changes of cofactor; the all-row alternative
uses those top owners explicitly. Neither interface describes
every possible improving exchange.

Extra same-cofactor depths do not give unrestricted repetition of
an independent trial. Each numerical depth label is available
only once. Its ternary mass is geometrically decreasing. For
source-attributed uniform marginal guarantees in a paired group,
even all depths k>=3 have total old-word-normalized capacity
sum_k 3^{2-k}=1/2. The resulting common guarantee is at most
1/[2(5+t)], namely 1/16 when t=3. For all three rows the
corresponding denominator is 2(6+t), giving 1/18 when t=3.
These bounds concern source-attributed uniform guarantees, not
instance-aware repair on the actual E0.

Scoped Lean applications check the exact prefix-weight tables on
the full period 81, their source and depth capacities, the coupling
marginals and zero diagonal, both optimal scalar balances, the
finite-sum consequence 32/18=16/9, prefix truncation and the count
and cost inequalities. Further scoped applications check the
three depth permutations, both triple balances, their local upper
bounds, the 110-owner finite-sum consequence, fresh-digit separation,
the three group costs and FP20. They reuse finite counting,
congruence monotonicity and rational arithmetic; these are transient
checks, not new canonical wrapper theorems. The conversion from
the actual whole-cover branch to those inputs and the probabilistic
construction above are the explicit ordinary arguments here.
Neither integral feasibility nor an unrestricted covering
contradiction is asserted to be proved.

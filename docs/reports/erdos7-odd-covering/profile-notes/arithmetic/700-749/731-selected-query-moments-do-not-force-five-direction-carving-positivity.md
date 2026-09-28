# Selected query moments do not force five-direction carving positivity

The separate moment bounds used by [Report730](730-one-common-shallow-source-supports-four-arbitrary-fresh-prime-heights.md), even together with one common law and exact finite-height padding, do not by themselves force the same carving lower bound to be positive on five new prime directions. An exact five-atom model satisfies stronger first, second and third moment bounds for every selected formal query and has zero clipped response everywhere.

This is a counterexample to a specified numerical relaxation. The formal queries are not realized as actual congruence incidence on the established old survivor source. In particular, bounds on its selected fields are not bounds on **every** complete numerical-divisor query. It neither gives an odd covering nor contradicts the four-direction theorem.

## The numerical response and the omitted condition

For distinct new primes $q_i$, put $r_i=q_i-1$. The general finite-support carving estimate in [Report728](728-one-common-shallow-source-supports-three-arbitrary-fresh-prime-heights.md) uses fields $C_J\ge1$, indexed by nonempty supports, and

$$
 u_i=(r_i-C_{\{i\}})_+,\qquad P=\prod_i u_i,\qquad
 F=\sum_{|J|\ge2}C_J\prod_{i\notin J}u_i,\qquad W=(P-F)_+.
 \tag{FM1}
$$

For actual original phases, the fibre survivor mass is bounded below by $W/\prod_i r_i$. This estimate remains true when $W=0$. The statement tested here is the additional claim that the selected-field moment ceilings and padding identities alone imply $\mathbb EW>0$.

The certified old-source bounds are

$$
 G_2=\frac{2607189975}{7283281},\qquad
 G_3=\frac{906617738995}{159166336}.
 \tag{FM2}
$$

In the actual theorem they hold for every complete query obtained by choosing one residue for each old numerical divisor. The relaxation keeps bounds only for the fields named in the construction. It discards the incidence dictionary and its closure under independent recombination of numerical-divisor slots.

## Five atoms and every finite exponent slot

Take $I=\{0,1,2,3,4\}$, new primes $(29,31,37,41,43)$, and one probability law

$$
 (p_0,p_1,p_2,p_3,p_4)
 =\frac1{100000}(34625,28046,15971,11494,9864).
 \tag{FM3}
$$

Set $B=5680<G_3$. For each nonempty $J\subseteq I$, define

$$
 p(J)=\sum_{i\in J}p_i,\qquad
 v_J=\frac{\left\lfloor1000(1+(B-1)/p(J))^{1/3}\right\rfloor}{1000},
 \qquad
 L_J(i)=\begin{cases}v_J&i\in J,\\1&i\notin J.\end{cases}
 \tag{FM4}
$$

These are rational-valued formal loads on the same five-atom space. Downward rounding, evaluated by exact integer cube comparisons, gives

$$
 \mathbb E L_J^3=1-p(J)+p(J)v_J^3\le B.
 \tag{FM5}
$$

Use this same $L_J$ for every exponent tuple in $\{1,2\}^J$. The assignment of a field to a tuple is fixed across all source atoms. The complete finite geometric weight and its constant-one padding are

$$
 t_J=\sum_{\mathbf e\in\{1,2\}^J}\prod_{j\in J}\frac{q_j-1}{q_j^{e_j}}
     =\prod_{j\in J}(1-q_j^{-2}),\qquad
 C_J=1+(L_J-1)t_J.
 \tag{FM6}
$$

There are 31 support fields and $3^5-1=242$ exponent slots. All are retained. Since $1\le C_J\le L_J$, and since $B<18^3$ and $B^2<320^3$, both the underlying symbols and padded fields satisfy

$$
 \mathbb E C_J<18,\quad \mathbb E C_J^2<320<G_2,\quad
 \mathbb E C_J^3\le5680<G_3,
 \tag{FM7}
$$

with the same inequalities for $L_J$. The exact consumer also checks these moments individually.

Every unary factor $u_i$ is strictly positive at every atom. Direct rational evaluation of FM1 gives $F(i)>P(i)$ for all five atoms, with

$$
 \min_i\frac{F(i)}{P(i)}
 =\frac{122185235033456772894749}{121954252494589465783560}>1.
 \tag{FM8}
$$

Thus $W(i)=0$ everywhere and $\mathbb EW=0$. This is an exact feasible zero-objective witness for the stated relaxation, so no sound inequality using only those retained conditions can force a positive objective. Replacing the rational probabilities by 100000 equiprobable copies leaves the example unchanged; uniformity alone does not restore actual congruence incidence.

## A seven-direction comparison with integer symbols

To separate the rational-load omission from the complete-query omission, take a singleton abstract source, primes $(29,31,37,41,43,47,53)$, and assign every selected query symbol the integer 17. Use the same height-two formula:

$$
 C_J=1+16\prod_{j\in J}(1-q_j^{-2}).
 \tag{FM9}
$$

There are 127 support fields and 2186 exponent slots. Each unpadded query has moments $(17,289,4913)$, already below the stated ceilings; padding lowers them. Every unary factor is positive. If $t_i=1-q_i^{-2}$, expansion of finite products gives an independent expression for the mixed fee:

$$
 F=\prod_i(u_i+1)+16\prod_i(u_i+t_i)-17P
      -\sum_i(1+16t_i)\frac P{u_i}.
 \tag{FM10}
$$

Both this expression and direct support enumeration give

$$
 \frac FP=\frac{185899170306847704706627330172}
                   {179895021493724830240504479897}>1.
 \tag{FM11}
$$

Again $W=0$, at the finite height two. Integer symbols alone do not repair the omitted query family. The actual old core $315\cdot11\cdot13\cdot17\cdot19\cdot23$ has 384 numerical divisor slots including the unit. On any actual singleton old state, choosing that state's own residue in every slot produces a complete query of load 384. Its cube exceeds $G_3$. The formal declaration of only load-17 symbols has omitted this legal query.

## A fourth moment is an additional condition

The example concerns the first three moments only. The increasing-convex comparator and the general moment transport in Report728 TC4--TC5 also give, on the same actual old source,

$$
 G_4=\mathbb EX^4\,
       \prod_{p\in\{11,13,17,19,23\}}\left(1+\frac{15}{p-1}\right)
       \bigg/\frac{1243487}{13077504}
     =\frac{3350218780205}{16165331}.
 \tag{FM12}
$$

Here $X$ is the already established eight-atom comparator, not a newly chosen source. At least one underlying query in FM4 has fourth moment greater than $G_4$. Thus the actual fourth-moment bound rejects this particular table. This does not establish positivity for every table satisfying the strengthened constraints. It distinguishes a new constraint from merely changing the weights assigned to the already insufficient first three moments.

## Consequence and remaining obligation

The examples preserve one source, every selected finite exponent slot, constant-one padding, and simultaneous first-three-moment bounds. They do not preserve the actual complete query dictionary. Possible additional inputs include higher moments, joint incidence and allowed recombinations; a different survivor source or a stronger lower-bound method is another route. No necessity or sufficiency claim about a particular repair is made.

Even a realizable instance with $W=0$ would only make this lower bound inconclusive. Here realizability is not supplied at all. Unrestricted prime support, unrestricted old heights and unrestricted Erdős #7 remain open.

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_selected_moment_obstruction.py) reconstructs both examples, every moment, every finite geometric sum and both seven-direction fee expressions. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_selected_moment_obstruction.json) contains the support data and exact per-atom margins. A separate implementation reconstructed the five-atom witness using direct exponent sums. These are ordinary proofs and exact finite checks, not new Lean verification.

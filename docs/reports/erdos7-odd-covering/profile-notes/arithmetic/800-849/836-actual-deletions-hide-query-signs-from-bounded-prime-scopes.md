# Actual deletions can hide opposite query signs from every scope missing a designated prime

Fix any nonnegative rational coefficient $\tau<12$. There are arbitrarily large finite sets of odd primes for which two actual distinct-modulus deletion families, on one declared weighted prior, have the following properties simultaneously:

- They use the same numerical original labels; every original has the same mass in either family, and all intersections between distinct originals are empty.
- Their surviving measures have equal total mass and equal joint marginals on every coordinate scope missing at least one designated prime.
- For one common finite inventory of globally phased numerical queries, both maximum hinge and maximum fourth moment can be calculated exactly, and the joint numerator $12\alpha-H^*-\tau K^*$ has opposite signs.

The query inventory below is a declared finite set, not every divisor of the ambient period. The opposite signs are asserted for that inventory. They are not asserted for its complete-divisor or all-height enlargement, or for the C/phase31 source of Reports 834–835. The example constrains which observations can determine a queried survivor criterion; it does not settle Erdős #7 or prove that every useful upper estimate must reconstruct a full joint table. The proof is ordinary mathematics, without a Lean claim.

## Relation to existing results

[Report 701](../700-749/701-equal-joined-boundaries-can-have-different-remaining-costs.md) already separates pair marginals using a three-axis parity retention on the fixed actual109 source. It also separates a shallow joint law from a deeper response. [Report 752](../750-799/752-joint-deletion-credit-distinguishes-equal-marginal-sources.md) already gives two actual deletion families with identical conditional singleton marginals and opposite marked-source certificate signs. The parity identity and the warning about optimizer switching are therefore reused.

Neither cited statement directly specializes to the assertion here: Report 701 changes retention fields and a screen cost, while Report 752 treats a fixed two-axis correlation and the sum of cylinder maxima. The additional construction here makes the ambiguity persist through *every scope missing at least one designated cube axis, with arbitrarily many such axes*, realizes each alternative by distinct odd original classes on the same prior, and proves both global phase maxima for the hinge-plus-fourth criterion. The parity mechanism and the convex maximum argument are standard; the assertion combines them with a literal original-family realization and both queried costs. No external originality is claimed.

## One prior and two literal original families

Put $Q=29^4$ and define

$$
A=12-\tau,
\qquad B=13+(Q-1)\tau,
\qquad C=1+Q\tau=B-A.
$$

Choose $k\ge2$, write $n=2^{k-1}$, and require

$$
An>B/2+C.
$$

Since $A>0$, arbitrarily large $k$ satisfy this. Set

$$
b=\frac{An-B/2}{C}>1.
$$

Choose distinct odd primes $p_1,\ldots,p_k,r,q$, let $M=\prod_i p_i$, and use the single carrier

$$
\Omega=\mathbb Z/(M r^n q^{28})\mathbb Z.
$$

For every $v\in\{0,1\}^k$, let $x_v$ be the CRT point with residues $v_i$ modulo $p_i$, zero modulo $r^n$, and zero modulo $q^{28}$. Give it mass one. Give one additional point $z$ mass $b$, where $z$ has cube vector zero, residue one modulo $r^n$, and zero modulo $q^{28}$. This defines one prior $\nu$ of mass $2n+b$. Dividing all masses by $2n+b$ gives a common probability if desired.

Let $E,O$ be the even and odd parity vectors, each of cardinality $n$. Enumerate either set in a fixed order. The original at index $j=1,\ldots,n$ has modulus $M r^j$; its phase has cube residue equal to the indexed vector and residue zero modulo $r^j$. Let $D_E$ and $D_O$ denote the corresponding actual unions.

The numerical labels are the same in both families, are odd nonunits, and are pairwise distinct. Within a family, two original classes have incompatible residues modulo $M$, so their entire classes are disjoint, not only their intersections with the prior. Each has a private point $x_v$, prior mass one, and removes exactly that cube point. The background point $z$ survives because its $r$-residue is one. The $r$-coordinate is essential to this separation.

Consequently both surviving measures have mass

$$
\alpha=n+b.
$$

Their labelled original masses and every unweighted original intersection agree. Their literal phases differ between scenarios; each phase is fixed globally within its scenario. The observation being tested does not retain those full phases together with each query incidence.

## Equality of the observed marginals

For a proper subset $J\subsetneq\{1,\ldots,k\}$, either parity class has exactly

$$
2^{k-|J|-1}
$$

extensions of every prescribed binary word on $J$. The retained cube points have the same fixed $r$- and $q$-coordinates, and the common background is unchanged. Hence the surviving joint marginals agree on $J$ together with the complete resolving $r^n$ and $q^{28}$ coordinates. Projection gives equality on every smaller scope as well.

At the full cube scope they differ: the zero-vector cluster has surviving mass $b$ under $D_E$ and $b+1$ under $D_O$. Thus the equality holds on all proper cube scopes with either auxiliary coordinate included; it does not hold at the full cube scope. Choosing $k$ larger than any proposed fixed bound on the number of jointly observed prime axes makes that observation unable to distinguish the two survivors. This means the number of axes in one observation, not a coordinate-elimination ordering. Scopes containing all cube axes and omitting only an auxiliary axis need not agree.

## Exact global query optimization

Use precisely the query labels

$$
\mathcal L=\{1,Mq,Mq^2,\ldots,Mq^{28}\}.
$$

Each query chooses one residue globally at its own numerical label, independently of the other labels. The unit contributes one. Every nonunit query either misses the prior or hits one entire cube-vector cluster; it cannot distinguish $z$ from $x_0$, because its modulus omits $r$.

Write $w_v$ for a surviving cluster mass and $t_v$ for its number of nonunit hits. Necessarily

$$
t_v\in\{0,\ldots,28\},
\qquad \sum_v t_v\le28,
\qquad N(v)=1+t_v.
$$

For any increasing convex $\psi$ on $[1,29]$, its chord bound gives

$$
\psi(1+t)\le\psi(1)+\frac t{28}\bigl(\psi(29)-\psi(1)\bigr).
$$

Therefore

$$
\sum_v w_v\psi(1+t_v)
\le \alpha\psi(1)+\max_v w_v\bigl(\psi(29)-\psi(1)\bigr).
$$

Equality is attained by assigning all 28 phases to a cluster of maximum mass, using its cube residue and zero $q$-digits at every depth. This is one valid whole layout. No per-cell phase choice or independent maximization of tuple intersections occurs.

Because $b>1$, the largest cluster has mass $b$ under $D_E$ and $b+1$ under $D_O$. Applying the formula first to $\psi(t)=(t-16)_+$ and then to $\psi(t)=t^4$ gives the exact suprema over **all** layouts on $\mathcal L$:

$$
\begin{aligned}
H_E^*&=13b,& K_E^*&=\alpha+(Q-1)b,\\
H_O^*&=13(b+1),&K_O^*&=\alpha+(Q-1)(b+1).
\end{aligned}
$$

Both maxima are proved separately; an assumption that an old maximizer remains optimal is unnecessary. In this construction the maximum cluster also attains both costs, consistently with the mixed-fourth reduction in Report 818.

The two joint numerators are now

$$
\begin{aligned}
12\alpha-H_E^*-\tau K_E^*&=An-Cb=B/2>0,\\
12\alpha-H_O^*-\tau K_O^*&=An-Cb-B=-B/2<0.
\end{aligned}
$$

For $\tau=0$, one may take $b=12n-13/2$, and the numerators are $\pm13/2$. Normalizing the one prior divides both by $2n+b$ and preserves their signs.

## Consequence for the next Erdős #7 method

The relevant restriction is not the parity construction alone. It is that *one numerical query label can involve arbitrarily many prime coordinates*. Four factors in a fourth moment do not impose a four-coordinate limit: even the diagonal tuple $(d,d,d,d)$ has the entire prime support of $d$. An observation restricted to a fixed number of jointly read prime axes, supplemented by exact retention and unweighted original-overlap data, therefore cannot determine all permissible queried survivor costs uniformly over support size.

This directs the next method toward scopes required by the actual original/query incidences, or certified inequalities on those scopes. It does not require every full survivor cell. Report 752's scope-union update, Report 562's weighted Gram certificate and Report 13's common signed-payoff cap remain possible tools. Selected-original nullities have zero mass under the present retained source and cannot alone produce new deletion credit.

For the current C/phase31 problem, a positive sufficient relation still needs quantitative information about one actual unresolved-original family and its intersection with dangerous whole query layouts, or a stronger same-source survivor mass estimate. This report supplies no such positive quantitative premise. Its role is to reject a specific information-losing replacement before another optimization campaign is started.

## Exact sparse controls

[actual_deletion_scope_counterexample.py](../../../frontier/cover-geometry/coherent-query-moments/actual_deletion_scope_counterexample.py) specifies the fixed control with cube primes 3 and 5, original tag prime 7 and query tag prime 11. It uses only five source points, two declared rational values of $\tau$, the convex chord bounds and literal attaining phases. It does not enumerate the CRT carrier or the product of phase choices. Its failure controls distinguish the background tag, numerical-label distinctness, one global query phase, the unit term, optimizer switching, full versus proper cube scopes, and query-tuple order versus prime support.

The saved result is [actual_deletion_scope_counterexample.json](../../../frontier/cover-geometry/coherent-query-moments/actual_deletion_scope_counterexample.json). Normal execution compares the complete deterministic result; `--write-result --result <new-path>` writes a new result and refuses overwrite. All checks remain active under `-O`. The exact replay passes 1,765 checks and rejects all seven declared failure controls. Independent reconstruction passes 325 grouped checks, including the literal CRT points, all twelve allowed coordinate scopes, both rational coefficients, both phase maxima and the two opposite signs; its 36 comparisons against the saved data agree. The finite controls supplement the ordinary parameterized proof; they do not replace its arbitrary-$k$ argument.

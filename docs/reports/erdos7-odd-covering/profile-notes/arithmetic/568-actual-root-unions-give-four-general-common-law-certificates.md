# Actual root unions give four general common-law certificates

Let `Q={5,7,11,13,17,19}`. Consider any finite family of nonunit Q-smooth original congruences with at most two originals at each full numerical modulus. Every original phase is fixed globally. Use the actual PA law in the fixed order `5,7,11,13,17,19`, with the ordinary caps

\[
(C_{11},C_{13},C_{17},C_{19})=(5/3,3/2,2,9/5).
\]

No prescribed old5/7 comb, first11 table, old projection, or original height is assumed.

For a later prime `q`, write each original assigned to that stage as `m_i=d_i q^{e_i}`, with `e_i>=1` and `d_i` supported on the preceding primes. On an actual old history `h`, define

\[
K_q(h)=\{a_i\bmod q:\ i\text{ is assigned to }q,
\ h\equiv a_i\pmod{d_i}\},\qquad
\kappa_q(h)=|K_q(h)|.
\]

All original heights participate. Pure-q originals have `d_i=1` and therefore participate at every history. Equal current roots are merged before taking the cardinality, even if their full original labels differ. Let `lambda_<q` be this same actual PA prefix law, without intermediate normalization.

Each row below is independently sufficient for a supported probability `nu` with the displayed complete-query bound:

| Actual root condition | Conditional row mass lower bound | Uniform `R_Q(nu)` upper bound |
|---|---|---|
| `kappa11 <= 5` almost everywhere under `lambda0` | `10/11` | `29843305414000981499/6308296226065877842 = 4.730802794372346...` |
| `kappa13 <= 6` almost everywhere under `lambda11` | `21/26` | `29046887322727376699/5910087180429075442 = 4.914798451521075...` |
| `kappa17 <= 9` almost everywhere under `lambda13` | `16/17` | `30017007870751190467/6395147454440982326 = 4.693716303586789...` |
| `kappa19 <= 10` almost everywhere under `lambda17` | `81/95` | `965171944673739731/201103734397830228 = 4.799373554965438...` |

Here

\[
R_Q(\nu)=\sum_{\substack{d>1\\p\mid d\Rightarrow p\in Q}}
\max_{r\bmod d}\nu(r\bmod d).
\]

Every displayed bound is strictly below `T=257/51`. The query sum includes all numerical labels and all heights, independently of the finite original inventory. A readily checked sufficient condition is that all originals in the chosen q-row have current residues modulo q in one fixed set of at most the indicated size. Their old projections, all other rows and all finite heights are then unrestricted under the two-copy rule. The more general displayed condition allows different histories to activate different root sets; every original residue is still fixed globally. The four conditions are alternatives on the same fixed PA construction; they are not additional old-phase restrictions.

## Actual union and one-row replacement

For each fixed old history, every active original lies inside one of the root cylinders in `K_q(h)`. The actual forbidden Haar mass therefore satisfies

\[
b_q(h)\le\kappa_q(h)/q.
\]

The actual capped row has mass

\[
s_q(h)=\min(1,C_q(1-b_q(h))).
\]

Consequently, if `kappa_q<=K`,

\[
s_q(h)\ge r_{q,K}:=\min(1,C_q(1-K/q)).
\]

This is an estimate for the union of actual current roots. It never interprets a count overload as an attained union loss, never averages separately clipped slot queries, and assumes no independence of actual prefix coordinates.

Let `x,y` be the actual pure5 and pure7 surviving Haar masses and `m` the actual mixed5/7 forbidden mass inside their product. The two-copy bounds give

\[
\tfrac12\le x\le1,\qquad\tfrac23\le y\le1,
\quad0\le m\le\tfrac1{12},\qquad
\lambda_0(1)=xy-m.
\]

Write `F_p(x,y)` for [Report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#retaining-the-actual-pure-anchor-masses)'s complete auxiliary stage hinges, and `Phi(x,y)` for the final threshold-three hinge, using the same actual pure-source parameters. The standard stage charges are

\[
(a_{11},a_{13},a_{17},a_{19})=(1/3,1/4,1/4,1/5).
\]

Define

\[
B_q(x,y)=xy-\frac1{12}-\sum_{p<q}a_pF_p(x,y),
\]

\[
A_{q,K}(x,y)=r_{q,K}B_q(x,y)-\sum_{p>q}a_pF_p(x,y),
\]

where the sums run only over the four later primes. The existing actual PA loss bounds give `lambda_<q(1)>=B_q`. Replace only the q-row loss estimate by the actual root-mass bound, then retain the ordinary later charges. Since `r_{q,K}>=0`,

\[
\lambda_{\rm final}(1)\ge A_{q,K}(x,y).
\]

All actual kernels retain their fixed order and their original phases; only the estimate for one row is replaced. There is no intermediate renormalization or switch of actual source.

## Four corners give the complete-query bounds

The pure-coordinate auxiliary measures depend affinely on `x` and `y`, while the later comparison factors are fixed. Thus every `F_p`, `Phi`, `B_q` and `A_{q,K}` is bilinear in `x,y`. At each selected threshold in the first table, all four values of `A_{q,K}` on

\[
(x,y)\in\{1/2,1\}\times\{2/3,1\}
\]

are strictly positive. The full exact corner data are retained in the companion JSON. These are
algebraic parameter endpoints; no infinite actual original family is
introduced.

For completeness, if `w_c` are the nonnegative rectangle interpolation weights, then

\[
\frac{\Phi(x,y)}{A_{q,K}(x,y)}
=\sum_c\frac{w_c A_{q,K}(c)}{A_{q,K}(x,y)}
\frac{\Phi(c)}{A_{q,K}(c)}.
\]

The new weights sum to one, so the ratio is bounded by its largest corner ratio. In all four cases this maximum occurs at `(x,y)=(1/2,2/3)`.

The existing complete-query comparison gives, for every finite complete query `L`,

\[
\lambda_{\rm final}(L-1)\le2\lambda_{\rm final}(1)+\Phi(x,y).
\]

The positive mass bound permits one final normalization. Finite labelwise maximization and nonnegative label exhaustion then give

\[
R_Q(\nu)\le2+\frac{\Phi(x,y)}{A_{q,K}(x,y)}
\le\max_c\left(2+\frac{\Phi(c)}{A_{q,K}(c)}\right),
\]

which yields the displayed constants. The conclusion includes all query heights; the finite four-corner calculation verifies the coefficients of an exact bilinear formula, rather than extrapolating finite original families.

For this particular one-row mass lower bound, the selected thresholds `5,6,9,10` are the largest integers certified by positive corner masses and a strict corner query bound below `T`. At `K+1`, the anchor corner already has the following negative target margins `A_{q,K+1}-Phi/(T-2)`:

| `q` | Next `K` | Anchor margin |
|---|---|---|
| `11` | `6` | `-42658987505509330211/1650097635185615616000` |
| `13` | `7` | `-32770009524080383811/1650097635185615616000` |
| `17` | `10` | `-9018514746780702407/1650097635185615616000` |
| `19` | `11` | `-11806619313371117/3172044665870080000` |

Larger `K` can only decrease `r_{q,K}` and the anchor mass bound. These failures concern this certificate; they do not construct an actual family violating the target, and they do not prove the thresholds are optimal for other methods.

## Same-source integrated excess and necessary dense-root conditions

Let `K_q` denote the certified integer threshold for row `q`. For every actual root count,

\[
\ell_q(h):=1-s_q(h)
\le 1-r_{q,K_q}+\frac{C_q}{q}(\kappa_q(h)-K_q)_+.
\]

Define the actual integrated excess

\[
J_q=\int(\kappa_q(h)-K_q)_+\,d\lambda_{<q}(h).
\]

The same argument gives `lambda_final(1)>=A_{q,K_q}(x,y)-(C_q/q)J_q`. The minimum target margins over the pure-source rectangle are

| `q` | `delta_q = min(A-Phi/(T-2))` | Strict sufficient threshold `J_q < (q/C_q) delta_q` |
|---|---|---|
| `11` | `19844710796976109789/1650097635185615616000` | `19844710796976109789/250014793209941760000 = 0.07937414639425820...` |
| `13` | `7500230382235235389/1650097635185615616000` | `7500230382235235389/190395880982955648000 = 0.03939281849751078...` |
| `17` | `22537098876604348793/1650097635185615616000` | `22537098876604348793/194129133551248896000 = 0.11609333676160818...` |
| `19` | `28939888963313439/3172044665870080000` | `9646629654437813/100169831553792000 = 0.09630274409773262...` |

Each strict threshold ensures `R_Q(nu)<T`. All integrals use the corresponding actual prefix from the same original family, not an independently optimized or auxiliary source.

The actual forbidden fractions give a stronger version. Define

\[
J_q^{\rm union}=\int(qb_q(h)-K_q)_+\,d\lambda_{<q}(h)
\le J_q.
\]

The function `b -> (1-Cq+Cq*b)_+` is nondecreasing and `Cq`-Lipschitz.
Its value at `Kq/q` is `1-r_(q,Kq)`, so on the entire real interval
`0<=b<=1`,

\[
\ell_q(h)\le1-r_{q,K_q}
             +\frac{C_q}{q}(qb_q(h)-K_q)_+.
\]

Consequently every displayed integral threshold remains sufficient with
`Jq_union` in place of `Jq`. Likewise the first table's query constants
hold if the actual forbidden fraction is at most `Kq/q` almost everywhere,
even when many additional roots contain only small forbidden subsets.
This uses the complete actual unions, not the sum of individual cylinder
masses. The real-variable envelope follows from the Lipschitz argument;
the producer's finite root-count checks are not its proof.

Therefore any family for which this fixed PA law has `R_Q(nu)>=T` must violate all four sufficient thresholds, including the stronger union thresholds. In particular it must have positive actual prefix mass on root-count levels at least `6,7,10,11`, respectively. Quantitatively,

\[
\lambda_{<q}\{\kappa_q\ge K_q+1\}
\ge\frac{(q/C_q)\delta_q}{q-K_q}
\]

is necessary, since `J_q <= (q-K_q) lambda_<q{kappa_q>=K_q+1}`.
The stronger necessary condition replaces this event by `bq>Kq/q`,
because `Jq_union <= (q-Kq) lambda_<q{bq>Kq/q}`. This is also necessary for a hypothetical family whose every supported law exceeds the target, because its actual PA law is one such law. These are necessary conditions only; the actual example below meets all four fixed integral thresholds while its law remains below the target.

## Finite first13 heads with an arbitrary actual source and complement

The first13 union estimate also has a finite-label sufficient condition.
Let `W` be a finite set of full numerical labels `5^a 7^b 11^c 13^d`,
where `a,b,c>=0` and `d>=1`. Let `r_W(h)` count the distinct first13
roots of the actual active originals whose labels belong to `W`, on
the same actual old history `h`. Each original phase remains fixed
globally. There is no prescribed old5/7 or first11 source.

Each of the following conditions `r_W<=6` almost everywhere under the
actual unnormalized `lambda11` is sufficient. Every original outside
the selected head, including every later17/19 original and every higher
pure13 original, is arbitrary under the two-copy rule.

| Head | Labels in the head | Old residue cells for an everywhere check | Complete-query bound |
|---|---:|---:|---|
| `W26` below |26|`125*343*121 = 5187875`|`200081276845190515421/39747143056052967358 = 5.033853038519727...`|
| `W54: 0<=a,b,c<=2, 1<=d<=2` |54|`25*49*121 = 148225`|`28574763710209932539/5674025374170353362 = 5.036065548858791...`|
| `W72: 0<=a<=3, 0<=b,c<=2, 1<=d<=2` |72|`125*49*121 = 741125`|`28779458484115209467/5776372761122991826 = 4.982271690949556...`|

All three bounds are strictly below `257/51`. Requiring the root bound
on every indicated old residue cell is a stronger purely finite check;
the almost-everywhere condition itself refers to the actual prefix law,
whose support can depend on originals of arbitrarily large finite height.
The cell counts describe a sufficient rectangular partition, not a
proved minimal partition or the cost of constructing the actual law.

In descending order of the anchor cap charge defined below, `W26` is

```
13,65,91,143,455,325,169,715,1001,845,637,2275,1183,
1625,1573,5005,3185,3575,1859,5915,4225,2197,7865,9295,7007,4459.
```

### Complete tail charge and the same-prefix inequality

Put

\[
u_5(0)=x,\quad u_5(a)=5^{-a}\ (a>0),\qquad
u_7(0)=y,\quad u_7(b)=7^{-b}\ (b>0),
\]
\[
u_{11}(0)=1,\qquad u_{11}(c)=\tfrac53\,11^{-c}\ (c>0).
\]

For any fixed phases the actual cylinder cap is

\[
\lambda_{11}(C_{5^a7^b11^c})\le u_5(a)u_7(b)u_{11}(c).
\tag{FH1}
\]

Indeed `lambda0` is dominated by the product of the actual pure5 and
pure7 survivor restrictions. When `c=0`, the first11 kernel has fibre
mass at most one; when `c>0`, its density is at most `5/3`.
This argument does not assume independence of the actual prefix.

Define the full two-slot complement charge

\[
\Theta_W(x,y)=\frac14(x+\tfrac14)(y+\tfrac16)\frac76
-3\sum_{(a,b,c,d):\,5^a7^b11^c13^d\in W}
u_5(a)u_7(b)u_{11}(c)13^{-d}.
\tag{FH2}
\]

The factor `3` is `C13` times two original slots. The full coordinate
sums are `x+1/4`, `y+1/6`, `7/6`, and
`sum_(d>=1)13^-d=1/12`. Thus (FH2) pays every omitted numerical label,
including cofactor one, with no finite-height cutoff. For `W54`,

\[
\Theta_{54}=\frac14\left[
(x+\tfrac14)(y+\tfrac16)\frac76
-(x+\tfrac6{25})(y+\tfrac8{49})\frac{141}{121}\frac{168}{169}
\right].
\]

For `W72`, replace `x+6/25` by `x+31/125`.

Let `g_H(h)` be the allowed13 fraction using only the actual head
originals. It is at least `1-r_W(h)/13`. Adding the complement can
reduce the capped fibre mass `min(1,(3/2)g_H)` by at most `3/2` times
the added forbidden Haar fraction. Integrate this scalar Lipschitz
bound and apply (FH1) to obtain the cost (FH2). No domination of
the head-only capped density over the actual full-row density is used.

Retain the actual old mixed loss `m` and the actual first11 saving
`S11=F11/3-Loss11`. Define

\[
A_{11}=xy-\tfrac1{12}-\tfrac13F_{11},\qquad
F_{11}=x/42+y/20+59/840,\qquad
H_{11}=\tfrac1{12}-m+S_{11}\ge0.
\]

The exact prefix identity is `lambda11(1)=A11+H11`. Write

\[
E_W=\int(r_W-6)_+\,d\lambda_{11},\qquad
P_W=\int\min\{5,3(6-r_W)_+\}\,d\lambda_{11}.
\]

For each integer `0<=r<=13`,

\[
\min(1,\tfrac32(1-r/13))
=\tfrac{21}{26}-\tfrac3{26}(r-6)_+
+\tfrac1{26}\min\{5,3(6-r)_+\}.
\]

Integrating, paying the complement, and retaining the ordinary complete
later17/19 charges gives

\[
\lambda_{\rm final}(1)\ge
M_W(x,y)+\frac3{26}(7H_{11}-E_W+P_W/3),
\tag{FH3}
\]
\[
M_W=\frac{21}{26}A_{11}-\Theta_W-\frac14F_{17}-\frac15F_{19}.
\]

All terms use the same actual source and the unchanged actual PA chain.
The head-only row is an intermediate scalar estimate, not a substitute
law on which subsequent original phases are reoptimized.

### Positive margins, weighted conditions, and the limited cardinality optimum

Set `D_W=M_W-(51/155)Phi`. For each of the three heads, its expansion
in `d5=x-1/2`, `d7=y-2/3` has four strictly positive coefficients.
The exact coefficients and four corners are in the
[companion data](../../frontier/cover-geometry/pa_finite_root_heads.json).
In particular:

| Head | `min D_W` | `min (26/3)D_W` |
|---|---|---|
|`W26`|`2174129260179264907/11550683446299309312000`|`2174129260179264907/1332771166880689536000`|
|`W54`|`182314388214850909/1650097635185615616000`|`182314388214850909/190395880982955648000`|
|`W72`|`3355083383746643293/1650097635185615616000`|`3355083383746643293/190395880982955648000`|

The minima occur at the algebraic corner `(1/2,2/3)`. Under `r_W<=6`,
`E_W=0` and the other credits are nonnegative. The preceding positive
corner interpolation then bounds `2+Phi/M_W` by its anchor value,
yielding the table. More generally the same target is certified whenever

\[
E_W-P_W/3-7H_{11}<\frac{26}{3}D_W(x,y).
\tag{FH4}
\]

Consequently a family with actual final mass at most `(51/155)Phi`
must satisfy the reverse weak inequality for every displayed head,
with all quantities evaluated on its one actual prefix. These conditions
have not been proved inconsistent. Nor does failure of a lower-mass
estimate imply failure of the actual complete-query bound.

The label count26 is minimal for the specific six-root mass certificate
`M_W>=(51/155)Phi` over the full parameter rectangle, using (FH2) and
no `H11` or below-six-root credit. To check this limited claim, order
labels by their summand in (FH2) at `(1/2,2/3)`. Each coordinate factor
decreases with its exponent, including the step from exponent zero.
The first26 all lie in `a<=3,b<=3,c<=2,1<=d<=3`, a set of144 labels.
Any label outside it is bounded by one of the first-outside axial
charges

\[
2/8125,\quad3/62426,\quad5/51909,\quad1/28561,
\]

each less than the26th charge `3/8918`. Exact sorting within the box
therefore proves the infinite-label ranking. Even the largest possible
25 summands give anchor margin

\[
-244500137708955299/1650097635185615616000<0,
\]

whereas `W26` gives the positive margin above. This is a minimum for
that scalar certificate, not a minimum sufficient boundary for the
covering problem, and not a lower bound on actual laws.

These finite-head criteria reuse the preceding integrated-union method.
Their role is to isolate explicit finite phase hypotheses while paying
an arbitrary complete complement; no enlargement over every earlier
union certificate is claimed. In particular `r_W72<=6` implies
`r_W54<=6`, but gives a better bound by paying a smaller tail. `W26`
uses fewer labels and a finer rectangular old partition. No domination
or independence of their weighted success regions is asserted.

The [standard-library producer](../../frontier/cover-geometry/pa_finite_root_heads.py)
reconstructs the complete auxiliary hinges, verifies all14 possible
root counts, the box tail formulas, all four corners, the positive
deficit coefficients and the finite ranking with its infinite complement
bound. All96 explicit checks pass with Python optimizations enabled.
The unrestricted-height statement uses the geometric-sum proof above;
these calculations add no Lean verification.

## The four fixed limits are not a universal alternative

There is a finite actual family for which all four fixed integral limits
above are exceeded, while the same actual PA law still satisfies the
complete-query target. Thus the candidate assertion

\[
\text{every actual family has some }q
\text{ with }J_q^{\rm union}<\tau_q
\]

is false for the four displayed uniform constants `tau_q`. This does not
contradict their sufficiency. The following construction has664 originals
at332 distinct full numerical moduli, exactly two originals at every
chosen label; it is an auxiliary two-copy family, not a distinct-modulus
covering of the integers.

There are no old5/7 originals, so `x=y=1` and `lambda0` is Haar. At row11
use old cofactors `1,5,7,35`, with current roots respectively
`(1,2),(3,4),(5,6),(7,8)` and old residues1 on every old coordinate
that occurs. Row13 uses those same cofactors and current roots, with old
residues2 instead. Every current exponent is one.

At row17 use every old exponent tuple in `{0,1,2}^4` over
`(5,7,11,13)`, all old residues zero, and the two nonzero current roots
from the [fixed root table](../../frontier/cover-geometry/actual_four_union_counterexample.input.json).
Row19 uses `{0,1,2}^5` over `(5,7,11,13,17)` in the same manner.
The arrays are indexed by lexicographic exponent order. Each tuple and
root determines one full integer CRT residue before any history is read.
The [exact result](../../frontier/cover-geometry/actual_four_union_counterexample.json)
expands all664 literal moduli and residues.

| `q` | Actual `Jq_union` | Decimal | Uniform limit |
|---|---|---:|---:|
|11|`3/35`|0.0857142857142857|0.0793741463942582...|
|13|`2/35`|0.0571428571428571|0.0393928184975108...|
|17|`7996598579/62494802370`|0.1279562183692685|0.1160933367616082...|
|19|`350316280698322/3418309452633075`|0.1024823192729021|0.0963027440977326...|

The inequalities are checked against the exact rational limits, not
their rounded decimals. The actual masses after11 and13 are `379/385`
and `9733/10010`; after19 the mass is

\[
\lambda_{\rm final}(1)
=\frac{305834805525730823}{324739398000142125}.
\]

The complete comparison uses
`Phi(1,1)=413209846699493/764619061606400` and gives

\[
R_Q(\nu)\le2+\frac{\Phi(1,1)}{\lambda_{\rm final}(1)}
=2.573817268790\ldots<T.
\]

### Exactness of the actual finite partition

Retain each truncated valuation `min(v_p(x_p),2)`. Before the seed rows,
also distinguish the5/7 first roots1,2 and the other nonzero roots.
An exact positive valuation `v<2` has Haar mass `(p-1)/p^(v+1)`;
the terminal cell `v>=2` has mass `p^-2`, accounting for all higher digits.

At a stage whose union contains `U` distinct nonzero first roots,
the actual density is `min(C_q,q/(q-U))`. The allowed valuation-zero
cell has Haar mass `(q-1-U)/q`; positive-valuation cells are unchanged
because zero is not forbidden. Multiplying those masses by this density
therefore gives the actual outgoing subprobability, without normalization.

For rows17 and19, a numerical old tuple `e` is active exactly when
`e<=v` coordinatewise. Taking the union of its fixed roots gives the
actual forbidden fraction `U/q`. All future old-coordinate tests have
exponent at most two and residue zero, so the retained valuations decide
every one of them. After13 the seed-specific nonzero-root distinctions
may consequently be aggregated. Row19 is evaluated on the actual row17
output. The finite calculation is exact for this full original family;
it does not optimize a phase separately at each valuation or drop a
future original test.

The [standard-library replay](../../frontier/cover-geometry/actual_four_union_counterexample.py)
checks the fixed root table, integer CRT classes, actual prefix transport,
all four rational inequalities and the final query bound; all33 explicit
checks pass with Python optimizations enabled. Its finite
original heights do not truncate the complete query bound: that bound
uses the existing all-height comparison for this same law.

The [optional phase-search program](../../frontier/cover-geometry/actual_four_union_search.py)
uses NumPy and floating-point scores to select one fixed table at row17,
recomputes its actual output exactly, and searches row19 on that same
output. It emits the selected fixed table and exact finite evaluation.
Optimality is not claimed; verification of the retained example requires
only the standard-library replay, with no rerun of the heuristic search.

### Preserve the actual pure parameters in the next search

The proof above already supplies the sharper sufficient threshold

\[
\tau_q(x,y)=\frac{q}{C_q}
\left(A_{q,K_q}(x,y)-\frac{\Phi(x,y)}{T-2}\right).
\]

The fixed `tau_q` is its rectangle minimum. At this example's actual
parameters `(1,1)`, the four parameter-specific limits are approximately
`3.3027183917,3.8088515917,4.4640526178,4.9762534604`; none is exceeded.
Hence the example rules out universal adequacy of the four fixed tests,
not the parameter-specific consumers or the final-mass method.
[Report348 NC4--NC7](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#actual-pure-union-deficits-must-lie-in-a-strict-joint-region)
already excludes this pure-parameter region. A search for failure of
the PA target must retain those same-source conditions as well as the
actual final mass, rather than target the four rectangle minima alone.

## Increasing an earlier forbidden union need not reduce later excess

The density caps also prevent a scalar monotonicity argument from closing
the remaining joint problem. The following four small actual families
keep the later13 originals fixed and only enlarge the first11 inventory.
There are no old5/7 or later17/19 originals.

Let `A_n`, for `n=2,4,6,8`, contain the first `n` originals from the
following ordered pairs:

| First11 old cofactor | Required old residues | Current11 roots |
|---|---|---|
|1|none|1,2|
|5|`x5=4 mod5`|3,4|
|7|`x7=6 mod7`|5,6|
|35|both preceding conditions|7,8|

In every family put two row13 originals at each old cofactor
`11,55,77,385`. Require `x11=0 mod11`, additionally `x5=4 mod5`
and `x7=6 mod7` whenever those coordinates occur, and assign their
current13 roots respectively `(1,2),(3,4),(5,6),(7,8)`.
These prescriptions are fixed full CRT classes; every numerical modulus
occurs exactly twice. Define

\[
E=\{x_5=4\bmod5,\ x_7=6\bmod7,\ x_{11}=0\bmod11\}.
\]

The later excess is exactly `(13b13-6)_+=2*1_E`. On the old5/7 cell
in `E`, family `A_n` forbids exactly `n` first11 roots and retains root0.
Thus

\[
\lambda_{11}^{A_n}(E)
=\frac1{385}\min\left(\frac53,\frac{11}{11-n}\right).
\]

Literal CRT evaluation gives:

| Family | `J11_union` | Actual first11 mass loss | `J13_union` |
|---|---:|---:|---:|
|`A2`|0|0|`2/315`|
|`A4`|0|0|`2/245`|
|`A6`|`1/35`|`8/1155`|`2/231`|
|`A8`|`3/35`|`6/385`|`2/231`|

From `A4` to `A6`, the earlier union, integrated excess and actual loss
increase, while the later excess also increases. From `A6` to `A8`,
the earlier quantities increase again but the later excess is unchanged.
The added forbidden roots raise the density on the common retained root
until the cap is reached; beyond that point its density remains `5/3`.
This refutes both nonincreasing downstream excess under earlier deletion
and a mandatory strict downstream improvement from larger earlier loss.

The mechanism is already present in the capped transport and the
[Report334 backward future-payoff formulas](../321-384/334-same-chain-overlap-and-future-risk-certificates.md#a-backward-supersolution-retains-the-future-relation-instead).
The new finite examples evaluate that limitation for the actual union
quantities used here. They do not show that a useful joint inequality is
impossible: such an inequality must retain where the future payoff lies
relative to the changed prefix measure. Each comparison uses an actual
fixed family and its own PA law; no mass from different families is
combined in a certificate.

## One near-critical source can fail all three finite-head tests

The finite-head certificates are not a universal alternative, even on
one actual prefix strictly inside NC4's necessary hard region. Keep
the exact70 old and200 first11 originals of Report558 Section6, and
add the following18 row13 originals. No17 or19 original is present.

| Full numerical modulus | Two full residues |
|---|---|
|13|0,1|
|169|2,3|
|2197|8,12|
|65|4,44|
|845|344,514|
|325|294,269|
|4225|1869,1194|
|1625|519,1144|
|21125|519,16394|

This is288 distinct modulus-residue pairs at144 numerical labels,
exactly two at each label. It is a legal finite two-copy family; no
irredundancy or pairwise-distinct-modulus claim is made. Every residue
is fixed jointly, and the actual prefix through11 is unchanged.

For this prefix,

\[
x=1563/3125,\quad y=11205/16807,\quad
\lambda_{11}(1)=19543635187/92276732625,
\]

\[
H_{11}=\frac{9458012327}{55366039575000},\qquad
(T-2)\alpha-\Phi
=-\frac{75039987614613334196523}
        {6774123938712274144000000}<0.
\tag{JC1}
\]

Thus the example satisfies the joint NC4 necessary condition, including
the original near-saturated pure5/7 combs. NC4 is not a sufficient
condition for an actual hard family.

Let `Q_W=E_W-P_W/3` and `eta_W=(26/3)D_W(x,y)` in FH4. Consider the
proposed implication

\[
\text{NC4 and one common actual prefix}\quad\Longrightarrow\quad
\min_{W\in\{W_{26},W_{54},W_{72}\}}
       (Q_W-7H_{11}-\eta_W)\le0.
\tag{JC0}
\]

This implication is false. To calculate all its terms on the same
source, use the nested cylinders

\[
C_5=\{x_5=4\bmod5\},\quad
C_{25}=\{x_5=19\bmod25\},\quad
C_{125}=\{x_5=19\bmod125\}.
\]

Their actual prefix masses, obtained from the literal H5 old
congruences and actual capped first11 kernel, are

\[
\mu_5=9070623361/92276732625,\quad
\mu_{25}=15701435/738213861,\quad
\mu_{125}=3244691/762617625.
\]

The simultaneous active root counts are

| Actual prefix region | `r26` | `r54` | `r72` |
|---|---:|---:|---:|
|`C5` complement|6|4|4|
|`C5` minus `C25`|10|8|8|
|`C25` minus `C125`|13|12|12|
|`C125`|13|12|13|

Integrating the exact FH4 functions gives

\[
Q_{26}=4\mu_5+3\mu_{25},\qquad
Q_{54}=2\mu_5+4\mu_{25}
              -\tfrac53(\lambda_{11}(1)-\mu_5),\qquad
Q_{72}=Q_{54}+\mu_{125}.
\]

Evaluating each head's own parameter-specific `eta_W`, not its corner
value, produces strict reverse margins

| Head | `Q_W-7H11-eta_W` |
|---|---|
|W26|`2239841558988584124453944117/4938750155272255161840000000`|
|W54|`63295047281631052888207331/705535736467465023120000000`|
|W72|`381776501843931159361131317/4938750155272255161840000000`|

The smallest is `0.07730225053728906...>0`, refuting JC0. In particular,
retaining the exact common source and the nesting `W54 subset W72`
does not force one of these three sufficient tests to pass.

### Actual deep unions still give an easy PA law

The actual forbidden13 fractions in the four regions above are,
respectively,

\[
366/2197,\quad730/2197,\quad1093/2197,\quad97/169.
\]

The first two produce no mass loss. The last two have loss fractions
`541/2197` and `61/169`. Hence the actual row loss is only

\[
\Delta_{13}
=\frac{541\mu_{25}+252\mu_{125}}{2197}
=\frac{1160746659847}{202731981577125}.
\tag{JC2}
\]

With no17/19 originals, the actual final mass is
`13925539948664/67577327192375`. The existing complete-query numerator
already gives

\[
R_Q\le2+\frac{\Phi}{\lambda_{\rm final}(1)}
=\frac{3984126407618460290849887}
       {1115779320809599838208000}
=3.5707118184692765\ldots<T.
\tag{JC3}
\]

Thus failure of the three finite-head tests does not imply a difficult
actual final law. Projecting deep cylinders to occupied roots loses
their depth and overlap, and can overestimate the forbidden fraction.
This is a boundary of those sufficient certificates, not a refutation
of them, of PA, or of Erdős #7.

There is no conflict with Report567's17-projection theorem: this family
uses old5 residues19 at cofactors25 and125, whereas that theorem
prescribes14 at both. Removing those projection hypotheses requires
another argument; neither the head conditions nor the necessary NC4
region supplies it automatically.

The [portable exact producer](../../frontier/cover-geometry/pa_three_head_compatibility_counterexample.py)
reconstructs the literal source, all288 CRT pairs, the four actual
prefix masses, each head's parameter-dependent FH4 terms and the
actual13 unions. Its [rational data](../../frontier/cover-geometry/pa_three_head_compatibility_counterexample.json)
retain the full inventory and all133 successful checks. All heights in
the query numerator are retained by their full geometric moments.

## Reuse and scope

The actual law, complete-query comparison and two-copy stage losses are
[Report348 CP2--CP5 and PA2--PA4](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md).
[Report559](559-pure-union-savings-control-all-four-later-rows.md)
supplies the same-law saving notation and pure-union criteria;
[Report546](546-dense-irredundant-families-separate-stage-debits-from-actual-unions.md)
treats particular dense families with small actual unions. A scoped search of Reports348,546,559,560 found no existing general occupied-root consumer of the above form. No literature-priority claim is made.

The only added hypotheses in the four sufficient certificates are the stated actual root-profile conditions, or their integrated excess versions. There is no old-comb or fixed-first11 restriction. The664-original example refutes universal adequacy of the four uniform limits. It does not resolve the parameter-specific joint problem, and their actual joint activation cannot be reconstructed by independently maximizing marginal phases.

The [standard-library producer](../../frontier/cover-geometry/actual_root_union_consumers.py)
reconstructs all complete auxiliary hinges from rational masses, full first
moments and below-threshold product corrections; scans the possible integer
root counts for each current prime; checks each root-excess envelope
on its full integer range; and evaluates the four small extension families
by their literal CRT classes. All144 explicit checks passed with Python
optimizations enabled. [Exact data](../../frontier/cover-geometry/actual_root_union_consumers.json)
retain the four corners, selected bounds and the failure of the next
integer threshold for this certificate, together with the four actual
cross-stage counterexamples. The separate664-original replay verifies
the simultaneous-threshold example from its fixed input table.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_root_union_consumers.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_four_union_counterexample.py
```

The generality comes from the actual-root argument and bilinear
interpolation above. This is ordinary mathematics and exact arithmetic;
no Lean was added or run. No unrestricted solution of Erdős#7 is asserted.

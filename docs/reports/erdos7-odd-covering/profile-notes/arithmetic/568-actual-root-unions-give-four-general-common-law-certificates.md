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
because `Jq_union <= (q-Kq) lambda_<q{bq>Kq/q}`. This is also necessary for a hypothetical family whose every supported law exceeds the target, because its actual PA law is one such law. No existence of a family meeting these necessary conditions is asserted.

## Reuse and scope

The actual law, complete-query comparison and two-copy stage losses are
[Report348 CP2--CP5 and PA2--PA4](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md).
[Report559](559-pure-union-savings-control-all-four-later-rows.md)
supplies the same-law saving notation and pure-union criteria;
[Report546](546-dense-irredundant-families-separate-stage-debits-from-actual-unions.md)
treats particular dense families with small actual unions. A scoped search of Reports348,546,559,560 found no existing general occupied-root consumer of the above form. No literature-priority claim is made.

The only added hypotheses are the stated actual root-profile conditions, or their integrated excess versions. There is no old-comb or fixed-first11 restriction. Conversely, no universal bound for these profiles over arbitrary original phases has been proved. Their actual joint activation cannot be reconstructed by independently maximizing marginal phases.

The [standard-library producer](../../frontier/cover-geometry/actual_root_union_consumers.py)
reconstructs all complete auxiliary hinges from rational masses, full first
moments and below-threshold product corrections; scans the possible integer
root counts for each current prime; and checks each root-excess envelope
on its full integer range. All109 explicit checks passed with Python
optimizations enabled. [Exact data](../../frontier/cover-geometry/actual_root_union_consumers.json)
retain the four corners, selected bounds and the failure of the next
integer threshold for this certificate.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_root_union_consumers.py
```

The generality comes from the actual-root argument and bilinear
interpolation above. This is ordinary mathematics and exact arithmetic;
no Lean was added or run. No unrestricted solution of Erdős#7 is asserted.

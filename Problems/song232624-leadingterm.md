---
slug: song232624-leadingterm
bibkey: song2019a232624
doi: null
url: https://oeis.org/A232624
triage: theorem
motivation_gids:
  - D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.result
---

# Song's leading term for odd and doubled conductors

## Problem

Jianing Song's Comment in [OEIS A232624](https://oeis.org/A232624), revision 109, attributes the conjecture to July 11, 2019. The exact quotation and coefficient-array definition are in [the source note](../Library/PrimeForms/song2019a232624.md). [Preregistration #21790](https://github.com/the-omega-institute/trureturing/issues/21790) specifies the complete assertion, including all coefficient consequences.

Let $P_n$ be the monic minimal polynomial over $\mathbb Q$ of $2\cos(2\pi/n)$, and let $a(n,j)=[X^j]P_n$. For odd $n>1$, put $d=\varphi(n)/2$, $m=n/\operatorname{rad}(n)$, $\varepsilon=(-1)^{\omega(n)}$, and $F_n=(P_{2n}-P_n)/2$. The settled assertion is

$$F_n\ne0,\qquad \deg F_n=d-m,\qquad \operatorname{lc}(F_n)=\varepsilon.$$

For every odd $k<m$, both $a(n,d-k)$ and $a(2n,d-k)$ vanish. At the first nonzero odd offset, $a(n,d-m)=-\varepsilon$ and $a(2n,d-m)=\varepsilon$.

### Statement echo

| Source clause | Lean counterpart and scope |
| --- | --- |
| MPR2 is the monic minimal polynomial of the stated real cosine | `MPR2` applies `minpoly` over the rationals to exactly that real expression. It is not defined through cyclotomic roots. |
| The array is the coefficient of MPR2 | `a n j` is `Polynomial.coeff` of `MPR2 n`. |
| For odd n greater than one | The only hypotheses of `claim` are `Odd n` and `1 < n`. |
| Highest term has exponent phi(n)/2 minus n/rad(n) and sign (-1)^omega(n) | `result` proves nonzeroness, `natDegree` and `leadingCoeff`. |
| Both arrays vanish for k=1,3,...,m-2 | The universally quantified odd `k < m` clause; empty when $m=1$. |
| The two first coefficients are minus epsilon and epsilon | The last two conjuncts of `claim`. |
| Natural division and subtraction | The proof establishes $0<m\le d$, so truncated subtraction equals the ordinary nonnegative difference. Nonzeroness makes the natural-degree convention faithful. |

The three public definitions and the sole public theorem `result` belong to `D5.S3.Arith.InterlaceFan.SongA232624LeadingTerm`. The module is generality `G`, utility `none`.

## Motivation

The settling declaration is `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.result`, with admission basis `open-problem-resolution (#21790; Proved)`. It settles an external named assertion, without a digestion atom. The Scribe attaches one `OpenProblemResolutionClaim` with outcome Proved to this declaration.

## Gap

A cyclotomic coefficient alone does not determine a cosine minimal-polynomial coefficient without proving the bridge for the actual minimal polynomial and excluding cancellation. Both bridges are proved in this module. No extra squarefree or prime-power restriction occurs in the settled assertion.

The [unfinished escape audit #22136](https://github.com/the-omega-institute/trureturing/issues/22136) covers the sole new public theorem, `result`. Equality, order, iff and existential readout templates do not directly reconstruct its guarded compound assertion. The available dependent-family enrollment still needs exact source reconstruction, an equivalence bridge, whole-family variation, role/anchor sensitivity and observational dependence for these polynomial readouts. No Reg mirror or completed registration is claimed.

## Route

Möbius inversion is applied in the units of rational power series. Reduction modulo $X^{m+1}$ kills every nonconstant factor except the divisor-antidiagonal pair $(\operatorname{rad}(n),m)$. The surviving factor yields

$$\Phi_n(X)\equiv 1-\mu(\operatorname{rad}(n))X^m\pmod {X^{m+1}}.$$

For odd $n$, reflection gives $\Phi_{2n}(X)=\Phi_n(-X)$, while $m$ is odd and $\mu(\operatorname{rad}(n))=\varepsilon$. Hence the first nonzero coefficient of $(\Phi_{2n}-\Phi_n)/2$ is $\varepsilon$ at exponent $m$.

The reciprocal substitution is realized by homogeneous evaluation, using `Polynomial.homogenize`, `MvPolynomial.eval₂`, and `Polynomial.eval_homogenize`. For $N>2$ the actual cosine minimal polynomial has degree $\varphi(N)/2$ and its lift is $\Phi_N$. For a nonzero polynomial $H$ of degree $e\le d$ with leading coefficient $c$, the least exponent of $X^dH(X+X^{-1})$ is $d-e$, with coefficient $c$: the top monomial contributes there once, and every smaller monomial has larger least exponent. This transfers the cyclotomic first coefficient to the degree and leading coefficient of $F_n$. Minimal-polynomial reflection supplies the coefficient consequences.

The direct D5 dependency is `D5.S3.Arith.InterlaceFan.Cyclotomic`, whose `zeta` definition is used. Radical arithmetic, power-series inversion and homogeneous evaluation use their pinned Mathlib owners.

## Falsifier

A single odd $n>1$ violating any conjunct would refute the source assertion. The theorem quantifies over all such $n$. Finite checks supply a separate exact arithmetic comparison and do not replace that universal proof. The exclusion of even conductors is material, as the computed $n=4$ case below shows.

## Evidence

`D5.S3.Arith.InterlaceFan.SongA232624LeadingTerm.result` proves the full `claim`; its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. Its Scribe theorem displays the expanded proposition, including every coefficient clause. The public definition bodies match the preregistered conventions.

### Exact finite experiment

The experiment is [song-a232624-minpoly at commit 062b9491b31f0f372c7c322e8b15e921c994acf3](https://github.com/the-omega-institute/trureturing-experiments/tree/062b9491b31f0f372c7c322e8b15e921c994acf3/docs/reports/song-a232624-minpoly). The script `check.py` has SHA-256 `7b3f8b095ff19702236890e76580945f68e2c7849890d71f85d946e66b6eb585` and Apache-2.0 license. Its committed bytes and local executable bytes compare equal.

From that repository, `python3 docs/reports/song-a232624-minpoly/check.py` exits 0 with final line `ALL_CHECKS_OK`. It reproduces all 20 source coefficient-table rows and $F_{15}=X^3-4X$. For all 225 odd conductors $3\le n\le451$ it checks nonzeroness, degree, leading coefficient, reflection and every stated coefficient consequence. Both polynomials in each comparison agree independently with the script's Chebyshev divisor construction. It uses exact integer arithmetic.

The same committed script's functions give the even boundary reading with command `python3 -c 'import runpy; s=runpy.run_path("/Users/auric/trureturing-experiments/docs/reports/song-a232624-minpoly/check.py"); p=s["real_poly"](4); q=s["real_poly"](8); print("P4",p,"P8",q,"twiceF4",s["add"](q,p,-1))'`, exit 0, using the same SHA-256: $P_4=X$, $P_8=X^2-2$, and $2F_4=X^2-X-2$. Thus $F_4$ has degree 2 and leading coefficient $1/2$.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Möbius inversion leaves the unique radical-indexed factor; odd reflection gives the first half-difference coefficient | proved | Kernel-checked private `cyclotomic_initial` and `cyclotomic_half_difference`, consumed by `result`. |
| The preliminary individual cyclotomic coefficient formula includes even n | proved | Kernel-checked private `cyclotomic_initial`, whose only conductor hypothesis is $n>1$. The comparison and reflection require oddness. |
| Actual cosine minpoly bridge and degree phi(N)/2 for every N>2 | proved | Kernel-checked private `MPR2_bridge`, with hypothesis $2<N$, used in `result`. |
| All 225 odd conductors 3 through 451, all coefficient consequences and independent Chebyshev construction | computed | The pinned experiment command above, exit 0 and `ALL_CHECKS_OK`, with the stated script SHA-256. No unbounded inference is drawn from it. |
| Direct even extension at n=4 | computed | The pinned-script function command above, exit 0, gives $2F_4=X^2-X-2$; the odd-conductor conclusion does not extend verbatim. |
| Subsequent nonzero odd coefficients and modified even-conductor comparisons | open | Neither is a conclusion of `result`; no literature-wide openness claim is made. |

### What the settlement shows

The kernel-checked `result` determines the exact gap $m=n/\operatorname{rad}(n)$, including repeated-prime conductors, and makes every coefficient consequence in Song's quoted Comment unconditional for odd $n>1$. The constant boundary $n=3$ is included. Its proof's private `cyclotomic_initial` establishes the individual coefficient formula for every $n>1$, and private `MPR2_bridge` establishes the actual minimal-polynomial bridge and degree for every $N>2$; these are proof components, not additional public identity theorems.

The even counterexample above is computed. Modified even comparisons and later nonzero odd coefficients remain open in this delivery. No claim about other, unexamined assertions in the OEIS entry or literature is made. The literature screen in #21790 located no settlement in its specified scope, and its completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature screen covers the explicitly listed arXiv metadata searches, seven targeted TeX sources, Lang's OEIS supplementary note, Crossref metadata, and the specified MathOverflow, Math StackExchange and MathDB queries. OpenAlex and Semantic Scholar rate limits prevented citing-work inventories. The original Watkins–Zeitlin, Surowski–McCombs, Cafure, Lehmer and Barnes articles were not all read in full; some ingredient statements were read through Doi. No exhaustive prior-art, priority or worldwide openness claim follows. Source and literature readings attributed to the preregistration are orchestrator/research-seat readings rather than independent replications by the implementation seat.

Four-slot escape registration remains unfinished under #22136. A frozen theorem and a successful required check do not by themselves establish `declared_validated`.

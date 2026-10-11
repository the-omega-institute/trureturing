---
slug: krishna-2022-cstar-higher-order-smale-mean-value
bibkey: krishna2022cstarsmale
doi: 10.48550/arXiv.2206.08154
url: https://arxiv.org/abs/2206.08154v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.result
---

# The Higher Order C*-algebraic Smale Mean Value Conjecture

## Problem

K. Mahesh Krishna, *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*, arXiv:2206.08154v1, Section 2, Conjecture HIGHERMEAN; journal DOI 10.26117/2079-6641-2026-54-2-38-47, Conjecture 2.3, p. 44:

> Let $\mathcal A$ be a commutative C*-algebra. Let $P(z)\coloneqq(z-a_1)\cdots(z-a_n)$ be a polynomial of degree $n\ge2$ over $\mathcal A$, $a_1,\ldots,a_n\in\mathcal A$. If $z\in\mathcal A$ is not a critical point of $P$, then there exists a critical point $w\in\mathcal A$ of $P$ such that
>
> $$\frac{\|P^{(k)}(z)\|}{k!}\frac{\|P(z)-P(w)\|^{k-1}}{\|P'(z)\|^k}\le4^{k-1},\qquad\forall\,2\le k\le n.$$

The binding convention of [#14982](https://github.com/the-omega-institute/trureturing/issues/14982) uses `Polynomial A`, iterates of `Polynomial.derivative`, and `CommCStarAlgebra A`. The factor index `Fin n` retains every root with multiplicity. Noncritical means $P'(z)\ne0$; the same $w$ must satisfy every inequality.

## Motivation

The frozen declaration `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.result : ¬ claim` refutes the conjecture already in the commutative unital C*-algebra $\mathbb C\times\mathbb C$ with its supremum norm, at degree three.

## Gap

The Tier 1 preregistration #14982 records the source and literature readings: the only arXiv version is v1; the journal retains the named conjecture; the checked later Casas–Alvero, Bieberbach/Corona and non-Archimedean Smale/Dubinin–Sugawa papers do not address this inequality in a product C*-algebra. No MathDB page was located. These are attributed preregistration readings, `not-found-in-searched-scope`, rather than a claim of worldwide priority.

## Route

At $t=21$, take $\mathcal A=\mathbb C\times\mathbb C$, $n=3$, $z=0$, and the three roots

$$a_1=(0,0),\quad a_2=\left(\frac{-21+\sqrt{437}}2,\sqrt3\right),\quad a_3=\left(\frac{-21-\sqrt{437}}2,-\sqrt3\right).$$

Their factor product is $P(x,y)=(x^3+21x^2+x,y^3-3y)$. Its complete critical set is

$$w=\left(-7\pm\frac{\sqrt{438}}3,\ \pm1\right),$$

with the signs independent. The second coordinate gives $|P_2(0)-P_2(\pm1)|=2$, hence $\|P(0)-P(w)\|\ge2$. At zero, $P'(0)=(1,-3)$ and $P''(0)=(42,0)$, with norms $3$ and $42$. For every critical point the $k=2$ term is therefore at least

$$\frac{42}{2}\frac2{3^2}=\frac{14}3>4.$$

## Falsifier

The public `claim` preserves the universal source statement. A nonzero first derivative at $z=0$ and failure at $k=2$ for every critical point contradict its existential conclusion. The private `critical_set` lemma enumerates all four critical points, so the refutation does not rely on selecting only some of them.

## Evidence

The Lean module is `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.lean`, with public definitions `smalePoly` and `claim` and the sole public theorem `result`. The private lemmas compute the factor polynomial and its derivatives, enumerate the critical points, prove the gap bound and the strict failure. Their live uses culminate in `result`. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The numerical experiment entry is [docs/reports/krishna-2022-cstar-higher-order-smale-mean-value/](https://github.com/the-omega-institute/trureturing-experiments/tree/12e6350cffc13b530eb62f9cae571b2dd8fa94d0/docs/reports/krishna-2022-cstar-higher-order-smale-mean-value/). Command: `python3 check.py`; exit 0; script SHA-256 `66a503c5e957e7d7f9619a59f92cae90311bdb0d6fedc396f20bd7d8e8a74ebe`. Tested scope: $t=21$, $n=3$, $z=0$, all four critical points. The readings are $\|P'(0)\|=3$, $\|P''(0)\|=42$; the two critical points with first coordinate $-7-\sqrt{438}/3$ have gap approximately $1358.01191829$ and term approximately $3168.69447602$, and the other two have gap $2$ and term $14/3\approx4.66666666667$. The exact minimum is $14/3$. These numerical readings corroborate the kernel-checked fixed instance.

## Triage

Tier 1; resolution **Refuted** by `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.result`. `proof_shape: bind-only`; `escape_witness: none`; `admission_basis: open-problem-resolution` (#14982). Utility: `certified-instance`, with `basis=refutes` the module's `claim`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### What the settlement shows

- **Proved, kernel-checked fixed witness:** at $t=21$, private `critical_set` gives second coordinate $\pm1$ for every critical point; `critical_gap` proves $\|P(0)-P(w)\|\ge2$. Private `derivative_norm` and `second_norm` give norms $3$ and $42$; these imply the lower bound $14/3$, and `failing_term` proves the strict failure $4<\text{term}$. The public `result` refutes the full claim.
- **Proved in prose, not formalized, family and unboundedness:** for every real $t>18$, the roots $0$ and $(-t\pm\sqrt{t^2-4})/2$ in the first coordinate, paired with $0,\pm\sqrt3$ in the second, yield $P_t(x,y)=(x^3+tx^2+x,y^3-3y)$. At zero its derivative norms are $3$ and $2t$. Every critical point still has second coordinate $\pm1$ and critical-value gap at least $2$, so the $k=2$ term is at least $2t/9>4$. Given any finite proposed replacement constant $C$, choosing $t>\max(18,9C/2)$ makes that term exceed $C$ at every critical point. No finite constant replaces $4$ already at degree three in $\mathbb C\times\mathbb C$.
- **Proved in prose, mechanism:** the supremum norm combines curvature from the first coordinate with an unavoidable critical-value gap from the second. Separate scalar bounds on each coordinate do not control the product of these maxima. The fixed witness proves that this obstruction occurs in an actual common polynomial and every one of its critical points.
- **Literature reading, degree two:** the source's Theorem 2.2 (journal p. 44) proves Conjecture 2.3 for degree two. The counterexample has degree three; the degree-two theorem and scalar higher-order theorem retain their stated scopes and are not formalized here.
- **Computed readings:** the pinned experiment entry and command in Evidence test exactly $t=21$, $n=3$, $z=0$ and all four critical points. They give minimum $14/3>4$. The uniform family conclusion above is a prose argument, rather than an extension of the numerical tested scope.
- **Related literature/delivery:** the same paper's Conjecture DUALSMALE is refuted in the separate delivery [#14940](https://github.com/the-omega-institute/trureturing/issues/14940); it is a different first-derivative assertion.
- **Open:** whether additional restrictions on the coordinates of $\mathcal A=C(X)$, for example connected $X$, imply this inequality. The disconnected two-point space underlying $\mathbb C\times\mathbb C$ does not decide the connected case.
- **Open:** the paper's CSMALE conjecture, its strong form and its dynamics conjecture. This module supplies no settlement of them.
- **Effect on source results:** HIGHERMEAN fails at degree three and any unrestricted bound obtained by assuming it lacks that premise. The source's independently proved degree-two and scalar results are unaffected; no additional source theorem is refuted here.

## ASSUMED-UNVERIFIED

Absence of a prior settlement outside the accessible literature scope is unverified. The general $t>18$ family and no-finite-constant conclusion are proved in prose, not Lean. The connected-space case and the other named conjectures remain open. Numerical values are computational corroboration, not additional kernel-checked declarations.

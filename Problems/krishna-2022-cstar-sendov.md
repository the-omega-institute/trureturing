---
slug: krishna-2022-cstar-sendov
bibkey: krishna2022cstarsendov
doi: 10.48550/arxiv.2203.06916
url: https://arxiv.org/abs/2203.06916v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/CStarSendov.result
  - D5/S3/Quantum/Algebra/CStarSendovCommutative.result
---

# Krishna's C*-algebraic Sendov conjectures

## Problem

Krishna, *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*, arXiv:2203.06916v1 (Definitions 2.1 and 2.3, Equation (1), Conjectures 2.4 and 2.5, and Theorem 2.6), asks whether, for every root $a_j$, there exists an algebra-valued zero $z$ of $p'$ in the disc of radius $1$ about $a_j$, under the stated disc, derivative-root and convex-form hypotheses (Conjectures 2.4 and 2.5; the claims end in $\forall j,\exists z$). Conjecture 2.5 is the general C*-algebra question; Conjecture 2.4 is its commutative dense-invertibles variant. The journal version is Vestnik KRAUNC Fiz.-Mat. Nauki 54(1) (2026), 56–63, DOI 10.26117/2079-6641-2026-54-1-56-63.

Both conjectures are **Refuted**. One resolution claim names both refuting results as its members: `D5/S3/Quantum/Algebra/CStarSendov.result` and `D5/S3/Quantum/Algebra/CStarSendovCommutative.result` for this dossier.

## Motivation

The obstruction is global branch selection. A polynomial whose coefficients trace a loop around the derivative discriminant can have two pointwise critical branches that exchange at the endpoints. A continuous algebra-valued zero must choose one branch on the whole connected spectrum, so no single zero stays within radius one of the selected root.

## Gap

The source proves the degree-two case (Theorem 2.6) and states the universal conjectures. The preregistration is issue [#15036](https://github.com/the-omega-institute/trureturing/issues/15036). The six public helper theorems in `CStarSendov` have an unfinished escape audit tracked by [#15114](https://github.com/the-omega-institute/trureturing/issues/15114); no Reg file is delivered.

In `CStarSendovCommutative`, the only public theorem is `result`. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Route

Take $\mathcal A=C([0,6],\mathbb C)$, roots $a_1=1/2$, $a_2=-1/2$, and $a_3=c$, where $c$ is the piecewise-linear loop through $-9/10$, $-1/10+4i/5$, $1/10+4i/5$, $1/10+9i/10$, $-1/10+9i/10$, $-1/10+4i/5$, and $-9/10$ at parameters $0,\ldots,6$. The real-square-root charts switch at $t=2$ and $t=4$, where their selected values agree. Put $D=c^2+3/4$ and choose the continuous square root $s$ with $s(0)=\sqrt{39}/5$ and $s(6)=-\sqrt{39}/5$. Then

$$b_+=(c+s)/3,\qquad b_-=(c-s)/3,$$

and $p'(z)=3(z-b_+)(z-b_-)$. The branch-exhaustion argument shows every algebra-valued zero is one of these global branches. Positive inverse-square-distance weights give the required convex forms, and both branches remain in the unit disc. At the endpoints,

$$|b_-(0)-1/2|=|b_+(6)-1/2|=(12+\sqrt{39})/15>1.$$

The commutative module proves density of invertibles in $C([0,6],\mathbb C)$ and identifies the C*-algebraic derivative with the ordered derivative for this cubic, transferring the same witness to Conjecture 2.4.

## Falsifier

The construction fails as a refutation if any root leaves the unit disc, either critical branch lacks the required convex form or derivative equation, the branch-exhaustion step admits an additional continuous zero, the endpoint distance is at most one, the invertibles are not dense, or the C*-derivative identification is invalid. The kernel-checked `result` declarations settle these obligations with the stated Lean conventions.

## Evidence

The source and journal metadata are recorded in `Library/QuantumBounds/krishna2022cstarsendov.md`. The independent numerical reading is the experiment entry [`docs/reports/krishna-2022-cstar-sendov-branch-exchange/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/90100c52fd2119542be2630ea8dfd8a1bc950e3f/docs/reports/krishna-2022-cstar-sendov-branch-exchange) at commit `90100c52fd2119542be2630ea8dfd8a1bc950e3f`, script SHA-256 `4a0e3a2dab42900894c1fbd5cc99fca685cdbc9a7577ad2525b9020a3fec377c`; command `python3 check.py`; exit code `0`. It checks the derivative zeros, positive barycentric weights, endpoint branch exchange, endpoint distance, unit-disc margins, nonzero discriminant and exact rational inequalities. The program text is not embedded here.

## Triage

### What the settlement shows

- **The mechanism — proved (kernel-checked branch exchange and exhaustion; paper argument for winding).** The polygon consists of the counterclockwise rectangle $[-1/10,1/10]\times[4/5,9/10]$ with a tail traversed in both directions. Since $(4/5)^2<3/4<(9/10)^2$, it winds once around $i\sqrt3/2$. The exact square-root endpoint identities and branch exhaustion on the live proof path of `CStarSendov.result` show that the two critical branches exchange between $t=0$ and $t=6$. For any algebra-valued derivative zero $z$, the continuous quotient $(3z-c)/s$ has square $1$; connectedness forces this quotient to be constantly $1$ or $-1$. Thus $z=b_+$ or $z=b_-$ globally, and each branch is more than $1$ from $a_1=1/2$ at one endpoint. The square-root chart cuts are $2$ and $4$.
- **The journal variant — proved in prose from the same factorization.** The witness has complete factorization $p'(z)=3(z-b_+)(z-b_-)$, so it also violates the journal's complete-factorization variant (journal Conjecture 4). That variant is not formalized here.
- **Degree 2 — proved in the source (literature reading).** Theorem 2.6 proves Conjecture 2.5 for degree $2$; this refutation has degree $3$, the first degree beyond that theorem.
- **Readings — computed.** The experiment entry in `Evidence` was run as `python3 check.py`, exit `0`, script SHA-256 `4a0e3a2dab42900894c1fbd5cc99fca685cdbc9a7577ad2525b9020a3fec377c`. On the 60001-point grid $t=6k/60000$, $0\le k\le60000$, the maximum norm of the roots and critical branches is `0.9055385138137417`, the minimum discriminant modulus is `0.06000000000000005`, the minimum branch separation is `0.16329931618554525`, and the minimum root gap $|c\mp1/2|$ is `0.28284271247461906`. The endpoint distance is `1.2163331998932265`. The script also checks the polygon vertices and the exact rational inequalities $(4/5)^2<3/4<(9/10)^2$ and the vertex bound $|c|^2\le82/100$. These numerical margins are finite-grid results; uniform numerical margins beyond that grid are open. The disc and nonvanishing statements used for the refutation have independent kernel proofs.
- **Where the obstruction lives — proved in prose.** For $\mathcal A=\mathbb C^k$, and for $C(X)$ with finite $X$, a zero of $p'$ can be chosen coordinatewise. Conjecture 2.4 then reduces to scalar Sendov in each coordinate: for each root, choose a scalar derivative zero in each coordinate and combine the finitely many choices into an element of $C(X)$. Scalar Sendov is known for degree at most $8$ (J. E. Brown and G. Xiang, *J. Math. Anal. Appl.* **232** (1999), 272–292, [DOI 10.1006/jmaa.1999.6267](https://doi.org/10.1006/jmaa.1999.6267)) and all sufficiently large degree (T. Tao, *Acta Math.* **229** (2022), 347–392, [arXiv:2012.04125](https://arxiv.org/abs/2012.04125)). Thus this coordinatewise argument proves the finite-spectrum conclusion in those ranges; at other degrees its scalar premise remains open. The present counterexample uses a connected spectrum and a coefficient loop around the discriminant locus.
- **Totally disconnected spectra — open.** It is open whether either conjecture holds for $C(X)$ with $X$ totally disconnected at every degree.
- **Local or larger-radius conclusions — open.** It is open whether a weaker conclusion holds with a zero allowed to depend on a neighbourhood, or with radius $1$ replaced by a larger constant.
- **Beyond commutative witnesses — open.** The noncommutative case beyond this commutative witness remains open.

## ASSUMED-UNVERIFIED

No worldwide originality or priority claim is made beyond the bounded literature readings recorded in the preregistration and Library note. The journal's complete-factorization variant is reported from the source metadata and is not a separate Lean claim. The six-helper escape audit remains unfinished under issue #15114.

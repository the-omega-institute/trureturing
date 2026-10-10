---
slug: krishna-2022-cstar-dubinin-sugawa-dual-mean-value
bibkey: krishna2022cstarsmale
doi: 10.48550/arXiv.2206.08154
url: https://arxiv.org/abs/2206.08154v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/CStarDualMeanValue.result
---

# The C*-algebraic Dubinin–Sugawa norm mean value conjecture is false

## Problem

K. Mahesh Krishna, *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*, arXiv:2206.08154v1, Section 3, p. 7, Conjecture DUALSMALE (journal Conjecture 3.1), states:

> Let $\mathcal A$ be a commutative C*-algebra. Let $P(z)=(z-a_1)\cdots(z-a_n)$ be a polynomial of degree $n\geq2$ over $\mathcal A$, with $a_1,\ldots,a_n\in\mathcal A$. If $z\in\mathcal A$ is not a critical point of $P$, then there exists a critical point $w\in\mathcal A$ such that
> $$\frac{\|P'(z)\|}{n}\leq\frac{\|P(z)-P(w)\|}{\|z-w\|}.$$

Section 2 defines $P'$ as the sum of ordered products obtained by omitting one factor. The source's gloss makes noncritical mean $P'(z)\ne0$; critical means $P'(w)=0$. The Lean definitions preserve this convention, use zero-based `Fin n` root indices, and cast $n$ to $\mathbb R$ in the displayed quotient.

The carrier `A : Type` with `[CommCStarAlgebra A]` restricts the universal claim to unital commutative C*-algebras in `Type`. This weakens the source assertion, so its negation refutes that assertion. The witness algebra $\mathbb C\times\mathbb C$ is in this subclass.

## Motivation

A supremum norm can select different coordinates for the derivative and the displacement. A scalar lower bound for one coordinate need not survive this combination. The cubic witness tests that obstruction in the smallest nontrivial finite product, at the first degree beyond the source's degree-two theorem.

## Gap

Issue [#14940](https://github.com/the-omega-institute/trureturing/issues/14940) preregisters the source statement, complete rational witness, binding Lean conventions and Tier-1 classification. Its literature readings find no settlement of DUALSMALE in the searched scope. Comment [6091424038](https://github.com/the-omega-institute/trureturing/issues/14940#issuecomment-6091424038) specifies the certified-instance refutation utility. The scalar dual conjecture and the source's operator-order formulation are distinct targets.

## Route

Use $\mathcal A=\mathbb C\times\mathbb C$ with coordinatewise operations and supremum norm, $n=3$, $z=(0,0)$ and roots $a=((0,3/2),(3,3/2),(3,3/2))$. Then
$$
P(x,y)=(x(x-3)^2,(y-3/2)^3),\qquad
P'(x,y)=(3(x-1)(x-3),3(y-3/2)^2).
$$
The complete critical set is $\{(1,3/2),(3,3/2)\}$. At zero, $P'(0)=(9,27/4)$ and $\|P'(0)\|/3=3$. The two quotients are $8/3$ and $9/8$, both strictly below $3$.

`CStarSchoenberg.orderedDeriv` supplies the imported ordered derivative. `orderedPoly` is the literal ordered product. The ten private helper theorems compute the closed forms, enumerate the critical set and establish the exact norm comparisons used by `result : ¬ claim`.

## Falsifier

A missed critical point with quotient at least $3$, a discrepancy between the ordered derivative and the source's omitted-factor expression, or a prior settlement of the same quantified assertion would invalidate the corresponding mathematical or literature conclusion. The Lean proof enumerates the entire critical set; it does not sample it.

## Evidence

The kernel-checked settling declaration is `D5/S3/Quantum/Algebra/CStarDualMeanValue.result`. The only public definitions are `orderedPoly` and `claim`, and the only public theorem is `result`. Its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The declaration's admission basis is `open-problem-resolution` (#14940; Refuted), with `proof_shape: bind-only` and `escape_witness: none`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment entry: [the pinned check directory](https://github.com/the-omega-institute/trureturing-experiments/tree/a42a734188621bee70e58f859b4a20055464a9aa/docs/reports/krishna-2022-cstar-dubinin-sugawa-dual-mean-value), specifically [check.py](https://github.com/the-omega-institute/trureturing-experiments/blob/a42a734188621bee70e58f859b4a20055464a9aa/docs/reports/krishna-2022-cstar-dubinin-sugawa-dual-mean-value/check.py). From that directory, `python3 check.py` exits 0. Script SHA-256: `335cb48b9105211645643b961a35d12bdbd5952a97278047cbca68d462af26b9`. The tested scope is exactly two degree-three witnesses in $\mathbb C\times\mathbb C$ at $z=0$: the repeated-root rational witness and the simple-root witness below. The program computes all coordinatewise critical points and their quotients. It does not enumerate the full parameter interval of the family.

## Triage

### What the settlement shows

- **Mechanism — proved in this module.** `critical_set`, `deriv_norm_at_zero`, `quotient_one`, `quotient_three` and their strict-threshold helpers establish the complete obstruction used by `result`. The first coordinate contributes derivative norm $9$. At $(1,3/2)$, the second coordinate increases the displacement norm from $1$ to $3/2$ while the numerator norm remains $4$. At $(3,3/2)$, the first coordinate has zero polynomial difference and the quotient is $9/8$. Thus the scalar lower bound does not pass to products, already at degree three in $\mathbb C\times\mathbb C$.
- **Degree two — proved by the source, not formalized here.** ArXiv Theorem 3.3 (journal Theorem 3.1) proves the case $n=2$. Its unique critical point is $c=(a_1+a_2)/2$, with $P'(z)=2(z-c)$ and $P(z)-P(c)=(z-c)^2$. For the commutative C*-algebra norm, the quotient equals $\|z-c\|=\|P'(z)\|/2$ at noncritical $z$. Degree three is the first degree beyond that theorem.
- **Family — computed identities and inequalities in prose, not Lean-formalized.** Replace $3/2$ in all second coordinates by a real $M$ with $4/3<M<\sqrt3$. The derivative norm at zero remains $9$ because $3M^2<9$. The critical points are $(1,M)$ and $(3,M)$, with quotients $\max(4/M,M^2)$ and $M^3/3$. Here $4/M<3$, $M^2<3$, and $M^3/3<\sqrt3<3$. These algebraic inequalities establish the whole stated interval; the pinned experiment entry checks its member $M=3/2$, giving $8/3$ and $9/8$. No program-based verification of the whole interval is claimed.
- **Simple roots — computed, not Lean-formalized.** For $a=((0,11/8),(23/8,3/2),(25/8,13/8))$ at $z=0$, the pinned experiment entry gives threshold $575/192$. The critical points are all four pairs $(2\pm\sqrt{579}/24,3/2\pm\sqrt3/24)$. In the sign order $(-,-),(-,+),(+,-),(+,+)$, the quotients are approximately $2.7905226344663068$, $2.5343305177315836$, $1.1164701865553526$ and $1.1159694485505827$, and every exact comparison fails the threshold. The two scalar root triples have distinct roots; repeated roots are unnecessary for this computed counterexample.
- **Strong form — proved reduction in prose, not formalized.** On $\mathbb C^k$, operator order is coordinatewise. STRONGERDUALSMALE reads $|z_i-w_i|^2|P_i'(z_i)|^2/n^2\leq|P_i(z_i)-P_i(w_i)|^2$ in each coordinate. Assuming a scalar dual instance, choose its critical point in every noncritical coordinate; when $P_i'(z_i)=0$, choose $w_i=z_i$. Conversely, the one-coordinate case is the scalar bound. This is a conditional reduction to the scalar conjecture, not its proof. For this cubic, $w=(1,3/2)$ satisfies the strong inequality coordinatewise, so the norm counterexample does not refute it.
- **Smale direction — proved preservation in prose, not formalized.** Suppose each scalar instance has a critical point with $A_i=|P_i(z_i)-P_i(w_i)|\leq c B_iD_i$, where $B_i=|z_i-w_i|$ and $D_i=|P_i'(z_i)|$. Then $\max_i A_i\leq c(\max_i B_i)(\max_i D_i)$. With nonzero $\max_i B_i$, the product difference quotient is at most $c\max_i D_i$. Equivalently, for positive $B_i$, $\max_i A_i/\max_i B_i\leq\max_i(A_i/B_i)$. Coordinates with zero derivative can use $w_i=z_i$ and contribute zero. Thus CSMALE survives products of scalar instances; the scalar conjecture itself is not settled here.
- **Source consequences — proved in prose.** The degree-two theorem is intact. The same norm-form universal assertion for Banach algebras mentioned in Remark 3.4(i) is also false, since this product algebra is a Banach algebra. No general settlement of CSMALE or STRONGERDUALSMALE follows from `result`.
- **Smaller constants — open.** Whether replacing $1/n$ by a smaller universal constant, for example $1/(n\,4^n)$, restores DUALSMALE on $\mathbb C^k$ or $C(X)$ is not settled by this witness.
- **Continuous selection — open.** STRONGERDUALSMALE on $C(X)$ for connected $X$ remains open here, including the obstruction to continuously selecting critical points across $X$.

## ASSUMED-UNVERIFIED

The literature screen is limited to the sources and searches in #14940. Exhaustive prior-art coverage and publication priority are unverified. The family and simple-root evidence are not additional Lean theorems. The strong-form and Smale preservation statements above are the specified conditional arguments; neither proves the unresolved scalar conjectures or continuous selection on general $C(X)$.

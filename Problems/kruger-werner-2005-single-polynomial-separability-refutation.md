---
slug: kruger-werner-2005-single-polynomial-separability-refutation
bibkey: krugerwerner2005openproblems
doi: null
url: https://arxiv.org/abs/quant-ph/0504166v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.result
---

# No single polynomial inequality characterizes separability in every dimension

## Problem

O. Krüger and R. F. Werner, *Some Open Problems in Quantum Information Theory*, arXiv:quant-ph/0504166v1, Problem 3, "Polynomial entanglement invariants", the third closely related problem:

> Decide whether the set of separable states can be described in terms of a polynomial invariant $f$, such that $f(\rho)\ge 0$ is equivalent to separability. There are many weaker versions of this statement, which may be of interest. For example, we might merely ask for a sufficient or a necessary separability criterion, and we might allow $f$ to depend on the dimensions.

Here a polynomial invariant is a real function on bipartite density operators that is constant on local-unitary orbits $\rho\mapsto(U_A\otimes U_B)\rho(U_A\otimes U_B)^*$ and is computed by a polynomial in the matrix elements of $\rho$. The definitions are quoted in [the literature note](../Library/QuantumContext/krugerwerner2005openproblems.md).

Issue [#20112](https://github.com/the-omega-institute/trureturing/issues/20112) fixes the reading: for all local dimensions $d_A,d_B\ge2$ there is a real polynomial $f$ in the real and imaginary parts of the entries, invariant under local unitaries on density operators, with $f(\rho)\ge0$ iff $\rho$ is separable for every density operator $\rho$. This dimension-dependent version, the weakest the source names for a characterization, is refuted.

## Motivation

The main question of the problem, the completeness of polynomial invariants, is answered in the source by the Onishchik–Vinberg theorem. The separability question asks whether the separable set itself is cut out by one invariant inequality. At $2\times2$ it is: $\rho$ is separable iff $\det\rho^\Gamma\ge0$ (Augusiak–Demianowicz–Horodecki 2008). Later work at $2\times3$ uses several polynomial inequalities.

## Gap

The literature check before any Lean is recorded in #20112:
- the source's solution section and the 2026 formal-conjectures entry (google-deepmind/formal-conjectures#3403) treat only the completeness question;
- Zhang–Xie (arXiv:2609.11090) states that no single determinant inequality suffices at $2\times3$ and uses several inequalities, without excluding a single polynomial;
- the other works inspected contain no statement of the impossibility;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

At $2\times3$, let $\Gamma$ be the partial transpose on the qutrit, $P_1,P_2$ the projectors onto $(e_{00}+e_{11})/\sqrt2$ and $(e_{01}+e_{12})/\sqrt2$, $B_0=(I-P_1^\Gamma-P_2^\Gamma)/4$, $B_1=(I-P_2^\Gamma)/5$, $B_2=(I-P_1^\Gamma)/5$ and $\rho(x,y)=(1-x-y)B_0+xB_1+yB_2$.
1. **States.** For $|x|,|y|\le1/4$, $\rho(x,y)$ has trace one and is an explicit sum of eight positive rank-one terms.
2. **Separable on the quadrant.** The corners $B_0,B_1,B_2$ have explicit decompositions into products of positive matrices, so $\rho(x,y)$ is separable for $0\le x,y\le1/4$.
3. **Entangled off the quadrant.** The partial transpose of $\rho(x,y)$ takes the value $2x/5$ on $e_{00}+e_{11}$ and $2y/5$ on $e_{01}+e_{12}$, and separable matrices have positive semidefinite partial transpose. So $\rho(x,y)$ is entangled if $x<0$ or $y<0$.
4. **No polynomial.** For any polynomial $f$, $q(x,y)=f(\rho(x,y))$ is a polynomial because $\rho$ is affine.
   - For $0<y<1/4$, $q(0,y)\ge0$ while $q(x,y)<0$ for $-1/4<x<0$, so $q(0,y)=0$ by continuity.
   - The polynomial $q(0,\cdot)$ then vanishes identically, so $q(0,-1/8)=0\ge0$.
   - Yet $\rho(0,-1/8)$ is entangled, a contradiction.

## Falsifier

The counterexample would not refute the question if the module's class of polynomials or its separable set were narrower than the source's. The module:
- allows any real polynomial in the real and imaginary parts of the entries, which contains the polynomials in the entries and their conjugates;
- requires invariance only on density operators, as the source's definition does;
- lets $f$ depend on the dimensions;
- uses the frozen separable cone of finite sums of tensor products of positive semidefinite matrices.

The argument uses neither invariance nor a degree bound, so it refutes the weaker non-invariant version as well.

## Evidence

The canonical source is `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.lean` (319 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.lean.json`, statement `sha256:028f2b025d0432cedf5467e49818996946a28237fedb422c5794e467ea275119`.

Declaration statements:
- `result`: `sha256:a224bc0cef29f2c2d74eb2280fe0335e285b7ef9e9db0553d45ad19294189332`;
- `claim`: `sha256:ded22751866d024e034aadf2960c18f9f27f54baafa10c022792014c20290f96`.

## Triage

Tier 1 open subquestion of a 2005 open-problem list, preregistered in issue #20112 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved in the module:** at local dimensions $2$ and $3$, no real polynomial $f$ in the entries, invariant or not, satisfies $f(\rho)\ge0\iff\rho$ separable on all density operators. Hence the dimension-dependent single-polynomial characterization fails.

**Computed, not formalized** (orchestrator, sympy, recorded in #20112): the characteristic polynomial of $\rho(x,y)^\Gamma$ is $(x-5\lambda)(y-5\lambda)(20\lambda+x+y-5)^4/(4\cdot10^6)$, with eigenvalues $x/5$, $y/5$ and $(5-x-y)/20$ (fourfold).

**Argued, not formalized.**
- *Mechanism.* The boundary of the separable set contains a segment of the line $x=0$ whose continuation inside the state space, $y<0$, consists of entangled states. A polynomial with $f\ge0$ exactly on the separable set must vanish on the segment, hence on the whole line, so it cannot exclude the entangled continuation.
- *Other dimensions.* Embedding the $2\times3$ family into $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ with $d_A\ge2$, $d_B\ge3$ gives the same obstruction. At $2\times2$ the characterization exists, so among $d_A,d_B\ge2$ the single-polynomial description holds only at $2\times2$.
- *Weaker versions.* The source's "sufficient" and "necessary" criteria remain available: $\det\rho^\Gamma\ge0$ type inequalities give necessary conditions in all dimensions. The refutation concerns only a characterization by a single inequality.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized; the embedding to higher dimensions was not checked in detail.

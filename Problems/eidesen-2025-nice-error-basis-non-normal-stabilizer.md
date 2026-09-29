---
slug: eidesen-2025-nice-error-basis-non-normal-stabilizer
bibkey: eidesen2025projectiveerror
doi: 10.48550/arXiv.2506.01843
url: https://arxiv.org/abs/2506.01843v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.result
---

# A nice-error-basis code whose stabilizer group is not normal

## Problem

Eidesen models quantum errors by a projective error model `(G, π)` on a
finite-dimensional Hilbert space `V`: a projectively faithful irreducible
projective representation of a finite group. For a subspace `W` with orthogonal
projection `P_W`, the logical operators and the stabilizers are

> L_{(G,π)}(W) := { x ∈ G : P_W π(x) = π(x) P_W },
> S_{(G,π)}(W) := { x ∈ G : P_W π(x) P_W ∈ 𝕋 P_W }.

After recording that no code has been found that is a Clifford code and a
weak stabilizer code but not a stabilizer code, §11 of arXiv:2506.01843v3
asks Question 11.3:

> Does there exist a Hilbert space V, a subspace W ⊂ V, and a projective error
> model (G, π) ∈ PEM_V with |G| = (dim V)^2, such that the equation
> |G| = |L_{(G,π)}(W)| · |S_{(G,π)}(W)| holds, but S_{(G,π)}(W) is not normal
> in G?

Issue #10156 fixes the readings: `V = EuclideanSpace ℂ (Fin d)`; `π` takes
values in `d × d` complex matrices acting on `V`; a projective representation
has unitary values with `π(x)π(y) = c π(xy)` for some `|c| = 1`; projective
faithfulness is the injectivity of `q ∘ π`; irreducibility means that the only
invariant subspaces are `0` and `V`; `P_W` is the orthogonal projection; the
orders are `Set.ncard`; and "not normal" means that some conjugate `g s g⁻¹`
of an element of `S_{(G,π)}(W)` lies outside it. The formal `claim` is the
negative answer, and the formal `result` refutes it.

## Motivation

The frozen declaration
`D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.result` answers
Question 11.3 affirmatively in the paper's own model. The follow-up paper
arXiv:2606.02531 assumes that the logical group is normal, citing that it was
normal in all examples studied so far; in this example the logical group is
not normal either.

## Gap

Issue #10156 preregisters the question and its literature check. arXiv lists
version 3 (2026-02-25). Semantic Scholar reports one citing paper,
arXiv:2606.02531 by the same author with Kribs and Nemec, which states the
normality assumption above and gives no example of the kind asked for.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

Proposition 8.1 of the source, with `n = 2`, gives
`G = C₂ × D_{2n} = ⟨a, b, c | a⁴ = b² = c² = [a, c] = [b, c] = 1, bab = a⁻¹⟩`
of order 16 acting on `ℂ⁴` by
`π(cᵏ bˡ aᵐ) = Cᵏ (X ⊕ X)ˡ (P ⊕ −P)ᵐ`, where `C` swaps the two coordinate
blocks, `X` is the Pauli matrix and `P = diag(1, i)`. All sixteen matrices
have entries in `{0, ±1, ±i}`. Over the Gaussian integers:

- each `π(x)` is unitary, and `π(x)π(y) = σ π(xy)` with `σ ∈ {1, −1, i, −i}`;
- distinct elements have trace-orthogonal matrices, so `π(x) = c π(y)` with
  `x ≠ y` forces `4c = 0`, which contradicts unitarity; hence `π` is
  projectively faithful;
- `4 E_{kl} = Σ_x conj(π(x)_{kl}) π(x)` for every matrix unit, so an
  invariant subspace is invariant under all matrices and is `0` or `ℂ⁴`.

For `W = ℂ u`, `u = (1, 1, 1, 1)`, the projection is
`P_W v = (Σ v_i / 4) u`. So `x ∈ L(W)` exactly when every column sum of
`π(x)` equals every row sum, and `x ∈ S(W)` exactly when the sum of all
entries of `π(x)` has absolute value 4. Both hold exactly for
`x ∈ {1, b, c, bc}`, so `|L(W)| · |S(W)| = 4 · 4 = 16 = |G| = 4²`, while
`a b a⁻¹ = b a²` does not lie in `S(W)`.

## Falsifier

The answer would change if the question required `W` to be a code of a
particular class (the question asks only for a subspace), or if the orders
`|L|` and `|S|` referred to something other than the subsets defined above.

## Evidence

Exact computation over the Gaussian integers confirms unitarity, the
projective relation for all 256 pairs, trace orthogonality for all 240
ordered pairs of distinct elements, and the matrix-unit expansion for all 16
matrix units, and gives `L(W) = S(W) = {1, b, c, bc}` and `a S(W) a⁻¹ ≠ S(W)`.
The paper's own description of this model (Proposition 8.1) states that it is
a projectively faithful irreducible projective representation; the formal
proof establishes both properties independently.

The canonical source is
`D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.lean`. Its public
declarations are `IsProjRep`, `ProjFaithful`, `IrredProj`, `IsPEM`,
`logicalOps`, `stabilizers`, `claim`, and `result`; the matrices, the group
alias and the projection matrix are private non-proposition definitions. The
frozen module state has statement identity
`sha256:2472f150ec6ec35a8693ad3f168988866b15c5081fae2f9d7c1539daf2cdac17`.
The result declaration has statement identity
`sha256:8b06b24b4e1cb4d7614cb8906611942c113dc3e9fe5329a1b5cf079f422cafd9`.
The Freeze event is
`sha256:6b0c48ae22f7c2bb349ebaa1a9d3709cb4b89e1c90f05a45127a9ed4374d3b0d`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named question, preregistered in issue #10156 before the
probe. `theorem`; resolution `refuted` for the negative answer, that is,
Question 11.3 is answered yes. The public theorem has `proof_shape: content`:
irreducibility over every invariant subspace and projective faithfulness are
derived from the finite checks, and the orthogonal projection is identified
with the averaging matrix, which reduces `L(W)` and `S(W)` to finite criteria.
Its escape witness is form (2), the public conclusion itself, and its
admission basis is `open-problem-resolution`. Its computational use is a
`certified-instance` with `basis=refutes`: the result negates the closed claim.

## ASSUMED-UNVERIFIED

Whether the example also answers Question 11.2 (a code that is a Clifford code
and a weak stabilizer code but not a stabilizer code) depends on the source's
theorem relating the two questions for `|G| = (dim V)^2`, which is not
formalized here. The bounded literature check does not establish exhaustive
worldwide novelty, priority, or the absence of an independent answer. The
Lean kernel does not authenticate the external source or its version history.

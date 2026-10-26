---
slug: shala-2024-coset-like-lattice-question-7-4
bibkey: shala2024cosetlike
doi: null
url: https://arxiv.org/abs/2112.13766v6
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.result
---

# Shala Question 7.4: weakly but not strongly coset-like atomistic lattices

## Problem

B. Shala, *The Probabilistic Zeta Function of a Finite Lattice*, arXiv:2112.13766v6 (published in Rocky Mountain Journal of Mathematics 54 (2024), 1511–1526), asks in Question 7.4: “Does there exist a weakly coset-like atomistic lattice that is not strongly coset-like? In particular, is the d-divisible partition lattice weakly coset-like?”

The negation of the first question is formalized as the universal implication that every finite atomistic weakly coset-like lattice is strongly coset-like. The settling theorem refutes that implication and answers the existence question affirmatively; Refuted refers to this universal implication.

### Statement echo

Equation (3.1) is represented by `P`, with Mathlib's incidence-algebra Möbius function and the rational ratio of join-irreducible cardinalities. Definitions 5.1 and 5.2 are represented by `StronglyCosetLike` and `WeaklyCosetLike`. The universal first question is `claim`, and the settling node proves `result : ¬ claim`.

## Motivation

The source reports weakly coset-like non-strong examples among non-atomistic lattices and asks whether an atomistic example exists. The twelve-element finite lattice in the settling result supplies such an example, answering the first sentence affirmatively.

## Gap

The family proposed in issue #19710 is for every $m \ge 4$; the source itself asks an existence question, whose second sentence concerns d-divisible partition lattices. The delivered kernel proof settles the $m=4$ instance and therefore refutes the universal implication. It does not formalize the full family or the partition-lattice sentence.

The literature screen read all six arXiv versions at Question 7.4, checked the author's later work and citation searches, and found no settlement in that searched scope. The journal version was not read, so completeness is `ASSUMED-UNVERIFIED`.

## Route

The counterexample carrier has twelve elements: bottom, top, two intermediate elements, and eight singleton atoms. Its finite order and lattice operations are checked by decision procedures. The singleton atoms are exactly the join-irreducibles and every element is a join of atoms. The computed Möbius values yield

$$P(L_4,s)=1-2^{-s}-4\,8^{-s}.$$

The element $x$ has three join-irreducibles below it while the full join-irreducible set has cardinality eight, so $3\nmid 8$. Thus the lattice is weakly coset-like and not strongly coset-like.

## Falsifier

The refutation would fail if the twelve-element carrier were not a lattice, were not atomistic, or if its zeta expression did not have the finite ordinary Dirichlet representation proved by `Counterexample.weak`. The source's d-divisible partition-lattice question and the $m>4$ family are outside this witness.

## Evidence

The kernel-checked settling declaration is `D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice.result`; its declaration proves the negation of the expanded `claim` proposition. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The numerical check is published in [the experiments repository](https://github.com/the-omega-institute/trureturing-experiments/tree/fce01566372ef403b4de3c56124fed2b489c46ac/docs/reports/shala-2021-weakly-coset-like-atomistic-lattice-question-7-4) at commit `fce01566372ef403b4de3c56124fed2b489c46ac`, file `docs/reports/shala-2021-weakly-coset-like-atomistic-lattice-question-7-4/check.py`. The command `python3 /Users/auric/trureturing-experiments/docs/reports/shala-2021-weakly-coset-like-atomistic-lattice-question-7-4/check.py` exits 0 with `RESULT PASS` for exactly $m=4,\ldots,8$; its sha256 is `f24aa976fb08078044e5b23aadea886d0b06eb42b62493e95ba5333ae52e2677`.

## Triage

| item | status | evidence |
| --- | --- | --- |
| The verified $L_4$ counterexample is a complete formal refutation of the first question. | proved | Kernel-checked declaration `result`; the witness supplies atomistic, weakly coset-like, and not strongly coset-like facts. |
| The stronger uniform family assertion for every $m\ge4$ remains the continuation F1–F5. | open | The experiment checks $m=4,\ldots,8$ only; no Lean declaration proves the uniform family. |
| The finite fallback's explicit normalization route is bind-only, while the external-problem exception supplies the admission basis. | computed; semantic classification | Inspection of the elaborated proof dependencies, finite decision checks, Möbius-recurrence applications and normalization steps supports the bind-only classification. This classification is a review judgment, not a theorem or machine admission verdict; `result` uses `open-problem-resolution (#19710; Refuted)`. |
| The d-divisible partition-lattice sentence of Question 7.4. | open | No delivered declaration addresses it. |
| Minimality of twelve elements. | open | The witness has twelve elements, but no minimality theorem is delivered. |
| Exhaustive priority or absence of a published journal settlement. | open | The literature screen is bounded and the journal version remains unread; completeness is `ASSUMED-UNVERIFIED`. |

The full-family continuation F1–F5 consists of: F1, construct the intersection-closed subset lattice on $2m+4$ elements; F2, prove atomisticity and identify its $2m$ join-irreducibles; F3, compute all upper Möbius values; F4, derive the ordinary Dirichlet formula $1-2^{-s}-m(2m)^{-s}$; F5, prove $m-1\nmid 2m$ for $m\ge4$ and conclude the separation. Each uniform assertion remains open in Lean.

### What the settlement shows

The failure mechanism is the non-divisibility $3\nmid 8$ at the element $x$, while the Möbius coefficient of $x$ vanishes because its upper interval is the chain $x<a<\top$. The source's second question about d-divisible partition lattices remains open in this delivery. The source reports a search through ten-element lattices and part of the eleven-element range; the twelve-element witness does not establish minimality. The question is posed at the end of the paper, and no earlier source theorem is asserted here to depend on its answer.

## ASSUMED-UNVERIFIED

- The journal version may answer or revise Question 7.4; the completeness and priority status of the literature screen are `ASSUMED-UNVERIFIED`.
- The family statement for all $m\ge4$ is `ASSUMED-UNVERIFIED` in Lean beyond the delivered $m=4$ refutation; the experiment's finite range does not establish a uniform theorem.

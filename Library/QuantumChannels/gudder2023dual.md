---
bibkey: gudder2023dual
authors: Stanley Gudder
year: 2023
title: Dual Quantum Instruments and Sub-observables
doi: null
url: https://arxiv.org/abs/2302.12243v1
claim: "Section 3 conjectures that an instrument's image of effects need not be a Sob effect algebra and asks whether an arbitrary Luders instrument has this property."
strata_touched:
  - D5/S3/Quantum/Measurement/LudersSubObservableClosure
license: citation-only
triage: anchor
---

# Gudder, dual quantum instruments and sub-observables

## Verified locator

Source: https://arxiv.org/abs/2302.12243v1

## Source statements

Section 2, p. 2:

> We call $a \in L(H)$ an effect if $0 \le a \le I$ where $0, I$ are the zero and identity operators, respectively.

Section 2, p. 3:

> If $\Delta \mapsto A(\Delta)$ is countably additive but $A(\Omega_A)$ need not be $I$, then $A$ is called a sub-observable.

Section 3, p. 11:

> Let $U \subseteq \operatorname{Sob}(H)$ and assume that all elements of $U$ have the same outcome set $(\Omega,\mathcal F)$. We call $U$ a Sob effect algebra if:
> (S1) there exists an observable $Z \in U$,
> (S2) if $A \in U$ then $A' = Z - A \in U$,
> (S3) if $A, B \in U$ and $A + B \in \operatorname{Sob}(H)$, then $A + B \in U$.

After Theorem 3.1, p. 11:

> If $\mathcal I \in \operatorname{In}(H)$ and $U_{\mathcal I} = \{\mathcal I_a^* : a \in \mathcal E(H)\}$, then we conjecture that $U$ need not be a Sob effect algebra.

Example 3, p. 14:

> If $\mathcal L_x(\rho) = a_x \circ \rho$ is an arbitrary Lüders instrument, we do not know whether $U_{\mathcal L}$ is a Sob effect algebra. However, in the case where $a_x$ are projections (we then call $\mathcal L$ sharp) we can show that it is.

Section 2, pp. 4–5 gives the Lüders dual action
$\mathcal L_x^*(b) = a_x^{1/2} b a_x^{1/2}$.
The finite encoding uses outcome values on `Fin n`, matrices on `Fin d → ℂ`,
and $K_x = a_x^{1/2}$. Event values are sums over their outcomes. Positive
semidefiniteness of each outcome and of the complement of the total expresses
sub-observability; equality of the total to the identity expresses observability.

## Settlement and scope

The two-outcome qubit family with $K_0=\operatorname{diag}(4/5,3/5)$ and
$K_1=\operatorname{diag}(3/5,4/5)$ gives a negative answer to the arbitrary
Lüders question and proves the existential conjecture. For
$E=\frac1{400}\begin{pmatrix}151&50\\50&151\end{pmatrix}$, both $E$ and its
complement are positive. Its output $A_x=K_xEK_x$ belongs to the effect image.
The doubled output is a sub-observable but has no effect preimage: invertibility
of $K_0$ forces the preimage $2E$, whose complement has negative quadratic form
on $(1,1)$. This does not assert failure for every unsharp instrument.

Example 3's sharp case and Theorems 3.1–3.4 keep their stated hypotheses.
In particular, Theorem 3.2 uses orthogonality of preimages, rather than ambient
Sob sum closure; the counterexample distinguishes these two notions.

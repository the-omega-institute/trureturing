---
slug: capel-costa-rico-2026-forward-geodesic-cmi-matched-marginals
bibkey: capelcostarico2026geodesic
doi: null
url: https://arxiv.org/abs/2608.15833v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/PartialTraceMutualInformation
---

# Forward geodesic CMI with matching two-body marginals

## Problem

Open questions 6 asks whether “fixing the conditioning marginal restores
continuity for some $t>0$.” Issue #32416 registers a strengthened task.
Construct one sequence of pairs $(R_n,S_n)$ of faithful three-qubit states
whose $AB$, $AC$ and $BC$ marginals agree within each pair. Both $B$ marginals
are $I/2$, and both $AC$ and both $BC$ marginals are $I/4$ at every index.
The common $AB$ marginal may vary with the index. The trace distance tends
to zero from above. For every fixed $0<t\le 1$, the value at $R_n$ minus the
value at $S_n$ tends to $\log 2$ in each forward orientation of equation (357).
Use the fixed one-sided reference $I/2$ and the actual $C$ marginal for the
two-sided quantity.
[Open questions 6](https://arxiv.org/html/2608.15833v1#S12.I1.i6) ·
[Issue #32416](https://github.com/the-omega-institute/trureturing/issues/32416)

## Motivation

The forward deficits compare the joint state with a product reference built
from its observed marginals. These pairs test whether exact agreement on
all two-qubit observations can coexist with a persistent gap at vanishing
trace distance.

## Gap

Theorem 10.16 already rules out a trace-distance modulus on faithful states
at fixed $B$ for each positive $t$. Relabel its signal and balanced classical label as $A$ and $C$,
adjoin a fixed faithful independent $B$, and apply Proposition 4.3 to
equation (357). In that reduction $AC$ is the varying two-qubit input.
The registered target additionally matches $AC$ and $AB$ within each pair,
fixes $AC$ and $BC$ for the entire sequence, and quantifies over all positive
parameters after choosing the sequence.
[Theorem 10.16](https://arxiv.org/html/2608.15833v1#S10.Thmdefinition16) ·
[Proposition 4.3](https://arxiv.org/html/2608.15833v1#S4.Thmdefinition3)

## Route

Let $u_n=1/(n+3)$ and take $S_u=(I+(1-2u)Z_AZ_B)/8$ with identity on $C$.
Add $(1-\eta)\sqrt{u(1-u)}X_AZ_BZ_C/4$ to form $R_{u,\eta}$ for
$0<\eta<1$. Tracing out any one factor cancels the added term. Mixing the
unsmoothed positive semidefinite state with $S_u$ supplies faithfulness.
Both forward deficits reduce to $D^t(R_{u,\eta}\Vert S_u)$ on the first arm
and vanish on the second arm. Whitening at $\eta=0$ gives twice a projection
of $S_u$-weight $1/2$, yielding $\log 2$ for every $0<t\le1$. At index $n$,
regularize to error below $u_n$ on $[u_n,1-u_n]$ and at $t=1$ separately.

## Falsifier

The half trace norm is $(1-\eta)\sqrt{u(1-u)}$. At every fixed $t$ in the
stated interval, the two gaps tend to a strictly positive constant while
the right-hand trace-distance modulus would tend to zero. The same
sequence thus rules out such a modulus for either forward deficit on
these faithful pairs.

## Evidence

The density and projection modules give the exact marginals, distance,
faithfulness, and singular boundary value. `CapelCostaRicoForwardGeodesicCMI`
contains the native ordered deficits and the pointwise sequence statement.
`CapelCostaRicoForwardGeodesicCommonSequence.result` is the declaration for
a single sequence across all fixed positive parameters.

## Triage

This is the theorem candidate of #32416. The preprint's rank-one mechanism
is Lemma 10.14, equation (593). The real-state masking antecedent is
Theorem 4.2 of Ambainis et al. The Belavkin–Staszewski conditional-entropy
antecedent is Proposition 6.7 of Bluhm et al. The independent reverse
question and the preprint's binary implication are documented in #32390.
[Lemma 10.14](https://arxiv.org/html/2608.15833v1#S10.Thmdefinition14) ·
[Ambainis et al., Theorem 4.2](https://doi.org/10.1109/SFCS.2000.892142) ·
[Bluhm et al., Proposition 6.7](https://arxiv.org/pdf/2208.00922v3#page=27) ·
[Issue #32390](https://github.com/the-omega-institute/trureturing/issues/32390)

## ASSUMED-UNVERIFIED

The targeted literature screen recorded in #32416 found no equivalent
statement with all the registered constraints. The scope of that search
leaves publication priority unverified.
[Issue #32416](https://github.com/the-omega-institute/trureturing/issues/32416)

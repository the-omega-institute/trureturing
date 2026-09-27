---
bibkey: "godley2023absorber"
authors: "Alfred Godley and Mădălin Guţă"
year: 2023
title: "Adaptive measurement filter: efficient strategy for optimal estimation of quantum Markov chains"
doi: "10.22331/q-2023-04-06-973"
url: "https://arxiv.org/abs/2204.08964v3"
claim: "Lemma 4.1 constructs a coherent absorber whose fixed interaction preserves a shared stationary purification and returns each noise unit to its input state."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Shared stationary initialization and coherent absorption

The primary source is Godley–Guţă, *Quantum* 7, 973 (2023),
[Lemma 4.1 and its proof](https://arxiv.org/html/2204.08964v3#S4).
The stated lemma assumes a primitive finite-dimensional quantum Markov
chain. It purifies the source's stationary state with an absorber of the
same dimension. After the source interacts with a fresh pure noise unit,
the source marginal remains stationary. The two resulting purifications
are therefore connected by a unitary on absorber and noise unit. This
single unitary restores the shared purification and the original pure
noise state at every step when the initial joint state is that purification.

The proof's purification step uses stationarity and an orthonormal
Schmidt family; it does not supply an independently prepared absorber
for arbitrary source–reference inputs. Starting from a different joint
state is a different initialization problem. Stationary or asymptotic
output statements must not be read as exact blank output from every
independent initial state.

The same construction is recalled with explicit Kraus formulas in
Girotti–Godley–Guţă, *Estimating quantum Markov chains using coherent
absorber post-processing and pattern counting estimator*, *Quantum* 9,
1835 (2025), [§3.1](https://arxiv.org/html/2408.00626v3#S3.SS1),
[DOI:10.22331/q-2025-08-27-1835](https://doi.org/10.22331/q-2025-08-27-1835).
That paper expressly refers back to Lemma 4.1 for the construction.

In §8 of [the phase-boundary volume](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md),
this established construction is an intermediate comparison in Corollary
8.4. The displayed rank-two stationary state and its purification specify
the comparison source. The new repository derivation is Theorem 8.3:
under independent pure receiver initialization, all source–reference
inputs, one fixed local unitary and exact blank output at every step,
the specified source needs receiver dimension two for one step and
2N−1 for N steps when N is at least two. The lower bound and matching
construction use actual coefficient domains and their orthogonal
isometric images. The cited absorber lemma does not optimize this
independent-initialization problem.

This source comparison attributes established ingredients and their
initialization conditions; it is not a global originality certificate.

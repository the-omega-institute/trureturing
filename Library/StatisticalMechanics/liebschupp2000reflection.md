---
bibkey: liebschupp2000reflection
authors: Elliott H. Lieb; Peter Schupp
year: 2000
title: "Singlets and reflection symmetric spin systems"
doi: 10.1016/S0378-4371(99)00521-X
url: https://arxiv.org/abs/math-ph/9910037v1
claim: "Positive-semidefinite ground coefficient matrices and singlet-ground-state existence for reflection-symmetric spin systems with antiferromagnetic crossing bonds."
strata_touched: []
license: citation-only
triage: anchor
---

## Source and actual theorem scope

Physica A 279 (2000), 378-385; arXiv first version submitted 24 October 1999. Sections 2-5 give the reflected coefficient-matrix representation, a trace inequality and the existence of a positive-semidefinite ground coefficient matrix. The paper establishes that at least one ground state is a singlet. It applies to frustrated reflected systems beyond the ordinary bipartite setting. The abstract's existence conclusion must not be quoted as an unrestricted uniqueness theorem.

The primary arXiv abstract and parsed PDF text were read. PDF screenshot retrieval failed, and no comparison here relies on an unseen figure. The earlier related paper is Lieb and Schupp, *Ground State Properties of a Fully Frustrated Quantum Spin System*, Physical Review Letters 83 (1999), 5362-5365, arXiv:math-ph/9908019, DOI 10.1103/PhysRevLett.83.5362.

## Exact correspondence to the HS4 model

[HS4 many-body exchange](../../docs/develop/theory/HIGUCHI_SUDBERY_MANY_BODY_EXCHANGE.md), Sections 11-16, uses four spin-1/2 sites in each reflected cell, identical onsite Hamiltonians h=Delta L/2 and positive matched crossing exchanges. The one-cell time-reversal matrix is R=Y tensor Y tensor Y tensor Y. The reflected full-space operator is hC+Ch-sum_i g_i sum_alpha J_i^alpha C J_i^alpha.

The positive-coefficient mechanism is inherited methodology. The chapter proves its needed specialization directly: replacing a Hermitian C by |C| does not raise the energy; the kernel of a positive ground coefficient is invariant under every single-site Pauli; all g_i>0 therefore force strict positivity. A singular-endpoint argument then proves uniqueness. This irreducibility step, the all-coupling three-dimensional ground block for uniform links, and the ordered Schmidt-spectrum and recovery formulas are explicit derivations in the chapter. Their historical priority has not been established by an exhaustive search.

Unequal positive matched couplings retain the uniqueness/full-rank proof, but do not inherit the uniform-link three-dimensional formula or its monotonicity statement. Arbitrary real crossing matrices from the earlier perturbative chapter have a different scope and are not silently included. Finite-system uniqueness gives no thermodynamic-limit gap.

## Additional source roles

Nielsen, *Conditions for a class of entanglement transformations*, Physical Review Letters 83 (1999), 436-439, arXiv:quant-ph/9811053, DOI 10.1103/PhysRevLett.83.436, supplies established majorization and LOCC context. The HS4 chapter derives its coupling-dependent majorization and fixed 47-branch recovery instrument rather than claiming a new general conversion theorem.

Kranitz and Penc, *Rigorous Anderson-type lower bounds on the ground-state energy of the pyrochlore Heisenberg antiferromagnet*, arXiv:2601.07800v1, Introduction Eqs. (1)-(3), supplies current primary-source context for cluster lower bounds. Its overlapping pyrochlore motifs differ from the chapter's disjoint four-spin cells. Only the stated cluster-bound mechanism is reused; no numerical lattice bound or phase claim is transferred.

## Verified locator

- DOI: https://doi.org/10.1016/S0378-4371(99)00521-X
- Source: https://arxiv.org/abs/math-ph/9910037v1

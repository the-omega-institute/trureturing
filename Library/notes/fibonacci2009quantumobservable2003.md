# Fibonacci fusion trees and finite quantum observable completion

Recorded 2026-09-27 for the continuation of PR #10310. Theory owner: [Fusion spin-chain QCA cut obstructions, sections 12–20](../../docs/develop/theory/FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md). This note records source attribution and the exact scope of reusable mathematics. No new Lean declaration or Scribe binding is claimed.

## Fusion-tree basis, associator and local interaction

Simon Trebst, Matthias Troyer, Zhenghan Wang and Andreas W. W. Ludwig, *A short introduction to Fibonacci anyon models*, Progress of Theoretical Physics Supplement 176, 384–407 (2008). The arXiv first submission is 19 February 2009; these dates refer to different records.

Sources: https://arxiv.org/html/0902.3275v1 and https://arxiv.org/abs/0902.3275 . Sections 2.3–2.5 define fusion paths, the F basis change, the pentagon and the additional R/braiding structure. Section 3.1 constructs the nearest-neighbor vacuum-channel interaction. The PDF pages 7 and 10 were visually checked during this continuation. Equation (2.4) in the PDF gives the chosen real F matrix. The HTML's equation numbering displays it as (4).

The theory uses the full admissibility table, all scalar F blocks, and the nontrivial block [[r,s],[s,-r]], with r=phi^-1, s=sqrt(r). It spells out all 32 pentagon boundary assignments and gives the nontrivial matrix products. This is a constructive reconstruction of known Fibonacci associator data, not a claim to a new fusion category or new pentagon solution.

The local weighted-path projectors and Temperley–Lieb relations are known structures. Attribution also belongs to Adrian Feiguin, Simon Trebst, Andreas W. W. Ludwig, Matthias Troyer, Alexei Kitaev, Zhenghan Wang and Michael H. Freedman, *Interacting anyons in topological quantum liquids: The golden chain*, Physical Review Letters 98, 160409 (2007), https://arxiv.org/abs/cond-mat/0612341 . The original abstract and the explicit treatment in Trebst et al. were consulted; no new check of the critical conformal-field-theory conclusions is claimed.

The theory's Theorem 14.1 provides its own coefficient proof for arbitrary path length on a finite symmetric zero-one adjacency graph with positive Perron weights. Projector indices are 1 <= i < n; the adjacent relation with i+1 is asserted when 1 <= i < n-1. Distant commutation requires both indices in 1,...,n-1 and their distance at least two. The empty path sector has the unique empty-matrix identities. Positive real weights, positive delta and the exact Perron equation are premises; the desired projector/TL identities are conclusions, not input fields.

## Observable-space closure

Domenico D'Alessandro, *On Quantum State Observability and Measurement*, Journal of Physics A: Mathematical and General 36, 9721–9735 (2003). Sources: https://arxiv.org/abs/quant-ph/0307127 and https://arxiv.org/pdf/quant-ph/0307127 . Section 2, the observable-space construction, its terminating linear-algebra algorithm and Theorem 1 with proof were read.

The general iterated-commutator observability method belongs to this literature. The continuation writes out a version for a nonzero finite Hilbert space C^m, m >= 1, finitely many Hermitian controls and readouts, nonnegative segment durations, arbitrary finite control words, and terminal expectation measurements on identically prepared copies. Its proof separately handles the right derivatives at zero and the finite-dimensional exponential invariant subspace. The dimension lower bound concerns independent real linear expectation coordinates on the trace-one state space; it does not exclude arbitrary discontinuous encodings.

The explicit Fibonacci P,Q specialization, three-setting inversion, and sharp deterministic noise coefficient are derived in the theory. No global priority for that particular combination is established. The tomography protocol separately assumes access to both P and Q readouts plus the P-phase pulse. Exact expectation values are not inferred from three individual random measurement outcomes.

## Additional attribution and boundaries

Strictification and global associativity coherence use Etingof, Gelaki, Nikshych and Ostrik, *Tensor Categories* (2015), sections 2.8–2.9, already recorded in [the original QCA source note](joneslim2024fusionqca.md). Checking a finite F table does not by itself finish the Lean construction of a monoidal or braided category. No R data or hexagon proof is supplied in this continuation.

The diagonal-algebra normalizer characterization of monomial unitaries is standard finite linear algebra. The theory gives an explicit proof using basis projectors and the four relative-phase test states; it does not claim a new general classification of quantum channels.

The new exact verifier checks arithmetic in Q[s]/(s^4+s^2-1), complex matrix identities, finite path sectors and a deliberately wrong associator. It does not establish positivity of a chosen real embedding, arbitrary-length theorems, von Neumann algebra properties, DHR naturality or the Jones–Lim counterexample independently. Those obligations remain separated in the theory's formalization table. No Lean compilation, independent review, CI pass or hardware experiment is claimed.

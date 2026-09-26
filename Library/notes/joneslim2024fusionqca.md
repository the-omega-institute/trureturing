# Jones–Lim fusion-chain QCA classification: source record

Recorded 2026-09-26. This is a literature/provenance note, not a Lean proof or a completed formalization atom. Research owner: [fusion-chain QCA cut-obstruction volume](../../docs/develop/theory/FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md). No Scribe binding is supplied because no new Lean declaration is supplied.

## Jones–Lim: problem and half-chain input

Corey Jones and Junhwi Lim, *An index for quantum cellular automata on fusion spin chains*, Annales Henri Poincaré 25 (2024), 4399–4422. DOI: https://doi.org/10.1007/s00023-024-01429-y . Source read: https://arxiv.org/pdf/2309.10961v2 (18 March 2024).

Precise inputs are Example 2.3 (the coherent net), Definitions 2.4–2.5 (strict QCA/FDQC), Theorem 3.9 (unique trace and finite-index half-chains), Remark 3.10 (relative commutants), Proposition 4.1 (translation index), and §6 Question 6.1. Printed pp.8–9 and p.17 were visually checked against the PDF.

For a self-dual strongly tensor-generating object X, Remark 3.10 identifies the relative commutant of two half-chains with the actual intervening window algebra End(X^n). This is substantially stronger than an equality of dimensions. Section 6 also states that the full braided autoequivalence group of Z(Fib), modulo unitary monoidal natural isomorphism, is trivial.

The paper does NOT assert that opposite translations on a product Fibonacci chain are circuits. The cut-obstruction argument in the linked volume is a separate ordinary-mathematics proof draft, not a quotation or a published theorem attributed to Jones–Lim.

## Jones: actual DHR bimodules and tensorators

Corey Jones, *DHR bimodules of quasi-local algebras and symmetric quantum cellular automata*, Quantum Topology. Sources: https://arxiv.org/abs/2304.00068 and https://arxiv.org/pdf/2304.00068 . Theorems 3.4 and 3.15 give the action on the braided category; Theorem 4.19 and Corollary 4.22 identify fusion-chain DHR with the center.

The finite-stage AF bimodule construction in §4.2, printed pp.35–36, and its tensorators/connecting maps were read. They supply the specific construction used to check product naturality in volume §5. The DHR twist includes both left/right actions via the inverse algebra automorphism AND transformation of the algebra-valued inner product. Preserving names of simple objects is not sufficient.

## Tensor-category foundation

Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych and Victor Ostrik, *Tensor Categories*, AMS Mathematical Surveys and Monographs 205 (2015). Author's authorized final version: https://math.mit.edu/~etingof/egnobookfinal.pdf . Theorem 7.16.6, printed p.168, states FPdim(Z(C)) = FPdim(C)^2. Together with factorized half-braidings and full faithfulness, this closes essential surjectivity of the center-product functor used in volume §5. Strictification and coherence are the standard material of §§2.8–2.9; Deligne tensor products are treated in §4.6.

## Later classification results: scope must be retained

Corey Jones, Kylan Schatz and Dominic J. Williamson, *Quantum Cellular Automata and Categorical Dualities of Spin Chains*, Communications in Mathematical Physics 407, 66 (2026), published 9 March 2026. Publisher source: https://link.springer.com/article/10.1007/s00220-026-05571-y . arXiv: https://arxiv.org/abs/2410.08884 (v3 dated 1 April 2025).

The publisher's Corollary 1.4 covers arbitrary finite groups in the regular representation. Its introduction still separates the general fusion-chain classification problem. An extension to a larger algebra is not itself a proof of FDQC triviality on a fixed smaller algebra.

Carolyn Zhang, *Note on quantum cellular automata and strong equivalence*, https://arxiv.org/abs/2306.03171 , first submitted 5 June 2023. Strong versus stable equivalence and extra symmetry-sensitive invariants predate this volume. No priority is claimed for that general distinction.

Ian Bunner and Corey Jones, *Universal fusion category symmetries on tensor products of infinite-dimensional Hilbert spaces*, https://arxiv.org/abs/2605.21327 , submitted 20 May 2026. Only the abstract-level model and equivalence scope were checked here. Infinite-dimensional on-site stabilization is not silently substituted for the fixed finite-window FDQC definition used in the linked proof.

## Mathematical and verification status

The volume supplies ordinary proofs of the bounded cut-localization lemma, a group action on local-unitary classes of half-chain-like subfactors, an exact Fibonacci countertranslation obstruction, and the explicit multilayer translation subgroup result. The proof depends on the published operator-algebra and DHR inputs above. Its external novelty and independent correctness review remain unsettled.

The accompanying 7302 exact-integer parameter checks test arithmetic formulas only. They are not a Lean proof, a DHR computation, an operator-algebra verification, a complete classification, or a machine-issued closure status. In the Chinese volume, references to monoidal natural isomorphisms mean tensor-compatible natural isomorphisms (张量自然同构), not monads.

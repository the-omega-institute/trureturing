---
bibkey: oszmaniec2021relational
title: Measuring relational information between quantum states, and applications
authors: Michał Oszmaniec, Daniel J. Brod, Ernesto F. Galvão
year: 2021
url: https://arxiv.org/abs/2109.10006v1
claim: Higher-degree Bargmann invariants retain relational information absent from pair overlaps and admit resource-dependent coherent cycle tests.
strata_touched: []
license: citation-only
triage: anchor
doi: 10.1088/1367-2630/ad1a27
---

# Bargmann cycle tests: source and convention boundaries

The text used here is arXiv:2109.10006v1, submitted 21 September 2021,
with a manuscript header dated 22 September 2021. The journal citation
is *New Journal of Physics* **26**, 013053 (2024). That publication metadata
does not imply that the journal version was the text inspected here.

Equation (1), PDF page 1, defines the ordered pure-state Bargmann
invariant as the cyclic product of inner products. For two states it is
the squared overlap. Figure 1 and its discussion on page 2 give a
controlled-cycle test, generalizing the SWAP test, with a control phase
gate selecting the real or imaginary part. The example on page 3 uses
Pauli X, Y and Z eigenstates with identical pair overlaps 1/2 and
three-state invariants (1+i)/4 and (1−i)/4. C129's order (Z,X,Y) is a
cyclic relabeling of that example. This is a known example and protocol,
not a new theorem or literature-novelty claim.

The sign of the imaginary-part readout requires the full convention.
C129 defines C|a,b,c⟩=|b,c,a⟩, for which the product-input expectation
is B=Tr(P₁P₂P₃), and uses the relative branch factor q=−i. Its resulting
zero probability is (1+Im B)/2. The paper's Figure 1 labels its phase
gate diag(1,i); that symbol must be read together with its cycle
convention, not transferred unchanged into C129's explicitly defined
permutation. A reversed cycle conjugates B.

The mixed-state discussion on page 4 identifies the measured invariant
with Tr(ρ₁⋯ρₘ). Appendix B, equation (B11), explicitly expresses this as
a cycle expectation on the tensor product of the input states. C129
therefore supplies the joint product promise, three preparations and
storage, a control qubit, coherent controlled permutation, calibrated
branch phase, and Born readout. Individual input vectors need no common
global-phase locking. Correlated inputs with the same marginals are
outside this product-input derivation. The paper does not derive these
resources or the Born rule from positive-kernel data. This trusted
operation calculation is not a device-independent certification; the
conclusion on page 5 lists semi-device-independent self-testing among
possible future applications.

The geometric-phase discussion on page 1 is path and convention
sensitive. C129 uses its exact Bloch scalar-triple-product formula and
the nonzero B of its witnesses; the theoretical source volume's specified
geometric-phase convention is −arg B. Neither identifies a Bloch-sphere
orientation with physical spatial chirality.

The reconstruction argument on pages 2–3 uses cycles in the nonzero
overlap graph, including cycles longer than three where required. It
does not justify replacing all such cycles by triangles in arbitrary
zero-edge networks. A nonreal invariant excludes a simultaneous real
representation preserving that invariant, not every enlarged real
simulation. Distinct cycle-test Bernoulli laws give statistical
distinguishability, not one-shot perfect identification.

This note paraphrases the primary text. No article, figure, or extended
quotation is redistributed.

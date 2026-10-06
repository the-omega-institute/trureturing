# Exact K4 signed-rotation certificate

This package checks Conjecture 1 of Ghanbari–Šámal under the explicit probability law implemented in their [pinned notebook](https://github.com/babakghanbari993/cdc-random-embeddings/blob/0d4404941894d3ef8dd9f27f1e61829bec2bcde5/notebooks/random_embedding_experiment.ipynb). The paper's phrase “random embedding” is not used to silently choose a different measure.

The uniform experiment consists of two cyclic rotations at each of the four vertices and one fair sign bit at each of the six edges. Exactly 1024 outcomes are enumerated. In the order (good singular, bad singular, regular), the totals are (2208,1728,2208), and the expected counts are (69/32,27/16,69/32). The conjectured triple is (2,2,2).

## Run

From this directory, with Python 3 and Node.js:

```sh
python3 enumerate_signed_rotations.py
node verify_ribbon_boundaries.mjs computed_certificate.json
```

The first program follows cycles of the product of two involutions on 24 flags, accounting for doubled oriented facial walks. The second was written independently using physical ribbon-boundary components. It emits the full exact JSON certificate, including all 64 fixed-rotation representatives.

Additional checks in the second program:

- Every graph edge has exactly two physical side occurrences
- The two involution-product conventions give identical category counts
- Classification agrees with the author's pair-count definition
- Vertex switches preserve edge categories; gauge orbits all have size 16
- Single-edge twists exchange good and regular status, preserving bad status
- Automorphism transport and the further graph-isomorphism quotient are checked explicitly
- The ribbon surface is connected, with Euler characteristic and orientability recorded

The labelled gauge quotient is uniform on 64 outcomes and preserves the expected counts. A further uniform distribution over unlabelled maps is a different law; its separate counts are included only to keep that distinction checkable.

The mathematical proof of the obstruction does not depend on enumeration. Relabelling invariance and edge transitivity force a common edge-type marginal. Its denominator is a power of two, so it cannot equal one third.

See the [theory](../../develop/theory/FACIAL_RANDOM_EMBEDDING_DYADIC_OBSTRUCTION.md) for the generic finite-symmetry theorem, full hypotheses, K4 application, gauge proof, and corrected good/regular expectation identity.

No Lean kernel verification or whole-repository check is represented by these scripts. They contain no copied notebook implementation and require no Sage installation, network access, or random sampling.

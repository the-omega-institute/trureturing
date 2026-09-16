# Pending insertion into QUANTUM-REALITY.md

This directory stages research text for the existing volume `docs/develop/theory/QUANTUM-REALITY.md`. It is not a replacement theory volume. The canonical theory file has NOT been changed by this branch; applying the cumulative insertion is still required before this can be considered an integrated theory update.

## Snapshot and source preservation

- Reviewed dev commit: `630aac657042e88ca8bb69ee272cfcc6eb070bb8`.
- Canonical theory blob: `09df8199fd2cd36a90a8df1cd3dfd6cbe3962b32`, 998827 bytes.
- Insertion location: immediately after the earlier ST0-ST9 insertion and before `# 钟记录、径向俘获与视界红移`, preserving original chapter numbering.
- The preceding ST0-ST9 insertion remains in the conversation delivery bundle. The cumulative local bundle contains its exact 26259-byte original plus this continuation, cumulative and incremental patches, a guarded application script, and complete check scripts/results.
- The available connector can replace complete text files but exposes no partial-file patch application. A complete runtime copy of the 998827-byte target could not be obtained. No truncated read was used to overwrite it.
- This staged continuation was read back from GitHub and its blob `1b240ad7a8dfcd867358b1df631e6f381b0daf82` matches the locally checked 25065-byte text exactly.

## Mathematical content

ST10-ST18 gives ordinary finite-dimensional proofs of the Schur energy-derivative norm identity; normalized pole residue and Hellmann-Feynman response; invariant-graph isometric encoding; exact Kraus leakage and adaptive-record closure; Riccati-residual error bounds including an inert reference system; graph quantum geometry and Frobenius spectral-gap bounds; moving-subspace connection and counted transitionless control; a same-frozen-response/different-holonomy two-state counterexample; and the ambient-plus-normal-curvature identity.

The positive Hilbert space assumption means a positive-inner-product physical state space, not a claim about a Gaussian state or the full indefinite ghost space. Connecting these statements to a specified string model requires that model's physical quotient, inner product, source/instrument definitions and parameter-space connection. BV consistency alone does not imply the instrument closure hypothesis. Parameter-space curvature is not identified with Einstein curvature.

## Checks actually run

The local `check_ST10_ST18.py` completed 1762 numerical assertions in 36 families, using seed 20260917, 48 spectral/graph cases and 32 two-parameter geometry cases. It also checked three exact symbolic identities. Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0 and SymPy 1.14.0 were used.

Selected maximum absolute residuals:

- Graph quantum tensor identity: 4.760477938058707e-17.
- Flat curvature identity (finite-difference connection derivative): 1.6725900559948886e-11.
- Ambient curvature identity: 3.756511733806885e-11.
- Adaptive branch intertwining: below the script's 2e-9 bound.
- Closed-loop phase discretization: 2.2040098124342933e-7, within the 1e-6 grid tolerance.
- Explicit full transitionless evolution: 7.873487133216864e-11.

Detected omission witnesses:

- Dropping the normalization in the golden two-state hidden response changes it by 0.10557280900008414.
- Ignoring a Pauli-X instrument's leakage loses total probability 1.
- Omitting ambient curvature produces a tested discrepancy up to 0.28189027127649186.
- Omitting the loop connection changes the phase factor by 1.5264824504491104.

Cumulative and incremental unified patches were checked and applied on an exact insertion-context fixture. The guarded application logic was checked for a pristine fixture, an ST0-ST9-present fixture, idempotence, and five malformed/drifted inputs. These are CONTEXT-FIXTURE tests, not application to the complete original volume. The full scripts and JSON receipts are in the conversation's downloadable cumulative bundle; this README is a summary, not a substitute for those scripts.

## Admission boundary

No Lean declarations or Scribe records were added, no Lean compilation was run, no CI or workflow was edited, and no merge or auto-merge was performed. Existing general mathematics is attributed in the manuscript; no global novelty claim is made. This branch should remain a draft until the insertion has been applied to the complete original theory file and its preservation has been verified.

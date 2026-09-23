# Quantum recovery finite checks

These programs test the finite-dimensional constructions used in the
`ST19-ST42` continuation of
`docs/develop/theory/QUANTUM-REALITY.md`.

`check_ST19_ST26.py` checks instrument completion, adaptive record bounds,
compressed commutators, bundle-chart loss, curvature decomposition, and the
associated sharp examples. It uses deterministic seed `2026091703` and writes
the requested JSON result file.

`verify_constructive_closure.py` checks finite Kraus recovery, matrix-unit
decoding, reference-entangled inputs, entropy and relative-entropy identities,
transport generators, lifted instruments, explicit time evolution, and sphere
support examples. It uses deterministic seed `20260923` and writes
`constructive_closure_checks.json` beside the program.

Both programs require Python, NumPy, and SciPy; the first also requires SymPy.
Their floating-point tolerances and exact symbolic checks are recorded in the
generated JSON. These are error probes and counterexample checks, not proofs of
the universal statements and not Lean kernel verification.

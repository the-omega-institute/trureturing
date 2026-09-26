# Finite Verification Data

The mathematical statements are in `docs/develop/theory/QUANTUM-REALITY.md`, ST0-ST42. This directory retains independent finite probes of selected matrix, instrument, and transport identities.

- `check_ST19_ST26.py` tests finite examples and exact symbolic identities for leakage, protocol error, and bundle geometry. `verification_ST26_summary.json` records 2,635 assertions in 38 families with seed 2026091703.
- `verify_constructive_closure.py` probes reversible and noncorrectable channels, recovery and decoder formulas, matrix units, lifted instruments, transport, and sphere support examples. It uses seed 20260923 and requires NumPy and SciPy.

The floating-point tolerances in these programs distinguish candidate identities and counterexamples. They do not establish universal statements or replace Lean kernel verification.

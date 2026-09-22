# Observer recovery and geometric transport: current research status

This directory contains the ST0-ST42 mathematical continuations prepared for the existing `docs/develop/theory/QUANTUM-REALITY.md`. That large canonical volume remains unchanged by this draft PR. These staged texts must not be reported as already integrated into it. The older ST0-ST26 integration script covers only its original three chunks; it does not incorporate ST27-ST42 and is not an admission tool.

## Actual existing-theory change

`docs/develop/theory/ENTROPY-INFO-PRIMES-O5.md` has been genuinely extended with section 10. Its original 14151 bytes, blob `04f5856ba0492d6dd221c01cbdd0f306a7600217`, are an exact prefix of the current 20440-byte file, blob `64ce864aeaf1b718293518a28662fa700f3ce95e`. The new section proves explicit syndrome recovery, entropy addition with preservation of relative distinguishability, the exact recovery criterion, and counterexamples for discarded labels and coherent implementation data. It directly elaborates the existing volume's information-movement discussion. Earlier historical claims in that volume have not thereby acquired a new validation status.

## Constructive mathematical scope

ST34-ST42 supplies an inverse-square-root recovery candidate for every finite Kraus channel and proves its equivalence to exact recoverability through scalar Kraus products. It then constructs the logical matrix algebra, global decoder Kraus operators, a smooth ancillary factor bundle, a Chern-number divisibility obstruction, a matrix-unit transport generator, and the Hamiltonian/instruments realizing prescribed finite logical protocols.

All this takes place in finite positive-inner-product quantum theory. The algebra of all effects, Born probabilities, CPTP maps and specified experimental permissions are explicit starting data. Exact channel equality is not decided by a floating-point tolerance. The constructed active Hamiltonian is not asserted to arise for free in a particular physical device or to satisfy an Einstein field equation. String BRST/BV and infinite-dimensional causal-field constructions have not been completed here.

The new ST34-ST42 manuscript is stored as `QUANTUM-REALITY.ST34-ST42.append.md`; its read-back blob is `81a38378a40375a67ae465adb11512185396cb2b`, matching the locally checked 21596-byte text. Standard recovery classification and transpose-channel mechanisms are attributed to Knill-Laflamme, Nayak-Sen and Barnum-Knill. The coherent-control limitation is attributed to Araújo and collaborators. Four corresponding Library notes are included.

## Candidate formal sources now actually present remotely

- `D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.lean`: five public matrix recovery and transport statements.
- `D5/S3/Quantum/Recovery/TwoSyndromePhaseDefect.lean`: three public exact complex-phase statements.

Each has a matching `Blueprint/.../*.scribe.cs` using `StatementSource.FromLean()`. These files were first pushed in commit `cc3bdf648bcd5478fc13f62970335dfd45de6ce4`. They are candidate proof sources, not compiled or frozen declarations. The full recovery classification, channel norms, bundle topology and differential transport theorems are not claimed as covered by these eight declarations.

No Lean/lake or Scribe compilation has been run. No new axiom, freeze event, atom coverage status or admission receipt is asserted. No workflow/CI file was modified or manually triggered; no merge or auto-merge was performed.

## Reproducible finite verification

Run `python verify_constructive_closure.py` with NumPy and SciPy. The executed script completed 2918 numerical assertions in 40 families with seed 20260923, Python 3.13.5, NumPy 2.3.5 and SciPy 1.17.0. It checks random reversible channels, zero branches, reference-entangled inputs, two independent decoder formulas, Choi-square-root Kraus reconstruction, matrix-unit transport, lifted instruments, the coupled time-dependent evolution formula and both sphere support examples. A noncorrectable amplitude-damping channel is retained as a negative control.

These are finite numerical error probes, not directed interval certificates, independent review or a substitute for the ordinary proofs. The local output JSON is included in the conversation delivery; the script regenerates it next to itself. Prior ST10-ST26 checks and fixture-only insertion history are retained in earlier commits and their original scripts. No full-file application of the staged QUANTUM-REALITY continuations is claimed.

The implementation used a single assistant with direct tools and no independent reviewer. The research manuscripts, existing entropy-volume update, Library notes and candidate Lean/Scribe sources are actual remote changes. The remaining distinction between these changes and integration of the large canonical volume is deliberate and must remain visible until integration is performed.

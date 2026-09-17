# ST0-ST26: theory insertion, proof status and reproducible checks

This directory supports the existing `docs/develop/theory/QUANTUM-REALITY.md`. The canonical volume is **still unchanged** by this draft PR. The directory now contains all three prerequisite insertions and a guarded integration script. Merging only these staged files does not complete integration into the theory volume.

## Current scope

ST0-ST9 connects string effective theory, gauge-compatible reduction, transferred sources, duality and observer reconstruction. ST10-ST18 adds Born-normalized spectral reduction, invariant graph encoding, exact instrument closure and local parameter geometry. ST19-ST26 adds outcome-preserving nonzero-leakage completion, reference-safe sharp error bounds, adaptive composition and a coherent accumulation counterexample; projection-algebra defects; a fixed-rank global-chart obstruction; and ambient-corrected topological/control bounds with an exactly saturating sphere family.

The current ST19-ST26 supplement is 510 lines, 22793 bytes, with 16 numbered theorem/corollary/example headings. It contains ordinary proofs, not new compiled Lean declarations. Existing mathematics is attributed, including the sharpened gentle-measurement function of Regula-Lami-Datta (2026), sub-bundle geometry of Oancea-Mieling-Palumbo (2026), and the established quantum-metric topology bounds of Mera-Ozawa (2021). Palumbo's August 2026 extended-object Hall model is cited with its assumed gapped/isotropic sector; no actual full string vacuum is claimed.

All norm and channel bounds use positive Hilbert spaces. Parameter-space curvature is not identified with an Einstein tensor. Infinite string spectra, unbounded fields, BRST/BV consistency and spacetime causal propagation retain separate obligations.

## Original preservation and integration

Reviewed dev: `11036b0baf142c8e6535e61f29d2cae83ecf7bba`. The canonical file still has blob `09df8199fd2cd36a90a8df1cd3dfd6cbe3962b32`, 998827 bytes. The insertion anchor is `# 钟记录、径向俘获与视界红移`, between chapters 30 and 31. Original chapter numbering and bytes are preserved by the guarded transformation.

A complete runtime copy of the canonical volume was not obtained. The available connected writer replaces whole files and does not apply a partial patch. No truncated response was used to replace the original. Keep this PR draft until the complete original has been updated and checked.

The three insertion sources are now present together. Their canonical cumulative content is 74117 bytes with SHA-256 `a6b0e89073dc2ec00f472fd46e27423dec40ca135cea2b7949d8688293cfc862`. The remotely retained ST0-ST9 copy omits only the original final blank line. The application script recognizes exactly that blob (`910ca3fcf62ec35c2cd01eb4f623ff7ba57c40af`) and restores that one newline before checking the original insertion SHA-256. It accepts no other content change.

From a complete local research-branch checkout, run:

```sh
python docs/reports/string-observer-born-geometry-20260917/apply_ST0_ST26.py --repo .
# Only after reviewing the dry-run report:
python docs/reports/string-observer-born-geometry-20260917/apply_ST0_ST26.py --repo . --write
```

The script verifies the entire original blob after removing any exact already-present prefix. It rejects source drift, partial/duplicate/reordered content, the wrong insertion position, dirty target files, protected branches and a concurrently changed target. It does not commit, push or run CI.

## Checks actually run this round

`check_ST19_ST26.py` completed **2635 numerical/symbolic assertions in 38 families**, seed 2026091703, using Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0 and SymPy 1.14.0. The count includes four exact symbolic identities. Reproduce with:

```sh
python check_ST19_ST26.py --out checks_ST19_ST26.json
```

The check source SHA-256 is `0d3296c71cd7a88303be6719478566b412f02c552b07930acb15be4a35645955`; its remotely read blob is `bf2b24412aff233df3939f202bc5efefbadf5076`, matching the locally executed source. `verification_ST26_summary.json` records selected residuals and counterexamples. The downloadable cumulative delivery includes the full output JSON. A zero inequality residual means no sampled violation, not a proof by testing.

The coherent witness at N=1024 has calibrated per-step leakage about 2.3531e-6, their naive probability sum about 0.00240957, and final distinguishability one. The correct bound is compatible with this result. In the ambient sphere family, kappa=-1/2 has zero normal mixing and Chern number -1; the ambient flux is -2 pi, exactly accounting for the difference.

`check_insertion_ST26.py` completed 17 checks, including all four existing-prefix states, idempotence/preservation, corrupt-input rejections, and actual `git apply` on exact-context fixtures. These tests **do not constitute application to the complete original volume**. Running that script regenerates cumulative/incremental patches and the cumulative insertion; it performs no network call or remote mutation.

## Delivery status

The new manuscript blob `f36f20d89fb46d33d3d0ea2dac8258ac82f8c31e` was read back and matches the locally checked text. The previous ST10-ST18 blob remains `1b240ad7a8dfcd867358b1df631e6f381b0daf82`.

No Lean or Scribe source was added, no Lean compilation was run, no workflow/CI file was changed, and no merge or auto-merge was performed. Prior ST10-ST18 check claims are retained in the earlier README at commit `761dfa4c299bf7d70439018a6811843a3a7a26dd`; this round's numbers refer only to the new retained scripts.

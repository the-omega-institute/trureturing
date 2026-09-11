# I52 bounded navigation repair verification

This record verifies the current S20 whole-section contract against the complete original report bytes. The report used was `docs/reports/quantized-gh/balanced-prime-237-all-slabs-0910.md`, identity `bytes=58191`, `LF=792`, `terminal_LF=true`, SHA256 `29d239c8f3f0bb3cde6bc8fb780360856955846ecc8c48ffe1f7f16b218a73c6`. No fixture or rewritten report was used.

## Reproducible recipe

From the repository root, copy the complete Python blocks from the current S19 and S20 READMEs to `/tmp/s19_evidence.py` and `/tmp/s20_evidence.py`. The following fixed text script is `/tmp/verify_i52.py`; it reads the report bytes, tracks fenced code blocks, records every heading with its byte offset and level, and computes each expected section as the interval ending at the next heading whose level is no greater than the starting level. It then calls the real `S20Evidence.section(anchor)` for all 33 current anchors, compares returned bytes and identities to the independently computed intervals, checks descendant containment, and checks the three repaired regressions.

```text
python3 -B /tmp/verify_i52.py
```

Actual result (exit 0):

```text
{'headings': 33, 'anchors_checked': 33, 'descendant_intervals_checked': 33, 'regressions': {'balanced-237-whole-box-all-real-slab-fixed-certificate-s20--c43': 58191, 'c85--s20-section-31-archival-representation-i29-2026-09-10': 18855, 'verbatim-relocated-source-payloads': 8081}, 'independent_hierarchy': 'fence-aware next heading level <= start', 'result': 'PASS'}
```

The three prior declared slices were 2394, 3328, and 40 bytes. The fixed results are respectively `[0,58191)`, `[39336,58191)`, and `[42664,50745)`, with returned sizes 58191, 18855, and 8081 bytes. Child Archive headings are included in the third and second repaired sections, and all descendants are contained by their computed parent intervals.

## Public checks and preservation

After the edit, the S20 public `verify()` implementation was read in full and run once with Python `-B`. It exited 0 and returned `versions=14`, `whole_units=282`, `structural_regions=1`, `own_addresses=22`, `report_sections=33`. The inherited S23 public `verify()` was also run once because the changed S20 navigation is consumed by the composed S23 evidence; it exited 0 and returned `versions=20`, `aliases=9`, `whole_units=345`, `structural_regions=4`, source `bytes=440285`, `LF=8740`, SHA256 `75e41aeca17b0343d6ecb5cb16e6cee13d7a64f8f798556921351e855c3e6af9`.

The complete source and report identities above compare byte-for-byte with the registered input capture. The public Python API blocks for S19, S20, S21, S22, and S23 remain byte-identical to their pre-I52 references (S19/S21/S22 against HEAD; S20/S23 against the explicit I52 capture). The seven `before-I52/` files are exact byte copies of their registered sources, including final LF and opaque `log_ref` strings.

## Scope and omissions

This bounded check does not rerun unrelated top-level checks, canonical producers, ingestion, Lean, mathematical programs, historical replays, or opaque/private diagnostics. The original R1 architecture `approve`, quality `comment`, and tests `reject` verdicts remain separately preserved. The quality worker's full source review remains unresolved: its prior envelope records zero source bytes read and establishes no source defect. Fresh complete reviews and caller-owned sealing, required gates, and delivery remain outstanding.

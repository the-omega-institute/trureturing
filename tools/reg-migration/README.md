# Registration migration generator

This directory contains the P2b migration planner and renderer.  The planner
reads source spans and a compiled `raw-lean-report.json` snapshot, then emits
the fixed `LeanInformationAudit.Contract` declarations used by the next
interface generation.  It never imports a `Reg` module, invokes a recorder
command, or calls the judge.  A Lean companion (`ExtractInputs.lean`) is
provided for producing a JSON snapshot from an explicitly selected import
driver; the Python planner treats that snapshot as data.

The command line entry point is:

```text
python3 tools/reg-migration/generate.py plan \
  --repo . --report .lake/build/stratalint/raw-lean-report.json \
  --mapping /path/to/root-kind-mapping.json --output /tmp/p2b
```

`plan` validates the complete source/report bijection before rendering.  It
writes only to the requested output directory.  `--apply` is deliberately
separate and writes generated files to an explicit target tree after all
checks pass.  Rendering is deterministic: paths and records are sorted,
input SHA256 values are recorded, and no clock, host path, or random value is
included in a declaration.

The renderer supports legacy, forward, witness, source, finite-source and
occurrence registrations, template enrollment, root catalogs, seals and the
three notation declarations that are part of the migration inventory.  Every
unsupported or incomplete input is a named failure; failures prevent target
tree writes.

# Interface remark 3.5 exhaustive-certificate atom: open report

## Disposition

`open`; no formalization deposit.

The selected atom asserts a concrete exhaustive machine-verification result,
but the repository does not contain the asserted 17-case carrier/table, the
checked formula column, the enumeration script, its seed, or a certificate
artifact. The atom calls the target only "the formula"; the adjacent theorem
3.4 displays an escape count/probability, while the supplied example
`2107/19683` is the complementary non-escape proportion. A faithful Lean
declaration cannot be selected without resolving that ambiguity and
fabricating missing certificate data.

The report therefore stops at the statement-echo/library-search/fidelity
boundary required by `skills/codex-formalize/SKILL.md`. No file under
`Meta/Digestion/**`, `Golden/Frozen/**`, or
`Meta/Digestion/formalizations/**` was edited. No generated projection, Lean,
Blueprint, or Scribe artifact was edited.

## Environment and base

The assigned isolated lane was checked directly:

```text
pwd -P = /Users/mstudio3/trureturing-diag-month-r2-a
git rev-parse --show-toplevel = /Users/mstudio3/trureturing-diag-month-r2-a
branch = harness/diag-month-r2-a
```

The branch was fast-forwarded before diagnosis:

```sh
git merge --no-edit origin/dev
```

This exited `0`. The synchronized identities were:

```text
HEAD = e3d4b21439a18c1f143385a6f6f55a091cc4c06e
origin/dev = e3d4b21439a18c1f143385a6f6f55a091cc4c06e
git merge-base origin/dev HEAD = e3d4b21439a18c1f143385a6f6f55a091cc4c06e
```

The required ancestry check was run bare:

```sh
git merge-base --is-ancestor origin/dev HEAD
```

It exited `0`. The worktree was clean before this report was created. The live
PATH declaration was read from `tools/scripts/local-harness-gate.sh`; it
includes `/usr/sbin` as required by the formalization workflow.

## Authoritative atom

Exactly one atom was selected, the unsuffixed occurrence/1 ID:

```text
pzg-residual-3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570
```

The authoritative read was:

```sh
make show-atom \
  ATOM_ID=pzg-residual-3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570
```

It exited `0` and reported:

```text
SHOW_ATOM atom_id=pzg-residual-3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570 source_id=interface-v1 source_path=docs/develop/theory/INTERFACE_PAPER.md atomizer=pzg-v1 ast_path=remark/3.5/occurrence/1
HASH_VERIFY raw_sha256=sha256:3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570 normalized_sha256=sha256:3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570 cas_ref=sha256:3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570 status=match
```

The complete authoritative raw text returned by that command is:

```text
**注 3.5(检验)。** 公式经穷举验证于 (n, A) ∈ {2,3,4} × {2,3} 之全部 17 组 (k)-层(附录 A.1),无一例外;含 n = 3, A = 3, k = 1 之 2107/19683 等。[机验·穷举恰合]
```

The normalized text was byte-for-byte the same text, and the raw,
normalized, and CAS hashes all matched.

## Duplicate occurrence

The source repeats the same prose at `remark/3.5/occurrence/2`. Its atom ID is:

```text
pzg-residual-3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570-cee046030d12bac964d75a8b951151a6d378d0c240964e2a8987aa2b371adef7
```

The exact command was:

```sh
make show-atom \
  ATOM_ID=pzg-residual-3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570-cee046030d12bac964d75a8b951151a6d378d0c240964e2a8987aa2b371adef7
```

It exited `0`, reported `ast_path=remark/3.5/occurrence/2`, and reported the
same raw SHA-256, normalized SHA-256, CAS reference, and raw text. This is a
duplicate source occurrence, not an independent certificate and not coverage
of the selected occurrence/1 atom.

## Clause-level statement echo

| Authoritative clause | Required faithful counterpart | Evidence and status |
|---|---|---|
| `公式` ("the formula") | An exact named formula or exact output column being checked | **Ambiguous.** The atom does not identify it internally. The adjacent theorem 3.4 displays both an escape count/probability and a complementary non-escape count. |
| `(n, A) in {2,3,4} x {2,3}` | Finite binders/carrier restricted to the six named `(n,A)` pairs | The pair domain is stated, but the per-pair `k` domain is not. |
| `全部 17 组 (k)-层` | An addressable 17-row list/table, including each admissibility rule and the checked expected/actual value | **Missing.** No 17-row carrier or admissibility rule is present in the atom or repository evidence. |
| `附录 A.1` | The actual Appendix A.1 table as a tracked, inspectable artifact | **Missing.** The source has only a one-line appendix summary saying that the table is on file. |
| `无一例外` | A universal result over exactly those 17 rows | **Blocked.** The quantified finite carrier and row results are absent. |
| `n=3, A=3, k=1` | One identified row in that carrier | The parameters are explicit, but the output's meaning is not. |
| `2107/19683` | A checked value in a named result column | The arithmetic value is derivable as the **non-escape** proportion; it is not theorem 3.4's displayed escape probability. |
| `[机验·穷举恰合]` | Reproducible script/executable, explicit seed or deterministic no-seed declaration, inputs, output/table, and verification receipt | **Missing.** No such artifact was found. |

The dropped-or-weakened set is nonempty: formula identity, exact 17-case
carrier, every row result, Appendix A.1 table, script, seed/determinism record,
and machine-verification provenance are all unavailable. Statement echo
therefore fails before any Lean declaration can be written.

The number 17 cannot safely reconstruct the missing `k` carrier. There are six
stated `(n,A)` pairs. Taking the obvious positive fixed-point-count range
`1 <= k <= n` gives `2 * (2 + 3 + 4) = 18` rows; taking `0 <= k <= n` gives
`2 * (3 + 4 + 5) = 24` rows. The source does not say which row is excluded or
give another admissibility rule. Choosing one would fabricate certificate
data.

## Current-tree and history searches

The exact current report/receipt search was:

```sh
rg -n -F \
  'pzg-residual-3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570' \
  docs/devloop/reports Meta/Digestion/formalizations
```

It produced no output and exited `1`.

The exact scoped all-ref atom search was:

```sh
git log --all --oneline \
  -S'pzg-residual-3033ac6f443ddb6b04e0192ca76446823358795aa0f6394b34065c5271e5d570' \
  -- D5 Meta/Digestion/formalizations docs/devloop/reports
```

It produced no output and exited `0`; `git log` uses exit `0` for an empty
match set. The unscoped history search found only ingestion/infrastructure
history:

```text
5f34ebbd fix(digestion): 再次删除被坏合并恢复的 Meta/BACKFILL.yaml
0f0edb92 Migrate digestion backfill to per-atom directories
a5f4de09 feat(digestion): register the interface-v1 theory source
```

Those commits do not provide a D5 declaration, formalization receipt, report,
or certificate artifact.

The exact current certificate-artifact search was:

```sh
rg -n '2107/19683|全部 17 组|17 组.*全表|脚本与种子|恰式穷举' \
  D5 Evidence Meta/Digestion/formalizations docs/devloop/reports
```

It produced no output and exited `1`.

The exact scoped all-ref searches were:

```sh
git log --all --oneline -S'2107/19683' \
  -- D5 Evidence Meta/Digestion/formalizations docs/devloop/reports

git log --all --oneline -S'全部 17 组' \
  -- D5 Evidence Meta/Digestion/formalizations docs/devloop/reports
```

Both produced no output and exited `0`.

The source-only search was:

```sh
rg -n '2107/19683|全部 17 组|17组全表|脚本与种子|附录 A\.1|附录A\.1' \
  docs/develop/theory/INTERFACE_PAPER.md
```

It exited `0` and found only:

```text
36:  a general assertion that raw scripts and seeds accompany Appendix A
97:  remark 3.5 occurrence/1
115: remark 3.5 occurrence/2
232: the one-line A.1 summary claiming a 17-row table, script, and seed are on file
```

Thus the repository has assertions that the archive exists, but no actual
Appendix A.1 table, enumeration script, seed, result file, or verification
receipt in the formal/evidence/receipt/report stores.

## Existing formula machinery

The relevant D5 search was:

```sh
rg -n \
  'theorem escaped_listing_card|def escapeProbability|theorem escapeProbability|escaped_listing_card|escapeProbability' \
  D5/S0/Diagonal/EscapeCount.lean \
  D5/S0/Asymptotics/FixedPointFreeEscapeProbability.lean
```

It found:

```text
D5/S0/Diagonal/EscapeCount.lean:140:theorem escaped_listing_card ...
D5/S0/Asymptotics/FixedPointFreeEscapeProbability.lean:20:noncomputable def escapeProbability ...
```

The exact frozen count theorem is:

```lean
theorem escaped_listing_card [Fintype A] [Fintype Y] (f : Y -> Y) :
    Nat.card {g : A -> A -> Y // IsEscaped f g} =
      (Fintype.card Y ^ Fintype.card A - Nat.card {y : Y // f y = y}) ^
        Fintype.card A
```

This is the repository counterpart of the adjacent theorem 3.4 mechanism:

```text
N_esc(n,A,k) = (n^A-k)^A
P_esc = (1-k/n^A)^A
```

For the explicit source parameters, shell integer arithmetic gives:

```text
n^A = 27
N_esc = (27 - 1)^3 = 17576
total = 3^(3*3) = 19683
N_non = 19683 - 17576 = 2107
```

Consequently, theorem 3.4's escape probability is `17576/19683`, whereas
`2107/19683` is the complementary capture/non-escape proportion. The atom's
unnamed "formula" could refer to a non-escape column derived in theorem 3.4's
proof, but the absent Appendix A.1 is required to establish that meaning.

General formula machinery is not a substitute for the asserted computation
certificate. `escaped_listing_card` proves a symbolic cardinality identity;
`escapeProbability` normalizes the escaped-listing cardinality; related frozen
modules prove monotonicity and asymptotic consequences. None records the exact
17 inputs, expected and observed row values, the exhaustive execution, or its
script/seed provenance.

## Failed approaches and fabrication boundary

- **Bind directly to `escaped_listing_card`: rejected.** It captures the
  symbolic mechanism but not the claimed historical exhaustive execution,
  exact case carrier, table, or reproducibility data.
- **Prove only the `2107/19683` arithmetic instance: rejected.** One instance
  does not establish all 17 rows, and it would silently choose the non-escape
  interpretation despite the adjacent displayed formula being `P_esc`.
- **Reconstruct the 17 rows from `(n,A)` and a guessed `k` range: rejected.**
  The obvious ranges produce 18 or 24 rows, and the missing exclusion rule
  cannot be inferred from the atom.
- **Create a 17-row table, script, or seed: prohibited.** Those are concrete
  certificate data that the source claims exists but does not supply;
  inventing them violates the formalization skill's fabrication ban.
- **Use occurrence/2 as coverage: rejected.** It is identical source prose
  with the same CAS text, not an independent formal declaration or evidence
  artifact.
- **Encode the historical result as a bare proposition saying that a check
  occurred: rejected.** Such a declaration would have no independently
  addressable certificate object and would merely rename the prose.

The honest unlock condition is a tracked Appendix A.1 artifact that specifies
the formula/result column, all 17 `(n,A,k)` rows, expected results, executable
enumeration method, deterministic seed policy, and machine-verifiable output.
Until then, the fabrication ban forces `open`.

## Fidelity and non-hollowness gate

- **Conclusion substance:** the source asserts a nontrivial universal finite
  computation and a machine-verification outcome. No faithful declaration or
  certificate was produced.
- **Hypothesis satisfiability:** blocked. The exact 17-case hypothesis/carrier
  is missing, so no Lean term can witness the intended quantified input set.
- **Domain inhabitance:** individual finite `n`, `A`, and `k` examples exist,
  but no term can inhabit the claimed complete case-table type because that
  type's rows and admissibility rule are unspecified.
- **Proof substance:** `escaped_listing_card` is a substantive general theorem,
  but it does not prove that the stated exhaustive run was performed or that
  every missing table row matched.
- **Deposit substance:** no new definition or theorem earns a freeze here.
  Adding a proposition without the certificate would freeze a paraphrase, not
  the claimed evidence.
- **Duplicate search:** complete. The selected atom is absent from current
  reports/receipts and scoped all-ref history; occurrence/2 is duplicate prose,
  not coverage.
- **Clause fidelity:** failed for formula identity, the 17-case carrier,
  Appendix A.1 table, complete row results, script, seed, and execution
  provenance. Any deposit would drop or invent clauses.
- **Rendered-statement fidelity:** not run because no Lean declaration or
  Scribe mirror was created.

No item above is hidden behind an `ASSUMED-UNVERIFIED` factual claim: the
repository searches and arithmetic were run. The missing certificate data is
the measured blocker, not an assumed premise.

## Grader-trap audit

- **Witness vs universal:** the `2107/19683` witness cannot discharge the
  universal "all 17 rows, without exception" claim.
- **Instance vs general:** the `(3,3,1)` instance cannot replace the full
  finite case table.
- **Conditional vs unconditional:** values derived conditional on theorem
  3.4 do not establish the unconditional historical claim that an exhaustive
  machine check ran and matched.
- **Pointwise vs operator:** not applicable; the atom is a finite certificate
  claim, not an operator identity. Its analogous trap is rowwise versus
  table-wide coverage, which remains open.
- **Proof-internal vs addressable:** arithmetic inside a proof would not create
  an addressable Appendix A.1 table, script, seed, or execution receipt.
- **Multi-clause residue:** no certificate clause may be dropped: formula
  identity, exact carrier, all-row match, table, script, seed, and provenance
  remain jointly required.
- **Mechanism vs outcome:** theorem 3.4 and `escaped_listing_card` establish the
  mechanism; the claimed enumeration outcome and its provenance are separate
  and absent.

## Unreached workflow steps

The workflow stopped before artifact construction because clause fidelity
failed and the fabrication ban applies. Accordingly, these commands were not
run:

```text
lake build <new-module>       # no Lean module exists
make lean                    # no Lean source changed
make emit                    # no Scribe source exists
make deposit ATOM_ID=... GID=...
make preflight
make cover ATOM_ID=... GID=...
git push ...
make pr-open ...
```

`make deposit`, `make preflight`, and `make cover` require a fidelity-complete
formal artifact and GID; neither exists. Push and PR opening were also
explicitly withheld pending dispatcher review. The local full admission gate
was not used as a substitute for missing mathematical evidence; report-only
verification consists of the canonical .NET/selftest doors plus Git diff and
scope checks recorded at collection.

## Ledger balance

The only intended tracked change is this report under
`docs/devloop/reports/`. There are no changes to `Meta/Digestion/**`,
`Golden/Frozen/**`, formalization receipts, `Generated/**`, `D5/**`,
`Blueprint/**`, or Scribe sources. The selected digestion atom remains
untouched for dispatcher-owned disposition.

Report-only verification after writing this file:

```text
git diff --check: exit 0
make dotnet: exit 0 (0 warnings, 0 errors)
make selftest: exit 0 (SELFTEST PASS)
```

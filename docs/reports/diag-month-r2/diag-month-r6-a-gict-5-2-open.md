# Diagonal Month R6 Lane A: GICT Theorem 5.2 Open Report

Outcome: `open`, with no new formalization, bind recommendation, deposit, or
partial cover.

The selected atom is already partially covered by
`D5/S3/Constants/ElementaryExactValues.elementary_exact_values`. Its canonical
ledger row names exactly two unresolved subitems:
`phi-derivative-at-zero-identification` and
`ah-exact-value-delta-certificate`. Neither can be stated faithfully from the
current addressable carriers. The selected GICT atom does not define `Phi`, and
no D5 theorem connects a relevant function's derivative at zero to `kappa`.
The source's `Delta = 7.7e-8` also does not identify the unrounded measured
value or an executable residual whose distance from the exact `A_h` is being
reported. Creating either missing carrier would therefore install the desired
conclusion by definition or fabricate source data.

No Lean, Blueprint, Scribe, digestion, receipt, frozen-ledger, evidence, or
generated file was edited. The only intended path in this lane is this report.

## Environment and moving base

The dispatcher-assigned lane is:

```text
/Users/mstudio3/trureturing-diag-month-r4-a
branch = harness/diag-month-r6-a
```

The lane began at `8ee0a8fd825d3af6c1a8ff5e7dcc999f09f57a71`.
Before the first report edit, the dispatcher required a clean-tree fast-forward
to the then-current `origin/dev`:

```sh
git merge --ff-only origin/dev
```

It exited `0` and advanced the lane to:

```text
HEAD       = e97d6cb869d540e36c2d3c7518bcecb6ff543a9c
origin/dev = e97d6cb869d540e36c2d3c7518bcecb6ff543a9c
```

`git merge-base --is-ancestor origin/dev HEAD` exited `0`, and
`git status --porcelain=v1` was empty after the fast-forward.

The fast-forward also landed the phase-5 Make split. Consequently the old root
command `make dotnet` exited `2` with `No rule to make target 'dotnet'`.
`make help` and `make -C tools help` both exited `0` and identified the current
canonical tool-layer door as `make -C tools dotnet`. That command exited `0`
with zero warnings and zero errors.

The repository-authoritative skill was read from
`skills/codex-formalize/SKILL.md`; its current SHA-256 is
`e34d3e962fb6bf81ba972d668d58705add221ab93ef768956b8cad54dfc9e7b0`.
The installed projection has SHA-256
`99d45b8a0d249e4bd71f1bceaedf12f795b187af04a22672d7aa6e908d567ae6`
and was not treated as authority. `CLAUDE.md`, `agents/CONTEXT.md`, the
applicable role charters, `agents/echo-template.md`, the normative spec, and
the live Make help catalogues were read.

## Atom identity and authoritative statement

- Atom ID:
  `gict-residual-6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c`
- Source ID: `gict-v3.6`
- Source: `docs/develop/theory/GICT.md`
- AST path: `theorem/5.2`
- Atomizer: `gict-v1`
- Claim class: compact, multi-clause exact-value theorem with two remaining
  semantic/certificate obligations.

An initial command incorrectly prefixed the atom ID with `gict-v3.6/`; it
exited `2` and read no atom. The corrected authoritative command was:

```sh
make show-atom \
  ATOM_ID=gict-residual-6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c
```

After the base fast-forward and current harness rebuild it exited `0` and
reported:

```text
SHOW_ATOM atom_id=gict-residual-6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c source_id=gict-v3.6 source_path=docs/develop/theory/GICT.md atomizer=gict-v1 ast_path=theorem/5.2
HASH_VERIFY raw_sha256=sha256:6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c normalized_sha256=sha256:6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c cas_ref=sha256:6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c status=match
```

The complete authoritative raw text was:

```text
**定理 5.2(初等恰值群)**〔定理·证(sympy 级)〕。
A_F = κ = 1/(2φ)(Φ′(0)=−κ 为纯初等事实);h̄ = −½;**s₁ = (1+√5)/12**;**A_h = (5√5−3)/24**(恰值 Δ=7.7×10⁻⁸);E = (137−61√5)/24。〔轮 137/144/151〕
```

## Clause-level statement echo

The atom has no explicit quantifiers or hypotheses. Its mathematical clauses
are concrete real-valued equalities plus one numerical certificate. No clause
is silently discarded.

1. **`A_F = kappa = 1/(2 phi)`.** The canonical ledger already credits
   `elementary_exact_values` for the carried elementary exact-value group.
   That theorem states `kappa = 1/(2*goldenRatio)` and the equivalent radical
   form. This producing lane does not relitigate or edit dispatcher-owned
   coverage.
2. **`Phi'(0) = -kappa`.** This is unresolved. A faithful Lean counterpart
   would need an independently defined source function, for example an
   addressable `Phi : Real -> Real`, followed by a theorem such as
   `HasDerivAt Phi (-kappa) 0` or `deriv Phi 0 = -kappa`. The GICT atom and its
   nearby context do not define that function. D5 has no declaration joining
   any relevant `Phi`, differentiation at zero, and
   `D5.S3.Constants.Values.kappa`. Choosing a function now would choose the
   theorem's meaning rather than formalize it.
3. **`hBar = -1/2`.** Carried verbatim as the third conjunct of
   `elementary_exact_values`.
4. **`s1 = (1+sqrt(5))/12`.** Carried verbatim as the fourth conjunct.
5. **`A_h = (5*sqrt(5)-3)/24`.** Carried verbatim as the fifth conjunct using
   `Values.ah`.
6. **`exact value Delta = 7.7e-8`.** This is unresolved independently of
   clause 5. The atom does not name the observed value, residual, norm, data
   point, or comparison operator represented by `Delta`. The historical PZG
   narrative says `A_h = 0.3408474 +/- 3.3e-7` against the closed form and then
   reports `Delta = 7.7e-8`, but the printed seven-digit center is rounded and
   does not expose the unrounded datum that produced the stated delta. There
   is therefore no faithful exact Lean expression for this certificate.
7. **`E = (137-61*sqrt(5))/24`.** Carried verbatim as the final conjunct.

The round references `137/144/151`, the labels `sympy level` and `purely
elementary`, and the theorem title are provenance/proof-history narrative, not
additional mathematical conclusions. The two unresolved clauses above are
not reclassified as narrative.

The intended dropped-or-weakened set for a successful theorem cannot be empty:
clauses 2 and 6 have no faithful Lean counterpart. The state machine therefore
stops at statement echo/library search with `open` before artifact creation.

## Canonical coverage and current carriers

The canonical row is:

```text
Meta/Digestion/backfill/gict-v3.6/partial-closed/
  gict-residual-6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c.yaml
```

It records:

```yaml
coverage_gids:
  - D5/S3/Constants/ElementaryExactValues.elementary_exact_values
receipts:
  unresolved_subitems:
    - phi-derivative-at-zero-identification
    - ah-exact-value-delta-certificate
```

The matching formalization receipt names the same primary GID. The exact
current declarations are:

```lean
-- D5/S3/Constants/Values.lean
noncomputable def ah : ℝ := (5 * Real.sqrt 5 - 3) / 24
noncomputable def kappa : ℝ := 1 / (2 * goldenRatio)

-- D5/S3/Constants/ElementaryExactValues.lean
theorem elementary_exact_values :
    kappa = 1 / (2 * goldenRatio) ∧
      kappa = (Real.sqrt 5 - 1) / 4 ∧
      hBar = -1 / 2 ∧
      s1 = (1 + Real.sqrt 5) / 12 ∧
      ah = (5 * Real.sqrt 5 - 3) / 24 ∧
      e = (137 - 61 * Real.sqrt 5) / 24
```

Thus a new proof of the `A_h` radical equality would be both a definitional
restatement of `Values.ah` and a duplicate of the already covered theorem.

The current values projection was inspected with:

```sh
jq '.constants[] | select(.id == "D5/Ah") |
  {id, decimal, definition, comparison, error,
   reference_value, reference_error, lean_gid}' Evidence/D5/values.json
```

It exited `0` and reports:

```json
{
  "id": "D5/Ah",
  "decimal": "0.340847495312456187",
  "definition": "(5*sqrt(5)-3)/24",
  "comparison": "reference-exact",
  "error": "0",
  "reference_value": "(5*sqrt(5)-3)/24",
  "reference_error": "0",
  "lean_gid": "D5/S3/Constants/Values.ah"
}
```

This projection evaluates the closed form and compares it to the same closed
form. It does not contain the source's independent measured center or a
`7.7e-8` residual witness.

## Repository and pinned-mathlib search trace

The current D5 searches were:

```sh
rg -n --glob '*.lean' \
  'deriv .*0.*kappa|deriv .*0.*κ|HasDerivAt .*kappa.*0|HasDerivAt .*κ.*0|kappa.*deriv|κ.*deriv' D5
# exit 1, no output

rg -n --glob '*.lean' \
  'ah.*7\.7|7\.7.*ah|abs .*ah|ah.*abs|3408474|340847495' D5
# exit 1, no output

rg -n -F 'ah = (5 * Real.sqrt 5 - 3) / 24' D5 -g '*.lean'
# exit 0
# D5/S3/Constants/ElementaryExactValues.lean:21 only

rg -n -F '5 * Real.sqrt 5 - 3' D5 -g '*.lean'
# exit 0
# D5/S3/Constants/Values.lean:17
# D5/S3/Constants/ElementaryExactValues.lean:21
```

A broader `rg -n --glob '*.lean' '\bPhi\b|Φ' D5` exited `0`. Its `Phi`
hits were a quantum-channel binder and the unrelated Weil/Zeta function
`D5.S3.Weil.ZetaCore.Phi`; none was connected to the selected exact-value
`kappa` or to this atom. The exact derivative-shape search above remained
empty.

The pinned mathlib revision was:

```text
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f
```

The same derivative query, the fixed-string query
`5 * Real.sqrt 5 - 3`, and the regex
`3408474|340847495|7\.7.*10|7\.7e-8` were run over
`.lake/packages/mathlib/Mathlib/**/*.lean`. Each exited `1` with no output.

The source-context search found the selected GICT line and multiple PZG
historical/narrative occurrences of `Phi'(0) = -kappa`; the PZG discussion
names Abel summation and Bernoulli expansion as a derivation route. It does not
supply an addressable Lean function or theorem. PZG also supplies the rounded
`A_h = 0.3408474 +/- 3.3e-7` context quoted above, but no executable unrounded
measurement carrier. PZG is useful provenance; it is not permission to invent
missing semantics in the selected GICT atom.

## All-reference search

There were `1589` local and remote refs when this audit ran. The derivative
shape was searched across every ref with:

```sh
set -o pipefail
git grep -n -h -E \
  'deriv .*0.*kappa|deriv .*0.*κ|HasDerivAt .*kappa.*0|HasDerivAt .*κ.*0|kappa.*deriv|κ.*deriv' \
  $(git for-each-ref --format='%(refname)') -- 'D5/**/*.lean' | sort -u
```

It exited `1` with no output. The exact radical search:

```sh
set -o pipefail
git grep -n -h -F '5 * Real.sqrt 5 - 3' \
  $(git for-each-ref --format='%(refname)') -- 'D5/**/*.lean' | sort -u
```

exited `0` with only the same two unique lines from `Values.lean` and
`ElementaryExactValues.lean`.

The bounded all-ref numerical search over `D5/**` and `Evidence/D5/**` for
`3408474`, `340847495`, `7.7e-8`, and the source Unicode delta returned
historical one-line values projections. Across those variants the `D5/Ah`
record uses the exact radical as both value and reference and reports error
zero; it does not carry the independent source measurement that would witness
`7.7e-8`.

Exact atom history contains ingestion, projection, freeze, and formalization-
receipt commits, including the existing elementary-exact-values deposit. It
does not expose a second D5 derivative theorem or delta certificate. These are
bounded repository-history results, not a claim of mathematical absence
outside the searched corpus.

## Third-party Lean search

Standalone `gh auth status` exited `1` and standalone `gh api rate_limit`
exited `4`; those commands did not test the repository's intended credential
path. The repository-scoped wrapper was then used without changing global
configuration:

```sh
eval "$(/opt/homebrew/bin/gh-app shell-init zsh)"
gh auth status
gh api rate_limit --jq '{core: .resources.core, search: .resources.search}'
```

The combined command exited `0`, authenticated as `macstudio-3[bot]`, and
reported `search.remaining = 30` before the searches. The following bounded
GitHub code searches were then run with `--language Lean --limit 20 --json
repository,path,url`:

```text
"5 * Real.sqrt 5 - 3"  -> exit 0, []
"phi-derivative-at-zero" -> exit 0, []
"HasDerivAt" "kappa" -> exit 0, []
"3408474" -> exit 0, []
```

As a supplemental route, the same four terms were sent to grep.app's public
API with a Lean-language filter. Each request failed with HTTP 429
(`curl` exit `56`). This does not negate the completed GitHub searches and is
not presented as a no-hit result. No global external-absence claim is made.

## Rejected approaches

- Defining `Phi x := -kappa*x` and proving its derivative was rejected as a
  definitional tautology that installs the desired conclusion.
- Reusing the quantum-channel binder or the Weil/Zeta `Phi` was rejected:
  neither denotes the source function or has the required `kappa` bridge.
- Introducing an arbitrary `Phi : Real -> Real` plus the desired derivative as
  a hypothesis was rejected as a conditional weakening of the unconditional
  source claim.
- Re-proving `ah = (5*sqrt(5)-3)/24` was rejected as duplicate formalization;
  it is already both the definition and a covered theorem conjunct.
- Defining a measured value to be `ah +/- 7.7e-8` was rejected as fabrication.
  The source does not provide that unrounded datum or the sign/operator needed
  to reconstruct it.
- Treating the values projection's `error = 0` as the source delta was
  rejected because the projection compares the exact formula with itself.
- Binding or covering only the exact radical equality was rejected because it
  would leave both canonical unresolved-subitem names untouched while
  implying progress already credited by the ledger.

There was no failed Lean proof attempt. The workflow stopped before proposing
a fabricated or weakened signature.

## Scoped verification

After synchronizing the base, the current tool and existing carriers were
verified with:

```sh
eval "$(sed -n '/^export PATH=/p' tools/scripts/local-harness-gate.sh)"
make -C tools dotnet
# exit 0; 0 warnings, 0 errors

make show-atom \
  ATOM_ID=gict-residual-6e1053eef77278dd897b092fcb456d24c310e0f3556bfed13449ff25a1fc297c
# exit 0; all three hashes match

lake build D5.S3.Constants.Values \
  D5.S3.Constants.ElementaryExactValues
# exit 0; Build completed successfully (1918 jobs).
```

These green checks establish that the cited existing carriers and current
atom reader are healthy. They do not fill either semantic/certificate gap.

## Fidelity and non-hollowness accounting

- **Conclusion substance:** both missing conclusions are substantive. No
  `True`, hypothesis restatement, or new definitional equality was proposed.
- **Hypothesis satisfiability:** not applicable to a candidate signature;
  none was introduced. Adding derivative or measurement hypotheses would
  weaken the unconditional atom.
- **Domain inhabitance:** no candidate domain was introduced. In particular,
  the source function denoted by `Phi` is not addressably typed in D5.
- **Proof substance:** a derivative of a newly defined linear function or the
  existing `Values.ah` reflexive equality would be hollow for these residues.
- **Deposit substance:** no definition or theorem was added. A new function or
  datum cannot earn a freeze when it is selected only to make the target true.
- **Duplicate search:** the already-covered exact-value theorem was found in
  the current tree and across all refs and was not duplicated.
- **Clause fidelity:** all equality and certificate clauses are listed above.
  The derivative function semantics and delta comparison datum remain
  unresolved, so the dropped-or-weakened set for a proposed theorem is
  nonempty.
- **Rendered-statement fidelity:** not run because no Lean/Scribe artifact was
  created and no emitted statement exists to compare.

Grader-trap accounting:

- **Witness vs universal:** not applicable; no numerical witness is promoted
  to a general derivative theorem.
- **Instance vs general:** decisive for `Phi`; an unrelated D5 function cannot
  instantiate the unnamed source function.
- **Conditional vs unconditional:** decisive; the two missing facts were not
  inserted as assumptions.
- **Pointwise vs operator/series:** not applicable to the exact-value clauses;
  the derivative clause still requires function-level semantics, not a scalar
  identity alone.
- **Proof-internal vs addressable statement:** decisive; PZG prose calculations
  and the evidence projection are not addressable Lean theorems for either
  unresolved subitem.
- **Multi-clause residue names:** decisive; the canonical row names both
  remaining obligations, and an already-covered conjunct cannot cover them.
- **Mechanism vs outcome:** Abel/Bernoulli narrative is a proposed mechanism,
  not the addressable derivative outcome; exact-quadratic evaluation is a
  mechanism for the closed form, not the independent delta outcome.

## Unreached stages and final disposition

- New Lean/Scribe artifact creation: not run; clause fidelity failed first.
- Artifact-shape/capacity/freeze checks: not run; no artifact was proposed.
- Full `make lean`: not run for a report-only `open`; the two cited modules
  were built with the scoped command above.
- `make emit`: not run; there is no new Scribe artifact.
- `make deposit`: not run.
- `make preflight`: not run; it cannot supply missing source semantics/data.
- `make cover`: not run.
- Push and `make pr-open`: not run, per dispatcher scope.

The atom remains `open`. Faithful future closure requires an independently
addressed definition of the source `Phi` together with its derivative theorem,
and an executable unrounded `A_h` measurement/residual specification that
actually yields the source's `7.7e-8` comparison. Until both canonical
unresolved subitems can be named by addressable statements, no additional
bind or cover is valid.

Ledger balanced: yes. Intended changed path:
`docs/reports/diag-month-r2/diag-month-r6-a-gict-5-2-open.md`.

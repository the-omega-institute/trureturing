# Diagnostic Month R2 Lane B: CONE Petz 2.2 Open Report

Outcome: open, with no formalization deposit.

This report records the isolated lane `harness/diag-month-r2-b` at
`/Users/mstudio3/trureturing-diag-month-r2-b`. The lane began at the dispatched
base `e17a20fed21529321667d7c6dbf5ce915246f8a0`. Before this report was written,
the shared `origin/dev` reference had advanced by four commits. The lane was
fast-forwarded with `git merge --no-edit origin/dev` to
`e3d4b21439a18c1f143385a6f6f55a091cc4c06e`; afterwards `HEAD` and
`origin/dev` were equal and `git merge-base --is-ancestor origin/dev HEAD`
exited `0`.

No Lean, Blueprint, Scribe, digestion-ledger, frozen-ledger, formalization
receipt, or generated projection file was edited. The only intended change is
this report.

## Atom and authoritative statement

- Atom ID: `cone-residual-11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574`
- CAS reference: `sha256:11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574`
- Source ID: `cone-v1`; atomizer: `cone-v1`
- Source: `docs/develop/theory/CONE_PROGRAM_FORMAL.md`, `corollary/2.2`
- Claim class: a universal chained equality characterization plus a reversible-channel specialization.
- `make show-atom ATOM_ID=cone-residual-11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574` exited `0`.

The complete successful output was:

```text
SHOW_ATOM atom_id=cone-residual-11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574 source_id=cone-v1 source_path=docs/develop/theory/CONE_PROGRAM_FORMAL.md atomizer=cone-v1 ast_path=corollary/2.2
HASH_VERIFY raw_sha256=sha256:11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574 normalized_sha256=sha256:11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574 cas_ref=sha256:11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574 status=match
BEGIN_RAW_TEXT
**系 2.2(Petz 等号条件之经典形)[证]。**亏为零 ⟺ 两侧后验几乎处处相等 ⟺ 可由输出经贝叶斯逆恢复输入对。可逆信道(置换)之亏恰零。∎

END_RAW_TEXT
BEGIN_NORMALIZED_TEXT
**系 2.2(Petz 等号条件之经典形)[证]。**亏为零 ⟺ 两侧后验几乎处处相等 ⟺ 可由输出经贝叶斯逆恢复输入对。可逆信道(置换)之亏恰零。∎

END_NORMALIZED_TEXT
```

Raw, normalized, and CAS SHA-256 values match exactly.

## Clause echo

The atom has four addressable obligations. All four must share the same finite
classical channel, input pair, divergence loss, and support convention.

| Authoritative clause | Required formal counterpart | Repository evidence and status |
|---|---|---|
| `亏为零` | The KL data-processing defect of an input pair under a classical stochastic channel is zero. | `ClassicalDPI` defines `klDivergence`, `channelOutput`, and `posterior`; `PetzClassical` uses the exact defect expression. There is no separate named loss carrier. |
| `⟺ 两侧后验几乎处处相等` | Both directions between zero defect and equality of the two posteriors on output support. | Frozen `D5.S3.Divergence.PetzClassical.dpi_defect_zero_iff_posteriors_eq` proves this core for finite types under strictly positive normalized inputs and a strictly positive row-stochastic channel. |
| `⟺ 可由输出经贝叶斯逆恢复输入对` | A defined Bayesian reverse channel/recovery operator and both directions between posterior equality and simultaneous recovery of the input pair. | Missing. No classical Bayesian reverse/recovery carrier or theorem linking such an operator to the repository's `posterior` was found. |
| `可逆信道(置换)之亏恰零` | A defined permutation channel, proof that it is reversible in the same channel model, and a named theorem that its KL defect is exactly zero for the source domain. | Missing. Generic `Equiv.Perm` and unrelated quantum/observer channels do not instantiate `ClassicalDPI` as a permutation stochastic matrix or prove zero loss. |

The dropped-or-weakened set would be nonempty for any producing declaration
available from the current frozen library: Bayesian recovery, both equivalence
directions involving recovery, and the permutation specialization would all be
absent. The strictly positive hypotheses of the existing core also cannot be
silently presented as a support-general or measure-theoretic almost-everywhere
statement.

The existing emitted Blueprint states the boundary explicitly at
`Blueprint/D5/S3/Divergence/PetzClassical.md:21`:

> This declaration proves only the core equality characterization. Bayesian
> reverse recovery and the permutation-channel specialization are not part of
> this declaration; they require separate statements and proofs.

## Exact-ID and history audit

The exact all-reference search was run verbatim:

```sh
rg -n -F 'cone-residual-11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574' \
  Meta/Digestion/formalizations docs/devloop/reports Golden/Frozen
```

It exited `1` with no output. The all-history search was:

```sh
git log --all --oneline \
  -S'cone-residual-11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574' \
  -- . ':(exclude)Meta/Digestion/atoms/**'
```

Its complete output was:

```text
5f34ebbd fix(digestion): 再次删除被坏合并恢复的 Meta/BACKFILL.yaml
0f0edb92 Migrate digestion backfill to per-atom directories
ba7a7247 feat(digestion): ingest the positive-cone program volume (P1)
```

These are ingestion/migration history, not a complete formalization receipt.
Exact atom-ID absence is not treated as evidence that the mathematical carrier
exists.

The semantic history of the available core is:

```text
34614eae feat(cone): Petz classical equality condition (corollary 2.2 core)
5bcd9ac8 chore(cone): freeze + partial emit
```

Frozen record
`Golden/Frozen/accepted/924014dcb24003e22201fffff790f8a838ac28b2578d9dbeec194a39b821df05.json`
contains `klDivergence`, `channelOutput`, and `posterior`. Frozen record
`Golden/Frozen/accepted/404fc03f1b8ca8d8c7191ecd7021b01f5cf90681f1e6d1d816b6fd4b64e15250.json`
contains `dpi_defect_zero_iff_posteriors_eq`.

## D5 and library carrier searches

The declaration search was run verbatim:

```sh
rg -n --glob '*.lean' \
  '^(noncomputable )?(def|abbrev|structure|class|theorem|lemma) (klDivergence|channelOutput|posterior|dpi_defect_zero_iff_posteriors_eq|[A-Za-z0-9_]*(Bayes|bayes|Petz|petz|Recover|recover|Permutation|permutation|Channel|channel)[A-Za-z0-9_]*)' \
  D5 Library
```

The relevant exact hits were:

```text
D5/S3/Divergence/PetzClassical.lean:33:theorem dpi_defect_zero_iff_posteriors_eq {X Y : Type*}
D5/S3/Divergence/ClassicalDPI.lean:28:noncomputable def klDivergence {ι : Type*} [Fintype ι]
D5/S3/Divergence/ClassicalDPI.lean:33:noncomputable def channelOutput {X Y : Type*} [Fintype X]
D5/S3/Divergence/ClassicalDPI.lean:38:noncomputable def posterior {X Y : Type*} [Fintype X]
D5/S3/Divergence/ChannelMonotone.lean:22:theorem kl_divergence_channel_le
```

Other hits named quantum, observer-memory, total-variation, or Renyi channels;
none define the classical Bayesian inverse or permutation channel required here.

The exact recovery search was:

```sh
rg -ni --glob '*.lean' \
  'bayes|petz|recovery|recoverability|recoverable|reverse[_ ]channel|inverse[_ ]channel|recover.*input|recover.*pair' \
  D5 Library
```

It found references to `PetzClassical`, unrelated uses of “recover,” and comments
about mathlib Bayes risk. It found no definition or theorem for Bayesian reverse
recovery of the `ClassicalDPI` input pair.

The exact permutation-channel search was:

```sh
rg -ni --glob '*.lean' \
  '(permutation|permute|relabel|equiv).*(channel|stochastic|kl|divergence|loss)|(channel|stochastic|kl|divergence|loss).*(permutation|permute|relabel|equiv)' \
  D5 Library
```

It produced no relevant mathematical hit. The equality-shape search was:

```sh
rg -ni --glob '*.lean' \
  '(dpi_defect.*zero.*iff|posterior.*(iff|↔)|((iff|↔).*)posterior|klDivergence.*channelOutput.*=.*0)' \
  D5 Library
```

Its only theorem-level equality characterization was
`PetzClassical.dpi_defect_zero_iff_posteriors_eq`, plus its use by `StrictDpi`.

Pinned mathlib was searched separately with:

```sh
rg -ni --glob '*.lean' \
  '(Petz|bayes.*(reverse|inverse|kernel)|reverse.*(bayes|kernel)|posterior.*(recover|kernel)|recover.*(klDiv|Kullback|relative.*entropy)|sufficien.*(klDiv|Kullback|kernel)|condDistrib)' \
  .lake/packages/mathlib/Mathlib/Probability .lake/packages/mathlib/Mathlib/InformationTheory

rg -ni --glob '*.lean' \
  '(klDiv|Kullback|relative.*entropy).*(Equiv|equiv|permutation|permute|biject|injectiv)|(Equiv|equiv|permutation|permute|biject|injectiv).*(klDiv|Kullback|relative.*entropy)' \
  .lake/packages/mathlib/Mathlib/Probability .lake/packages/mathlib/Mathlib/InformationTheory
```

Mathlib's `Probability/Kernel/Posterior.lean` defines a measure-kernel
`posterior` and proves results including `posterior_comp_self`. Those results
recover one prior measure through its own posterior kernel. They do not state
the atom's equivalence between equality of the two repository posteriors and
one Bayesian inverse recovering an input pair, and they do not connect to the
repository's real-valued finite-sum `klDivergence` or its defect. The second
search produced no permutation/equivalence KL result. Importing this machinery
would therefore require a new, nontrivial bridge; it is not an exact upstream
bind for the missing clauses.

## Rejected sibling candidate

The other narrowed candidate was
`cone-residual-c4b27f4cb7321bd03276650f5b5e653ff7da3aa51c936213880bc617abacdf93`.
Its `show-atom` command exited `0`, with raw, normalized, and CAS hashes all
equal to `sha256:c4b27f4cb7321bd03276650f5b5e653ff7da3aa51c936213880bc617abacdf93`
and `status=match`. Its authoritative text is:

> **定理 6.1(分治引理)[证]。**凡定义为"对张量封闭之资源类取下确界"之泛函 F,必次可加:F(XY) ≤ F(X)+F(Y)(积策略可行)。∎

It is not distinct work. The all-history audit found:

```text
4b998f45 formalize: record deposit receipt for D5/S3/Resource/DivideConquer.resource_functional_subadditive
8dec6e84 feat(cone): divide-and-conquer subadditivity lemma (theorem 6.1)
```

Commit `8dec6e84` contains the exact `ResourceTheory` tensor object, tensor
strategy, feasibility, additive cost, infimum `value`, and named theorem
`resource_functional_subadditive`; commit `4b998f45` records a receipt for this
exact atom ID. Repeating it in this lane would violate the all-reference
distinctness requirement. The ancestry and current-tree checks distinguish the
two histories exactly:

```text
git merge-base --is-ancestor 8dec6e84 origin/dev: exit 0
D5/S3/Resource/DivideConquer.lean: present
Blueprint/D5/S3/Resource/DivideConquer.scribe.cs: present
Blueprint/D5/S3/Resource/DivideConquer.md: present
git merge-base --is-ancestor 4b998f45 origin/dev: exit 1
```

Thus the exact theorem and its Lean/Blueprint carriers are on current `dev`,
while the exact atom receipt is additional all-reference off-tip evidence.

## Failed approaches

- **Bind the entire atom to `dpi_defect_zero_iff_posteriors_eq`:** rejected. It
  binds only the first equivalence and its Blueprint explicitly excludes the
  recovery and permutation clauses.
- **Define recovery as posterior equality:** rejected as a definitional
  tautology. It would make the second equivalence true by construction without
  supplying a recovery channel or proving that it recovers either input.
- **Introduce an arbitrary reverse kernel and assume recovery:** rejected as a
  restatement of the missing conclusion and as an island carrier with no frozen
  connection to `ClassicalDPI`.
- **Use an `Equiv.Perm` as a channel without a bridge:** rejected. A generic
  equivalence is not the repository's real-valued row-stochastic matrix, and no
  theorem connects its action to `channelOutput`, `posterior`, or KL defect.
- **Use `ObserverMemory.JointCoherentReversal.reverseChannelOn`:** rejected. It
  is an unrelated quantum record-channel construction, not a Bayesian inverse
  for finite classical distributions.
- **Add the missing declarations to `PetzClassical.lean`:** prohibited because
  that module has an active Freeze event. A new module would still need genuine
  source-backed carriers and independent earning theorems; none currently
  exists.
- **Switch to the resource subadditivity atom:** rejected because its exact
  formalization and atom receipt already exist in all-reference history.

## Verification and fidelity gate

- `make dotnet`: exit `0`; zero warnings and zero errors.
- Both `make show-atom` commands: exit `0`; each reported `status=match`.
- `lake build D5.S3.Divergence.ClassicalDPI D5.S3.Divergence.PetzClassical`:
  exit `0`; `Build completed successfully (8561 jobs)`.
- `git merge --no-edit origin/dev`: exit `0`; fast-forwarded the lane from
  `e17a20fe` to `e3d4b214`.
- `git merge-base --is-ancestor origin/dev HEAD`: exit `0` after the fast-forward.
- Latest formal deposit template observed:
  `9da126e6d795a4b01d442020b41b9724a6a2b578`.

Fidelity checklist:

- Conclusion substance: no new theorem was proposed; no `True`, hypothesis
  restatement, or definition-created equivalence was deposited.
- Hypothesis satisfiability: not applicable because no candidate declaration
  was introduced. The existing core's hypotheses are checked by its scoped build.
- Domain inhabitance: not applicable because no new domain was introduced.
- Proof substance: blocked by the absent Bayesian recovery and permutation
  bridges; the existing posterior theorem is not presented as proof of them.
- Deposit substance: no new definition or module was created. An invented
  recovery predicate would have no independent earning theorem.
- Duplicate search: exact-ID, all-history, declaration-shape, and frozen-record
  searches are recorded above.
- Clause fidelity: every source clause remains in the open accounting; the
  missing clauses were not discarded to make the core theorem appear complete.
- Rendered-statement fidelity: no new Scribe source or emitted Markdown exists.
  The existing emitted core statement and its explicit limitation were read.

Grader traps:

- Witness vs universal: the atom is an equivalence, not an existence witness;
  no witness was substituted.
- Instance vs general: no permutation instance was substituted for the full
  recovery equivalence, and no generic equivalence was asserted to be a channel.
- Conditional vs unconditional: the strict-positivity hypotheses of the frozen
  core were not erased.
- Pointwise vs operator: posterior equality was not relabeled as existence of a
  recovery operator.
- Proof-internal vs addressable statement: no proof-local reverse construction
  was claimed; an addressable recovery theorem is missing.
- Multi-clause residue: all two iff links and the permutation clause are tracked;
  the core iff alone does not close the atom.
- Mechanism vs outcome: invertibility vocabulary alone was not used to claim
  zero KL loss without a theorem connecting it to the defect.

`make emit`, full `make lean`, Lean inspector/admission, `make deposit`,
`make preflight`, `make cover`, receipt emission, coverage alignment,
`git push`, and `make pr-open` were not run. The formalization workflow stops
before artifact creation and ceremony when the authoritative clauses cannot be
mapped without stand-ins or omissions.

No file under `Meta/Digestion/**`, `Golden/Frozen/**`, or any formalization
receipt path was edited. No protected-path exception or manual ledger operation
was attempted.

## Verdict

The atom remains **open**. The frozen library proves exactly the posterior-
equality core, but does not define or prove the Bayesian recovery equivalence or
the permutation-channel zero-loss specialization. A faithful future closure
requires source-backed classical reverse-channel and permutation-channel
carriers, together with named theorems proving all missing directions against
the existing `ClassicalDPI` definitions.

Ledger balanced: yes. No formalization deposit was made.

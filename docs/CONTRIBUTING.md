# Contributing

trureturing is a truth-discovery library. Help turn a precise question into a
result that others can check and reuse: through examples, counterexamples,
proofs, clearer explanations or useful tools. The current mathematical subjects
offer concrete places to start.

You do not need to write a new proof to make a useful contribution. Public-facing
documentation defaults to English.

[Project entrance](../README.md) ·
[Repository rules](../AGENTS.md) · [Working map](../agents/CONTEXT.md) ·
[Specification](develop/spec/golden-ledger-repo-spec.md)

## Choose a starting point

- **Read and explain.** Follow a [README example](../README.md#three-places-to-look)
  from explanation to Lean statement. Clarify terminology, fix a link or improve
  a translation while preserving the result's assumptions and scope.
- **Reproduce.** Run the [WDigits example](../README.md#first-run). For an
  experiment, follow its own instructions and report the input, environment and
  output. A computed sample and a theorem answer different questions.
- **Fix.** Bring a minimal reproduction of a build failure, misleading
  explanation or tool defect. A small, focused fix is a useful first PR.
- **Explore.** Start from a [problem dossier](../Problems/) or
  [open frontier task](../D5/X_Frontier/), state the exact missing fact, and
  search for existing results before writing a proof.

To report a problem, [open an issue](https://github.com/the-omega-institute/trureturing/issues)
with the source path or declaration, the commit from `git rev-parse HEAD`, your
OS and relevant tool versions, the smallest input and command that reproduce
it, the expected outcome and the actual output or exit code. For a mathematical
mismatch, quote the statement and identify the missing hypothesis or give the
counterexample. Include necessary diagnostics; omit credentials and session
transcripts. A precise explanation question is welcome too.

## Prerequisites

Reading the source and book needs no local toolchain. For local work, use Git,
Make and Bash, with these tools on `PATH`:

- [elan](https://github.com/leanprover/elan#installation), which selects
  Lean from [lean-toolchain](../lean-toolchain). Mathlib is declared in
  [lakefile.toml](../lakefile.toml), with resolved dependencies in
  [lake-manifest.json](../lake-manifest.json).
- [.NET SDK](https://dotnet.microsoft.com/en-us/download),
  selected by [global.json](../global.json) with roll-forward disabled. The
  repository's Lean wrapper also uses .NET.
- **Python** available as `python3` for the CI/preflight scripts, which require
  the standard-library `tomllib` module.

The shell examples below use macOS/Linux conventions. The installed SDK must
match [global.json](../global.json); a runtime alone is insufficient.
Check `dotnet --version`, `lean --version` and
`python3 --version` from the checkout. Dependency downloads need network access;
individual experiments may have additional prerequisites.

## Your first change

Fork [the repository](https://github.com/the-omega-institute/trureturing/fork)
on GitHub. In the following example, replace `YOUR-USERNAME` with your account.
Keep the initial checkout for tracking `dev`; make edits in an isolated
worktree created by the repository command:

```sh
git clone https://github.com/YOUR-USERNAME/trureturing.git
cd trureturing
git remote add upstream https://github.com/the-omega-institute/trureturing.git
git fetch upstream dev
make worktree KIND=governance NAME=first-docs BASE=upstream/dev DEST=../trureturing-first-docs
cd ../trureturing-first-docs
```

This creates `lane/governance/first-docs` and restores locked .NET dependencies.
Use a fresh task name for each change. The command's other current kinds are
`math` and `theory`; its branch kind does not replace file-level admission rules.
For a maintainer checkout, `BASE=origin/dev` selects the project remote instead.

The worktree starts without a Lean cache. Its first `make lean` prepares a
private cache, using a compatible local donor when available or downloading
dependencies. Use `make lean` before any `lake env lean` debugging command in a
new worktree. `make lean-cache-ensure` is an optional explicit prewarm command.

For a documentation edit, change the owning source, check links and preview
the Markdown. If you publish a command or example, run it. A typo fix needs no
new Lean theorem or test. Then follow the applicable checks and PR steps below.

## Edit the owning source

| What you are changing | Where it belongs |
| --- | --- |
| Public entrance or contribution instructions | `README.md` or this guide |
| Formal definitions and proofs | `D5/**/*.lean`, subject to frozen-state rules |
| Blueprint or paper narrative | The corresponding `*.scribe.cs` source; regenerate with `make emit` |
| Experimental evidence | `Evidence/` or the experiment's registered location |
| Harness code and tests | `tools/` and `tools/tests/` |
| Research input | `docs/develop/theory/`, under the append-only theory rules |

Read [AGENTS.md](../AGENTS.md) and [agents/CONTEXT.md](../agents/CONTEXT.md) before
editing. The [specification](develop/spec/golden-ledger-repo-spec.md) defines
the routing and delivery contracts. Generated Markdown, reports, frozen pins
and digestion state have designated writers; do not repair them by hand.
New files must fit the existing [FILEMAP](../Meta/FILEMAP.toml) and routing rules.

Keep each PR focused and keep **content changes separate from changes to the
rules that judge them**. The current FILEMAP classifies `README.md` as content
and `docs/CONTRIBUTING.md` as judge-plane, so changes to these two files belong
in separate PRs. This classification is about admission, not the file extension.

For mathematical work, follow [the reuse and admission rules](../CLAUDE.md#3-形式化逃逸内容用途与研究):
search this repository, pinned Mathlib and admissible upstream libraries before
proving anything locally. Reuse an existing result directly when it fits.
Do not add a theorem whose only contribution is renaming, specializing or
repackaging an existing one. The rules describe the existing settlement path
for such source claims, the requirements for new content and the narrowly
defined external open-problem exception.

Frozen results stay fixed. Changes involving assumptions, new axioms,
`Hearts.lean` or protected policy must follow their existing authorization
rules. An unresolved claim stays explicit; a successful experiment does not
close it. These requirements apply to human and AI contributions alike.

## Check your change

Use `make help` and `make -C tools help` for the current command list. Choose
focused checks while editing:

```sh
git diff --check
make lean LEAN_TARGETS=D5.S0.Conventions.WDigits
```

The second command is a **targeted Lean build**; replace the module with the
one you changed when doing mathematical work. It is not a full repository
check. For harness changes, `make -C tools check-fast` runs the selected fast
structure checks, and `make -C tools test` runs the full .NET harness test suite.

Commit each logical change and push it to your fork immediately; run any local
checks alongside remote CI. Under [AGENTS.md §8.2](../CLAUDE.md#82-本地早反馈与远端-ci-并行),
local `make preflight` and PR-mode preflight are **optional** early feedback and
diagnostics. Current remote CI checks remain **required and authoritative**.
The shared preflight entry selects the applicable engineering and current-tree
checks:

```sh
make preflight
```

Optionally, check the combination with the project's `dev` branch before
merge. To run this diagnostic, start from a clean, committed worktree and pass
an immutable base SHA:

```sh
git fetch upstream dev
base_sha="$(git rev-parse upstream/dev)"
make preflight MODE=pr BASE="$base_sha"
```

PR-mode preflight checks an isolated merge-tree candidate and its delta. It
does not merge your branch. If you have only the project remote, use
`git fetch origin dev`, then `git rev-parse origin/dev` to resolve the base SHA.
A targeted build, local preflight and
remote CI are distinct results: report the command and actual exit code, and
say explicitly which checks you did not run.

## Open a pull request

Push the branch to your fork with `git push -u origin lane/governance/first-docs`
(substitute your actual branch). Open a PR against **`the-omega-institute/trureturing:dev`**;
`main` is the release branch.

Describe the concrete problem, resulting behavior or explanation, source
evidence and verification. At the top, include the provenance required by
[AGENTS.md §5.2](../CLAUDE.md#52-工件产地与独立性披露): skills used (or none),
who produced and reviewed the work, and the actual review method and scope.
Disclose AI assistance when used. Keep the PR to useful results and necessary
diagnostics; do not paste process transcripts.

Arrange independent review. The repository's documented merge checks are
`push / engineering`, `push / current` and `delta`; inspect the actual check
results on your PR and address failures. GitHub branch-protection configuration
is an external setting, not a guarantee supplied by this guide. An open PR or
green local check is not a merged contribution: completion is **MERGED** into
`dev`. Clean up an isolated worktree only after confirming the merge and a
clean working tree.

The root [LICENSE](../LICENSE) contains Apache-2.0. The repository's
[licensing specification](develop/spec/golden-ledger-repo-spec.md#第八部治理)
assigns Apache-2.0 to repository-produced Lean code, CC-BY-4.0 to text, and CC0
to data. Third-party dependencies retain their upstream licenses and applicable
notices.

## Research boundaries

The two excerpts below preserve the original Chinese wording of boundary
statements in [GICT v3.6](develop/theory/GICT.md), a research input. They describe
that theory's limits and falsifiability criteria; quoting them does not establish
a formal result.

### Limits on interpretation

Source: GICT v3.6, Appendix C.

> 本理论:不证明黎曼假设;不主张宇宙以 φ 运行;不为黄金比例神秘主义背书;φ 在物理中处处"被选出"(不动点/临界点)而非"被写入"(公理);GCS 为黄金格原生坐标,非唯一非独尊。**凡"本质就是"四字,须过 27.94 之分家检验;凡统一感,须交 27.82 之收据。**

### Falsifiability

Source: GICT v3.6, Volume IX.

> **可证伪七条**(原样):三轴无压缩则移出样品;depth 必有限分辨率;R 不得过宽;唯一性不得误认(银比平行);复平面不得当底层;固定集不得全称分形;**任何失败若被释为"未看懂"、任何巧合若被释为"深层结构",理论即死。**

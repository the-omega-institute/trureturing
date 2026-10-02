# Contributing

trureturing develops a scientific method for AI to discover truth and use
checked results to guide further inquiry. Help turn a precise question into
a result that others can check and reuse: through examples, counterexamples,
proofs, clearer explanations or useful tools. The
[vision and research guide](VISION.md) connects the current mathematical
subjects to this purpose and the open research directions.

You do not need to write a new proof to make a useful contribution. Public-facing
documentation defaults to English.

[Project entrance](../README.md) ·
[Choose a starting point](#choose-a-starting-point) ·
[Repository rules](../AGENTS.md) · [Working map](../agents/CONTEXT.md) ·
[Specification](develop/spec/golden-ledger-repo-spec.md)

## Choose a starting point

- **Connect a question to a research direction.** Use the
  [research directions](VISION.md#research-directions) to identify an observation, missing relation
  or reusable lemma that could advance an existing line. State what would
  support or refute the proposed step, search the library first, and explain
  what the result would enable next. New evidence should also update the
  relevant explanation; preserve the distinction between a philosophical
  commitment, a model, an experiment and a checked theorem.
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

## Use Claude Code or Codex

Choose either client: follow the official [Claude Code setup](https://code.claude.com/docs/en/setup)
or [Codex CLI setup](https://learn.chatgpt.com/docs/codex/cli) to install and sign
in. Open the checkout as your client's workspace, or, in a terminal, change to
the checkout directory and start `claude` **or** `codex`. You need only one.
If you have not cloned the repository yet, follow the clone commands in the
README's [First run](../README.md#first-run); source exploration does not require
the build step.

Ask the agent to read [AGENTS.md](../AGENTS.md), [README.md](../README.md) and
this guide. In this repository, `AGENTS.md` points to `CLAUDE.md`; both names
lead to the same rules.
Those rules select [formal-thinking-and-answer](../skills/formal-thinking-and-answer/SKILL.md)
as the default thinking and answering workflow; you do not need to invoke it explicitly.
Work that produces or checks proofs needs the [build prerequisites](#prerequisites).
Client access, build tools, network search and independent review services
depend on your environment; the repository skills do not install them.

### Choose a skill for the question

[skills/](../skills/) is the canonical source. The existing `.claude/skills`
and `.codex/skills` directories are aliases to it. Discovery varies by client;
the portable way to use a skill is to ask the agent to read its canonical
`SKILL.md` explicitly. For example, paste this into the **client conversation**:

> Read skills/formal-thinking-and-answer/SKILL.md and use it to examine whether knowing every part determines the whole, making the assumptions and unresolved questions explicit.

- **[formal-thinking-and-answer](../skills/formal-thinking-and-answer/SKILL.md)**

  A mathematical, philosophical or conceptual question: “Does knowing every part
  determine the whole?”

  Reasons from repository results, uses formal checking where applicable, and
  returns an ordinary answer with its assumptions and unresolved boundaries;
  can create and retain scoped formal artifacts under repository rules.

- **[codex-formalize](../skills/codex-formalize/SKILL.md)**

  One existing open digestion atom: “Work on atom `<atom-id>`, reusing results
  first.”

  Searches for reusable results first, then works on formalization or settlement
  of that source claim; a new theorem or closure is not guaranteed.

- **[codex-theory-ingest](../skills/codex-theory-ingest/SKILL.md)**

  Externally authored material: “Ingest the document at `<path>` from
  `<source-URL>` under `<license>`.”

  Brings reference input through the digestion workflow into open formalization
  atoms; ingestion is not proof.

- **[theory-volume-template](../skills/theory-volume-template/SKILL.md)**

  Your own volume: “Draft a new volume on `<topic>`,” or “Append to
  `<volume-path>` while preserving existing atoms.”

  Structures the volume for digestion while preserving existing atoms; use this
  for authoring and appending, and the ingest skill for externally authored material.

A digestion atom is a source claim tracked by the repository's ingestion
workflow. Replace the placeholders with your actual input; each linked skill
contains the full workflow. A skill guides the work; [repository rules](../AGENTS.md), the
[specification](develop/spec/golden-ledger-repo-spec.md) and actual checks govern
what can be claimed or admitted.

If the skill appears in your client's list, [Codex](https://learn.chatgpt.com/docs/build-skills)
lets you select it with `/skills` or mention it as `$formal-thinking-and-answer`;
[Claude Code](https://code.claude.com/docs/en/skills) uses `/formal-thinking-and-answer`.
Substitute another listed skill name for the other workflows. These are client
inputs, not shell commands. Current Codex documentation describes repository
discovery under `.agents/skills`; do not assume this checkout's `.codex/skills`
alias is automatically discovered. Explicitly reading the canonical file
works without copying skills or changing global configuration.

### Take an exploration into a contribution

Give your agent a precise task, such as clarifying one explanation against its
linked source or reproducing a mismatch. Documentation and typo fixes do not
need a mathematical skill. A contribution request you can paste:

> Read AGENTS.md and docs/CONTRIBUTING.md, then clarify one README example against its linked source in an isolated worktree, preserve its assumptions and scope, check the changed documentation and prepare the diff for independent review and a PR to dev.

1. Define the expected improvement using [Choose a starting point](#choose-a-starting-point)
   and read the linked rules before editing.
2. Follow [Your first change](#your-first-change) to create or reuse a worktree;
   open that directory as the agent's workspace for the contribution.
3. [Edit the owning source](#edit-the-owning-source), run
   [focused validation](#check-your-change), and arrange independent review of
   the actual diff. Ask the agent to distinguish checks it ran from unmet
   prerequisites or unverified claims.
4. Follow [Open a pull request](#open-a-pull-request) to target `dev` and inspect
   the required remote checks. Local checks and an agent's confidence do not
   replace those results or independent review.

## Prerequisites

Reading the source and book needs no local toolchain. For local work, use Git,
Make and Bash, with these tools on `PATH`:

- [elan](https://github.com/leanprover/elan#installation), which selects
  Lean from [lean-toolchain](../lean-toolchain). Mathlib is declared in
  [lakefile.toml](../lakefile.toml), with resolved dependencies in
  [lake-manifest.json](../lake-manifest.json).
- [.NET SDK](https://dotnet.microsoft.com/en-us/download),
  selected by [global.json](../global.json) using its declared roll-forward
  policy. The
  repository's Lean wrapper also uses .NET.
- **Python 3.11+** as `python3` for CI/local checks scripts, which import
  standard-library `tomllib`.

The shell examples below use macOS/Linux conventions. Install the SDK version
specified in [global.json](../global.json), even when its roll-forward policy
allows a newer installed SDK: integration fixtures also exercise exact version
selection. A runtime alone is insufficient.
Check `dotnet --version`, `lean --version` and
`python3 --version` from the checkout. Dependency downloads need network access;
individual experiments may have additional prerequisites.

## Your first change

Fork [the repository](https://github.com/the-omega-institute/trureturing/fork).
Clone only if needed, replacing `YOUR-USERNAME`:

```sh
git clone https://github.com/YOUR-USERNAME/trureturing.git
cd trureturing
```

From your `dev` checkout, run `git worktree list --porcelain`; reuse this
session's worktree if listed. Otherwise replace `SESSION-ID` with your actual
session ID and run the following, adding `upstream` only if absent:

```sh
git remote add upstream https://github.com/the-omega-institute/trureturing.git
git fetch upstream dev
make worktree KIND=governance NAME=first-docs BASE=upstream/dev DEST=../trureturing-SESSION-ID
cd ../trureturing-SESSION-ID
```

This creates `lane/governance/first-docs` and restores locked .NET dependencies.
For later tasks, commit existing work, confirm a clean tree and switch to a
validated branch in the same session worktree, following
[§6.1](../CLAUDE.md#61-独立-worktree-与-merged-完成态).
Other branch kinds are `math` and `theory`; file-level checks still apply.
Maintainers use `BASE=origin/dev`.

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

Keep each PR focused. [Current policy](../CLAUDE.md#75-base-判官永久禁令与-sl-030-边界)
permits a coherent PR to include both content and its checking rules. FILEMAP
still selects each path's required checks; mixed scope waives none. Different
classifications for `README.md` and this guide do not themselves require
separate PRs.

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

The second command is a targeted Lean build; use your changed module. For harness
iteration use `make -C tools check-fast` and the affected test project:

```sh
make -C tools test TEST_PROJECT=tools/tests/<Project>/<Project>.csproj
```

`make test` generates the Lean report and runs check-current. For local validation
of cross-tree constraints, resolve an explicit base and run the independent commands:

```sh
base_sha="$(git rev-parse upstream/dev^{commit})"
make gate BASE="$base_sha"
```

The gate runs lean-report, check-current, Scribe, filemap-conform and check-delta.
Base supplies data only. Use `origin/dev` when that is your project remote.
Commit and push each logical change; local checks provide early feedback alongside
remote CI. Report actual commands and exit codes. Local success does not replace
required checks on the PR.

## Open a pull request

Push the branch to your fork with `git push -u origin lane/governance/first-docs`
(substitute your actual branch). Open a PR against **`the-omega-institute/trureturing:dev`**;
`main` is the release branch.

Describe the problem, resulting behavior or explanation, source evidence and
verification. At the top, include [AGENTS.md §5.2](../CLAUDE.md#52-工件产地与独立性披露)
provenance: skills used (or none), producers and reviewers, and the actual
review method and scope. For agent work, include the host session ID and
resume command. Disclose AI assistance. Keep useful results and necessary
diagnostics; omit process transcripts.

Arrange independent review. The repository's documented merge checks are
one required check per independent CI workflow; inspect the actual check
results on your PR and address failures. GitHub branch-protection configuration
is an external setting, not a guarantee supplied by this guide. An open PR or
green local check is not a merged contribution: completion is **MERGED** into
`dev`. Reuse the session worktree for subsequent tasks; cleanup follows
[§6.1](../CLAUDE.md#61-独立-worktree-与-merged-完成态).

The root [LICENSE](../LICENSE) contains Apache-2.0. The repository's
[licensing specification](develop/spec/golden-ledger-repo-spec.md#第八部治理)
assigns Apache-2.0 to repository-produced Lean code, CC-BY-4.0 to text, and CC0
to data. Third-party dependencies retain their upstream licenses and applicable
notices.

### Optional maintainer session queue

Maintainers can take a read-only snapshot of external contributions with Python
3 and an authenticated [GitHub CLI](https://cli.github.com/):

```sh
python3 tools/scripts/agent/contribution_queue.py
python3 tools/scripts/agent/contribution_queue.py --pr 123
```

Run these from the checkout, replacing `123` with the PR number to inspect.
From another directory, pass the script's absolute path. `--help` describes the
options; `--repo ORGANIZATION/REPOSITORY` selects another repository using the
same required-check policy adapter. The authenticated account must have active
organization membership and visibility of all organization owners (Members
read / `read:org`), plus read access to PRs, Issues, Actions, Checks, commit
statuses, branch protection and rules (including Administration read).

JSON output separates `prs.ready`, `prs.waiting` with reasons, and
`issues.triage`. Owners are enumerated dynamically from organization admins;
their PRs and Issues are excluded before queue checks. Missing owner or author
identity aborts classification rather than treating an owner as external.
`--pr` refreshes only that PR and skips the Issue and other PR lists.

A PR enters `ready` only when its current head has all configured required
contexts successful, bound to the configured GitHub Actions app. The observer
uses the latest matching checks, checks commit attachment and rejects conflicting
unsuccessful commit statuses. It supports non-strict branch protection and
rulesets that restate the same Actions-bound required checks; other active rules
keep the PR waiting with `unsupported_rulesets`.

The observer refreshes the PR identity, checks, protection and organization owners
before selection. These are perishable API observations, not workflow-execution
certificates or permission to merge. Missing, conflicting or changed evidence
keeps the PR waiting; API, permission or identity failures return an error snapshot
and exit 2. Refresh before acting.

The command makes only GitHub GET requests and fetches no blob contents. It executes no contribution text,
changes no PR or Issue metadata, and starts no builds, writes, daemon or merge.
It is an optional session tool and adds no required admission gate.

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

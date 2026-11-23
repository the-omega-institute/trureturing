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
[Branch, PR and Issue format](#branch-pr-and-issue-format) ·
[Repository rules](../AGENTS.md) · [Working map](../agents/CONTEXT.md) ·
[Specification](develop/spec/golden-ledger-repo-spec.md)

## Adopting a tools release

To adopt an open tools PR, prepare its head against the current consumer `dev` pin, pass tools CI at that head, and publish the `pr/NUMBER` preview from tools `dev`. Use `tools/consumer/pin.py` from the tools checkout to record its tag, SHA-256 and full source commit in this checkout. Submit the resulting lock to consumer `dev`. The tools workflow picks up the merged consumer PR and merges the exact tools PR head after its normal checks.

Every changed lock records the Git blob ID of the current consumer `dev` lock as `previous_pin`. Use `git rev-parse origin/dev:Meta/tools-release.json` after fetching `dev`. This also applies to stable releases and rollbacks. CI compares the field with the first parent's lock in the tested merge. The `-merge` attribute in `.gitattributes` makes competing changes to that file conflict as a whole.

If a concurrent consumer PR changes the pin, integrate that pin's tools source into the original tools PR, prepare the new head, pass tools CI, and publish a new preview. Then update the consumer lock against current `dev` and rerun consumer checks. Consumer branches can inherit historical pins from their parents when they merge `dev`. Each new pin introduced within the PR must be its baseline or its proposed lock. Rebase or condense intermediate pin edits when they leave an obsolete lock in that history. A consumer merge that leaves the pin unchanged keeps the preview eligible.

Stable releases and tools previews whose source has already merged still use the regular pin command. Their release commits must be in tools `main` and `dev` history, respectively. [Tools commands and delivery workflow](https://github.com/the-omega-institute/trureturing-tools#pair-a-tools-pr-with-a-consumer-pr)

Run the consumer pin regression tests with `python3 -B .github/scripts/test-install-tools.py`.

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

Follow the [Issue guidance](#issues) to report a problem, propose a change or ask
a question.

## Branch, PR and Issue format

### Branch names

Use `lane/<kind>/<task-slug>` for new implementation branches. Write the slug
as short, descriptive, lowercase words joined by hyphens. An existing Issue
number can go at the end, as in `lane/governance/fix-cache-diagnostics-123`.
Use the kind that matches the primary change.

| Kind | Primary change | Example |
| --- | --- | --- |
| `math` | Lean proofs, Blueprint or escape registration | `lane/math/petz-hessian-bound` |
| `theory` | Theory material maintained in this repository | `lane/theory/observer-ledger-notation` |
| `governance` | Documentation, tooling, CI or repository policy | `lane/governance/github-contribution-format` |

Start an implementation branch in a suitable linked worktree from fresh upstream
`dev`. Push
revisions for the same change to the branch behind its existing PR. Start a new
topic branch for independent work. [Your first change](#your-first-change)

### Pull requests

Write the title as `type(scope): action and result`, for example
`docs(contributing): standardize GitHub contribution formats`. Use an imperative
verb and a short lowercase scope that names the affected area. PR types are
`math`, `theory`, `docs`, `feat`, `fix`, `perf`, `refactor`, `test`, `ci` and
`chore`. Ordinary contributions target `dev`. Release PRs follow the `main`
release workflow.

Start with the provenance fields. State the result and its dependencies, report
the verification scope, commands, exit codes, relevant failed findings and open
cases, and complete the applicable mathematical or freeze fields. Check the
statement about previously closed results only when it holds.
[PR template](../.github/PULL_REQUEST_TEMPLATE.md)

If an Issue applies, link it in the PR body. Use `Refs #123` for a related or
partial change and `Closes #123` for a full resolution. The `Closes` keyword
takes effect at merge when the PR targets the base repository's default branch
(`dev` here). For an Issue in another repository, use `Refs owner/repo#123` or
`Closes owner/repo#123`.

### Issues

Search existing Issues and PRs before filing. Continue a matching active Issue
and use its related PR when one already covers the change. Use the common Issue
template for reports, proposals and questions.
[Issue chooser](https://github.com/the-omega-institute/trureturing/issues/new/choose)

File tools implementation work in the tools repository and consumer integration
or pin changes here. [Tools repository](https://github.com/the-omega-institute/trureturing-tools)

Route theory sources, intake and coverage to the theory source repository. Lean
formalization and its Blueprint belong here. Link related changes across
repositories. [Theory source repository](https://github.com/the-omega-institute/trureturing-source-theories/tree/dev)

Write ordinary Issue titles as `type(scope): concrete symptom, proposal or question`.
Use `bug`, `proposal` or `question`, for example
`bug(ci): FILEMAP misses a newly added template`. Research tracking uses the
existing `Preregister: <exact target>` and `Research unit: <exact target>` titles
and the relevant research workflow's body fields.
[Research workflow](../skills/autonomous-research/SKILL.md#3-preregister-probes-and-choose-one-unit)

Start with provenance and identify the affected path, declaration or workflow.
For a bug, include the commit, environment, smallest reproducing command or input,
expected behavior and observed output or exit code. For a mathematical mismatch,
quote the statement and identify a missing hypothesis or give a counterexample.
For a proposal, state the desired outcome and how to verify it. For a question,
state the exact point that needs an answer. Include necessary diagnostics and
source links. Keep Issue and PR bodies focused on current results and evidence.

Before implementing or delegating the work, record your claim on the matching
Issue with the current facts and proposed action. A comment is enough. Correct
invalidated premises promptly. Update the Issue when new evidence changes the
diagnosis or the chosen action, and before changing frozen or protected state.
Comments should add evidence or a decision, so skip routine status updates.

Close a question with the actual answer. If a PR merged into `dev` resolves
only part of an Issue, link the PR, record the remaining scope and keep the
Issue open. For a full implementation, record the PR merged into `dev`, its
merge SHA and the verified result of the first applicable `dev` push, then
close the Issue. If GitHub closes it at merge, add the push result once verified.
[Open a pull request](#open-a-pull-request)

Follow the repository's provenance requirements for skills, producers, review
scope and agent session recovery. When an agent takes over and updates an Issue
or PR, append its session ID and resume command and retain the original entries.
[AGENTS.md §5.2](../CLAUDE.md#52-工件产地与独立性披露)

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

- **[codex-theory-ingest](https://github.com/the-omega-institute/trureturing-source-theories/blob/dev/skills/codex-theory-ingest/SKILL.md)**

  Externally authored material: “Ingest the document at `<path>` from
  `<source-URL>` under `<license>`.”

  Brings reference input through the digestion workflow into open formalization
  atoms; ingestion is not proof.

- **[theory-volume-template](https://github.com/the-omega-institute/trureturing-source-theories/blob/dev/skills/theory-volume-template/SKILL.md)**

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
2. Follow [Your first change](#your-first-change) to reuse a suitable linked worktree
   or create one when isolation is needed;
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
- **Python 3.12+** as `python3` for CI/local checks scripts, which import
  standard-library `tomllib`.

The shell examples below use macOS/Linux conventions. Install the SDK version
specified in [global.json](../global.json), even when its roll-forward policy
allows a newer installed SDK: integration fixtures also exercise exact version
selection. A runtime alone is insufficient.
Check `dotnet --version`, `lean --version` and
`python3 --version` from the checkout. Dependency downloads need network access;
individual experiments may have additional prerequisites.

The root Makefile installs the release selected by `Meta/tools-release.json`. To exercise a tools preview, run `make install-tools`, then `python3 tools/consumer/pin.py <preview-tag>` and commit the updated lock. The consumer runs its Lean, FILEMAP, Scribe and release workflows. The tools repository runs its own build, unit tests and consumer-fixture tests before publishing.
Run `make install-tools` before using `make -C tools`, a script under `tools/`,
or Lake directly in `Reg/`. For an offline checkout, install a copy of the
same release asset with `python3 .github/scripts/install-tools.py --archive /path/to/trureturing-tools.tar.gz`.
The installer verifies the pinned SHA-256 in both cases. It moves extra tool
source files to the reported location under `build/tools-releases/previous-*`
and keeps the current release’s .NET and Lean build outputs.

To build a revision that tracked `tools/`, use a fresh worktree so the historical
compiler sees exactly that revision’s sources. Set `historical_commit` to the
commit to build and use an unused directory.

```sh
git worktree add --detach ../trureturing-historical "$historical_commit"
cd ../trureturing-historical
make -C tools help
```

## Your first change

Fork [the repository](https://github.com/the-omega-institute/trureturing/fork).
Clone only if needed, replacing `YOUR-USERNAME`:

```sh
git clone https://github.com/YOUR-USERNAME/trureturing.git
cd trureturing
```

For reading, search, statistics, diff, viewing commits/PRs/issues and
creating/editing GitHub issues, use the main checkout or a suitable existing worktree;
no new worktree or build is required. Prefer `git show <commit>:<path>` for
pinned-revision reads. Never switch a shared checkout's branch for reading.

For repository edits, worktree-mutating tests/verification, checkout changes,
incompatible builds and builds with write side effects, first reuse a suitable linked worktree;
create one only when isolation is needed. Builds that write are not read-only.
From your `dev` checkout, run `git worktree list --porcelain`; check registration,
repository identity, branch/commit and pin compatibility, existing material and
the HEAD-age/stale-marker policy under CLAUDE.md §6.1 before reuse. Reuse can cross sessions.
When isolation requires a new tree, replace `SESSION-ID` with your actual
session ID and run the following, adding `upstream` only if absent:

```sh
git remote add upstream https://github.com/the-omega-institute/trureturing.git
git fetch upstream dev
make worktree KIND=governance NAME=first-docs BASE=upstream/dev DEST=../trureturing-SESSION-ID
cd ../trureturing-SESSION-ID
```

This creates `lane/governance/first-docs` and restores the locked .NET dependencies.
To reuse this worktree for the next independent task, finish delivery of the
previous change and confirm the tree is clean, with no undelivered commits or
unfinished Git operations. If the tree is compatible, fetch upstream `dev` again
and create the next topic branch from it in the same worktree.
[§6.1](../CLAUDE.md#61-reusable-collaborative-worktrees-and-merged-delivery)
Other branch kinds are `math` and `theory`; file-level checks still apply.
Maintainers use `BASE=origin/dev`.

The worktree starts without a Lean cache. Ordinary tasks need no full Lean
build or full project cache. If a change needs Lean verification, run
`make lean LEAN_TARGETS="..."` with the affected module names. For a cold
project layer in a linked worktree, see the guarded scoped build in
[§8.3](../CLAUDE.md#83-worktree-与-lean-缓存入口).

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
| Harness code and tests | [trureturing-tools](https://github.com/the-omega-institute/trureturing-tools) |
| Research input | [Theory source repository](https://github.com/the-omega-institute/trureturing-source-theories/tree/dev), under its append-only theory rules |

Read [AGENTS.md](../AGENTS.md) and [agents/CONTEXT.md](../agents/CONTEXT.md) before
editing. The [specification](develop/spec/golden-ledger-repo-spec.md) defines
the routing and delivery contracts. Generated Markdown, reports, frozen pins
and digestion state have designated writers; do not repair them by hand.
New files must fit the existing [FILEMAP](../Meta/FILEMAP.toml) and routing rules.

Daily Scribe commands diagnose their selected definitions with the SDK from
`global.json` before executing any script. Set `SCRIBE_DOTNET` to an absolute
`dotnet` executable path, or supply `DOTNET_HOST_PATH` or `DOTNET_ROOT`; a missing
SDK is an infrastructure failure. Each definition compiles in a separate temporary
project under the ignored `build/scribe-sdk/`.
Projects inherit repository SDK, nullable, warning and analyzer configuration,
reference the already built Scribe API, and restore package-free locked inputs
offline. Package analyzers come from the API's locked build. Release resource
generation uses its separate full-corpus path.

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

For local validation of cross-tree constraints, resolve an explicit base and preview
the checks selected for your diff.

```sh
base_sha="$(git rev-parse upstream/dev^{commit})"
make gate-plan BASE="$base_sha"
```

Run `make gate BASE="$base_sha"` when the plan fits the local check scope. Ordinary CI and `make gate` use the changed paths to run
`check-current` and applicable `check-delta`. Each consumes the same scoped
Lean reports. Source-only input can be checked with an empty report list.
Use `make test BASE="$base_sha"` to run the scoped current check on its own.
Base supplies data only. Use `origin/dev` when that is your project remote.
Commit and push each logical change; local checks provide early feedback alongside
remote CI. Report actual commands and exit codes. Local success does not replace
required checks on the PR.

### Refresh frozen declaration evidence

`make deposit GID=…` records declaration evidence for a new frozen module. To
remeasure all existing frozen members, run `make frozen-refresh` from the checkout
root with the paired tools release pinned. It checks each member's statement pin
and declaration identities against current compiler evidence before updating the
optional fields. The fields describe the last measurement. A proof edit can
change dependencies while preserving the statement pin. Review the resulting
state-file diff before committing. [Frozen state specification, A14](develop/spec/golden-ledger-repo-spec.md)

A row supports an Omega-only, zero-axiom claim when its measured `libraries` is
a nonempty subset of `{OmegaInit, OmegaMath}` and its `axioms` is `[]`. That
claim applies to the compiled declaration at measurement time. For the library itself, the strict
audit checks every declaration in the selected Omega module and its imports for
an empty axiom set and replays the closure in a fresh Lean kernel environment.
`lake test -- OmegaMath.Projective` checks the projective topic.
[Strict library audit](../src/OmegaChecks/Audit.lean)

## Open a pull request

In the fork setup above, push your topic branch with
`git push -u origin lane/governance/first-docs`, substituting your branch name.
Select your fork and branch as the PR head and
**`the-omega-institute/trureturing:dev`** as the base.

For `make pr`, put the title on the first line of `MESSAGE` and the Markdown
body below it. For a personal fork named `trureturing`, qualify `HEAD` with
the fork owner's GitHub username. If you pushed the branch directly to the
upstream repository, use the bare branch name. [PR title and body](#pull-requests)

```sh
make pr HEAD=YOUR-USERNAME:lane/governance/first-docs MESSAGE=pr.md DRAFT=1
```

If review is pending, use `DRAFT=1` or `AUTO_MERGE=0`. `DRAFT=1` returns after
opening the draft. Mark the existing draft **Ready for review** when it is ready.
For a non-draft PR, `make pr` attempts to enable auto-merge by default before
waiting for required checks. Enabling auto-merge requires write access to the
base repository. Fork contributors without that access use `AUTO_MERGE=0` for
non-draft PRs. A maintainer can merge the existing PR after review and required
checks pass, or enable auto-merge after review. If a contributor without write
access pushes a new head while auto-merge is enabled, GitHub disables it. A
maintainer can enable it again after the new head is reviewed.

Arrange the applicable independent review and address failures in GitHub's
required checks on the current PR head. Replace `123` with your PR number and
look up its head on GitHub.

```sh
pr_number=123
head_sha="$(gh pr view "$pr_number" --repo the-omega-institute/trureturing \
  --json headRefOid --jq .headRefOid)" && printf '%s\n' "$head_sha"
```

When pushing a revision, record the full SHA of the exact source ref or commit
used in that push. Continue only once GitHub's `headRefOid` matches the SHA you
pushed. If you're observing the PR, use the current SHA GitHub reports.

Once you have the confirmed SHA, reuse the running wait handle or the completed
result for that PR and SHA, including any result already returned by `make pr`.
If neither exists, start a single watcher.

```sh
make pr-watch PR="$pr_number" HEAD_SHA="$head_sha"
```

Verify that GitHub reports **MERGED** into `dev` and record the merge SHA.
Check Actions for the first applicable `dev` push for that SHA and verify the
affected entry point. [Actions on dev](https://github.com/the-omega-institute/trureturing/actions?query=branch%3Adev)

Follow the worktree reuse or cleanup instructions.
[§6.1](../CLAUDE.md#61-reusable-collaborative-worktrees-and-merged-delivery)

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

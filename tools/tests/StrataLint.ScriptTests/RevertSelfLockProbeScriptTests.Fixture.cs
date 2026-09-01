using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class RevertSelfLockProbeScriptTests
{
    private sealed class OrchestrationFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string bin;
        private readonly string calls;
        private readonly string classifier;
        private readonly string controller;
        private readonly string decision;
        private readonly string gh;
        private readonly string isolator;
        private readonly string output;
        private readonly string scratch;

        internal OrchestrationFixture(bool descendantBeforeRevert = false)
        {
            Repository = Path.Combine(temporary.Path, "candidate");
            bin = Path.Combine(temporary.Path, "bin");
            calls = Path.Combine(temporary.Path, "calls");
            classifier = Path.Combine(bin, "classifier");
            controller = Path.Combine(bin, "controller");
            decision = Path.Combine(temporary.Path, "decision");
            gh = Path.Combine(bin, "gh");
            isolator = Path.Combine(bin, "isolator");
            output = Path.Combine(temporary.Path, "output");
            scratch = Path.Combine(temporary.Path, "scratch");
            ScriptHarnessScratch.EnsureDirectory(Repository);
            ScriptHarnessScratch.EnsureDirectory(bin);
            InitializeRepository(descendantBeforeRevert);
            WriteStubs();
        }

        internal bool AllowAuthorityCanaryWrite { get; set; }
        internal bool AttemptJ0HeadMutationFromJ1 { get; set; }
        internal string ClassifierBody { get; set; } = "";
        internal string ProbeDecision { get; set; } = "SELF_LOCK_CONFIRMED";
        internal string Repository { get; }
        internal bool SpawnDelayedJ1Descendant { get; set; }
        internal string TargetBaseSha { get; private set; } = string.Empty;
        internal string TargetMergeSha { get; private set; } = string.Empty;
        private string RedRunHeadSha { get; set; } = string.Empty;

        internal ProcessOutput Run(string eventName, string job = "engineering")
        {
            ScriptHarnessScratch.WriteScratchText(decision, ProbeDecision + "\n");
            ScriptHarnessScratch.WriteScratchText(output, string.Empty);
            ScriptHarnessScratch.WriteExecutableStub(
                classifier,
                "printf '%s\\n' classifier >> \"$SELF_LOCK_TEST_CALLS\"\n"
                + (ClassifierBody.Length == 0
                    ? "base=$(git -C \"$1\" rev-parse HEAD^1)\n"
                        + "head=$(git -C \"$1\" rev-parse HEAD)\n"
                        + "target=$(cat \"$SELF_LOCK_TEST_TARGET\")\n"
                        + "printf 'PURE_REVERT_TRUE base_sha=%s head_sha=%s target_merge_sha=%s changed_path_count=1\\n' \"$base\" \"$head\" \"$target\""
                    : ClassifierBody));
            ScriptHarnessScratch.WriteScratchText(
                Path.Combine(temporary.Path, "target"), TargetMergeSha + "\n");
            ScriptHarnessScratch.WriteScratchText(
                Path.Combine(temporary.Path, "target-base"), TargetBaseSha + "\n");
            ScriptHarnessScratch.WriteScratchText(
                Path.Combine(temporary.Path, "red-run-head"), RedRunHeadSha + "\n");
            var root = TestRepositoryLayout.FindRoot();
            var script = Path.Combine(
                root,
                "tools",
                "scripts",
                "workflow",
                "revert-self-lock-probe.sh");
            var arguments = new List<string>
            {
                "-u", "GIT_AUTHOR_NAME",
                "-u", "GIT_AUTHOR_EMAIL",
                "-u", "GIT_COMMITTER_NAME",
                "-u", "GIT_COMMITTER_EMAIL",
                "GIT_CONFIG_GLOBAL=/dev/null",
                "GIT_CONFIG_SYSTEM=/dev/null",
                "GIT_CONFIG_NOSYSTEM=1",
                "GIT_CONFIG_COUNT=0",
                "SELF_LOCK_PROBE_TEST_MODE=1",
                $"SELF_LOCK_PROBE_CLASSIFIER={classifier}",
                $"SELF_LOCK_PROBE_CONTROLLER={controller}",
                $"SELF_LOCK_PROBE_GH={gh}",
                $"SELF_LOCK_PROBE_ISOLATOR={isolator}",
                $"SELF_LOCK_TEST_CALLS={calls}",
                $"SELF_LOCK_TEST_TARGET={Path.Combine(temporary.Path, "target")}",
                $"SELF_LOCK_TEST_DECISION={decision}",
                $"SELF_LOCK_TEST_CANARY_WRITABLE={(AllowAuthorityCanaryWrite ? "true" : "false")}",
                $"SELF_LOCK_TEST_ATTEMPT_J0_MUTATION={(AttemptJ0HeadMutationFromJ1 ? "true" : "false")}",
                $"SELF_LOCK_TEST_DELAYED_DESCENDANT={(SpawnDelayedJ1Descendant ? "true" : "false")}",
                $"SELF_LOCK_TEST_DESCENDANT_MARKER={Path.Combine(temporary.Path, "descendant-finished")}",
                $"SELF_LOCK_TEST_TARGET_BASE={Path.Combine(temporary.Path, "target-base")}",
                $"SELF_LOCK_TEST_RED_RUN_HEAD={Path.Combine(temporary.Path, "red-run-head")}",
                "/bin/bash", script,
                Repository,
                eventName,
                "example/repository",
                output,
                scratch,
                job,
            };
            return TestProcessRunner.Run(
                "/usr/bin/env",
                arguments,
                root,
                TestBudgets.ScriptProcessHangGuard,
                512 * 1024);
        }

        internal string[] CallLines() => ScriptHarnessScratch.ReadRecordedCalls(calls);
        internal string[] OutputLines() => ScriptHarnessScratch.ReadScratchLines(output);

        private void InitializeRepository(bool descendantBeforeRevert)
        {
            Git("init", "--template=", "-b", "main");
            ConfigureRepository();
            Commit("seed", "tools/target.txt", "before\n");
            TargetBaseSha = GitText("rev-parse", "HEAD");
            Git("checkout", "-b", "feature");
            Commit("target", "tools/target.txt", "after\n");
            var feature = GitText("rev-parse", "HEAD");
            Git("checkout", "main");
            TargetMergeSha = CommitTree(feature, [TargetBaseSha, feature], "merge target");
            Git("update-ref", "refs/heads/main", TargetMergeSha, TargetBaseSha);
            Git("reset", "--hard", TargetMergeSha);
            RedRunHeadSha = TargetMergeSha;
            if (descendantBeforeRevert)
            {
                Commit("descendant", "tools/descendant.txt", "later\n");
                RedRunHeadSha = GitText("rev-parse", "HEAD");
            }
            var candidateBase = GitText("rev-parse", "HEAD");
            Git("checkout", "-b", "revert");
            Commit("inverse", "tools/target.txt", "before\n");
            var revert = GitText("rev-parse", "HEAD");
            Git("checkout", "main");
            var merge = CommitTree(revert, [TargetMergeSha, revert], "merge inverse");
            Git("update-ref", "refs/heads/main", merge, candidateBase);
            Git("reset", "--hard", merge);
        }

        private void WriteStubs()
        {
            ScriptHarnessScratch.WriteExecutableStub(
                gh,
                "if [[ \"$1\" == api ]]; then\n"
                + "  url=\"$2\"\n"
                + "  target=$(cat \"$SELF_LOCK_TEST_TARGET\")\n"
                + "  base=$(cat \"$SELF_LOCK_TEST_TARGET_BASE\")\n"
                + "  red_head=$(cat \"$SELF_LOCK_TEST_RED_RUN_HEAD\")\n"
                + "  if [[ \" $* \" == *\" --jq \"* ]]; then\n"
                + "    [[ \"$url\" == *\"head_sha=$red_head\"* ]] && printf '%s\\n' 101\n"
                + "  elif [[ \"$url\" == *\"head_sha=$base\"* ]]; then\n"
                + "    printf '{\"total_count\":1,\"workflow_runs\":[{\"id\":100,\"head_sha\":\"%s\",\"event\":\"push\",\"status\":\"completed\",\"conclusion\":\"success\"}]}\\n' \"$base\"\n"
                + "  else\n"
                + "    printf '{\"total_count\":1,\"workflow_runs\":[{\"id\":101,\"head_sha\":\"%s\",\"event\":\"push\",\"status\":\"completed\",\"conclusion\":\"failure\"}]}\\n' \"$red_head\"\n"
                + "  fi\n"
                + "else printf '%s\\n' 'ENGINEERING_TEST_EVIDENCE_FAILED TRX is missing protected-base planned test identities count=1 tests=Example.Tests::ExampleTests.Missing'; fi");
            ScriptHarnessScratch.WriteExecutableStub(
                isolator,
                "if [[ \"${1:-}\" == --canary ]]; then printf 'canary %s\\n' \"$2\" >> \"$SELF_LOCK_TEST_CALLS\"; [[ \"$SELF_LOCK_TEST_CANARY_WRITABLE\" == true ]]; exit; fi\n"
                + "mode=\"$1\"\nshift\n"
                + "if [[ \"$mode\" == --run-tree ]]; then\n"
                + "  shift\n  \"$@\"\n  status=$?\n"
                + "  if [[ \"$SELF_LOCK_TEST_DELAYED_DESCENDANT\" == true ]]; then\n"
                + "    for unused in {1..100}; do [[ -f \"$SELF_LOCK_TEST_DESCENDANT_MARKER\" ]] && break; sleep 0.01; done\n"
                + "  fi\n  exit \"$status\"\nfi\n"
                + "exec \"$@\"");
            ScriptHarnessScratch.WriteExecutableStub(controller, ControllerStub());
        }

        private string ControllerStub() => """
            command="$1"
            shift
            value() {
              local wanted="$1"
              shift
              while (( $# > 0 )); do
                if [[ "$1" == "$wanted" ]]; then printf '%s' "$2"; return 0; fi
                shift 2
              done
              return 1
            }
            case "$command" in
              extract-blockers)
                out="$(value --output "$@")"
                printf '%s\n' '{"schema_version":1,"blockers":[{"assembly":"Example.Tests","test_id":"ExampleTests.Missing"}]}' > "$out"
                ;;
              bind-red-edge)
                repository="$(value --repository "$@")"
                target="$(value --target-merge "$@")"
                green_runs="$(value --last-green-runs "$@")"
                red_runs="$(value --first-red-runs "$@")"
                out="$(value --output "$@")"
                base="$(git -C "$repository" rev-parse "$target^1")"
                green_id="$(jq -er --arg sha "$base" '.workflow_runs | if length == 1 and .[0].head_sha == $sha and .[0].conclusion == "success" then .[0].id else error("bad green") end' "$green_runs")" || exit 2
                red_id="$(jq -er --arg sha "$target" '.workflow_runs | if length == 1 and .[0].head_sha == $sha and .[0].conclusion == "failure" then .[0].id else error("bad red") end' "$red_runs")" || exit 2
                printf '{"schema_version":1,"target_merge_sha":"%s","last_green_sha":"%s","last_green_run_id":%s,"first_red_run_id":%s}\n' "$target" "$base" "$green_id" "$red_id" > "$out"
                ;;
              select-targets)
                out="$(value --output "$@")"
                printf '%s\n' '{"schema_version":1,"required_identities":[{"assembly":"Example.Tests","test_id":"ExampleTests.Missing"},{"assembly":"Example.Tests","test_id":"ExampleTests.Present"}],"blockers":[{"assembly":"Example.Tests","test_id":"ExampleTests.Missing"}]}' > "$out"
                ;;
              evaluator-digest)
                printf '%s\n' 'sha256:0000000000000000000000000000000000000000000000000000000000000000'
                ;;
              artifact-digest)
                printf '%s\n' 'sha256:0000000000000000000000000000000000000000000000000000000000000000'
                ;;
              seal-j0-control)
                out="$(value --output "$@")"
                printf '%s\n' '{"schema_version":1}' > "$out"
                ;;
              run-targeted)
                kind="$(value --subject-kind "$@")"
                repo="$(value --repository "$@")"
                staging="$(value --staging-bundle "$@")"
                printf 'run-targeted %s\n' "$kind" >> "$SELF_LOCK_TEST_CALLS"
                if [[ "$kind" == merge && "$SELF_LOCK_TEST_ATTEMPT_J0_MUTATION" == true ]]; then
                  j0="$(dirname "$repo")/j0"
                  if git -C "$j0" update-ref HEAD "$(git -C "$j0" rev-parse HEAD^1)" 2>/dev/null; then
                    printf '%s\n' j0-mutation-succeeded >> "$SELF_LOCK_TEST_CALLS"
                  else
                    printf '%s\n' j0-mutation-blocked >> "$SELF_LOCK_TEST_CALLS"
                  fi
                fi
                if [[ "$kind" == merge && "$SELF_LOCK_TEST_DELAYED_DESCENDANT" == true ]]; then
                  (sleep 0.15; printf '%s\n' j1-descendant-finished >> "$SELF_LOCK_TEST_CALLS"; : > "$SELF_LOCK_TEST_DESCENDANT_MARKER") &
                fi
                if [[ "$kind" == synthetic_noop ]]; then
                  printf 'noop %s %s %s\n' \
                    "$(git -C "$repo" rev-parse 'HEAD^{tree}')" \
                    "$(git -C "$repo" rev-parse 'HEAD^1^{tree}')" \
                    "$(git -C "$repo" rev-parse HEAD^1)" >> "$SELF_LOCK_TEST_CALLS"
                fi
                mkdir -p "$staging/trx"
                printf '%s\n' '<TestRun />' > "$staging/trx/engineering.trx"
                printf '%s\n' '{}' > "$staging/supervisor-result.json"
                ;;
              publish)
                bundle="$(value --bundle-root "$@")"
                case "$bundle" in *j1-bundle) label=j1 ;; *) label=j0 ;; esac
                if [[ "$label" == j1 && "$SELF_LOCK_TEST_DELAYED_DESCENDANT" == true && ! -f "$SELF_LOCK_TEST_DESCENDANT_MARKER" ]]; then
                  printf '%s\n' publisher-before-tree-exit >> "$SELF_LOCK_TEST_CALLS"
                fi
                printf 'publish %s\n' "$label" >> "$SELF_LOCK_TEST_CALLS"
                printf '{"authority_receipt_path":"/authority/%s.json","payload_path":"/payload/%s","publication_id":"%064d"}\n' "$label" "$label" 0
                ;;
              evaluate)
                printf '%s\n' evaluate >> "$SELF_LOCK_TEST_CALLS"
                decision="$(cat "$SELF_LOCK_TEST_DECISION")"
                allow=false
                status=2
                if [[ "$decision" == SELF_LOCK_CONFIRMED ]]; then allow=true; status=0; fi
                if [[ "$decision" == TRUE_RED_CONFIRMED ]]; then status=1; fi
                target="$(cat "$SELF_LOCK_TEST_TARGET")"
                printf '{"schema_version":1,"decision":"%s","authorization":{"allow_exact_revert":%s,"changes_gate_status":false,"rerun_required_after_dev_push":true,"confirmed_red_gates":["engineering"],"candidate_head_sha":"0000000000000000000000000000000000000000","target_merge_sha":"%s"},"reason_codes":[],"judgments":[]}\n' "$decision" "$allow" "$target"
                exit "$status"
                ;;
              *) exit 2 ;;
            esac
            """;

        private void Commit(string message, string path, string content)
        {
            var full = Path.Combine(Repository, path);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(full)!);
            ScriptHarnessScratch.WriteScratchText(full, content);
            Git("add", "--", path);
            Git("commit", "-m", message);
        }

        private string CommitTree(string treeSource, IReadOnlyList<string> parents, string message)
        {
            var arguments = new List<string>
            {
                "commit-tree", GitText("rev-parse", treeSource + "^{tree}"),
            };
            foreach (var parent in parents)
            {
                arguments.Add("-p");
                arguments.Add(parent);
            }
            arguments.Add("-m");
            arguments.Add(message);
            return GitText(arguments.ToArray());
        }

        private void ConfigureRepository()
        {
            Git("config", "--local", "user.name", "Probe Wiring Test");
            Git("config", "--local", "user.email", "probe-wiring@example.invalid");
            Git("config", "--local", "commit.gpgsign", "false");
            Git("config", "--local", "tag.gpgsign", "false");
            Git("config", "--local", "core.hooksPath", "/dev/null");
            Git("config", "--local", "gc.auto", "0");
            Git("config", "--local", "maintenance.auto", "false");
        }

        private void Git(params string[] arguments)
        {
            var result = GitRun(arguments);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
        }

        private string GitText(params string[] arguments)
        {
            var result = GitRun(arguments);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private ProcessOutput GitRun(IEnumerable<string> arguments) => TestProcessRunner.Run(
            "/usr/bin/env",
            [
                "-u", "GIT_AUTHOR_NAME",
                "-u", "GIT_AUTHOR_EMAIL",
                "-u", "GIT_COMMITTER_NAME",
                "-u", "GIT_COMMITTER_EMAIL",
                "-u", "GIT_CONFIG",
                "-u", "GIT_CONFIG_PARAMETERS",
                "-u", "GIT_TEMPLATE_DIR",
                "GIT_CONFIG_GLOBAL=/dev/null",
                "GIT_CONFIG_SYSTEM=/dev/null",
                "GIT_CONFIG_NOSYSTEM=1",
                "GIT_CONFIG_COUNT=0",
                "/usr/bin/git", "-C", Repository,
                .. arguments,
            ],
            Repository,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        public void Dispose() => temporary.Dispose();
    }
}

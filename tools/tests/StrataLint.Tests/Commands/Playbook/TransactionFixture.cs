using StrataLint.Engine;
using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

// 本类此前作为**嵌套 partial 类**散布在 DepositCoverWorkflowScriptTests 的 7 个文件片段中,
// 却被 5 处 StrataLint.Tests 内部用例与 1 处 ScriptTests 共同消费 ——
// 「共享夹具寄居在某个测试类内部」。提升为顶层类,使 ScriptTests 不必再引用
// StrataLint.Tests 的测试**类型**(#5419 的 D 2→1 前置)。
//
// **纯搬迁**:可见性、成员、行为逐字不变。唯一风险是搬漏,
// 而嵌套改顶层会让任何未更新的引用在**编译期** CS0246 —— 编译器是这一层的判官。

internal sealed partial class TransactionFixture : IDisposable
{
    internal const string AtomId = "atom-1";
    internal const string SecondaryAtomId = "atom-2";
    internal const string Gid = "D5/S0/Carrier/Probe.probe";
    internal const string LeanPath = "D5/S0/Carrier/Probe.lean";
    internal const string SecondaryGid =
        "D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition";
    internal const string SecondaryLeanPath = "D5/S3/Observer/WindowRegisterCRT.lean";
    internal const string NewGid = "D5/S2/NewModule.new_module";
    internal const string NewLeanPath = "D5/S2/NewModule.lean";
    internal const string NewEmissionPath = "Blueprint/D5/S2/NewModule.md";
    internal const string DefinitionPath = "Blueprint/D5/S0/Carrier/Probe.scribe.cs";
    internal const string EmissionPath = "Blueprint/D5/S0/Carrier/Probe.md";
    internal const string LedgerPath = FrozenLedgerChangeClassifier.AcceptedRoot;
    internal const string BackfillPath = "Meta/BACKFILL.yaml";
    private const string ScriptPath = "tools/scripts/workflow/playbook-workflows.sh";
    private readonly TemporaryDirectory temporary = new();
    private readonly string binPath;
    private readonly string callsPath;
    private readonly string freezeProbePath;

    internal TransactionFixture()
    {
        Root = temporary.Path;
        binPath = Path.Combine(Root, "bin");
        callsPath = Path.Combine(Root, "calls");
        freezeProbePath = Path.Combine(Root, "freeze-probes");
        Directory.CreateDirectory(binPath);
        CopyScript();
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), "Makefile"),
            Path.Combine(Root, "Makefile"));
        WriteFile(
            ".gitignore",
            ".lake/\n.report-source\nbin/\ncalls\nfreeze-probes\nfail-ledger-once\n.ledger-frozen-status\n");
        WriteFile(LeanPath, ExactSixLineLean(Gid, "theorem probe : True := by trivial\n"));
        WriteFile(DefinitionPath, "definition baseline\n");
        WriteFile(EmissionPath, "emission: baseline\n");
        Directory.CreateDirectory(Path.Combine(Root, LedgerPath));
        File.WriteAllBytes(Path.Combine(binPath, "StrataLint.Cli.dll"), []);
        WriteFile(BackfillPath, $"atom_id: {AtomId}\ncoverage: false\naligned: false\n");
        WriteMakeStub();
        WriteDotnetStub();
        WriteGitGuardStub();
        Git("init", "-q");
        Git("config", "user.email", "playbook@example.invalid");
        Git("config", "user.name", "Playbook Test");
        Git("add", "-A");
        Git("commit", "-qm", "fixture baseline");
        File.Copy(Path.Combine(Root, LeanPath), Path.Combine(Root, ".report-source"));
    }

    internal string Root { get; }

    internal string BackfillContents() => File.ReadAllText(Path.Combine(Root, BackfillPath));

    internal string EmissionContents() => File.ReadAllText(Path.Combine(Root, EmissionPath));

    internal void ChangeFormalization()
    {
        WriteFile(LeanPath, ExactSixLineLean(Gid, "theorem probe : True := by\n  trivial\n"));
        WriteFile(DefinitionPath, "definition deposited\n");
    }

    internal void AddNewFormalization(bool withMirror)
    {
        WriteFile(NewLeanPath, ExactSixLineLean(NewGid, "theorem new_module : True := by trivial\n"));
        if (withMirror)
        {
            WriteFile(NewEmissionPath, "emission: new module\n");
        }
    }

    internal void AddSecondaryFormalization()
    {
        WriteFile(SecondaryLeanPath,
            ExactSixLineLean(
                SecondaryGid,
                "theorem window_register_crt_decomposition : True := by trivial\n"));
        WriteFile(
            "Blueprint/D5/S3/Observer/WindowRegisterCRT.scribe.cs",
            "secondary definition\n");
        WriteFile(
            "Blueprint/D5/S3/Observer/WindowRegisterCRT.md",
            "secondary emission\n");
    }

    internal void FailAfterNextFreeze() => WriteFile("fail-ledger-once", "1\n");

    internal void FailFrozenQuery() => WriteFile(".ledger-frozen-status", "2\n");

    internal void WriteRevokedSnapshot()
    {
        WriteLedger(Array.Empty<string>());
    }

    internal void WriteActiveFreeze()
    {
        var freeze = JsonSerializer.Serialize(new
        {
            event_hash =
                "sha256:3333333333333333333333333333333333333333333333333333333333333333",
            event_type = "Freeze",
            payload = new
            {
                declaration_statement_ids = Array.Empty<object>(),
                descriptor_selector = LeanPath,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                statement_id =
                    "sha256:3333333333333333333333333333333333333333333333333333333333333333",
            },
            schema_version = 5,
        });
        WriteLedger(freeze);
        WriteFile(".ledger-frozen-status", "0\n");
    }

    internal int CommitCount() => int.Parse(Git("rev-list", "--count", "HEAD").Trim());

    internal int FreezeCount(string leanPath = LeanPath) =>
        Directory.EnumerateFiles(Path.Combine(Root, LedgerPath), "*.json")
        .Count(path =>
        {
            using var document = JsonDocument.Parse(File.ReadAllText(path));
            var root = document.RootElement;
            if (!root.TryGetProperty("event_type", out var eventType)
                || eventType.GetString() != "Freeze")
            {
                return false;
            }

            var payload = root.GetProperty("payload");
            var selector = payload.TryGetProperty(
                "descriptor_selector",
                out var descriptorSelector)
                ? descriptorSelector.GetString()
                : null;
            return selector == leanPath;
        });

    private void WriteLedger(params string[] events)
    {
        WriteLedger(events.Select(static (json, index) => ($"fixture-{index}.json", json)).ToArray());
    }

    private void WriteLedger(params (string FileName, string Json)[] events)
    {
        var directory = Path.Combine(Root, LedgerPath);
        foreach (var path in Directory.EnumerateFiles(directory, "*.json")) File.Delete(path);
        foreach (var (fileName, json) in events)
        {
            File.WriteAllText(
                Path.Combine(directory, fileName),
                json + "\n",
                new UTF8Encoding(false));
        }
    }

    internal string[] Status() => Git("status", "--porcelain=v1")
        .Split('\n', StringSplitOptions.RemoveEmptyEntries);

    internal string[] TrackedPaths() => Git("ls-files")
        .Split('\n', StringSplitOptions.RemoveEmptyEntries);

    internal string[] LedgerState() =>
        Directory.EnumerateFiles(Path.Combine(Root, LedgerPath), "*.json")
            .Order(StringComparer.Ordinal)
            .Select(path => Path.GetRelativePath(Root, path) + "\n" + File.ReadAllText(path))
            .ToArray();

    internal string[] CallKinds() => !File.Exists(callsPath)
        ? []
        : File.ReadAllLines(callsPath).Select(static call =>
        {
            if (!call.StartsWith("dotnet:", StringComparison.Ordinal)) return call;
            var command = call["dotnet:".Length..];
            var separator = command.IndexOf(' ');
            return "dotnet:" + (separator < 0 ? command : command[..separator]);
        }).ToArray();

    internal string[] Calls() => File.Exists(callsPath) ? File.ReadAllLines(callsPath) : [];

    internal void ClearCalls()
    {
        if (File.Exists(callsPath)) File.Delete(callsPath);
    }

    private string Git(params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/git",
            arguments,
            Root,
            TestBudgets.PlaybookProcessHangGuard,
            128 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                $"git {string.Join(' ', arguments)} failed: "
                + Encoding.UTF8.GetString(result.StandardError));
        }

        return Encoding.UTF8.GetString(result.StandardOutput);
    }

    private void WriteExecutable(string name, string body)
    {
        var path = Path.Combine(binPath, name);
        File.WriteAllText(
            path,
            "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n",
            new UTF8Encoding(false));
        if (OperatingSystem.IsWindows()) return;
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

    private void WriteFile(string relativePath, string content)
    {
        var path = Path.Combine(Root, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(path) ?? Root);
        File.WriteAllText(path, content, new UTF8Encoding(false));
    }

}

internal sealed partial class TransactionFixture
{
    internal int FreezeProbeCount() => File.Exists(freezeProbePath)
        ? File.ReadAllLines(freezeProbePath).Length
        : 0;

    private void CopyScript()
    {
        var root = TestRepositoryLayout.FindRoot();
        var target = Path.Combine(Root, ScriptPath);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.Copy(Path.Combine(root, ScriptPath), target);
    }

    private void WriteGitGuardStub() => WriteExecutable("git", """
        arguments=("$@")
        index=0
        while [[ $index -lt ${#arguments[@]} ]]; do
          token=${arguments[index]}
          case "$token" in
            -C|-c|--git-dir|--work-tree|--namespace|--super-prefix|--config-env)
              index=$((index + 2))
              ;;
            --git-dir=*|--work-tree=*|--namespace=*|--super-prefix=*|--config-env=*)
              index=$((index + 1))
              ;;
            --no-pager|--paginate|--bare|--literal-pathspecs|--no-literal-pathspecs|--glob-pathspecs|--noglob-pathspecs|--icase-pathspecs)
              index=$((index + 1))
              ;;
            --)
              index=$((index + 1))
              break
              ;;
            -*) index=$((index + 1)) ;;
            *) break ;;
          esac
        done
        subcommand=${arguments[index]:-}
        if [[ $subcommand == hash-object && ${PLAYBOOK_INSIDE_LEDGER_STUB:-0} != 1 ]]; then
          printf 'freeze-exists\n' >> "$PLAYBOOK_TEST_FREEZE_PROBES"
        fi
        if [[ $subcommand == merge ]]; then
          printf 'git-branch-merge:%s\n' "${arguments[*]}" >> "$PLAYBOOK_TEST_CALLS"
          exit 97
        fi
        exec /usr/bin/git "${arguments[@]}"
        """);

    private void WriteMakeStub() => WriteExecutable("make", """
        printf 'make:%s\n' "$*" >> "$PLAYBOOK_TEST_CALLS"
        case "${1:-}" in
          lean-report)
            mkdir -p .lake/build/stratalint
            printf '{"schema":"synthetic-lean-report"}\n' \
              > .lake/build/stratalint/raw-lean-report.json
            if [[ ${PLAYBOOK_STALE_REPORT:-0} != 1 ]]; then
              cp D5/S0/Carrier/Probe.lean .report-source
            fi
            ;;
          emit)
            if ! cmp -s D5/S0/Carrier/Probe.lean .report-source; then
              echo 'STALE_LEAN_REPORT emit refused stale input' >&2
              exit 41
            fi
            mkdir -p Generated
            printf '{"truth":{"nodes":[{"repo_path":"D5/S0/Carrier/Probe.lean","state":"closed"}]}}\n' \
              > Generated/truth-graph.v1.json
            if grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
              printf 'emission: covered\n' > Blueprint/D5/S0/Carrier/Probe.md
            else
              printf 'emission: open\n' > Blueprint/D5/S0/Carrier/Probe.md
            fi
            ;;
        esac
        """);

    private void WriteDotnetStub() => WriteExecutable("dotnet", """
        args="$*"
        command=${args##* -- }
        printf 'dotnet:%s\n' "$command" >> "$PLAYBOOK_TEST_CALLS"
        read -r -a parts <<< "$command"
        case "${parts[0]:-}" in
          deposit-header-check)
            if [[ ${parts[1]:-} != --target \
                || ${parts[2]:-} != "${PLAYBOOK_TARGET_MODULE:-}" ]]; then
              echo 'DEPOSIT_HEADER_CHECK_INVALID synthetic target transport mismatch' >&2
              exit 96
            fi
            if [[ ${PLAYBOOK_REJECT_DEPOSIT_HEADER:-0} == 1 ]]; then
              printf 'SL-012 %s: expected the exact six-line header at byte zero\n' \
                "${parts[2]}"
              exit 1
            fi
            ;;
          ledger-frozen)
            if [[ ${parts[1]:-} != --target \
                || ${parts[2]:-} != "${PLAYBOOK_TARGET_MODULE:-}" ]]; then
              echo 'LEDGER_FROZEN_INVALID synthetic target transport mismatch' >&2
              exit 96
            fi
            if [[ ${PLAYBOOK_USE_CANONICAL_FROZEN_QUERY:-0} == 1 ]]; then
              exec "$PLAYBOOK_REAL_CLI" "${parts[@]}"
            fi
            status=1
            [[ ! -f .ledger-frozen-status ]] || status=$(<.ledger-frozen-status)
            [[ $status != 2 ]] || echo 'LEDGER_FROZEN_INVALID synthetic failure' >&2
            exit "$status"
            ;;
          ledger-align)
            if [[ ${parts[1]:-} == --add ]]; then
              if [[ ${parts[2]:-} != "${PLAYBOOK_TARGET_MODULE:-}" \
                  || ${parts[3]:-} != --candidate-lean-report ]]; then
                echo 'LEDGER_ALIGN_INVALID synthetic target transport mismatch' >&2
                exit 97
              fi
            elif [[ ${parts[1]:-} != --candidate-lean-report ]]; then
              echo 'LEDGER_ALIGN_INVALID synthetic target transport mismatch' >&2
              exit 97
            fi
            target_module=${PLAYBOOK_TARGET_MODULE:-D5/S0/Carrier/Probe.lean}
            if [[ $target_module == D5/S0/Carrier/Probe.lean ]]; then
              event_id=2222222222222222222222222222222222222222222222222222222222222222
            else
              event_id=3333333333333333333333333333333333333333333333333333333333333333
            fi
            printf '{"event_hash":"sha256:%s","event_type":"Freeze","payload":{"declaration_statement_ids":[],"descriptor_selector":"%s","prerequisite_frozen_node_ids":[],"statement_id":"sha256:%s"},"schema_version":5}\n' \
              "$event_id" "$target_module" "$event_id" \
              > "Golden/Frozen/accepted/${event_id}.json"
            printf '0\n' > .ledger-frozen-status
            if [[ -f fail-ledger-once ]]; then
              rm fail-ledger-once
              echo 'LEDGER_ALIGN_INTERRUPTED synthetic kill after align' >&2
              exit 75
            fi
            ;;
          cover-atom)
            atom=''
            gid=''
            align=0
            for ((index=1; index<${#parts[@]}; index+=2)); do
              case "${parts[index]}" in
                --cover-atom) atom=${parts[index+1]} ;;
                --gid) gid=${parts[index+1]} ;;
                --align-scribe-receipt) align=1 ;;
              esac
            done
            if [[ ${PLAYBOOK_COVER_DISPOSITION_FAILURE:-0} == 1 ]]; then
              printf 'atom_id: %s\ncoverage: false\naligned: false\ncover_disposition: synthetic\n' "$atom" \
                > Meta/BACKFILL.yaml
              [[ $align -eq 0 ]] || echo 'COVER_ATOM_ALIGNED cover=failed' >&2
              echo 'COVER_INVALID synthetic disposition' >&2
              exit 1
            fi
            secondary=''
            existing_atom=$(sed -n 's/^atom_id: //p' Meta/BACKFILL.yaml)
            if [[ $existing_atom == "$atom" ]] \
                && grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
              [[ $gid == D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition ]] || {
                echo 'COVER_INVALID hosted cover omitted the selected secondary GID' >&2
                exit 1
              }
              secondary='secondary: true'
            fi
            printf 'atom_id: %s\ncoverage: true\naligned: false\n%s\n' \
              "$atom" "$secondary" > Meta/BACKFILL.yaml
            if [[ $align -eq 1 ]]; then
              definition_path="Blueprint/${gid%.*}.scribe.cs"
              verified_emission=''
              if [[ -s $definition_path ]] \
                  && grep -q "^atom_id: ${atom}$" Meta/BACKFILL.yaml \
                  && grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                verified_emission='emission: covered'
              fi
              [[ $verified_emission == 'emission: covered' ]] || {
                echo 'COVER_ATOM_ALIGNED cover=passed align=failed' >&2
                echo 'ALIGN_SCRIBE_RECEIPT_INVALID no verified in-process Scribe emission' >&2
                exit 1
              }
              printf 'atom_id: %s\ncoverage: true\naligned: covered\n%s\n' \
                "$atom" "$secondary" > Meta/BACKFILL.yaml
              echo 'COVER_ATOM_ALIGNED cover=passed align=passed'
              echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=true'
            fi
            ;;
          align-scribe-receipt)
            atom=''
            gid=''
            for ((index=1; index<${#parts[@]}; index+=2)); do
              case "${parts[index]}" in
                --atom-id) atom=${parts[index+1]} ;;
                --gid) gid=${parts[index+1]} ;;
              esac
            done
            definition_path="Blueprint/${gid%.*}.scribe.cs"
            verified_emission=''
            if [[ -s $definition_path ]] \
                && grep -q "^atom_id: ${atom}$" Meta/BACKFILL.yaml \
                && grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
              verified_emission='emission: covered'
            fi
            [[ $verified_emission == 'emission: covered' ]] || {
              echo 'ALIGN_SCRIBE_RECEIPT_INVALID no verified in-process Scribe emission' >&2
              exit 1
            }
            secondary=''
            grep -q '^secondary: true$' Meta/BACKFILL.yaml && secondary='secondary: true'
            if grep -q '^aligned: covered$' Meta/BACKFILL.yaml; then
              echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=false'
            else
              printf 'atom_id: %s\ncoverage: true\naligned: covered\n%s\n' \
                "$atom" "$secondary" > Meta/BACKFILL.yaml
              echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=true'
            fi
            ;;
        esac
        """);

    internal ProcessOutput Run(
        string command,
        string gid = Gid,
        string atomId = AtomId,
        bool staleReport = false,
        bool coverDispositionFailure = false,
        TimeSpan? timeout = null,
        string? baseRevision = null,
        bool rejectDepositHeader = false,
        bool useCanonicalFrozenQuery = false) =>
        TestProcessRunner.Run(
            "/usr/bin/env",
            [
                $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                $"PLAYBOOK_TEST_CALLS={callsPath}",
                $"PLAYBOOK_TEST_FREEZE_PROBES={freezeProbePath}",
                $"PLAYBOOK_STALE_REPORT={(staleReport ? "1" : "0")}",
                $"PLAYBOOK_COVER_DISPOSITION_FAILURE={(coverDispositionFailure ? "1" : "0")}",
                $"PLAYBOOK_TARGET_MODULE={(gid == SecondaryGid ? SecondaryLeanPath : gid == NewGid ? NewLeanPath : LeanPath)}",
                $"PLAYBOOK_REJECT_DEPOSIT_HEADER={(rejectDepositHeader ? "1" : "0")}",
                $"PLAYBOOK_USE_CANONICAL_FROZEN_QUERY={(useCanonicalFrozenQuery ? "1" : "0")}",
                $"PLAYBOOK_REAL_CLI={Path.Combine(Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!, "StrataLint")}",
                "/bin/bash",
                Path.Combine(Root, ScriptPath),
                command,
                baseRevision ?? (command == "deposit" ? "HEAD" : "synthetic-base"),
                atomId,
                gid,
            ],
            Root,
            timeout ?? BoundedProcessRunner.HangDetectionBudget,
            128 * 1024);

    public void Dispose()
    {
        temporary.Dispose();
    }
}

internal sealed partial class TransactionFixture
{
    internal string HeadRevision() => Git("rev-parse", "HEAD").Trim();

    internal string CommitAll(string message)
    {
        Git("add", "-A");
        Git("commit", "-qm", message);
        return HeadRevision();
    }

    internal string WriteAcceptedFreezeV5()
    {
        var identity = new string('4', 64);
        var relativePath = $"{LedgerPath}/{identity}.json";
        WriteFile(relativePath, JsonSerializer.Serialize(new
        {
            event_hash = "sha256:" + identity,
            event_type = "Freeze",
            payload = new
            {
                declaration_statement_ids = Array.Empty<object>(),
                descriptor_selector = LeanPath,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                statement_id = "sha256:" + identity,
            },
            schema_version = 5,
        }) + "\n");
        return relativePath;
    }

    internal string WriteLegacyFreeze()
    {
        var identity = new string('5', 64);
        var relativePath = $"{LedgerPath}/{identity}.json";
        WriteFile(relativePath, JsonSerializer.Serialize(new
        {
            event_type = "Freeze",
            payload = new { descriptor_selector = LeanPath },
            schema_version = 4,
        }) + "\n");
        return relativePath;
    }
}

internal sealed partial class TransactionFixture
{
    internal void ChangeFormalizationToSevenLineWrappedDigest()
    {
        WriteFile(LeanPath, DepositCoverWorkflowScriptTests.SevenLineWrappedDigest(
            Gid[..Gid.LastIndexOf('.')],
            "theorem probe : True := by trivial\n"));
        WriteFile(DefinitionPath, "definition deposited\n");
    }

    internal string[] BlueprintState()
    {
        var directory = Path.Combine(Root, "Blueprint");
        return Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Order(StringComparer.Ordinal)
            .Select(path => Path.GetRelativePath(Root, path) + "\n" + File.ReadAllText(path))
            .ToArray();
    }

    internal static string ExactSixLineLean(string gid, string declaration)
    {
        var documentGid = gid[..gid.LastIndexOf('.')];
        return $"/- GID: {documentGid}\n"
            + "   generality: G\n"
            + $"   mirror-B: D5/B/{documentGid[3..]}\n"
            + "   mirror-E: none(waiver:pure-definition)\n"
            + "   anchors: []\n"
            + "   digest: Synthetic deposit workflow fixture. -/\n"
            + declaration;
    }
}

internal sealed partial class TransactionFixture
{
    internal bool LeanReportExists() => File.Exists(
        Path.Combine(Root, ".lake/build/stratalint/raw-lean-report.json"));

    internal ProcessOutput RunMakeCover(bool includeAtomId) =>
        TestProcessRunner.Run(
            "/usr/bin/env",
            includeAtomId
                ?
                [
                    $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"PLAYBOOK_TEST_CALLS={callsPath}",
                    "/usr/bin/make",
                    "cover",
                    $"ATOM_ID={AtomId}",
                ]
                :
                [
                    $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"PLAYBOOK_TEST_CALLS={callsPath}",
                    "/usr/bin/make",
                    "cover",
                ],
            Root,
            TestBudgets.ShortProcessHangGuard,
            128 * 1024);
}

internal sealed partial class TransactionFixture
{
    internal string WriteBatchFile(string contents)
    {
        const string path = ".lake/cover-batch.tsv";
        WriteFile(path, contents);
        return path;
    }

    internal ProcessOutput RunBatch(string atomsFile, bool coverDispositionFailure = false) =>
        TestProcessRunner.Run(
            "/usr/bin/env",
            [
                $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                $"PLAYBOOK_TEST_CALLS={callsPath}",
                "PLAYBOOK_STALE_REPORT=0",
                $"PLAYBOOK_COVER_DISPOSITION_FAILURE={(coverDispositionFailure ? "1" : "0")}",
                "/bin/bash",
                Path.Combine(Root, ScriptPath),
                "cover-batch",
                "synthetic-base",
                atomsFile,
            ],
            Root,
            BoundedProcessRunner.HangDetectionBudget,
            128 * 1024);
}

internal sealed partial class TransactionFixture
{
    internal void WriteActiveFreezeForCurrentModule() => WriteActiveFreeze();

    internal void AddUnrelatedMalformedLedgerShard() => WriteFile(
        LedgerPath + "/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json",
        "{\"event_type\":\"Freeze\",\"payload\":{\"node_path\":\"D5/S4/Unrelated.lean\"\n");
}

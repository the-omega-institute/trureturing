using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Tests;
using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

public sealed class BranchGrammarSignalWorkflowTests
{
    private const string SignalStepName = "Signal PR head branch grammar";
    private const string FixtureHeadRef = "lane/governance/w33-branch-signal";
    private static string ReadWorkflow() => File.ReadAllText(
        Path.Combine(RepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));

    [Fact]
    public void CandidateEngineeringHasBranchGrammarSignalAfterCandidateBuild()
    {
        var steps = CandidateEngineeringSteps();
        var buildIndex = Array.FindIndex(
            steps,
            static step => Scalar(step, "name") == "Build candidate with warnings as errors");
        var signalIndex = Array.FindIndex(
            steps,
            static step => Scalar(step, "name") == SignalStepName);

        Assert.True(buildIndex >= 0, "candidate build step is absent");
        Assert.True(signalIndex > buildIndex, "branch grammar signal must follow the candidate build");
        var script = Scalar(steps[signalIndex], "run");
        Assert.Contains(
            "dotnet run --project candidate/tools/StrataLint.Cli/StrataLint.Cli.csproj",
            script,
            StringComparison.Ordinal);
        Assert.Contains("--configuration Release --no-build", script, StringComparison.Ordinal);
        Assert.Contains("worktree validate-branch --branch \"$HEAD_REF\"", script, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateBuildAndBranchGrammarSignalAreNotEngineeringPlanGated()
    {
        var steps = CandidateEngineeringSteps();
        var expectedCondition =
            "github.event_name == 'pull_request_target' && github.event.pull_request.base.ref == 'dev'";

        foreach (var name in new[] { "Build candidate with warnings as errors", SignalStepName })
        {
            var step = Assert.Single(steps, candidate => Scalar(candidate, "name") == name);
            Assert.Equal(expectedCondition, NormalizeCondition(Scalar(step, "if")));
            Assert.DoesNotContain("run_required", Scalar(step, "if"), StringComparison.Ordinal);
        }
    }

    [Fact]
    public void BranchGrammarSignalRunsOnlyForDevPullRequestTargets()
    {
        var condition = Scalar(SignalStep(), "if");

        Assert.Equal(
            "github.event_name == 'pull_request_target' && github.event.pull_request.base.ref == 'dev'",
            NormalizeCondition(condition));
    }

    [Fact]
    public void BranchGrammarSignalPassesHeadRefThroughEnvironmentWithoutRunInterpolation()
    {
        var step = SignalStep();
        var environment = Mapping(step, "env");
        var script = Scalar(step, "run");

        Assert.Equal("${{ github.event.pull_request.head.ref }}", Scalar(environment, "HEAD_REF"));
        Assert.DoesNotContain("${{", script, StringComparison.Ordinal);
    }

    [Fact]
    public void BranchGrammarSignalAcceptsCanonicalReceipt()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunSignal("canonical");

        Assert.Equal(0, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("BRANCH_GRAMMAR_SIGNAL status=canonical", output, StringComparison.Ordinal);
        Assert.DoesNotContain("::warning", output, StringComparison.Ordinal);
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void BranchGrammarSignalTreatsExitOneAsAdvisorySuccess()
    {
        if (OperatingSystem.IsWindows()) return;

        var script = Scalar(SignalStep(), "run");
        var summaryFormat = ShellSingleQuotedConstant(script, "summary_format");
        var result = RunSignal("nonconforming");

        Assert.Equal(0, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("BRANCH_GRAMMAR_SIGNAL status=BRANCH_GRAMMAR_NONCONFORMING", output, StringComparison.Ordinal);
        var warningPrefix = Encoding.UTF8.GetBytes("::warning title=PR head branch grammar::");
        var warningOffset = result.StandardOutput.AsSpan().IndexOf(warningPrefix);
        Assert.True(warningOffset >= 0, "branch grammar warning is absent");
        var warningAndTail = result.StandardOutput.AsSpan(warningOffset + warningPrefix.Length);
        var warningTerminator = warningAndTail.IndexOf((byte)'\n');
        Assert.True(warningTerminator >= 0, "branch grammar warning is not line terminated");
        Assert.Equal(
            Encoding.UTF8.GetBytes(
                ProjectSummary(summaryFormat, FixtureHeadRef, "BRANCH_GRAMMAR_NONCONFORMING")),
            warningAndTail[..(warningTerminator + 1)].ToArray());
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void BranchGrammarSignalFailsClosedForUnexpectedExitCodesAndInvalidOutput()
    {
        if (OperatingSystem.IsWindows()) return;

        var step = SignalStep();
        var script = Scalar(step, "run");

        Assert.False(step.Children.ContainsKey(new YamlScalarNode("continue-on-error")));
        Assert.Contains("set +e", script, StringComparison.Ordinal);
        Assert.Contains("validation_exit=$?", script, StringComparison.Ordinal);
        Assert.Contains("set -e", script, StringComparison.Ordinal);
        Assert.Contains("exit \"$validation_exit\"", CaseBody(script, "\\*"), StringComparison.Ordinal);
        Assert.Contains("if ! jq -e -s", script, StringComparison.Ordinal);
        Assert.Contains("--arg head_ref \"$HEAD_REF\"", script, StringComparison.Ordinal);
        Assert.Contains("detector_status=invalid_output", script, StringComparison.Ordinal);
        Assert.Contains("exit 1", script, StringComparison.Ordinal);
        Assert.DoesNotContain("|| true", script, StringComparison.Ordinal);

        foreach (var invalidCase in new[] { "missing", "malformed", "multiple", "inconsistent" })
        {
            var result = RunSignal(invalidCase);
            Assert.Equal(1, result.ExitCode);
            Assert.Contains(
                "detector_status=invalid_output",
                Encoding.UTF8.GetString(result.StandardError),
                StringComparison.Ordinal);
        }

        var unexpectedExit = RunSignal("unexpected-exit");
        Assert.Equal(2, unexpectedExit.ExitCode);
        Assert.Contains(
            "detector_status=failed exit=2",
            Encoding.UTF8.GetString(unexpectedExit.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void BranchGrammarSignalRejectsReceiptForDifferentHeadRef()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunSignal("wrong-branch");

        Assert.Equal(1, result.ExitCode);
        Assert.Contains(
            "detector_status=invalid_output",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void BranchGrammarSignalLengthClauseRejectsMultipleReceiptsAtValidatorExitZero()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-length", validatorExit: 0));
    }

    [Fact]
    public void BranchGrammarSignalLengthClauseRejectsMultipleReceiptsAtValidatorExitOne()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-length", validatorExit: 1));
    }

    [Fact]
    public void BranchGrammarSignalEventClauseRejectsUnexpectedEventAtValidatorExitZero()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-event", validatorExit: 0));
    }

    [Fact]
    public void BranchGrammarSignalEventClauseRejectsUnexpectedEventAtValidatorExitOne()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-event", validatorExit: 1));
    }

    [Fact]
    public void BranchGrammarSignalStatusClauseRejectsUnexpectedStatusAtValidatorExitZero()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-status", validatorExit: 0));
    }

    [Fact]
    public void BranchGrammarSignalStatusClauseRejectsUnexpectedStatusAtValidatorExitOne()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-status", validatorExit: 1));
    }

    [Fact]
    public void BranchGrammarSignalBranchClauseRejectsDifferentHeadAtValidatorExitZero()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-branch", validatorExit: 0));
    }

    [Fact]
    public void BranchGrammarSignalBranchClauseRejectsDifferentHeadAtValidatorExitOne()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertInvalidReceipt(RunSignal("clause-branch", validatorExit: 1));
    }

    [Fact]
    public void BranchGrammarSignalRejectsMalformedReceiptFamiliesAtValidatorExitZero()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertMalformedReceiptFamiliesAreRejected(validatorExit: 0);
    }

    [Fact]
    public void BranchGrammarSignalRejectsMalformedReceiptFamiliesAtValidatorExitOne()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertMalformedReceiptFamiliesAreRejected(validatorExit: 1);
    }

    [Fact]
    public void BranchGrammarSignalSummaryWordingIsExactProjectionOfSingleFixedTemplate()
    {
        if (OperatingSystem.IsWindows()) return;

        var script = Scalar(SignalStep(), "run");
        var summaryFormat = ShellSingleQuotedConstant(script, "summary_format");

        Assert.Equal(
            "73f73b99353408ba133ea8ddb37539a2c8f4b56b9c500be9ab0166c200ebe0fb",
            Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(summaryFormat))).ToLowerInvariant());

        foreach (var (validationCase, validatorExit, expectedStatus) in new[]
        {
            ("canonical", 0, "canonical"),
            ("nonconforming", 1, "BRANCH_GRAMMAR_NONCONFORMING"),
        })
        {
            var result = RunSignalWithSummary(validationCase, validatorExit);

            Assert.Equal(0, result.Process.ExitCode);
            Assert.Equal(
                ProjectSummary(summaryFormat, FixtureHeadRef, expectedStatus),
                result.Summary);
        }
    }

    [Fact]
    public void BranchGrammarSignalWorkflowDoesNotOwnBranchGrammarVocabulary()
    {
        var signalSurface = string.Join(
            "\n",
            Scalar(SignalStep(), "name"),
            Scalar(SignalStep(), "if"),
            Scalar(SignalStep(), "run"));

        Assert.DoesNotContain(
            $"{WorktreeCommand.CreationNamespace}/",
            signalSurface,
            StringComparison.Ordinal);
        Assert.All(
            WorktreeCommand.CreationKinds,
            kind => Assert.DoesNotContain(kind, signalSurface, StringComparison.Ordinal));
    }

    [Fact]
    public void BranchGrammarSignalRunsNoGitCommands()
    {
        var script = Scalar(SignalStep(), "run");

        Assert.DoesNotMatch(
            new Regex(@"\bgit\b", RegexOptions.CultureInvariant | RegexOptions.IgnoreCase),
            script);
    }

    private static YamlMappingNode[] CandidateEngineeringSteps()
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(ReadWorkflow()));
        var root = Assert.IsType<YamlMappingNode>(Assert.Single(stream.Documents).RootNode);
        var jobs = Mapping(root, "jobs");
        var engineering = Mapping(jobs, "candidate-engineering");
        return Assert.IsType<YamlSequenceNode>(
                engineering.Children[new YamlScalarNode("steps")])
            .Children
            .OfType<YamlMappingNode>()
            .ToArray();
    }

    private static YamlMappingNode SignalStep() =>
        Assert.Single(
            CandidateEngineeringSteps(),
            static step => Scalar(step, "name") == SignalStepName);

    private static string CaseBody(string script, string label)
    {
        var match = Regex.Match(
            script,
            $@"(?ms)^\s*{label}\)\s*(?<body>.*?)^\s*;;");
        Assert.True(match.Success, $"case arm '{label})' is absent");
        return match.Groups["body"].Value;
    }

    private static string NormalizeCondition(string condition) =>
        Regex.Replace(condition.Trim(), @"\s+", " ", RegexOptions.CultureInvariant);

    private static void AssertMalformedReceiptFamiliesAreRejected(int validatorExit)
    {
        foreach (var validationCase in new[] { "missing", "malformed", "multiple", "inconsistent", "wrong-branch" })
        {
            AssertInvalidReceipt(RunSignal(validationCase, validatorExit));
        }
    }

    private static void AssertInvalidReceipt(ProcessOutput result)
    {
        Assert.Equal(1, result.ExitCode);
        Assert.Contains(
            "detector_status=invalid_output",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    private static string ShellSingleQuotedConstant(string script, string name)
    {
        var matches = Regex.Matches(
            script,
            $@"(?m)^{Regex.Escape(name)}='(?<value>[^']*)'$",
            RegexOptions.CultureInvariant);
        var match = Assert.Single(matches.Cast<Match>());
        return match.Groups["value"].Value;
    }

    private static string ProjectSummary(string format, string headRef, string status)
    {
        var projection = format.Replace(@"\n", "\n", StringComparison.Ordinal);
        foreach (var value in new[] { headRef, status })
        {
            var placeholder = projection.IndexOf("%s", StringComparison.Ordinal);
            Assert.True(placeholder >= 0, "summary_format has too few placeholders");
            projection = string.Concat(
                projection.AsSpan(0, placeholder),
                value,
                projection.AsSpan(placeholder + 2));
        }

        Assert.DoesNotContain("%s", projection, StringComparison.Ordinal);
        return projection;
    }

    private static ProcessOutput RunSignal(string validationCase, int? validatorExit = null) =>
        RunSignalWithSummary(
            validationCase,
            validatorExit ?? (validationCase == "nonconforming" ? 1 : 0)).Process;

    private static SignalExecution RunSignalWithSummary(string validationCase, int validatorExit)
    {
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        Directory.CreateDirectory(binDirectory);
        var dotnetPath = Path.Combine(binDirectory, "dotnet");
        File.WriteAllText(
            dotnetPath,
            """
            #!/usr/bin/env bash
            validator_exit="$FAKE_VALIDATOR_EXIT"
            if [[ "$validator_exit" -eq 1 ]]; then
              expected_status=BRANCH_GRAMMAR_NONCONFORMING
              expected_canonical=false
            else
              expected_status=canonical
              expected_canonical=true
            fi
            emit_valid() {
              printf '{"event":"branch_validation","status":"%s","branch":"%s","canonical":%s}\n' \
                "$expected_status" "$HEAD_REF" "$expected_canonical"
            }
            case "$FAKE_VALIDATOR_CASE" in
              canonical)
                emit_valid
                ;;
              nonconforming)
                emit_valid
                ;;
              clause-length)
                emit_valid
                emit_valid
                ;;
              clause-event)
                printf '{"event":"other_event","status":"%s","branch":"%s","canonical":%s}\n' \
                  "$expected_status" "$HEAD_REF" "$expected_canonical"
                ;;
              clause-status)
                if [[ "$validator_exit" -eq 1 ]]; then
                  wrong_status=canonical
                else
                  wrong_status=BRANCH_GRAMMAR_NONCONFORMING
                fi
                printf '{"event":"branch_validation","status":"%s","branch":"%s","canonical":%s}\n' \
                  "$wrong_status" "$HEAD_REF" "$expected_canonical"
                ;;
              clause-branch)
                printf '{"event":"branch_validation","status":"%s","branch":"other/branch","canonical":%s}\n' \
                  "$expected_status" "$expected_canonical"
                ;;
              wrong-branch)
                printf '{"event":"branch_validation","status":"%s","branch":"other/branch","canonical":%s}\n' \
                  "$expected_status" "$expected_canonical"
                ;;
              missing)
                printf '{"event":"branch_validation","status":"%s","canonical":%s}\n' \
                  "$expected_status" "$expected_canonical"
                ;;
              malformed)
                printf '%s\n' 'not-json'
                ;;
              multiple)
                emit_valid
                emit_valid
                ;;
              inconsistent)
                if [[ "$expected_canonical" == true ]]; then
                  wrong_canonical=false
                else
                  wrong_canonical=true
                fi
                printf '{"event":"branch_validation","status":"%s","branch":"%s","canonical":%s}\n' \
                  "$expected_status" "$HEAD_REF" "$wrong_canonical"
                ;;
              unexpected-exit)
                exit 2
                ;;
              *)
                exit 97
                ;;
            esac
            exit "$validator_exit"
            """ + "\n");
        if (!OperatingSystem.IsWindows())
        {
            File.SetUnixFileMode(
                dotnetPath,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        var scriptPath = Path.Combine(fixture.Path, "signal.sh");
        File.WriteAllText(scriptPath, Scalar(SignalStep(), "run"));
        var summaryPath = Path.Combine(fixture.Path, "summary.md");
        var hostPath = Environment.GetEnvironmentVariable("PATH") ?? string.Empty;

        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            [
                $"PATH={binDirectory}:{hostPath}",
                $"HEAD_REF={FixtureHeadRef}",
                $"FAKE_VALIDATOR_CASE={validationCase}",
                $"FAKE_VALIDATOR_EXIT={validatorExit}",
                $"GITHUB_STEP_SUMMARY={summaryPath}",
                "/bin/bash",
                scriptPath,
            ],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

        var summary = File.Exists(summaryPath)
            ? TemporaryFileSystem.File.ReadAllText(summaryPath)
            : string.Empty;
        return new SignalExecution(process, summary);
    }

    private sealed record SignalExecution(ProcessOutput Process, string Summary);

    private static YamlMappingNode Mapping(YamlMappingNode parent, string key) =>
        Assert.IsType<YamlMappingNode>(parent.Children[new YamlScalarNode(key)]);

    private static string Scalar(YamlMappingNode parent, string key) =>
        parent.Children.TryGetValue(new YamlScalarNode(key), out var node)
        && node is YamlScalarNode scalar
            ? scalar.Value ?? string.Empty
            : string.Empty;
    // 测试映射解析器(ScribeTestMapDeriver.IsTemporaryFileSystemRoot)按**语法**排除
    // receiver 名为 TemporaryFileSystem 的读取:临时夹具路径是变量,静态归因不到,
    // 也不该归因——它不是仓库输入。仓内既有同形包装见
    // EmitFormalizationReceiptTests.cs 与 TruthReleaseBundleWriterTests.cs。
    private static class TemporaryFileSystem
    {
        internal static class File
        {
            internal static string ReadAllText(string path) => System.IO.File.ReadAllText(path);
        }
    }

}

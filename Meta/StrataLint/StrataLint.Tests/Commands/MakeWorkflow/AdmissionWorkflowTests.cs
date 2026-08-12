using YamlDotNet.RepresentationModel;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

[Trait("Category", "Script")] public sealed class AdmissionWorkflowTests
{
    private const string ProjectionTest =
        "StrataLint.Scribe.Tests.StatementProjectionPilotTests.LiveReportMatchesPinnedFixtureWhenAvailable";
    private const string DocumentTest =
        "StrataLint.Scribe.Tests.DocumentDiscoveryTests.GeneratedMarkdownIsDeterministicAndMatchesTheCommittedTree";

    [Fact]
    public void OldSideShadowHasNoNeedsKey()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(ShadowHasNoNeeds(workflow));
        var tampered = workflow.Replace("  old-side-report-shadow:\n    name:",
            "  old-side-report-shadow:\n    needs: lean-inspect\n    name:", StringComparison.Ordinal);
        Assert.False(ShadowHasNoNeeds(tampered));
    }

    [Fact]
    public void OldSideShadowHasNoNeedsPathToBaselineAdmission()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(NoNeedsPath(workflow, "old-side-report-shadow", "baseline-admission"));
        var tampered = workflow.Replace("    needs: lean-inspect\n    runs-on: ubuntu-latest\n    timeout-minutes: 20",
            "    needs: [lean-inspect, old-side-report-shadow]\n    runs-on: ubuntu-latest\n    timeout-minutes: 20", StringComparison.Ordinal);
        Assert.False(NoNeedsPath(tampered, "old-side-report-shadow", "baseline-admission"));
    }

    [Fact]
    public void BaselineAdmissionNeedsExactlyLeanInspect()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(BaselineNeedsExactlyLeanInspect(workflow));
        var tampered = workflow.Replace("    needs: lean-inspect\n    runs-on: ubuntu-latest\n    timeout-minutes: 20",
            "    needs: [lean-inspect, old-side-report-shadow]\n    runs-on: ubuntu-latest\n    timeout-minutes: 20", StringComparison.Ordinal);
        Assert.False(BaselineNeedsExactlyLeanInspect(tampered));
    }

    [Fact]
    public void OldSideShadowRecordsHitFailuresAndHasFinalNoRecordFallback()
    {
        var workflow = AdmissionWorkflow();
        var shadow = Job(workflow, "old-side-report-shadow");
        var steps = Assert.IsType<YamlSequenceNode>(shadow.Children[new YamlScalarNode("steps")]);
        var finalStep = steps.Children.OfType<YamlMappingNode>().Single(step =>
            Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value ==
            "Record unreported old-side shadow outcome");
        Assert.Equal("Record unreported old-side shadow outcome",
            Assert.IsType<YamlScalarNode>(finalStep.Children[new YamlScalarNode("name")]).Value);
        Assert.Equal("always()", Assert.IsType<YamlScalarNode>(finalStep.Children[new YamlScalarNode("if")]).Value);
        Assert.Contains("outcome=\"hit-error\"", workflow, StringComparison.Ordinal);
        Assert.Contains("outcome:\"no-record\"", workflow, StringComparison.Ordinal);
        Assert.Contains("--arg stage", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void OldSideShadowRecordIsUploadedAsRequiredArtifact()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(ShadowRecordArtifactUploadIsRequired(workflow));

        var tampered = workflow.Replace(
            "      - name: Upload old-side shadow record\n        if: always()\n        uses: actions/upload-artifact@v4\n        with:\n          name: old-side-shadow-record-${{ github.run_id }}-${{ github.run_attempt }}\n          path: ${{ runner.temp }}/old-side-shadow-record.json\n          if-no-files-found: error\n",
            "",
            StringComparison.Ordinal);
        Assert.False(ShadowRecordArtifactUploadIsRequired(tampered));
    }

    [Fact]
    public void OldSideShadowMakesAbsoluteLakeAvailableToLeanReport()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(ShadowMakesAbsoluteLakeAvailable(workflow));
        var tampered = workflow.Replace(
            "          echo \"$HOME/.elan/bin\" >> \"$GITHUB_PATH\"\n",
            "",
            StringComparison.Ordinal);
        Assert.False(ShadowMakesAbsoluteLakeAvailable(tampered));
    }

    [Fact]
    public void OldSideShadowToolchainInstallHasBoundedRetry()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(ShadowToolchainInstallHasBoundedRetry(workflow));

        var tampered = workflow.Replace(
            "          max_attempts=3\n",
            "          max_attempts=1\n",
            StringComparison.Ordinal);
        Assert.NotEqual(workflow, tampered);
        Assert.False(ShadowToolchainInstallHasBoundedRetry(tampered));
    }

    [Fact]
    public void ReconcilesStatementProjectionAfterProducingLiveReport()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var leanInspect = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(leanInspect.Children[new YamlScalarNode("steps")]);
        var namedSteps = steps.Children.OfType<YamlMappingNode>()
            .Select(static step => new
            {
                Node = step,
                Name = Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value,
            })
            .ToArray();
        var reportIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Produce source-bound canonical Lean reports");
        var reconciliationIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Reconcile pinned statement projections with live Lean report");
        Assert.True(reportIndex >= 0, "admission must produce the canonical live Lean report");
        Assert.True(reconciliationIndex > reportIndex, "reconciliation must run after report production");

        var reconciliation = namedSteps[reconciliationIndex].Node;
        var environment = Assert.IsType<YamlMappingNode>(reconciliation.Children[new YamlScalarNode("env")]);
        Assert.Equal("1", Assert.IsType<YamlScalarNode>(
            environment.Children[new YamlScalarNode("STRATALINT_REQUIRE_LIVE_REPORT")]).Value);
        var run = Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
        var expectedTests = new HashSet<string>(StringComparer.Ordinal)
        {
            ProjectionTest,
            DocumentTest,
        };
        var filterTests = Regex.Matches(run, @"FullyQualifiedName=([^|'\s]+)")
            .Select(static match => match.Groups[1].Value)
            .ToHashSet(StringComparer.Ordinal);
        var pythonExpectedBlock = Regex.Match(
            run,
            @"(?s)expected\s*=\s*\{(?<body>.*?)\}",
            RegexOptions.CultureInvariant);
        Assert.True(pythonExpectedBlock.Success, "the TRX validator must declare its expected test-name set");
        var validatorTests = Regex.Matches(pythonExpectedBlock.Groups["body"].Value, "[\"'](?<name>[^\"']+)[\"']")
            .Select(static match => match.Groups["name"].Value)
            .ToHashSet(StringComparer.Ordinal);

        Assert.Equal(expectedTests.Order(), filterTests.Order());
        Assert.Equal(expectedTests.Order(), validatorTests.Order());
        Assert.Equal(filterTests.Order(), validatorTests.Order());
        Assert.Contains("--logger \"trx;LogFileName=$results\"", run, StringComparison.Ordinal);
        Assert.Contains("len(results) != 2", run, StringComparison.Ordinal);
        Assert.Contains("set(names) != expected", run, StringComparison.Ordinal);
    }

    public static TheoryData<string, string?> RejectedTrxReports => new()
    {
        { "missing file", null },
        { "empty file", "" },
        { "invalid XML", "not xml" },
        { "non-Passed outcome", Trx((ProjectionTest, "Passed"), (DocumentTest, "NotExecuted")) },
        { "one result", Trx((ProjectionTest, "Passed")) },
        { "three results", Trx((ProjectionTest, "Passed"), (DocumentTest, "Passed"), ("Extra.Test", "Passed")) },
        { "duplicate name", Trx((ProjectionTest, "Passed"), (ProjectionTest, "Passed")) },
        { "different name set", Trx((ProjectionTest, "Passed"), ("Wrong.Test", "Passed")) },
    };

    [Theory]
    [MemberData(nameof(RejectedTrxReports))]
    public void TrxValidatorRejectsInvalidReports(string _, string? trx)
    {
        Assert.NotEqual(0, RunTrxValidator(trx));
    }

    [Fact]
    public void TrxValidatorAcceptsExactlyTheExpectedPassingReports()
    {
        Assert.Equal(0, RunTrxValidator(Trx((ProjectionTest, "Passed"), (DocumentTest, "Passed"))));
    }

    private static int RunTrxValidator(string? trx)
    {
        var run = ReconciliationRun();
        var scriptMatch = Regex.Match(
            run,
            "(?s)python3 -c '(?<script>.*?)' \\\"\\$results\\\"",
            RegexOptions.CultureInvariant);
        Assert.True(scriptMatch.Success, "the reconciliation step must invoke its embedded TRX validator");

        var temporaryDirectory = Path.Combine(Path.GetTempPath(), $"stratalint-trx-validator-{Guid.NewGuid():N}");
        Directory.CreateDirectory(temporaryDirectory);
        try
        {
            var trxPath = Path.Combine(temporaryDirectory, "results.trx");
            if (trx is not null)
                File.WriteAllText(trxPath, trx);
            var startInfo = new ProcessStartInfo
            {
                FileName = "python3",
                RedirectStandardError = true,
                RedirectStandardOutput = true,
                UseShellExecute = false,
            };
            startInfo.ArgumentList.Add("-c");
            startInfo.ArgumentList.Add(scriptMatch.Groups["script"].Value);
            startInfo.ArgumentList.Add(trxPath);
            using var process = Process.Start(startInfo)!;
            process.WaitForExit();
            return process.ExitCode;
        }
        finally
        {
            Directory.Delete(temporaryDirectory, recursive: true);
        }
    }

    private static string Trx(params (string Name, string Outcome)[] results) =>
        "<TestRun><Results>" + string.Concat(results.Select(static result =>
            $"<UnitTestResult testName=\"{result.Name}\" outcome=\"{result.Outcome}\" />")) + "</Results></TestRun>";

    private static string ReconciliationRun()
    {
        var workflow = File.ReadAllText(Path.Combine(FindRepositoryRoot(), ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var leanInspect = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(leanInspect.Children[new YamlScalarNode("steps")]);
        var reconciliation = steps.Children.OfType<YamlMappingNode>().Single(step =>
            Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value ==
            "Reconcile pinned statement projections with live Lean report");
        return Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
    }

    private static string AdmissionWorkflow() =>
        File.ReadAllText(Path.Combine(FindRepositoryRoot(), ".github", "workflows", "ci.yml"));

    private static YamlMappingNode Jobs(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        return Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
    }

    private static YamlMappingNode Job(string workflow, string job) =>
        Assert.IsType<YamlMappingNode>(Jobs(workflow).Children[new YamlScalarNode(job)]);

    private static bool ShadowHasNoNeeds(string workflow) =>
        !Job(workflow, "old-side-report-shadow").Children.ContainsKey(new YamlScalarNode("needs"));

    private static bool ShadowMakesAbsoluteLakeAvailable(string workflow)
    {
        var shadow = Job(workflow, "old-side-report-shadow");
        var steps = Assert.IsType<YamlSequenceNode>(shadow.Children[new YamlScalarNode("steps")]);
        var namedSteps = steps.Children.OfType<YamlMappingNode>().ToDictionary(
            static step => Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value!,
            StringComparer.Ordinal);
        var toolchainRun = Assert.IsType<YamlScalarNode>(namedSteps["Install pinned Lean toolchains"]
            .Children[new YamlScalarNode("run")]).Value!;
        var missRun = Assert.IsType<YamlScalarNode>(namedSteps["Produce and verify old-side report on cache miss"]
            .Children[new YamlScalarNode("run")]).Value!;
        var exportsElanBin = toolchainRun.Contains(
            "echo \"$HOME/.elan/bin\" >> \"$GITHUB_PATH\"", StringComparison.Ordinal);
        var passesAbsoluteLake = missRun.Contains(
            "LAKE_BIN=\"$HOME/.elan/bin/lake\" make lean-report", StringComparison.Ordinal);
        return exportsElanBin || passesAbsoluteLake;
    }

    private static bool ShadowToolchainInstallHasBoundedRetry(string workflow)
    {
        var shadow = Job(workflow, "old-side-report-shadow");
        var steps = Assert.IsType<YamlSequenceNode>(shadow.Children[new YamlScalarNode("steps")]);
        var install = steps.Children.OfType<YamlMappingNode>().Single(step =>
            step.Children.TryGetValue(new YamlScalarNode("name"), out var name) &&
            name is YamlScalarNode { Value: "Install pinned Lean toolchains" });
        var run = Assert.IsType<YamlScalarNode>(install.Children[new YamlScalarNode("run")]).Value!;
        var attempts = Regex.Match(run, @"(?m)^max_attempts=(?<count>[0-9]+)$");

        return attempts.Success && attempts.Groups["count"].Value == "3" &&
            run.Contains("delay_seconds=5", StringComparison.Ordinal) &&
            run.Contains("install_toolchain || status=$?", StringComparison.Ordinal) &&
            run.Contains("if (( attempt >= max_attempts )); then", StringComparison.Ordinal) &&
            run.Contains("exit 1", StringComparison.Ordinal) &&
            run.Contains("sleep \"$delay_seconds\"", StringComparison.Ordinal) &&
            run.Contains("attempt=$((attempt + 1))", StringComparison.Ordinal) &&
            run.Contains("delay_seconds=$((delay_seconds * 2))", StringComparison.Ordinal) &&
            run.Contains("retry_attempt=", StringComparison.Ordinal) &&
            run.Contains("exit_code=", StringComparison.Ordinal);
    }

    private static bool ShadowRecordArtifactUploadIsRequired(string workflow)
    {
        var shadow = Job(workflow, "old-side-report-shadow");
        var steps = Assert.IsType<YamlSequenceNode>(shadow.Children[new YamlScalarNode("steps")]);
        var upload = steps.Children.OfType<YamlMappingNode>().SingleOrDefault(step =>
            step.Children.TryGetValue(new YamlScalarNode("name"), out var name) &&
            name is YamlScalarNode scalar && scalar.Value == "Upload old-side shadow record");
        if (upload is null) return false;
        if (!upload.Children.TryGetValue(new YamlScalarNode("uses"), out var uses) ||
            uses is not YamlScalarNode { Value: "actions/upload-artifact@v4" }) return false;
        if (!upload.Children.TryGetValue(new YamlScalarNode("if"), out var condition) ||
            condition is not YamlScalarNode { Value: "always()" }) return false;
        if (upload.Children.TryGetValue(new YamlScalarNode("with"), out var withNode) &&
            withNode is YamlMappingNode with)
        {
            var name = with.Children.TryGetValue(new YamlScalarNode("name"), out var nameNode) &&
                nameNode is YamlScalarNode { Value: string value } &&
                value.Contains("${{ github.run_id }}", StringComparison.Ordinal) &&
                value.Contains("${{ github.run_attempt }}", StringComparison.Ordinal);
            var noFiles = with.Children.TryGetValue(new YamlScalarNode("if-no-files-found"), out var noFilesNode) &&
                noFilesNode is YamlScalarNode { Value: "error" };
            return name && noFiles;
        }
        return false;
    }

    private static bool BaselineNeedsExactlyLeanInspect(string workflow) =>
        Needs(Job(workflow, "baseline-admission")).SequenceEqual(["lean-inspect"], StringComparer.Ordinal);

    private static bool NoNeedsPath(string workflow, string source, string target)
    {
        var jobs = Jobs(workflow);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Stack<string>();
        pending.Push(target);
        while (pending.TryPop(out var current))
        {
            if (!visited.Add(current)) continue;
            if (current == source) return false;
            if (!jobs.Children.TryGetValue(new YamlScalarNode(current), out var node) || node is not YamlMappingNode job)
                continue;
            foreach (var dependency in Needs(job)) pending.Push(dependency);
        }
        return true;
    }

    private static IEnumerable<string> Needs(YamlMappingNode job)
    {
        if (!job.Children.TryGetValue(new YamlScalarNode("needs"), out var needs)) yield break;
        if (needs is YamlScalarNode scalar)
        {
            yield return scalar.Value!;
            yield break;
        }
        foreach (var item in Assert.IsType<YamlSequenceNode>(needs).Children.OfType<YamlScalarNode>())
            yield return item.Value!;
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory);
             directory is not null;
             directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml")))
                return directory.FullName;
        }

        throw new InvalidOperationException("Repository root was not found.");
    }
}

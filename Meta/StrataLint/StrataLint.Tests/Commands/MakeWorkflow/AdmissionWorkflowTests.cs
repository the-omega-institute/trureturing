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

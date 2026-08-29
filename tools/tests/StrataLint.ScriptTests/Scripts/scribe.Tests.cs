using StrataLint.Engine;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/scribe.sh")]
public sealed class ScribeScriptTests
{
    private const string ReportConsumerScriptPath = "tools/scripts/report/report-consumer.sh";

    [Fact]
    public void ScribeWrapperConsumesOnlyAPrecomputedLeanReport()
    {
        var script = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/scribe.sh"));

        Assert.DoesNotContain("lean-inspector/inspect.sh", script, StringComparison.Ordinal);
        Assert.DoesNotContain("SCRIBE_USE_EXISTING_REPORT", script, StringComparison.Ordinal);
        Assert.Contains(ReportConsumerScriptPath, script, StringComparison.Ordinal);
        Assert.Contains("scribe-consumer", script, StringComparison.Ordinal);
        Assert.Contains(".lake/build/stratalint/raw-lean-report.json", script, StringComparison.Ordinal);
        Assert.DoesNotContain("CHECK_ARGS=()", script, StringComparison.Ordinal);
        Assert.Contains("emit|emit-values|filemap) run_scribe \"$1\"", script, StringComparison.Ordinal);
        Assert.Contains("generators=(emit emit-values filemap dag)", script, StringComparison.Ordinal);
        Assert.Contains("for generator in \"${generators[@]}\"", script, StringComparison.Ordinal);
    }
}

using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;
using TemporaryFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed partial class DagLedgerMathlibReanchorWriterTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CapturedBundleRetainsLiveContextAndLazyMaterials(bool contextFirst)
    {
        var before = QLoad("registered_g");
        var after = QLoad("absent_parentheses", 'b');
        TemporaryFile.WriteAllBytes(after.ReportPath + ".source-context.json",
            QualifiedSourceContextFixture.Bytes(after.Snapshot, before.Snapshot,
                "registered_g", "absent_parentheses"));
        using var bundle = new PrecomputedLeanReportSource.CapturedBundle(qualifiedReports.Path, after.ReportPath);
        ILeanReportSource source = bundle;
        if (contextFirst) _ = source.LoadSourceContext(after.Snapshot, before.Snapshot);
        var report = source.Load(after.Snapshot);
        TemporaryFile.WriteAllText(after.ReportPath + ".source-context.json", "replaced context");
        TemporaryFile.WriteAllText(after.ReportPath + ".materials.zip", "replaced materials");

        var context = source.LoadSourceContext(after.Snapshot, before.Snapshot);
        Assert.NotEmpty(context.GetFile(after.Snapshot, RepoPathFor("A"), "current").Commands);
        Assert.NotEmpty(context.GetFile(before.Snapshot, RepoPathFor("A"), "protected").Commands);
        Assert.Contains("value=", Assert.Single(report.Files[RepoPathFor("Helper")].Declarations)
            .LoadTypeRepresentation(), StringComparison.Ordinal);
    }
}

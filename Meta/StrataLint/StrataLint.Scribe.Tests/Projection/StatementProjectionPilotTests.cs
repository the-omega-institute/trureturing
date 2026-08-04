using System.Text.Json;
using Xunit;

namespace StrataLint.Scribe.Tests;

public sealed class StatementProjectionPilotTests
{
    [Fact]
    public void DecoderCoversEveryInspectorExpressionConstructor()
    {
        const string encoded = "statement-v1(uparams=[ns(n0,1:u)],type=ee(0,es(l0),ei(ln(7)),ej(ns(n0,1:S),0,ed(el(bd,ef(ns(n0,1:x)),ea(em(ns(n0,1:m)),eb(0)))))))";
        var statement = StatementV1Decoder.Decode(encoded);

        Assert.Single(statement.UniverseParameters);
        Assert.IsType<LeanExpr.Let>(statement.Type);
    }

    [Theory]
    [InlineData("")]
    [InlineData("statement-v2(uparams=[],type=es(l0))")]
    [InlineData("statement-v1(uparams=[],type=unknown())")]
    [InlineData("statement-v1(uparams=[],type=es(l0))junk")]
    public void DecoderFailsClosedOnMalformedOrUnknownInput(string encoded) =>
        Assert.Throws<FormatException>(() => StatementV1Decoder.Decode(encoded));

    [Fact]
    public void ProjectorMapsBindingAndPropositionCore()
    {
        const string encoded = "statement-v1(uparams=[],type=ep(bd,ec(ns(n0,4:Real),[]),ea(ea(ea(ec(ns(n0,2:Eq),[]),ec(ns(n0,4:Real),[])),eb(0)),eb(0))))";
        var result = StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type);

        var formula = Assert.IsType<ProjectionOutcome.Projected>(result).Formula;
        Assert.Equal("\\forall x0 \\in \\mathrm{Real},\\; \\mathit{x0} = \\mathit{x0}", LatexWriter.Write(formula));
    }

    [Fact]
    public void DenoiserStripsOnlyRegisteredElaborationArguments()
    {
        const string encoded = "statement-v1(uparams=[],type=ea(ea(ec(ns(ns(ns(ns(ns(n0,2:D5),2:S3),4:Weil),11:LabeledZeta),12:LedgerLength),[]),es(l0)),ec(ns(n0,9:AddMonoid),[])))";

        var result = StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type);

        var formula = Assert.IsType<ProjectionOutcome.Projected>(result).Formula;
        Assert.Equal("\\mathrm{LedgerLength}", LatexWriter.Write(formula));
    }

    [Fact]
    public void DenoiserFailsClosedForUnknownElaborationShape()
    {
        const string encoded = "statement-v1(uparams=[],type=ea(ea(ec(ns(n0,13:Unknown.noise),[]),ec(ns(n0,4:Real),[])),ei(ln(7))))";

        var result = Assert.IsType<ProjectionOutcome.Unprojectable>(
            StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type));

        Assert.Contains("Unknown.noise", result.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void PilotProjectsTenRealDeclarationsAndPinsTheComparisonReport()
    {
        using var fixture = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");
        var results = ProjectionPilot.Run(ReadFixtureDeclarations(fixture, expansion));

        Assert.Equal(10, results.Cases.Length);
        Assert.Equal(ProjectionPilot.GoldenReport, results.Report);
        Assert.Equal(ProjectionNotation.Entries.Count, results.NotationSize);
        Assert.All(results.Cases.Where(item => item.Unprojectable.IsEmpty),
            item => Assert.IsNotType<Formula.Placeholder>(item.Formula));
        Assert.All(results.Cases.Where(item => !item.Unprojectable.IsEmpty),
            item => Assert.IsType<Formula.Placeholder>(item.Formula));
        Assert.Equal(8, results.Cases.Count(item => item.Unprojectable.IsEmpty));
        Assert.Equal(2, results.Cases.Count(item => !item.Unprojectable.IsEmpty));
    }

    [LiveReportFact]
    public void LiveReportMatchesPinnedFixtureWhenAvailable()
    {
        var reportPath = Path.Combine(FindRepositoryRoot(), ".lake/build/stratalint/raw-lean-report.json");
        using var fixture = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");
        using var report = JsonDocument.Parse(File.ReadAllBytes(reportPath));
        var expected = ReadFixtureDeclarations(fixture, expansion).ToDictionary(
            item => item.Key,
            item => item.Value.GetProperty("type").GetString()!,
            StringComparer.Ordinal);
        var actual = report.RootElement.GetProperty("modules")
            .EnumerateArray().SelectMany(module => module.GetProperty("declarations").EnumerateArray())
            .Where(item => expected.ContainsKey(item.GetProperty("name").GetString()!))
            .GroupBy(item => item.GetProperty("name").GetString()!, StringComparer.Ordinal)
            .ToDictionary(
                group => group.Key,
                group => Assert.Single(group).GetProperty("type").GetString()!,
                StringComparer.Ordinal);

        Assert.Equal(expected, actual);
    }

    private static JsonDocument LoadPinnedFixture(string name) => JsonDocument.Parse(File.ReadAllBytes(Path.Combine(
        AppContext.BaseDirectory, "Projection", "Fixtures", name)));

    private static Dictionary<string, JsonElement> ReadFixtureDeclarations(params JsonDocument[] fixtures)
    {
        Assert.Equal("statement-projection-pilot-fixture-v1", fixtures[0].RootElement.GetProperty("schema").GetString());
        Assert.Equal("statement-projection-expansion-fixture-v1", fixtures[1].RootElement.GetProperty("schema").GetString());
        return fixtures.SelectMany(fixture => fixture.RootElement.GetProperty("declarations").EnumerateArray())
            .ToDictionary(item => item.GetProperty("name").GetString()!, StringComparer.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory); directory is not null; directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml"))) return directory.FullName;
        }

        throw new InvalidOperationException("Repository root was not found.");
    }

    private sealed class LiveReportFactAttribute : FactAttribute
    {
        public LiveReportFactAttribute()
        {
            var directory = new DirectoryInfo(AppContext.BaseDirectory);
            while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "lakefile.toml")))
                directory = directory.Parent;
            if (directory is null || !File.Exists(Path.Combine(
                    directory.FullName, ".lake/build/stratalint/raw-lean-report.json")))
                Skip = "Live raw Lean report is absent; pinned statement-v1 fixture remains the self-contained verifier asset.";
        }
    }
}

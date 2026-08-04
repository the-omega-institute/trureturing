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
    public void PilotProjectsFiveRealDeclarationsAndPinsTheComparisonReport()
    {
        var root = FindRepositoryRoot();
        using var report = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(
            root, ".lake/build/stratalint/raw-lean-report.json")));
        var declarations = report.RootElement.GetProperty("modules")
            .EnumerateArray().SelectMany(module => module.GetProperty("declarations").EnumerateArray())
            .GroupBy(item => item.GetProperty("name").GetString()!, StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.First(), StringComparer.Ordinal);

        var results = ProjectionPilot.Run(declarations);

        Assert.Equal(5, results.Cases.Length);
        Assert.Equal(ProjectionPilot.GoldenReport, results.Report);
        Assert.Equal(ProjectionNotation.Entries.Count, results.NotationSize);
        Assert.All(results.Cases, item => Assert.Equal(item.GoldenLatex, LatexWriter.Write(item.Formula)));
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory); directory is not null; directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml"))) return directory.FullName;
        }

        throw new InvalidOperationException("Repository root was not found.");
    }
}

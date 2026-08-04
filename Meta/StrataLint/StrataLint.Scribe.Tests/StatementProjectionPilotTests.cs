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
    public void PilotProjectsFiveRealDeclarationsAndPinsTheComparisonReport()
    {
        var root = FindRepositoryRoot();
        using var report = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(
            root, ".lake/build/stratalint/raw-lean-report.json")));
        var declarations = report.RootElement.GetProperty("modules")
            .EnumerateArray().SelectMany(module => module.GetProperty("declarations").EnumerateArray())
            .ToDictionary(item => item.GetProperty("name").GetString()!, StringComparer.Ordinal);

        var results = ProjectionPilot.Run(declarations);

        Assert.Equal(5, results.Cases.Count);
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

using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Engine.Tests;

public sealed class CoverageWriterTests
{
    [Fact]
    public void TextAndJsonAreCanonicalAcrossTwoIndependentWrites()
    {
        var report = Report();
        var tower = Tower();

        var text1 = CoverageCanonicalWriter.WriteText(report, tower);
        var text2 = CoverageCanonicalWriter.WriteText(report, tower);
        var json1 = CoverageCanonicalWriter.WriteJson(report, tower);
        var json2 = CoverageCanonicalWriter.WriteJson(report, tower);

        Assert.True(text1.AsSpan().SequenceEqual(text2.AsSpan()));
        Assert.True(json1.AsSpan().SequenceEqual(json2.AsSpan()));
        Assert.Equal((byte)'\n', text1[^1]);
        Assert.Equal((byte)'\n', json1[^1]);
        Assert.DoesNotContain((byte)'\r', text1);
        Assert.DoesNotContain((byte)'\r', json1);
    }

    [Fact]
    public void CanonicalOutputsExposeMatrixAndUngovernedAsSeparateMachineFacts()
    {
        var report = Report();
        var tower = Tower();

        var text = Encoding.UTF8.GetString(CoverageCanonicalWriter.WriteText(report, tower).AsSpan());
        using var json = JsonDocument.Parse(CoverageCanonicalWriter.WriteJson(report, tower).ToArray());

        Assert.Contains("MATRIX class=F artifacts=0", text, StringComparison.Ordinal);
        Assert.Contains("UNGOVERNED count=1", text, StringComparison.Ordinal);
        Assert.Contains("UNGOVERNED path=\"scratch/note.txt\"", text, StringComparison.Ordinal);
        Assert.Equal(1, json.RootElement.GetProperty("ungoverned").GetProperty("count").GetInt32());
        Assert.Equal(
            "scratch/note.txt",
            json.RootElement.GetProperty("ungoverned").GetProperty("artifacts")[0].GetString());
        Assert.Equal(12, json.RootElement.GetProperty("matrix").GetArrayLength());
    }

    private static CoverageReport Report()
    {
        Assert.True(RepoPath.TryCreate("scratch/note.txt", out var path));
        var mechanisms = new CoverageMechanisms(
            ImmutableArray<RuleId>.Empty,
            ImmutableArray<RuleId>.Empty,
            null,
            false,
            null,
            ImmutableArray<string>.Empty);
        var artifact = new ArtifactCoverage(path, ArtifactClass.Other, mechanisms);
        var matrix = Enum.GetValues<ArtifactClass>()
            .Select(@class => new CoverageMatrixRow(
                @class,
                @class == ArtifactClass.Other ? 1 : 0,
                0,
                0,
                0,
                0,
                0,
                @class == ArtifactClass.Other ? 1 : 0))
            .ToImmutableArray();
        return new CoverageReport([artifact], matrix);
    }

    private static ValidatedTowerManifest Tower()
    {
        var syntax = new TowerManifestSyntax(
            1,
            [new TowerComponentSyntax(
                "leaf",
                "repository-files",
                ["scratch/note.txt"],
                ["bootstrap-pr-1"],
                "verified")],
            new TowerBootstrapSyntax(
                "bootstrap-pr-1",
                "open",
                "Godel boundary: the trust root cannot prove its own consistency.",
                "sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262",
                "f3f471846dd81cfcc39ecaa386966fcf0b058464",
                1,
                "ASSUMED-UNVERIFIED"));
        return Assert.IsType<TowerValidationOutcome.Accepted>(
            TowerManifestValidator.ValidateStructure(syntax)).Manifest;
    }
}

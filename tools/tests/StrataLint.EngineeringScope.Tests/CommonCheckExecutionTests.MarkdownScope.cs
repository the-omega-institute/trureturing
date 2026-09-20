using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CommonCheckExecutionTests
{
    [Fact]
    public void MarkdownDeltaWithoutRegistrationCannotUseWholeTreeEvidence()
    {
        using var fixture = new Fixture();
        var error = Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.CheckInputFingerprints(
            fixture.Tree.Root, selectedIds: ["scribe-markdown"], changedPaths: ["Blueprint/D5/Changed.md"]));
        Assert.Equal("missing scribe-markdown path scope registration", error.Message);
    }

    [Fact]
    public void MarkdownEvidenceBindsTheSelectedScopeAndWholeTreeDiagnostics()
    {
        using var fixture = new Fixture();
        RegisterMarkdownScope(fixture);
        string Fingerprint(string[]? paths) => CommonExecutionEvidence.CheckInputFingerprints(fixture.Tree.Root,
            selectedIds: ["scribe-markdown"], changedPaths: paths)["scribe-markdown"];

        Assert.NotEqual(Fingerprint(["Blueprint/D5/First.md"]), Fingerprint(["Blueprint/D5/Second.md"]));
        Assert.NotEqual(Fingerprint(["Blueprint/D5/First.md"]), Fingerprint(null));
        Assert.Equal(Fingerprint(["Blueprint/D5/First.md", "Blueprint/D5/Second.md"]),
            Fingerprint(["Blueprint/D5/Second.md", "Blueprint/D5/First.md", "Blueprint/D5/First.md"]));
    }

    [Fact]
    public void MarkdownScopeRegistrationCannotBeMutatedAcrossValidationReaders()
    {
        using var fixture = new Fixture();
        RegisterMarkdownScope(fixture);
        var validation = CommonExecutionEvidence.ValidationScope.Create(fixture.Tree.Root);
        var scope = validation.CheckManifest().Single(check => check.Id == "scribe-markdown").MarkdownScope!;
        scope.ChangedInputs[0] = "docs/**";
        scope.WholeTreeInputs[0] = "**";

        var reread = validation.Fresh().CheckManifest().Single(check => check.Id == "scribe-markdown").MarkdownScope!;
        Assert.Equal(new[] { "Blueprint/**/*.md", "Blueprint/**/*.scribe.cs" }, reread.ChangedInputs);
        Assert.Equal(new[] { "tools/Renderer/**" }, reread.WholeTreeInputs);
    }

    [Fact]
    public void WholeCurrentExecutionExposesItsDeclaredMarkdownInventory()
    {
        using var fixture = new Fixture();
        RegisterMarkdownScope(fixture);
        fixture.Tree.Write("Blueprint/D5/First.md", "first");
        fixture.Tree.Write("Blueprint/D5/Second.md", "second");
        fixture.Tree.Write("docs/theory/Other.md", "other");
        fixture.Tree.Track();
        var checks = CommonExecutionEvidence.BeginChecks(fixture.Tree.Root, "current", fixture.Tree.Build(),
            TextWriter.Null, ["scribe-markdown"]);

        Assert.True(checks.MarkdownScope!.WholeTree);
        Assert.Equal(new[] { "Blueprint/D5/First.md", "Blueprint/D5/Second.md" }, checks.MarkdownScope.Paths);
    }

    private static void RegisterMarkdownScope(Fixture fixture)
    {
        var manifest = CommonExecutionEvidence.Read<CommonCheckManifest>(fixture.Tree.Root, CommonExecutionEvidence.CheckManifestPath);
        CommonExecutionEvidence.Write(fixture.Tree.Root, CommonExecutionEvidence.CheckManifestPath,
            manifest with { Checks = manifest.Checks.Select(check => check.Id != "scribe-markdown" ? check : check with
            {
                PathInventory = ["Blueprint/**/*.md"],
                MarkdownScope = new(["tools/Renderer/**"], ["Blueprint/**/*.md", "Blueprint/**/*.scribe.cs"]),
            }).ToArray() });
    }
}

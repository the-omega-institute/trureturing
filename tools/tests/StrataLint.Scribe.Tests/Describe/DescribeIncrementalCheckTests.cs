using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeIncrementalCheckTests
{
    private const string TargetGid = "D5/S0/Test/Target";
    private const string SourceGid = "D5/S0/Test/Source";
    private const string ChangedTargetPath = "Blueprint/D5/S0/Test/Target.scribe.cs";

    [Fact]
    public void IncrementalCheckFindingsEqualFullCheckForAffectedDefects()
    {
        using var root = new TemporaryRoot();
        WriteLeanSources(root);
        var target = Document(TargetGid, "replacement");
        var source = ReferencingDocument("target");
        var documents = new[] { target, source };

        var full = DescribeReport.Build(root.Path, documents);
        var incremental = DescribeReport.BuildIncremental(
            root.Path,
            documents,
            [ChangedTargetPath]);

        Assert.NotEmpty(full.RedFindings);
        Assert.Equal(full.RedFindings.ToArray(), incremental.RedFindings.ToArray());
    }

    [Fact]
    public void IncrementalCheckAcceptsValidAffectedClosure()
    {
        using var root = new TemporaryRoot();
        WriteLeanSources(root);
        var documents = new[] { Document(TargetGid, "target"), ReferencingDocument("target") };

        var incremental = DescribeReport.BuildIncremental(
            root.Path,
            documents,
            [ChangedTargetPath]);

        Assert.Empty(incremental.RedFindings);
        Assert.Equal("classified", incremental.Status);
    }

    [Fact]
    public void IncrementalCheckRevalidatesDocumentThatReferencesChangedTarget()
    {
        using var root = new TemporaryRoot();
        WriteLeanSources(root);
        var target = Document(TargetGid, "replacement");
        var source = ReferencingDocument("target");

        var incremental = DescribeReport.BuildIncremental(
            root.Path,
            [target, source],
            [ChangedTargetPath]);

        var finding = Assert.Single(incremental.RedFindings);
        Assert.Equal("dangling-describe-edge", finding.Code);
        Assert.Equal(SourceGid, finding.Path);
    }

    private static void WriteLeanSources(TemporaryRoot root)
    {
        File.WriteAllText(root.Resolve("D5/S0/Test/Target.lean"), "namespace D5.S0.Test.Target\n");
        File.WriteAllText(root.Resolve("D5/S0/Test/Source.lean"), "namespace D5.S0.Test.Source\n");
    }

    private static ScribeDocument ReferencingDocument(string describeId) =>
        Document(
            SourceGid,
            "source",
            [DocumentEdge.NarrativeReference.ToDescribe(
                GidRef.Create(TargetGid),
                DescribeId.Create(describeId))]);

    private static ScribeDocument Document(
        string gid,
        string describeId,
        IEnumerable<DocumentEdge>? edges = null) =>
        ScribeDocument.Create(
            DocumentHeader.Create(
                GidRef.Create(gid),
                Generality.Instance,
                GidRef.Create("D5/B/" + gid["D5/".Length..]),
                new EvidenceMirror.Waiver(WaiverReason.Create("test-only")),
                [],
                Digest.Create("Incremental Describe fixture.")),
            Heading.Create(gid),
            BlockSequence.Create(
            [
                Describe.Remark(
                    DescribeId.Create(describeId),
                    Heading.Create(describeId),
                    new Formula.Number(1),
                    AssessedProvenance.FromRepo(),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Fixture body.")),
                    ])),
            ]),
            edges ?? []);
}

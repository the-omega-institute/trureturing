using System.Collections.Immutable;

namespace StrataLint.Scribe.Tests;

public sealed class RelationLiteratureTests
{
    private const string AnchorTarget = "lit/sample2000anchor";
    private const string LiteratureTarget = "D5/L/sample2000source";
    private const string CreditTarget = "D5/L/sample2000credit";
    private const string EvidenceTarget = "D5/E/S0/Test/Relations.result--json";
    private const string HeaderAllowlist = """
        F:StrataLint.Engine.Generality.Instance
        P:StrataLint.Scribe.LibraryNoteRef.Anchor
        M:StrataLint.Scribe.DocumentHeader.Create(StrataLint.Scribe.GidRef,StrataLint.Engine.Generality,StrataLint.Scribe.GidRef,StrataLint.Scribe.EvidenceMirror,System.Collections.Generic.IEnumerable{StrataLint.Engine.Anchor},StrataLint.Scribe.Digest)
        M:StrataLint.Scribe.EvidenceMirror.Artifact.#ctor(StrataLint.Scribe.GidRef)
        M:StrataLint.Scribe.EvidenceMirror.Waiver.#ctor(StrataLint.Scribe.WaiverReason)
        M:StrataLint.Scribe.WaiverReason.Create(System.String)
        M:StrataLint.Scribe.Digest.Create(System.String)
        """;
    private const string Blocks = """
        new DocumentBlock.Section(H("section"), Blocks(
            Describe.Remark(DescribeId.Create("literature"), H("literature"), Num(1),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/sample2000source")),
                Blocks(Describe.Example(DescribeId.Create("credit"), H("credit"), Num(2),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/sample2000credit")),
                    Blocks(Paragraph(Text("content"))))))))
        """;
    private const string Anchors = """
        [Anchor.ParseCanonical("lit/sample2000anchor"),
         LibraryNoteRef.Create("D5/L/sample2000anchor").Anchor,
         Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Basic")]
        """;

    [Fact]
    public void MalformedLiteratureAnchorIsNamedUnreadable()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(\"content\"))",
            anchors: "[Anchor.ParseCanonical(\"lit/\")]");
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("InvalidAnchor", read.Failure?.Shape);
    }

    [Theory]
    [InlineData("node")]
    [InlineData("dsl")]
    [InlineData("typed")]
    public void TypedHeaderAndLiteratureRelationsMatchExecution(string factory)
    {
        using var root = Fixture(factory);
        RelationContractTests.EqualExecution(root, HeaderAllowlist);
        var projection = Read(root);
        Assert.Equal(new[] { AnchorTarget, AnchorTarget }, projection.LiteratureAnchors);
        Assert.Equal(factory == "typed" ? EvidenceTarget : null, projection.EvidenceReference);
        Assert.Equal(LiteratureTarget, projection.Describes.Single(item => item.Id == "literature").LiteratureReference);
        Assert.Equal(new[] { CreditTarget }, projection.Describes.Single(item => item.Id == "credit").AcknowledgementReferences);
    }

    [Fact]
    public void NovelProvenanceAcknowledgementsMatchExecution()
    {
        using var root = RelationContractTests.Fixture(Blocks.Replace(
            "AssessedProvenance.FromRepo(",
            "AssessedProvenance.NovelAfterSearch(GidRef.Create(\"D5/S0/Test/Search\"), ", StringComparison.Ordinal));
        RelationContractTests.EqualExecution(root,
            "M:StrataLint.Scribe.AssessedProvenance.NovelAfterSearch(StrataLint.Scribe.GidRef,StrataLint.Scribe.LibraryNoteRef[])\n");
        Assert.Equal(new[] { CreditTarget }, Read(root).Describes.Single(item => item.Id == "credit").AcknowledgementReferences);
    }

    [Theory]
    [InlineData("anchor")]
    [InlineData("literature")]
    [InlineData("acknowledgement")]
    [InlineData("evidence")]
    public void TargetReplacementChangesProjectionAndComparison(string relation)
    {
        using var root = Fixture("typed");
        var original = Read(root);
        var target = Target(relation);
        var source = File.ReadAllText(root.Resolve(RelationContractTests.Entry));
        File.WriteAllText(root.Resolve(RelationContractTests.Entry), source.Replace(
            target, target.Replace("sample2000", "sample2001", StringComparison.Ordinal)
                .Replace(".result--json", ".other--json", StringComparison.Ordinal), StringComparison.Ordinal));
        RelationContractTests.EqualExecution(root, HeaderAllowlist);
        Assert.NotEqual(original.Encode(), Read(root).Encode());
        AssertMismatch(root, original);
    }

    [Theory]
    [InlineData("anchor")]
    [InlineData("literature")]
    [InlineData("acknowledgement")]
    [InlineData("evidence")]
    public void TargetDeletionChangesProjectionAndComparison(string relation)
    {
        using var root = Fixture("typed");
        var original = Read(root);
        var source = File.ReadAllText(root.Resolve(RelationContractTests.Entry));
        var changed = relation switch
        {
            "anchor" => source.Replace(Anchors, "[]", StringComparison.Ordinal),
            "literature" => source.Replace(
                "AssessedProvenance.FromLiterature(LibraryNoteRef.Create(\"" + LiteratureTarget + "\"))",
                "AssessedProvenance.FromRepo()", StringComparison.Ordinal),
            "acknowledgement" => source.Replace(
                "AssessedProvenance.FromRepo(LibraryNoteRef.Create(\"" + CreditTarget + "\"))",
                "AssessedProvenance.FromRepo()", StringComparison.Ordinal),
            "evidence" => source.Replace(
                "new EvidenceMirror.Artifact(GidRef.Create(\"" + EvidenceTarget + "\"))",
                "new EvidenceMirror.Waiver(WaiverReason.Create(\"algebraically-proved\"))", StringComparison.Ordinal),
            _ => throw new ArgumentOutOfRangeException(nameof(relation)),
        };
        Assert.NotEqual(source, changed);
        File.WriteAllText(root.Resolve(RelationContractTests.Entry), changed);
        RelationContractTests.EqualExecution(root, HeaderAllowlist);
        Assert.NotEqual(original.Encode(), Read(root).Encode());
        AssertMismatch(root, original);
    }

    [Fact]
    public void RepeatedAcknowledgementsRetainTwoOccurrences()
    {
        using var root = Fixture("node");
        var original = Read(root);
        var source = File.ReadAllText(root.Resolve(RelationContractTests.Entry));
        File.WriteAllText(root.Resolve(RelationContractTests.Entry), source.Replace(
            "AssessedProvenance.FromRepo(LibraryNoteRef.Create(\"" + CreditTarget + "\"))",
            "AssessedProvenance.FromRepo(LibraryNoteRef.Create(\"" + CreditTarget + "\"), LibraryNoteRef.Create(\"" + CreditTarget + "\"))",
            StringComparison.Ordinal));
        RelationContractTests.EqualExecution(root, HeaderAllowlist);
        Assert.Equal(new[] { CreditTarget, CreditTarget }, Read(root).Describes.Single(item => item.Id == "credit").AcknowledgementReferences);
        AssertMismatch(root, original);
    }

    [Theory]
    [InlineData("anchor")]
    [InlineData("literature")]
    [InlineData("acknowledgement")]
    [InlineData("evidence")]
    public void EachRelationFieldParticipatesInCanonicalEncoding(string relation)
    {
        using var root = Fixture("typed");
        RelationContractTests.EqualExecution(root, HeaderAllowlist);
        var original = Read(root);
        var changed = relation switch
        {
            "anchor" => original with { LiteratureAnchors = [] },
            "evidence" => original with { EvidenceReference = null },
            "literature" => original with { Describes = original.Describes.Select(item => item with { LiteratureReference = null }).ToImmutableArray() },
            "acknowledgement" => original with { Describes = original.Describes.Select(item => item with { AcknowledgementReferences = [] }).ToImmutableArray() },
            _ => throw new ArgumentOutOfRangeException(nameof(relation)),
        };
        Assert.NotEqual(original.Encode(), changed.Encode());
        Assert.NotNull(original.FirstDifference(changed));
        AssertMismatch(root, changed);
    }

    [Fact]
    public void LiteratureMultisetsIgnoreOrderAndRetainMultiplicity()
    {
        using var root = Fixture("node");
        var original = Read(root);
        var credits = original.Describes.Select(item => item with
        {
            AcknowledgementReferences = [CreditTarget, LiteratureTarget],
        }).ToImmutableArray();
        var first = original with { Describes = credits, LiteratureAnchors = [AnchorTarget, "lit/sample2001anchor"] };
        var reordered = first with
        {
            LiteratureAnchors = first.LiteratureAnchors.Reverse().ToImmutableArray(),
            Describes = credits.Reverse().Select(item => item with
            {
                AcknowledgementReferences = item.AcknowledgementReferences.Reverse().ToImmutableArray(),
            }).ToImmutableArray(),
        };
        Assert.Equal(first.Encode(), reordered.Encode());
        Assert.NotEqual(first.Encode(), (first with { LiteratureAnchors = [AnchorTarget] }).Encode());
    }

    private static TemporaryRoot Fixture(string factory) => RelationContractTests.Fixture(Blocks, anchors: Anchors,
        header: factory switch
        {
            "node" => null,
            "dsl" => "Header(\"D5/S0/Test/Relations\", \"digest\", " + Anchors + ")",
            "typed" => "DocumentHeader.Create(GidRef.Create(\"D5/S0/Test/Relations\"), Generality.Instance, "
                + "GidRef.Create(\"D5/B/S0/Test/Relations\"), new EvidenceMirror.Artifact(GidRef.Create(\"" + EvidenceTarget + "\")), "
                + Anchors + ", Digest.Create(\"digest\"))",
            _ => throw new ArgumentOutOfRangeException(nameof(factory)),
        });

    private static string Target(string relation) => relation switch
    {
        "anchor" => "sample2000anchor",
        "literature" => LiteratureTarget,
        "acknowledgement" => CreditTarget,
        "evidence" => EvidenceTarget,
        _ => throw new ArgumentOutOfRangeException(nameof(relation)),
    };

    private static RelationProjection Read(TemporaryRoot root)
    {
        var result = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(result.Failure);
        return Assert.IsType<RelationProjection>(result.Projection);
    }

    private static void AssertMismatch(TemporaryRoot root, RelationProjection projection)
    {
        var host = ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, RelationContractTests.Entry, root.Resolve("allowlist.txt"));
        Assert.True(host.IsSuccess, host.Failure?.ToString());
        var result = RelationVerifier.Compare([new(RelationContractTests.Entry, projection, null)], [host], TimeSpan.Zero);
        Assert.Equal(1, result.Mismatches);
        Assert.Equal(1, result.Write(new StringWriter(), new StringWriter()));
    }
}

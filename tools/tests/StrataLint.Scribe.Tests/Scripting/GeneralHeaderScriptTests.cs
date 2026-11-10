using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class GeneralHeaderScriptTests
{
    private const string Gid = "D5/S3/Geometry/FiniteCriticalCellSphere";
    private const string Entry = "Blueprint/" + Gid + ".scribe.cs";
    private const string DigestText = "general-header-sdk-digest";
    private const string Waiver = "finite-critical-cell-sphere";
    private const string Member = "M:StrataLint.Scribe.DefinitionDsl.GeneralHeader(System.String,System.String,System.String,StrataLint.Engine.Anchor[])";
    private const string FirstAnchor = "mathlib/module/Mathlib.Topology.CompactOpen";
    private const string SecondAnchor = "mathlib/module/Mathlib.Topology.Piecewise";

    [Fact]
    public void AdmittedGeneralHeaderPreservesMetadataThroughResourceRoundTrip()
    {
        using var root = new TemporaryRoot();
        Write(root, $"GeneralHeader(\"{Gid}\", \"{DigestText}\", \"{Waiver}\", "
            + $"Anchor.ParseCanonical(\"{FirstAnchor}\"), Anchor.ParseCanonical(\"{SecondAnchor}\"))");

        var result = ScribeScriptHost.Execute(root.Path, Entry);

        AssertRoundTrip(result, Generality.General, Waiver, [FirstAnchor, SecondAnchor]);
    }

    [Theory]
    [InlineData("\"not-a-gid\", \"digest\", \"reason\"")]
    [InlineData("\"D5/B/S3/Geometry/FiniteCriticalCellSphere\", \"digest\", \"reason\"")]
    [InlineData("\"D5/S3/Geometry/FiniteCriticalCellSphere\", \"two\\nlines\", \"reason\"")]
    [InlineData("\"D5/S3/Geometry/FiniteCriticalCellSphere\", \"digest\", \"Not_Canonical\"")]
    [InlineData("null!, \"digest\", \"reason\"")]
    [InlineData("\"D5/S3/Geometry/FiniteCriticalCellSphere\", null!, \"reason\"")]
    [InlineData("\"D5/S3/Geometry/FiniteCriticalCellSphere\", \"digest\", null!")]
    [InlineData("\"D5/S3/Geometry/FiniteCriticalCellSphere\", \"digest\", \"reason\", (Anchor[])null!")]
    [InlineData("\"D5/S3/Geometry/FiniteCriticalCellSphere\", \"digest\", \"reason\", new Anchor[] { null! }")]
    public void InvalidHeadersAreAdmittedButFailDuringCreate(string arguments)
    {
        using var root = new TemporaryRoot();
        Write(root, $"GeneralHeader({arguments})");

        var result = ScribeScriptHost.Execute(root.Path, Entry);

        Assert.False(result.IsSuccess);
        Assert.Null(result.Definition);
        Assert.Equal(ScribeScriptFailureCode.CreateFailed, result.Failure?.Code);
        Assert.Equal(Entry, result.Failure!.RelativePath);
        Assert.NotEmpty(result.Failure.Message);
    }

    [Theory]
    [InlineData(null)]
    [InlineData("")]
    [InlineData(" ")]
    [InlineData(" leading")]
    [InlineData("trailing ")]
    [InlineData("two\nlines")]
    [InlineData("two\rlines")]
    public void DigestValidationIsNotNormalizedOrBypassed(string? digest)
    {
        Assert.Throws<ArgumentException>(() => DefinitionDsl.GeneralHeader(Gid, digest!, Waiver));
    }

    [Theory]
    [InlineData(null)]
    [InlineData("")]
    [InlineData(" ")]
    [InlineData("Noncanonical")]
    [InlineData("under_score")]
    [InlineData(" leading")]
    [InlineData("trailing ")]
    public void WaiverValidationIsNotNormalizedOrBypassed(string? waiver)
    {
        Assert.Throws<ArgumentException>(() => DefinitionDsl.GeneralHeader(Gid, DigestText, waiver!));
    }

    [Fact]
    public void AnchorNullChecksAreForwardedToDocumentHeader()
    {
        Assert.Throws<ArgumentNullException>(() => DefinitionDsl.GeneralHeader(Gid, DigestText, Waiver, (Anchor[])null!));
        Assert.Throws<ArgumentException>(() => DefinitionDsl.GeneralHeader(Gid, DigestText, Waiver, new Anchor[] { null! }));
    }

    [Fact]
    public void RevokingOnlyGeneralHeaderRejectsItAndKeepsLegacyHeaderDefaults()
    {
        using var root = new TemporaryRoot();
        Write(root, $"GeneralHeader(\"{Gid}\", \"{DigestText}\", \"{Waiver}\")");
        AssertRoundTrip(ScribeScriptHost.Execute(root.Path, Entry), Generality.General, Waiver, []);
        var original = Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt");
        var lines = File.ReadAllLines(original);
        Assert.Single(lines, line => line == Member);
        var revoked = root.Resolve("Scripting/WithoutGeneralHeader.txt");
        TemporaryFileSystem.File.WriteAllText(revoked, string.Join("\n", lines.Where(line => line != Member)));

        var rejected = ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, revoked);

        AssertRejected(rejected, Member);
        Write(root, $"Header(\"{Gid}\", \"{DigestText}\")");
        var legacy = ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, revoked);
        AssertRoundTrip(legacy, Generality.Instance, "algebraically-proved", []);
    }

    [Theory]
    [InlineData("Generality.General", "F:StrataLint.Engine.Generality.General")]
    [InlineData("WaiverReason.Create(\"reason\")", "M:StrataLint.Scribe.WaiverReason.Create(System.String)")]
    [InlineData("Digest.Create(\"digest\")", "M:StrataLint.Scribe.Digest.Create(System.String)")]
    [InlineData("new EvidenceMirror.Waiver(null!)", "M:StrataLint.Scribe.EvidenceMirror.Waiver.#ctor(StrataLint.Scribe.WaiverReason)")]
    [InlineData("new EvidenceMirror.Artifact(null!)", "M:StrataLint.Scribe.EvidenceMirror.Artifact.#ctor(StrataLint.Scribe.GidRef)")]
    [InlineData("DocumentHeader.Create(null!, default, null!, null!, Array.Empty<Anchor>(), null!)",
        "M:StrataLint.Scribe.DocumentHeader.Create(StrataLint.Scribe.GidRef,StrataLint.Engine.Generality,StrataLint.Scribe.GidRef,StrataLint.Scribe.EvidenceMirror,System.Collections.Generic.IEnumerable{StrataLint.Engine.Anchor},StrataLint.Scribe.Digest)")]
    public void RawHeaderCapabilitiesRemainDisallowed(string expression, string id)
    {
        using var root = new TemporaryRoot();
        Write(root, $"GeneralHeader(\"{Gid}\", \"{DigestText}\", \"{Waiver}\")", $"_ = {expression};");

        AssertRejected(ScribeScriptHost.Execute(root.Path, Entry), id);
    }

    private static void AssertRoundTrip(ScribeScriptResult result, Generality generality, string waiver, string[] anchors)
    {
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        var definition = result.Definition!;
        Assert.Equal(Entry, definition.SourcePath);
        AssertHeader(definition.Document.Header, generality, waiver, anchors);
        var bytes = ScribeResourceCodec.Encode(definition);

        var decoded = ScribeResourceCodec.Decode(bytes, expectedGid: Gid, expectedSourcePath: Entry);

        Assert.Equal(Entry, decoded.SourcePath);
        AssertHeader(decoded.Document.Header, generality, waiver, anchors);
        Assert.Equal(bytes, ScribeResourceCodec.Encode(decoded));
    }

    private static void AssertHeader(DocumentHeader header, Generality generality, string waiver, string[] anchors)
    {
        Assert.Equal(Gid, header.Gid.Value);
        Assert.Equal("D5/B/S3/Geometry/FiniteCriticalCellSphere", header.MirrorBlueprint.Value);
        Assert.Equal(generality, header.Generality);
        Assert.Equal(waiver, Assert.IsType<EvidenceMirror.Waiver>(header.MirrorEvidence).Reason.Value);
        Assert.Equal(DigestText, header.Digest.Value);
        Assert.Equal(anchors, header.Anchors.Select(anchor => anchor.CanonicalString));
    }

    private static void AssertRejected(ScribeScriptResult result, string id)
    {
        Assert.False(result.IsSuccess);
        Assert.Null(result.Definition);
        Assert.Equal(ScribeScriptFailureCode.DisallowedSymbol, result.Failure?.Code);
        Assert.Equal(Entry, result.Failure!.RelativePath);
        Assert.Contains(id, result.Failure.Message, StringComparison.Ordinal);
        Assert.Contains(Entry + ":", result.Failure.Message, StringComparison.Ordinal);
    }

    private static void Write(TemporaryRoot root, string header, string statements = "") =>
        TemporaryFileSystem.File.WriteAllText(root.Resolve(Entry), $$"""
            using StrataLint.Engine;
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create()
                {
                    {{statements}}
                    return DocumentDefinition.Create(ScribeDocument.Create(
                        {{header}}, H("General header"), Blocks(Paragraph(Text("content")))));
                }
            }
            """);
}

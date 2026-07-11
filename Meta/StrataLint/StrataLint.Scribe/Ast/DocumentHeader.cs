using System.Collections.Immutable;
using System.Text.RegularExpressions;
using Dunet;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record AnchorRef
{
    private static readonly Regex Pattern = new(
        "^[A-Za-z0-9][A-Za-z0-9._-]*$",
        RegexOptions.CultureInvariant);

    private AnchorRef(string value) => Value = value;

    public string Value { get; }

    public static AnchorRef Create(string value) =>
        value is not null && Pattern.IsMatch(value)
            ? new AnchorRef(value)
            : throw new ArgumentException("Anchor is not canonical.", nameof(value));

    public override string ToString() => Value;
}

public sealed record WaiverReason
{
    private static readonly Regex Pattern = new(
        "^[a-z][a-z0-9-]*$",
        RegexOptions.CultureInvariant);

    private WaiverReason(string value) => Value = value;

    public string Value { get; }

    public static WaiverReason Create(string value) =>
        value is not null && Pattern.IsMatch(value)
            ? new WaiverReason(value)
            : throw new ArgumentException("Waiver reason is not canonical.", nameof(value));

    public override string ToString() => Value;
}

public sealed record Digest
{
    private Digest(string value) => Value = value;

    public string Value { get; }

    public static Digest Create(string value) =>
        !string.IsNullOrWhiteSpace(value)
        && string.Equals(value, value.Trim(), StringComparison.Ordinal)
        && value.IndexOfAny(['\r', '\n']) < 0
            ? new Digest(value)
            : throw new ArgumentException("Digest must be one non-empty canonical line.", nameof(value));

    public override string ToString() => Value;
}

[Union(EnableImplicitConversions = false)]
public partial record EvidenceMirror
{
    public partial record Artifact(GidRef Reference);

    public partial record Waiver(WaiverReason Reason);
}

public sealed class DocumentHeader
{
    private DocumentHeader(
        GidRef gid,
        Generality generality,
        GidRef mirrorBlueprint,
        EvidenceMirror mirrorEvidence,
        ImmutableArray<AnchorRef> anchors,
        Digest digest)
    {
        Gid = gid;
        Generality = generality;
        MirrorBlueprint = mirrorBlueprint;
        MirrorEvidence = mirrorEvidence;
        Anchors = anchors;
        Digest = digest;
    }

    public GidRef Gid { get; }

    public Generality Generality { get; }

    public GidRef MirrorBlueprint { get; }

    public EvidenceMirror MirrorEvidence { get; }

    public ImmutableArray<AnchorRef> Anchors { get; }

    public Digest Digest { get; }

    public static DocumentHeader Create(
        GidRef gid,
        Generality generality,
        GidRef mirrorBlueprint,
        EvidenceMirror mirrorEvidence,
        IEnumerable<AnchorRef> anchors,
        Digest digest)
    {
        ArgumentNullException.ThrowIfNull(gid);
        ArgumentNullException.ThrowIfNull(mirrorBlueprint);
        ArgumentNullException.ThrowIfNull(mirrorEvidence);
        ArgumentNullException.ThrowIfNull(anchors);
        ArgumentNullException.ThrowIfNull(digest);

        if (!gid.IsFormalModule)
        {
            throw new ArgumentException("Document GID must identify a formal module.", nameof(gid));
        }

        var expectedMirror = "D5/B/" + gid.Value["D5/".Length..];
        if (!mirrorBlueprint.IsBlueprint
            || !string.Equals(mirrorBlueprint.Value, expectedMirror, StringComparison.Ordinal))
        {
            throw new ArgumentException(
                "Blueprint mirror must be the document GID in the B plane.",
                nameof(mirrorBlueprint));
        }

        if (mirrorEvidence is EvidenceMirror.Artifact artifact && !artifact.Reference.IsEvidence)
        {
            throw new ArgumentException(
                "Evidence mirror must identify an E-plane artifact.",
                nameof(mirrorEvidence));
        }

        var anchorArray = anchors.ToImmutableArray();
        if (anchorArray.Any(static anchor => anchor is null))
        {
            throw new ArgumentException("Anchors cannot contain null.", nameof(anchors));
        }

        return new DocumentHeader(
            gid,
            generality,
            mirrorBlueprint,
            mirrorEvidence,
            anchorArray,
            digest);
    }
}

using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal sealed record DigestionFingerprints(string RawSha256, string NormalizedSha256);

internal sealed record DigestionContext(int Level, string Text);

internal sealed record DigestionAtom(
    int StartByte,
    int EndByte,
    ImmutableArray<byte> RawBytes,
    DigestionFingerprints Fingerprints,
    ImmutableArray<DigestionContext> Context,
    DigestionAtomStatusMarker StatusMarker)
{
    internal DigestionAtom(
        int startByte,
        int endByte,
        ImmutableArray<byte> rawBytes,
        DigestionFingerprints fingerprints,
        ImmutableArray<DigestionContext> context)
        : this(startByte, endByte, rawBytes, fingerprints, context, DigestionAtomStatusMarker.Absent)
    {
    }

    internal static DigestionAtom FromFrozenCas(ImmutableArray<byte> rawBytes) =>
        new(
            0,
            rawBytes.Length,
            rawBytes,
            DigestionFingerprint.Compute(rawBytes.AsSpan()),
            [],
            DigestionAtomStatusMarker.Parse(rawBytes.AsSpan()));

    internal static DigestionAtom FromFrozenCas(
        ImmutableArray<byte> rawBytes,
        DigestionFingerprints fingerprints) =>
        new(
            0,
            rawBytes.Length,
            rawBytes,
            fingerprints,
            [],
            DigestionAtomStatusMarker.Absent);
}

internal sealed record DigestionSlice(bool IsClaim, ImmutableArray<byte> RawBytes);

internal sealed record DigestionClausePlan
{
    internal DigestionAtom Parent { get; }
    internal ImmutableArray<DigestionSegment> Segments { get; }
    internal ImmutableArray<DigestionAtom> Children { get; }
    internal bool IsExplicit { get; init; }

    internal DigestionClausePlan(DigestionAtom parent, ImmutableArray<DigestionAtom> children)
        : this(parent, children.Select(static child => new DigestionSegment(DigestionSegmentKind.Claim, child)).ToImmutableArray()) { }

    internal DigestionClausePlan(DigestionAtom parent, ImmutableArray<DigestionSegment> segments)
    {
        Parent = parent;
        Segments = segments;
        Children = segments.Where(static segment => segment.Kind == DigestionSegmentKind.Claim)
            .Select(static segment => segment.Atom).ToImmutableArray();
    }
}

internal enum GenreRegistryCheckKind
{
    Collected,
    NoRegistry,
}

internal static class GenreRegistryCheckNames
{
    internal static string Render(GenreRegistryCheckKind kind) => kind switch
    {
        GenreRegistryCheckKind.Collected => "collected",
        GenreRegistryCheckKind.NoRegistry => "no-registry",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };
}

/// <summary>
/// An empty collected set and an absent registry both contain no tokens, but only the former
/// proves the dialect was checked. Keeping the states distinct prevents omission from becoming
/// a false clean report.
/// </summary>
internal sealed record GenreRegistryCheck
{
    private GenreRegistryCheck(
        GenreRegistryCheckKind kind,
        ImmutableArray<string> unregisteredGenres)
    {
        Kind = kind;
        UnregisteredGenres = unregisteredGenres;
    }

    internal static GenreRegistryCheck NoGenreRegistry { get; } =
        new(GenreRegistryCheckKind.NoRegistry, []);

    internal static GenreRegistryCheck Collected(ImmutableArray<string> unregisteredGenres)
    {
        if (unregisteredGenres.IsDefault)
        {
            throw new InvalidOperationException(
                "collected unregistered genres must be initialized");
        }

        return new GenreRegistryCheck(GenreRegistryCheckKind.Collected, unregisteredGenres);
    }

    internal GenreRegistryCheckKind Kind { get; }

    internal ImmutableArray<string> UnregisteredGenres { get; }
}

internal enum DigestionAtomStatusMarkerKind
{
    Absent,
    Valid,
    Malformed,
}

internal sealed record DigestionAtomStatusMarker(
    DigestionAtomStatusMarkerKind Kind,
    string? Status,
    string? Qualifier)
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    internal static readonly DigestionAtomStatusMarker Absent =
        new(DigestionAtomStatusMarkerKind.Absent, null, null);

    internal static DigestionAtomStatusMarker Parse(ReadOnlySpan<byte> atomBytes)
    {
        var atomText = StrictUtf8.GetString(atomBytes);
        if (!atomText.StartsWith("**", StringComparison.Ordinal))
        {
            return Absent;
        }

        var titleEnd = atomText.IndexOf("**", 2, StringComparison.Ordinal);
        if (titleEnd < 0)
        {
            return Absent;
        }

        var suffix = atomText.AsSpan(titleEnd + 2);
        var whitespaceLength = 0;
        while (whitespaceLength < suffix.Length && char.IsWhiteSpace(suffix[whitespaceLength]))
        {
            whitespaceLength++;
        }

        if (whitespaceLength >= suffix.Length || suffix[whitespaceLength] != '〔')
        {
            return Absent;
        }

        var markerStart = titleEnd + 3 + whitespaceLength;
        var markerEnd = atomText.IndexOf('〕', markerStart);
        var marker = markerEnd < 0 ? atomText[markerStart..] : atomText[markerStart..markerEnd];
        var namespaceMarker = marker.AsSpan().TrimStart();
        if (!namespaceMarker.StartsWith("closed", StringComparison.Ordinal)
            || (namespaceMarker.Length > "closed".Length
                && namespaceMarker["closed".Length] is not (';' or '；')
                && !char.IsWhiteSpace(namespaceMarker["closed".Length])))
        {
            return Absent;
        }

        var separator = marker.IndexOf(';', StringComparison.Ordinal);
        var status = separator < 0 ? marker : marker[..separator];
        var qualifier = separator < 0 ? null : marker[(separator + 1)..];
        var isPlainClosed = marker == "closed";
        var isQualifiedClosed = status == "closed"
            && separator == "closed".Length
            && marker.LastIndexOf(';') == separator
            && qualifier is not null
            && !string.IsNullOrWhiteSpace(qualifier);
        var kind = whitespaceLength == 0 && markerEnd >= 0 && (isPlainClosed || isQualifiedClosed)
            ? DigestionAtomStatusMarkerKind.Valid
            : DigestionAtomStatusMarkerKind.Malformed;
        return new DigestionAtomStatusMarker(kind, status, qualifier);
    }
}

internal sealed class AtomizedTheoryDocument
{
    internal AtomizedTheoryDocument(
        ImmutableArray<DigestionAtom> claims,
        ImmutableArray<DigestionSlice> slices,
        GenreRegistryCheck genreRegistryCheck)
        : this(claims, slices, [], genreRegistryCheck)
    {
    }

    internal AtomizedTheoryDocument(
        ImmutableArray<DigestionAtom> claims,
        ImmutableArray<DigestionSlice> slices,
        ImmutableArray<DigestionClausePlan> clausePlans,
        GenreRegistryCheck genreRegistryCheck)
    {
        ArgumentNullException.ThrowIfNull(genreRegistryCheck);
        Claims = claims;
        Slices = slices;
        ClausePlans = clausePlans;
        GenreRegistryCheck = genreRegistryCheck;
    }

    internal ImmutableArray<DigestionAtom> Claims { get; }

    internal ImmutableArray<DigestionSlice> Slices { get; }

    internal ImmutableArray<DigestionClausePlan> ClausePlans { get; }

    internal GenreRegistryCheck GenreRegistryCheck { get; }

    /// <summary>
    /// Genre tokens the volume used that its dialect does not register. The parser addresses
    /// such a claim by its own token rather than refusing it, so this is what carries the
    /// refusal to the layer that owns it: the ledger, which admits atoms, not the parser,
    /// which only reads them.
    /// </summary>
    internal ImmutableArray<string> UnregisteredGenres => GenreRegistryCheck.UnregisteredGenres;

    internal ImmutableArray<byte> Reassemble()
    {
        var length = Slices.Sum(static slice => slice.RawBytes.Length);
        var builder = ImmutableArray.CreateBuilder<byte>(length);
        foreach (var slice in Slices)
        {
            builder.AddRange(slice.RawBytes);
        }

        return builder.MoveToImmutable();
    }
}

internal static class DigestionFingerprint
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static DigestionFingerprints Compute(ReadOnlySpan<byte> rawBytes)
    {
        var raw = Sha256(rawBytes);
        var normalized = NormalizeText(rawBytes);
        return new DigestionFingerprints(raw, Sha256(StrictUtf8.GetBytes(normalized)));
    }

    internal static string NormalizeText(ReadOnlySpan<byte> rawBytes)
    {
        var text = StrictUtf8.GetString(rawBytes);
        if (text.StartsWith('\uFEFF'))
        {
            text = text[1..];
        }

        return text
            .Replace("\r\n", "\n", StringComparison.Ordinal)
            .Replace('\r', '\n')
            .Normalize(NormalizationForm.FormC);
    }

    internal static bool IsCanonicalSha256(string value) =>
        value.Length == 71
        && value.StartsWith("sha256:", StringComparison.Ordinal)
        && value.AsSpan(7).IndexOfAnyExcept("0123456789abcdef") < 0;

    internal static DigestionFingerprints ComputeOpaque(ReadOnlySpan<byte> rawBytes)
    {
        var raw = Sha256(rawBytes);
        return new DigestionFingerprints(raw, raw);
    }

    /// <summary>A short content address, for locators that have no readable text to slug.</summary>
    internal static string ShortHash(string value) =>
        Convert.ToHexStringLower(SHA256.HashData(StrictUtf8.GetBytes(value)))[..8];

    private static string Sha256(ReadOnlySpan<byte> bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));
}

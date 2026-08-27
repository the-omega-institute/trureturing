using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record DigestionFingerprints(string RawSha256, string NormalizedSha256);

internal sealed record DigestionContext(int Level, string Text);

internal sealed record DigestionAtom(
    string AstPath,
    int StartByte,
    int EndByte,
    ImmutableArray<byte> RawBytes,
    DigestionFingerprints Fingerprints,
    ImmutableArray<DigestionContext> Context,
    DigestionAtomStatusMarker StatusMarker)
{
    internal DigestionAtom(
        string astPath,
        int startByte,
        int endByte,
        ImmutableArray<byte> rawBytes,
        DigestionFingerprints fingerprints,
        ImmutableArray<DigestionContext> context)
        : this(astPath, startByte, endByte, rawBytes, fingerprints, context, DigestionAtomStatusMarker.Absent)
    {
    }

    internal static DigestionAtom FromFrozenCas(string astPath, ImmutableArray<byte> rawBytes) =>
        new(
            astPath,
            0,
            rawBytes.Length,
            rawBytes,
            DigestionFingerprint.Compute(rawBytes.AsSpan()),
            [],
            DigestionAtomStatusMarker.Parse(rawBytes.AsSpan()));
}

internal sealed record DigestionSlice(bool IsClaim, ImmutableArray<byte> RawBytes);

internal sealed record DigestionClausePlan(
    string ParentAstPath,
    ImmutableArray<DigestionAtom> Children);

internal static class UnregisteredGenreLocator
{
    internal const string Prefix = "unregistered/";

    internal static string ForToken(string token) =>
        Prefix + Uri.EscapeDataString(token);

    internal static string ForNumbered(string token, string number) =>
        ForToken(token) + "/" + number;

    internal static bool MatchesToken(string astPath, string token)
    {
        var tokenPath = ForToken(token);
        return string.Equals(astPath, tokenPath, StringComparison.Ordinal)
            || astPath.StartsWith(tokenPath + "/", StringComparison.Ordinal);
    }

    internal static bool TryGetToken(string astPath, out string token)
    {
        token = string.Empty;
        if (!astPath.StartsWith(Prefix, StringComparison.Ordinal))
        {
            return false;
        }

        var suffix = astPath[Prefix.Length..];
        var separator = suffix.IndexOf('/', StringComparison.Ordinal);
        var encoded = separator < 0 ? suffix : suffix[..separator];
        if (encoded.Length == 0)
        {
            return false;
        }

        token = Uri.UnescapeDataString(encoded);
        return token.Length > 0
            && string.Equals(Uri.EscapeDataString(token), encoded, StringComparison.Ordinal);
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

    internal DigestionAtom ResolveClaim(string astPath)
    {
        var exact = Claims
            .Concat(ClausePlans.SelectMany(static plan => plan.Children))
            .Where(atom => atom.AstPath == astPath)
            .ToArray();
        if (exact.Length == 1)
        {
            return exact[0];
        }

        var prefix = astPath + "/occurrence/";
        var qualified = Claims.Where(atom => atom.AstPath.StartsWith(prefix, StringComparison.Ordinal)).ToArray();
        return qualified.Length switch
        {
            1 => qualified[0],
            0 => throw new FormatException($"Markdown claim locator is absent: {astPath}"),
            _ => throw new FormatException($"ambiguous Markdown claim locator: {astPath}"),
        };
    }

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

/// <summary>The lead shape both numbered dialects share: <c>**&lt;genre&gt; &lt;number&gt;</c>.</summary>
internal sealed class NumberedClaims
{
    private static readonly Regex AnyNumberedLead = new(
        "^\\*\\*(?<kind>\\p{L}+)\\s*(?<number>[0-9]+\\.[0-9]+)",
        RegexOptions.CultureInvariant);

    private readonly ImmutableArray<AtomizerMapping> genres;
    private readonly Regex registered;
    private readonly SortedSet<string> unregistered = new(StringComparer.Ordinal);

    internal NumberedClaims(
        ImmutableArray<AtomizerMapping> genres,
        string numberPattern)
    {
        this.genres = genres;
        registered = new Regex(
            "^\\*\\*(?<kind>"
            + string.Join('|', genres.Select(static item => Regex.Escape(item.Token)))
            + ")\\s*(?<number>" + numberPattern + ")",
            RegexOptions.CultureInvariant);
    }

    /// <summary>Genre tokens seen on a claim lead that this dialect does not register.</summary>
    internal ImmutableArray<string> Unregistered => [.. unregistered];

    /// <summary>
    /// A registered token normalizes to its canonical kind; an unregistered one addresses the
    /// claim by its own words and is recorded. Refusing here would be the table acting as a
    /// gate on a document it does not own, and the cost is not small: one unwritten word
    /// replaces a whole volume with a single coarse atom.
    /// </summary>
    internal string? Identify(string paragraph)
    {
        var match = registered.Match(paragraph);
        if (match.Success)
        {
            return Kind(match.Groups["kind"].Value) + "/" + match.Groups["number"].Value;
        }

        var unknown = AnyNumberedLead.Match(paragraph);
        if (!unknown.Success)
        {
            return null;
        }

        var token = unknown.Groups["kind"].Value;
        unregistered.Add(token);
        return UnregisteredGenreLocator.ForNumbered(
            token,
            unknown.Groups["number"].Value);
    }

    private string Kind(string value) =>
        genres.FirstOrDefault(item => item.Token == value)?.Value
        ?? throw new InvalidOperationException($"unregistered kind reached Kind: {value}");
}

internal static class GictAtomizer
{
    private const string NumberPattern = "[0-9]+\\.[0-9]+";
    private static readonly Regex AppendixClaimPattern = new(
        "^\\*\\*(?<number>E\\.[0-9]+)\\s+[^\\r\\n*]+\\*\\*",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules)
    {
        // One instance per document rather than per paragraph: it accumulates the unregistered
        // tokens the volume used, and it owns a compiled regex worth building once.
        var claims = new NumberedClaims(rules.GictGenres, NumberPattern);
        return MarkdownAstAtomizer.Atomize(
            bytes,
            paragraph => Identify(paragraph, rules, claims),
            () => GenreRegistryCheck.Collected(claims.Unregistered),
            value => IdentifyConstant(value, rules));
    }

    private static string? Identify(string paragraph, TheoryAtomizerRules rules, NumberedClaims claims)
    {
        var appendix = AppendixClaimPattern.Match(paragraph);
        if (appendix.Success)
        {
            return "appendix/" + appendix.Groups["number"].Value;
        }

        return claims.Identify(paragraph)
            ?? rules.GictClaimPrefixes
                .FirstOrDefault(item => paragraph.StartsWith(item.Token, StringComparison.Ordinal))
                ?.Value;
    }

    private static string? IdentifyConstant(string value, TheoryAtomizerRules rules) =>
        rules.GictConstants.FirstOrDefault(item => item.Token == value)?.Value;

}

internal static class PeriodicTreeAtomizer
{
    private static readonly Regex SectionHeadingPattern = new(
        "^(?<number>[0-9]+)\\.\\s+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules _)
    {
        var document = MarkdownAstAtomizer.Atomize(
            bytes,
            static _ => null,
            static () => GenreRegistryCheck.NoGenreRegistry,
            identifyHeading: IdentifyHeading);
        if (document.Claims.Length > 0 || bytes.IsEmpty)
        {
            return document;
        }

        var rawBytes = ImmutableArray.CreateRange(bytes.ToArray());
        var atom = new DigestionAtom(
            "coarse/source",
            0,
            rawBytes.Length,
            rawBytes,
            DigestionFingerprint.ComputeOpaque(rawBytes.AsSpan()),
            []);
        return new AtomizedTheoryDocument(
            [atom],
            [new DigestionSlice(true, rawBytes)],
            GenreRegistryCheck.NoGenreRegistry);
    }

    private static string? IdentifyHeading(string heading)
    {
        var match = SectionHeadingPattern.Match(heading);
        return match.Success ? "section/" + match.Groups["number"].Value : null;
    }
}

internal static class PzgAtomizer
{
    private const string NumberPattern = "[0-9]+\\.[0-9]+(?:\\.[0-9]+)?[′″]*";
    private static readonly Regex OpenPattern = new(
        "^\\*\\*(?<id>O-[0-9]+)\\*\\*",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules)
    {
        // See GictAtomizer: one instance per document so unregistered tokens accumulate.
        var claims = new NumberedClaims(rules.PzgGenres, NumberPattern);
        var document = MarkdownAstAtomizer.Atomize(
            bytes,
            paragraph => Identify(paragraph, rules, claims),
            () => GenreRegistryCheck.Collected(claims.Unregistered),
            identifyHeading: heading => IdentifyHeading(heading, rules));
        return new AtomizedTheoryDocument(
            document.Claims,
            document.Slices,
            document.Claims
                .Select(PlanClauses)
                .Where(static plan => plan is not null)
                .Select(static plan => plan!)
                .ToImmutableArray(),
            document.GenreRegistryCheck);
    }

    // generic-v1 复用同一分解(GenericAtomizer.Atomize):子句语义跨方言一致,
    // 执法侧(RequireDecompositionBeforeNewAbsorption)对全部方言生效,生产侧也必须。
    internal static DigestionClausePlan? PlanClauses(DigestionAtom parent)
    {
        var text = Encoding.UTF8.GetString(parent.RawBytes.AsSpan());
        var lines = SourceLines(text);
        var explicitStarts = lines
            .Skip(1)
            .Where(static line => line.Text.StartsWith("**", StringComparison.Ordinal))
            .Select(static line => line.Start)
            .ToArray();
        int[] clauseStarts;
        if (explicitStarts.Length > 0)
        {
            clauseStarts = [0, .. explicitStarts];
        }
        else
        {
            var listStarts = lines
                .Where(static line => line.Text.StartsWith("- ", StringComparison.Ordinal)
                    || line.Text.StartsWith("* ", StringComparison.Ordinal))
                .Select(static line => line.Start)
                .ToArray();
            if (listStarts.Length < 2)
            {
                return null;
            }

            clauseStarts = [0, .. listStarts.Skip(1)];
        }

        var children = ImmutableArray.CreateBuilder<DigestionAtom>(clauseStarts.Length);
        for (var index = 0; index < clauseStarts.Length; index++)
        {
            var relativeStart = MarkdownAstAtomizer.ByteOffset(text, clauseStarts[index]);
            var relativeEnd = index + 1 == clauseStarts.Length
                ? parent.RawBytes.Length
                : MarkdownAstAtomizer.ByteOffset(text, clauseStarts[index + 1]);
            var childBytes = parent.RawBytes[relativeStart..relativeEnd];
            children.Add(new DigestionAtom(
                $"{parent.AstPath}/clause/{index + 1}",
                parent.StartByte + relativeStart,
                parent.StartByte + relativeEnd,
                childBytes,
                DigestionFingerprint.Compute(childBytes.AsSpan()),
                parent.Context,
                DigestionAtomStatusMarker.Parse(childBytes.AsSpan())));
        }

        return new DigestionClausePlan(parent.AstPath, children.MoveToImmutable());
    }

    private static ImmutableArray<PzgSourceLine> SourceLines(string text)
    {
        var lines = ImmutableArray.CreateBuilder<PzgSourceLine>();
        var offset = 0;
        while (offset < text.Length)
        {
            var lineEnd = text.IndexOfAny(['\r', '\n'], offset);
            if (lineEnd < 0)
            {
                lineEnd = text.Length;
            }

            var line = text[offset..lineEnd];
            var leadingWhitespace = line.Length - line.TrimStart().Length;
            if (!string.IsNullOrWhiteSpace(line))
            {
                lines.Add(new PzgSourceLine(offset + leadingWhitespace, line.TrimStart()));
            }

            while (lineEnd < text.Length && text[lineEnd] is '\r' or '\n')
            {
                lineEnd++;
            }

            offset = lineEnd;
        }

        return lines.ToImmutable();
    }

    private sealed record PzgSourceLine(int Start, string Text);

    private static string? Identify(string paragraph, TheoryAtomizerRules rules, NumberedClaims claims)
    {
        var trace = Regex.Match(
            paragraph,
            "^\\*\\*〔(?<number>[0-9]+\\.[0-9]+)\\s+"
                + Regex.Escape(rules.PzgMarkers["trace-note"]),
            RegexOptions.CultureInvariant);
        if (trace.Success)
        {
            return "trace-note/" + trace.Groups["number"].Value;
        }

        var open = OpenPattern.Match(paragraph);
        if (open.Success)
        {
            return "open/" + open.Groups["id"].Value;
        }

        return claims.Identify(paragraph);
    }

    private static string? IdentifyHeading(string heading, TheoryAtomizerRules rules)
    {
        var supplementPrefix = rules.PzgHeadingPrefixes
            .Single(item => item.Value == "metadata/supplement").Token;
        var supplement = Regex.Match(
            heading,
            "^" + Regex.Escape(supplementPrefix) + "\\s*(?<version>[0-9]+)\\s*版",
            RegexOptions.CultureInvariant);
        if (supplement.Success)
        {
            return "metadata/supplement/" + supplement.Groups["version"].Value;
        }

        var remark = rules.PzgGenres
            .Where(static item => item.Value == "remark")
            .Select(item => Regex.Match(
                heading,
                "^" + Regex.Escape(item.Token)
                    + "\\s+(?<range>[0-9]+\\.[0-9]+(?:[–—-][0-9]+\\.[0-9]+)?)",
                RegexOptions.CultureInvariant))
            .FirstOrDefault(static match => match.Success);
        if (remark is { Success: true })
        {
            return "remark/" + remark.Groups["range"].Value
                .Replace('–', '-')
                .Replace('—', '-');
        }

        return rules.PzgHeadingPrefixes
            .Where(static item => item.Value != "metadata/supplement")
            .FirstOrDefault(item => heading.StartsWith(item.Token, StringComparison.Ordinal))?.Value;
    }
}
